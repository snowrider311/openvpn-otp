#include <config.h>

#include <stdio.h>
#include <stdint.h>
#include <time.h>
#include <endian.h>
#include <string.h>
#include <ctype.h>
#include <inttypes.h>
#include <errno.h>
#include <json-c/json.h>

#ifndef htobe64
#include <netinet/in.h>
#endif

#include <openssl/evp.h>
#include <openssl/hmac.h>
#include <openssl/sha.h>

#ifdef HAVE_OPENVPN_OPENVPN_PLUGIN_H
#include "openvpn/openvpn-plugin.h"
#elif HAVE_OPENVPN_PLUGIN_H
#include "openvpn-plugin.h"
#endif

#include "base32.h"
#include "hex.h"
#define MAXWORDLEN 256

#include "openvpn-cr.h"


int record_successful_totp_event(const char *userId, const char *ip);
int is_new_totp_required(const char *userId, const char *ip);


static char *aws_credentials_file = "undefined";
static char *aws_region = "undefined";
static char *aws_dynamodb_table_name = "undefined";
static int otp_expiration_seconds = 60*60*24;

static char *otp_secrets = "/etc/ppp/otp-secrets";
static char *hotp_counters = "/var/spool/openvpn/hotp-counters/";
static int otp_slop = 180;

static int totp_t0 = 0;
static int totp_step = 30;
static int totp_digits = 6;

static int motp_step = 10;

static int hotp_syncwindow = 2;

static int debug = 0;

static int password_is_cr = 0;

typedef struct user_entry {
    char name[MAXWORDLEN];
    char server[MAXWORDLEN];
    char secret[MAXWORDLEN];
    char addr[MAXWORDLEN];
} user_entry_t;

typedef struct otp_params {
    const char *method;
    const char *hash;
    const char *encoding;
    const char *key;
    const char *pin;
    const char *udid;
} otp_params_t;

#define LOG(format, ...) logmessage(format, ## __VA_ARGS__)

#define DEBUG(format, ...) logdebug(format, ## __VA_ARGS__)

static void logmessage(const char *format, ...)
{
    va_list va;

    va_start(va, format);
    vfprintf(stderr, format, va);
    va_end(va);
}

static void logdebug(const char *format, ...)
{
    if (debug > 0) {
        va_list va;

        va_start(va, format);
        vfprintf(stderr, format, va);
        va_end(va);
    }
}

#ifndef htobe64

static uint64_t
htobe64(uint64_t value)
{
#if __BYTE_ORDER == __LITTLE_ENDIAN
    uint32_t low = htonl(value);
    uint32_t high = htonl(value >> 32);
    return (((uint64_t)low) << 32) | high;
#elif __BYTE_ORDER == __BIG_ENDIAN
    return value;
#else
#error "Unknown BYTE_ORDER"
#endif
}

#endif




static void
seek_eoln(FILE *secrets_file)
{
    while (!feof(secrets_file) && '\n' != fgetc(secrets_file)) {
        // Do nothing
    }
}


static int
read_word(FILE *secrets_file, char word[MAXWORDLEN])
{
    char ch = 0;
    char *p = word;
    char *q = word + MAXWORDLEN - 1;
    char quote = 0;

    while (!feof(secrets_file) && isspace((ch = fgetc(secrets_file)))) {
        // Do nothing
    }

    while (!feof(secrets_file)) {
        if (quote) {
            if (ch == quote) {
                quote = 0;
            }
            else {
                *p++ = ch;
            }
        }
        else if (isspace(ch) || '#' == ch) {
            *p = *q = 0;
            return ch;
        }
        else if ('\'' == ch || '"' == ch) {
            quote = ch;
        }
        else if ('\\' == ch) {
            *p = fgetc(secrets_file);
            if ('\n' != *p) {
                ++p;
            }
        }
        else {
            *p++ = ch;
        }

        if (p > q) {
            return -1;
        }

        ch = fgetc(secrets_file);
    }

    return -1;
}


static int
read_user_entry(FILE *secrets_file, user_entry_t *user_entry)
{
    int rc;

retry:
    if (feof(secrets_file)) {
        return -1;
    }

    rc = read_word(secrets_file, user_entry->name);
    if ('#' == rc || -1 == rc) {
        seek_eoln(secrets_file);
        goto retry;
    }

    if ('\n' == rc) {
        goto retry;
    }

    rc = read_word(secrets_file, user_entry->server);
    if ('#' == rc || -1 == rc) {
        seek_eoln(secrets_file);
        goto retry;
    }

    if ('\n' == rc) {
        goto retry;
    }

    rc = read_word(secrets_file, user_entry->secret);
    if ('#' == rc || -1 == rc) {
        seek_eoln(secrets_file);
        goto retry;
    }

    if ('\n' == rc) {
        goto retry;
    }

    rc = read_word(secrets_file, user_entry->addr);
    if (-1 == rc) {
        seek_eoln(secrets_file);
        goto retry;
    }

    if ('\n' != rc) {
        seek_eoln(secrets_file);
    }

    return 0;
}


static int
split_secret(char *secret, otp_params_t *otp_params)
{
    char *p = secret;

    otp_params->method = p;
    if (NULL == (p = strchr(p, ':'))) {
        return -1;
    }
    *p++ = 0;

    otp_params->hash = p;
    if (NULL == (p = strchr(p, ':'))) {
        return -1;
    }
    *p++ = 0;

    otp_params->encoding = p;
    if (NULL == (p = strchr(p, ':'))) {
        return -1;
    }
    *p++ = 0;

    otp_params->key = p;
    if (NULL == (p = strchr(p, ':'))) {
        return -1;
    }
    *p++ = 0;

    otp_params->pin = p;
    if (NULL != (p = strchr(p, ':'))) {
        *p++ = 0;
    }

    otp_params->udid = p;

    if (p && strchr(p, ':')) {
        return -1;
    }

    return 0;
}

static int
hotp_read_counter(const void * otp_key)
{
    /* Compute SHA1 for the otp_key */
    unsigned char hash[SHA_DIGEST_LENGTH];
    unsigned char hexdigest[SHA_DIGEST_LENGTH*2];
    char line[256];
    char path[256];
    FILE *counter_file;
    int i;

    SHA1(otp_key, strlen(otp_key), hash);

    for (i = 0; i < 20; i++) {
        sprintf(&hexdigest[i*2], "%02x", hash[i]);
    }
    snprintf(path, sizeof(path), "%s%s", hotp_counters, hexdigest);
    /* Find matching SHA1*/
    DEBUG("OTP-AUTH: opening HOTP counter file '%s'\n", path);
    counter_file = fopen(path, "r");
    if (counter_file != NULL) {
        if (fgets(line, sizeof(line), counter_file)) {
          fclose(counter_file);
          int ret = atoi(line);
          DEBUG("OTP-AUTH: current HOTP value is %i\n", ret);
          return atoi(line);
        }
        fclose(counter_file);
    }
    LOG("OTP-AUTH: failed to read HOTP counter file '%s'\n", path);
    return -1;
}

static int
hotp_set_counter(const void * otp_key, int counter)
{
    /* Compute SHA1 for the otp_key */
    unsigned char hash[SHA_DIGEST_LENGTH];
    unsigned char hexdigest[SHA_DIGEST_LENGTH*2];
    char line[256];
    char path[256];
    FILE *counter_file;
    int i;

    SHA1(otp_key, strlen(otp_key), hash);

    for (i = 0; i < 20; i++) {
        sprintf(&hexdigest[i*2], "%02x", hash[i]);
    }
    snprintf(path, sizeof(path), "%s%s", hotp_counters, hexdigest);

    /* Find matching SHA1*/
    DEBUG("OTP-AUTH: opening HOTP counter file '%s' for writing\n", path);
    counter_file = fopen(path, "w");
    if (counter_file != NULL) {
        DEBUG("OTP-AUTH: setting HOTP counter value to %i\n", counter);
        if (fprintf(counter_file, "%d", counter)) {
          fclose(counter_file);
          DEBUG("OTP-AUTH: HOTP counter update successful\n", counter);
          return 0;
        }
        fclose(counter_file);
    }
    LOG("OTP-AUTH: failed to write HOTP counter file '%s'\n", path);
    return -1;
}

/**
 * Verify user name and password
 */
static int otp_verify(const char *vpn_username, const char *vpn_secret)
{
    FILE *secrets_file;
    user_entry_t user_entry;
    otp_params_t otp_params;

    const EVP_MD *otp_digest;
    char secret[256];
    uint8_t decoded_secret[256];
    int i;
    int ok = 0;

    secrets_file = fopen(otp_secrets, "r");
    if (NULL == secrets_file) {
        LOG("OTP-AUTH: failed to open %s\n", otp_secrets);
        return ok;
    }

    DEBUG("OTP-AUTH: trying to authenticate username '%s'\n", vpn_username);

    while (!feof(secrets_file)) {
        if (read_user_entry(secrets_file, &user_entry)) {
            continue;
        }

        if (strcmp(vpn_username, user_entry.name)) {
            continue;
        }

        DEBUG("OTP-AUTH: username '%s' exists in '%s'\n", vpn_username, otp_secrets);

        /* Handle non-otp passwords before trying to parse out otp fields */
        if (!strncasecmp(user_entry.secret, "plain:", sizeof("plain:") - 1)) {
            const char *password = user_entry.secret + sizeof("plain:") - 1;
            if (vpn_username && !strcmp (vpn_username, user_entry.name)
                && vpn_secret && password && !strcmp (vpn_secret, password)) {
                ok = 1;
            }
            goto done;
        }

        if (split_secret(user_entry.secret, &otp_params)) {
            goto done;
        }

        otp_digest = EVP_get_digestbyname(otp_params.hash);
        if (!otp_digest) {
            LOG("OTP-AUTH: unknown digest '%s'\n", otp_params.hash);
            goto done;
        }

        unsigned int key_len;
        const void * otp_key;

        if (!strcasecmp(otp_params.encoding, "base32")) {
            key_len = base32_decode((uint8_t *) otp_params.key, decoded_secret, sizeof(decoded_secret));
            otp_key = decoded_secret;
        } else
        if (!strcasecmp(otp_params.encoding, "hex")) {
            key_len = hex_decode(otp_params.key, decoded_secret, sizeof(decoded_secret));
            otp_key = decoded_secret;
        } else
        if (!strcasecmp(otp_params.encoding, "text")) {
            otp_key = otp_params.key;
            key_len = strlen(otp_params.key);
        } else {
            LOG("OTP-AUTH: unknown encoding '%s'\n", otp_params.encoding);
            goto done;
        }
    
        uint64_t T, Tn, Ti;
        uint8_t mac[EVP_MAX_MD_SIZE];
        unsigned maclen;

        if (!strncasecmp("totp", otp_params.method, 4)) {
            HMAC_CTX hmac;
            const uint8_t *otp_bytes;
            uint32_t otp, divisor = 1;
            int tstep = totp_step;
            int tdigits = totp_digits;
            if (!strcasecmp("totp-60-6", otp_params.method)) {
                tstep = 60;
                tdigits = 6;
            }
            int range = otp_slop / tstep;


            T = (time(NULL) - totp_t0) / tstep;

            for (i = 0; i < tdigits; ++i) {
                divisor *= 10;
            }

            for (i = -range; !ok && i <= range; ++i) {
                Tn = htobe64(T + i);

                HMAC_CTX_init(&hmac);
                HMAC_Init(&hmac, otp_key, key_len, otp_digest);
                HMAC_Update(&hmac, (uint8_t *)&Tn, sizeof(Tn));
                HMAC_Final(&hmac, mac, &maclen);

                otp_bytes = mac + (mac[maclen - 1] & 0x0f);
                otp = ((otp_bytes[0] & 0x7f) << 24) | (otp_bytes[1] << 16) |
                    (otp_bytes[2] << 8) | otp_bytes[3];
                otp %= divisor;

                snprintf(secret, sizeof(secret), "%s%0*u", otp_params.pin, tdigits, otp);

                DEBUG("OTP-AUTH: trying method='%s', client_username='%s', client_secret='%s', server_username='%s', server_secret='%s'\n", otp_params.method, vpn_username, vpn_secret, user_entry.name, secret);

                if (vpn_username && !strcmp (vpn_username, user_entry.name)
                    && vpn_secret && !strcmp (vpn_secret, secret)) {
                    ok = 1;
                    DEBUG("OTP-AUTH: auth ok for method='%s', client_username='%s', client_secret='%s'\n", otp_params.method, vpn_username, vpn_secret);
                }
            }
        }
        else if (!strncasecmp("hotp", otp_params.method, 4)) {
            HMAC_CTX hmac;
            const uint8_t *otp_bytes;
            uint32_t otp, divisor = 1;
            int tdigits = totp_digits;
            int i = 0;

            i = hotp_read_counter(otp_params.key);

            if (i >= 0) {
              T = i;

              for (i = 0; i < tdigits; ++i) {
                  divisor *= 10;
              }

              for (i = 0; !ok && i <= hotp_syncwindow; i++) {
                  Ti = T+i;
                  Tn = htobe64(Ti);

                  HMAC_CTX_init(&hmac);
                  HMAC_Init(&hmac, otp_key, key_len, otp_digest);
                  HMAC_Update(&hmac, (uint8_t *)&Tn, sizeof(Tn));
                  HMAC_Final(&hmac, mac, &maclen);

                  otp_bytes = mac + (mac[maclen - 1] & 0x0f);
                  otp = ((otp_bytes[0] & 0x7f) << 24) | (otp_bytes[1] << 16) |
                         (otp_bytes[2] << 8) | otp_bytes[3];
                  otp %= divisor;

                  snprintf(secret, sizeof(secret), "%s%0*u", otp_params.pin, tdigits, otp);

                  DEBUG("OTP-AUTH: trying method='%s', client_username='%s', client_secret='%s', server_username='%s', server_secret='%s', hotp=%"PRIu64"\n", otp_params.method, vpn_username, vpn_secret, user_entry.name, secret, Ti);

                  if (vpn_username && !strcmp (vpn_username, user_entry.name)
                      && vpn_secret && !strcmp (vpn_secret, secret)) {
                      ok = 1;
                      DEBUG("OTP-AUTH: auth ok for method='%s', client_username='%s', client_secret='%s', hotp=%"PRIu64"\n", otp_params.method, vpn_username, vpn_secret, Ti);
                      hotp_set_counter(otp_params.key, Ti+1);
                  }
              }
            }
        }
        else if (!strcasecmp("motp", otp_params.method)) {
            char buf[64];
            int n;
            int range = otp_slop / motp_step;

            T = time(NULL) / motp_step;

            for (i = -range; !ok && i <= range; ++i) {
                EVP_MD_CTX ctx;
                EVP_MD_CTX_init(&ctx);
                EVP_DigestInit_ex(&ctx, otp_digest, NULL);
                n = sprintf(buf, "%" PRIu64, T + i);
                EVP_DigestUpdate(&ctx, buf, n);
                EVP_DigestUpdate(&ctx, otp_key, key_len);
                EVP_DigestUpdate(&ctx, otp_params.pin, strlen(otp_params.pin));
                if (otp_params.udid) {
                    int udid_len = strlen(otp_params.udid);
                    EVP_DigestUpdate(&ctx, otp_params.udid, udid_len);
                }
                EVP_DigestFinal_ex(&ctx, mac, &maclen);
                EVP_MD_CTX_cleanup(&ctx);

                snprintf(secret, sizeof(secret),
                         "%02x%02x%02x", mac[0], mac[1], mac[2]);

                DEBUG("OTP-AUTH: trying method='%s', client_username='%s', client_secret='%s', server_username='%s', server_secret='%s'\n", otp_params.method, vpn_username, vpn_secret, user_entry.name, secret);

                if (vpn_username && !strcmp (vpn_username, user_entry.name)
                    && vpn_secret && !strcmp (vpn_secret, secret)) {
                    ok = 1;
                    DEBUG("OTP-AUTH: auth ok for method='%s', client_username='%s', client_secret='%s'\n", otp_params.method, vpn_username, vpn_secret);
                }
            }
        }
        else {
            LOG("OTP-AUTH: unknown OTP method %s\n", otp_params.method);
        }

    done:
        memset(secret, 0, sizeof(secret));

    }

    if (NULL != secrets_file) {
        fclose(secrets_file);
    }

    return ok;
}


/*
 * Given an environmental variable name, search
 * the envp array for its value, returning it
 * if found or NULL otherwise.
 */
static const char * get_env (const char *name, const char *envp[])
{
  if (envp)
    {
      int i;
      const int namelen = strlen (name);
      for (i = 0; envp[i]; ++i)
        {
          if (!strncmp (envp[i], name, namelen))
            {
              const char *cp = envp[i] + namelen;
              if (*cp == '=')
                return cp + 1;
            }
        }
    }
  return NULL;
}


/*
 * Given an environment variable name, search the envp array for its value. If found, a string copy of that
 * value will be returned. Otherwise, a copy of default_value will be returned.
 *
 * This way, the caller is always responsible for freeing the memory allocated for the returned string.
 *
 * The final value of the environment variable is always logged.
 */
char *alloc_string_from_env(const char *envp[], const char *name, char *default_value) {
    const char *str_val = get_env(name, envp);
    char *rv = strdup(str_val ? str_val : default_value);
    LOG("OTP-AUTH: alloc_string_from_env: %s=%s\n", name, rv);
    return rv;
}


/*
 * Given an environment variable name, search the envp array for its value. If found, the value will be
 * converted to an int (if possible) and it will be returned. Otherwise, this is a no-op. In any case,
 * the value of the environment variable is logged, along with any conversion errors that might happen.
 */
int get_int_from_env(const char *envp[], const char *name, int default_value) {
    int rv = default_value;

    const char *in_str = get_env(name, envp);
    if (in_str) {
        char *end;
        
        errno = 0;
        
        long lnum = strtol(in_str, &end, 10);
        if (end == in_str) {
            LOG("OTP-AUTH: maybe_store_converted_int: Error: Can't convert '%s' to number\n", in_str);
        } else if ((lnum == LONG_MAX || lnum == LONG_MIN) && errno == ERANGE) {
            LOG("OTP-AUTH: maybe_store_converted_int: Error: Number '%s' out of range\n", in_str);
        } else if ((lnum > INT_MAX) || (lnum < INT_MIN)) {
            LOG("OTP-AUTH: maybe_store_converted_int: Error: Number '%s' out of range\n", in_str);
        } else {
            rv = (int) lnum;
        }
    }

    LOG("OTP-AUTH: get_int_from_env: %s=%ld\n", name, rv);
    return rv;
}


/**
 * Plugin open (init)
 */
OPENVPN_EXPORT openvpn_plugin_handle_t
openvpn_plugin_open_v1 (unsigned int *type_mask, const char *argv[], const char *envp[])
{
  OpenSSL_add_all_digests();

  /*
   * We are only interested in intercepting the
   * --auth-user-pass-verify callback.
   */
  *type_mask = OPENVPN_PLUGIN_MASK (OPENVPN_PLUGIN_AUTH_USER_PASS_VERIFY);


  /* Set up configuration variables */
    
  aws_credentials_file = alloc_string_from_env(argv, "aws_credentials_file", aws_credentials_file);
  aws_region = alloc_string_from_env(argv, "aws_region", aws_region);
  aws_dynamodb_table_name = alloc_string_from_env(argv, "aws_dynamodb_table_name", aws_dynamodb_table_name);
  otp_expiration_seconds = get_int_from_env(argv, "otp_expiration_seconds", otp_expiration_seconds);

  otp_secrets = alloc_string_from_env(argv, "otp_secrets", otp_secrets);
  hotp_counters = alloc_string_from_env(argv, "hotp_counters", hotp_counters);

  otp_slop = get_int_from_env(argv, "otp_slop", otp_slop);
  totp_t0 = get_int_from_env(argv, "totp_t0", totp_t0);
  totp_step = get_int_from_env(argv, "totp_step", totp_step);
  totp_digits = get_int_from_env(argv, "totp_digits", totp_digits);
  motp_step = get_int_from_env(argv, "motp_step", motp_step);
  hotp_syncwindow = get_int_from_env(argv, "hotp_syncwindow", hotp_syncwindow);
  password_is_cr = get_int_from_env(argv, "password_is_cr", password_is_cr);
  debug = get_int_from_env(argv, "debug", debug);

  if (debug) DEBUG("OTP_AUTH: debug mode has been enabled\n");

  return (openvpn_plugin_handle_t) otp_secrets;
}


/**
 * Check credentials
 */
OPENVPN_EXPORT int
openvpn_plugin_func_v1 (openvpn_plugin_handle_t handle, const int type, const char *argv[], const char *envp[])
{
  /* get username/password from envp string array */
  const char *username = get_env ("username", envp);
  const char *password = get_env ("password", envp);
  const char *ip = get_env ("untrusted_ip", envp);
  const char *port = get_env ("untrusted_port", envp);

  const int ulen = strlen(username);
  const int pwlen = strlen(password);
  if ( ulen > MAXWORDLEN || ulen == 0 || pwlen > MAXWORDLEN || pwlen == 0) {
	  return OPENVPN_PLUGIN_FUNC_ERROR;
  }

  const char *otp_password;
  openvpn_response resp;
  if (password_is_cr) {
	  char *parse_error;
	  if (!extract_openvpn_cr(password, &resp, &parse_error)) {
		  LOG("OTP-AUTH: Error extracting challenge/response. Parse error = '%s'\n", parse_error);
		  return OPENVPN_PLUGIN_FUNC_ERROR;
	  }
	  /*Take the response part, 'password' is for other authenticators*/
	  otp_password = (const char *)resp.response;
  }
  else {
	  otp_password = password;
  }

  int new_totp_required = is_new_totp_required(username, ip);
  LOG("OTP-AUTH: New TOTP required for remote [%s:%s]? %d\n", username, ip, new_totp_required);

  /* check entered username/TOTP against what we require */
  int ok = otp_verify(username, otp_password);

  if (ok == 1 || (strlen(otp_password) == 0 && new_totp_required == 0)) {
    if (ok == 1) {
        /* User may have entered a valid TOTP, even if not required. If so, let's record that event anyway
         * and reset the clock. */
        LOG("OTP-AUTH: authentication succeeded for username '%s', remote [%s:%s]\n", username, ip, port);
        record_successful_totp_event(username, ip);
    }
    return OPENVPN_PLUGIN_FUNC_SUCCESS;
  }
  else {
    LOG("OTP-AUTH: authentication failed for username '%s', remote [%s:%s]\n", username, ip, port);
    return OPENVPN_PLUGIN_FUNC_ERROR;
  }
}


/*
 * Reads the contents of a file into a string, which the caller is then responsible for freeing.
 */
char *read_file_contents(FILE *fp) {
    const int bufSize = 256;
    char buf[bufSize];
    
    char *str = NULL;
    char *temp = NULL;
    unsigned int size = 1;  // start with size of 1 to make room for null terminator
    unsigned int strlength;
    
    while (fgets(buf, sizeof(buf), fp) != NULL) {
        strlength = strlen(buf);
        temp = realloc(str, size + strlength);  // allocate room for the buf that gets appended
        if (temp == NULL) {
            // allocation error
        } else {
            str = temp;
        }
        strcpy(str + size - 1, buf);     // append buffer to str
        size += strlength;
    }
    
    return str;
}


/**
 * Records a successful TOTP login event in AWS DynamoDB. Returns 0 if this was successful, -1 if not.
 */
int record_successful_totp_event(const char *userId, const char *ip) {
    const char *cmdTemplate = "AWS_SHARED_CREDENTIALS_FILE='%s' aws dynamodb put-item --region=%s --table-name %s --item '%s'";
    
    time_t rawtime = time(NULL);
    char rawtime_str[32];
    sprintf(rawtime_str, "%ld", rawtime);

    struct json_object *rootJ = json_object_new_object();
    
    struct json_object *userIdJ = json_object_new_object();
    json_object_object_add(userIdJ, "S", json_object_new_string(userId));

    struct json_object *ipAddressJ = json_object_new_object();
    json_object_object_add(ipAddressJ, "S", json_object_new_string(ip));

    struct json_object *lastLoginJ = json_object_new_object();
    json_object_object_add(lastLoginJ, "N", json_object_new_string(rawtime_str));

    json_object_object_add(rootJ, "userId", userIdJ);
    json_object_object_add(rootJ, "ipAddress", ipAddressJ);
    json_object_object_add(rootJ, "lastLogin", lastLoginJ);
    
    const char *json_rep = json_object_to_json_string(rootJ);
    DEBUG("OTP-AUTH: record_successful_totp_event: JSON object: %s\n", json_rep);
    
    const int bufSize = 1024;
    char buf[bufSize];
    sprintf(buf, cmdTemplate, aws_credentials_file, aws_region, aws_dynamodb_table_name, json_rep);
    LOG("OTP-AUTH: record_successful_totp_event: Command: %s\n", buf);

    json_object_put(rootJ); // Delete the json object
    
    FILE *fp;
    if ((fp = popen(buf, "r")) == NULL) {
        LOG("OTP-AUTH: record_successful_totp_event: Error opening pipe!\n");
        return -1;
    }
    
    char *str = read_file_contents(fp);
    LOG("OTP-AUTH: record_successful_totp_event: Command OUTPUT: %s\n", str);
    free(str);
    
    if (pclose(fp)) {
        LOG("OTP-AUTH: record_successful_totp_event: Error: Command not found or exited with error status\n");
        LOG("OTP-AUTH: Failed to record TOTP success event\n");
        return -1;
    }
    
    return 0;
}


/*
 * Given a JSON string (generally returned from a call to Amazon DynamoDB), parse it and determine if too much time
 * has passed since the user last submitted a valid TOTP token. Return 1 if that's the case, 0 if not, and
 * -1 in the error case.
 */
int has_too_much_time_elapsed(const char *str) {
    int64_t last_login_time = 0;
    time_t rawtime = time(NULL);
    
    if (!str || !strlen(str)) return -1;
    struct json_object *jobj = json_tokener_parse(str);
    if (!jobj) return -1;
    
    struct json_object *target1 = NULL;
    struct json_object *target2 = NULL;
    struct json_object *target3 = NULL;
    
    if (json_object_object_get_ex(jobj, "Item", &target1)) {
        if (json_object_object_get_ex(target1, "lastLogin", &target2)) {
            if (json_object_object_get_ex(target2, "N", &target3)) {
                last_login_time = json_object_get_int64(target3);
                LOG("OTP-AUTH: has_too_much_time_elapsed: Last login: %ld. Current time: %ld. Diff: %ld, Max-Allowed-Diff: %ld\n",
                    last_login_time, rawtime, rawtime-last_login_time, otp_expiration_seconds);
            }
        }
    }
    
    if (!last_login_time) {
        LOG("OTP-AUTH: has_too_much_time_elapsed: No previous login record found.");
    }
    
    /* release memory used for JSON objects */
    json_object_put(jobj);
    json_object_put(target1);
    json_object_put(target2);
    json_object_put(target3);
    
    return rawtime - last_login_time > otp_expiration_seconds;
}


/*
 * Determine if too much time has elapsed since the user last entered a valid TOTP. Return 1 if so,
 * -1 on an error condition, and 0 otherwise (i.e. user doesn't need to enter a new TOTP).
 */
int is_new_totp_required(const char *userId, const char *ip) {
    const char *cmdTemplate = "AWS_SHARED_CREDENTIALS_FILE=%s aws dynamodb --region=%s get-item --table-name %s --key '%s'";
    
    struct json_object *rootJ = json_object_new_object();
    
    struct json_object *userIdJ = json_object_new_object();
    json_object_object_add(userIdJ, "S", json_object_new_string(userId));
    
    struct json_object *ipAddressJ = json_object_new_object();
    json_object_object_add(ipAddressJ, "S", json_object_new_string(ip));
    
    json_object_object_add(rootJ, "userId", userIdJ);
    json_object_object_add(rootJ, "ipAddress", ipAddressJ);

    const char *json_rep = json_object_to_json_string(rootJ);
    DEBUG("OTP-AUTH: is_new_totp_required: JSON object: %s\n", json_rep);
    
    const int bufSize = 1024;
    char buf[bufSize];
    sprintf(buf, cmdTemplate, aws_credentials_file, aws_region, aws_dynamodb_table_name, json_rep);
    LOG("OTP-AUTH: is_new_totp_required: Command: %s\n", buf);

    json_object_put(rootJ); /* Free JSON object */

    FILE *fp;
    if ((fp = popen(buf, "r")) == NULL) {
        LOG("OTP-AUTH: is_new_totp_required: Error opening pipe!\n");
        return -1;
    }
    
    char *str = read_file_contents(fp);
    DEBUG("OTP-AUTH: is_new_totp_required: Command OUTPUT: %s\n", str);
    int rv = has_too_much_time_elapsed(str);
    free(str);
    
    if (pclose(fp)) {
        LOG("OTP-AUTH: is_new_totp_required: Error: Command not found or exited with error status\n");
        return -1;
    }
    
    return rv;
}


/**
 * Plugin close
 */
OPENVPN_EXPORT void
openvpn_plugin_close_v1 (openvpn_plugin_handle_t handle)
{
}
