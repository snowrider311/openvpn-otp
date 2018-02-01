#! /bin/bash

apt-get update
apt-get -y install openvpn autoconf libtool libssl-dev libjson0 libjson0-dev make
./autogen.sh
./configure --with-openvpn-plugin-dir=/usr/lib/openvpn --prefix=/usr
make
make install
