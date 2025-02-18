#!/bin/bash
set -e

home=~/

git submodule update --init --remote
cd agda-stdlib
git checkout v1.7.1
cd ..
cd src/ && make all && cd ..

cd hacl-star-verified/
cc -I /$home/hacl-star/dist/gcc-compatible -I /$home/hacl-star/dist/karamel/include/ -I /$home/hacl-star/dist/karamel/krmllib/dist/minimal/ -c -o /$home/.armor/ecdsa_P256_verify.o ecdsa_P256_verify.c
cc -I /$home/hacl-star/dist/gcc-compatible -I /$home/hacl-star/dist/karamel/include/ -I /$home/hacl-star/dist/karamel/krmllib/dist/minimal/ -c -o /$home/.armor/hash.o hash.c
cc /$home/.armor/ecdsa_P256_verify.o /$home/hacl-star/dist/gcc-compatible/libevercrypt.a /$home/.opam/default/lib/krml/dist/generic/libkrmllib.a -o /$home/.armor/ecdsa_P256_verify.exe
cc /$home/.armor/hash.o /$home/hacl-star/dist/gcc-compatible/libevercrypt.a /$home/.opam/default/lib/krml/dist/generic/libkrmllib.a -o /$home/.armor/hash.exe
cd ..