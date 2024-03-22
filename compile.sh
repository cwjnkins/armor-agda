#!/bin/bash
set -e

git submodule update --init
cd src/ && make && cd ..
