#!/bin/bash

bin=$1

if [[ $1 == "-d" ]]; then
  D="-s -S"
  bin=$2
fi

qemu-system-arm $D -M mps2-an386 -nographic -semihosting -kernel $bin
