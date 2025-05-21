#!/usr/bin/env bash


PLAT=nucleo-l4r5zi
if [[ $QEMU -eq 1 ]]; then
  PLAT=mps2-an386
fi

DEB=$DEBUG

TARGET=$1

make -j`nproc` PLATFORM=$PLAT DEBUG=$DEB $TARGET
