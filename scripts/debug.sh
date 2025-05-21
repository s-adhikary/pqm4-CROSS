#!/usr/bin/env bash

echo $#

if [[ $# -ne 1 ]]; then
  echo "Pass a hex file to load."
  exit -1
fi

# Compile the hex file
make -j`nproc` PLATFORM=nucleo-l4r5zi DEBUG=1 $1
#make -j`nproc` PLATFORM=nucleo-l4r5zi $1

# Program the board
openocd -f st_nucleo_l4r5.cfg -c "program ${1} verify reset exit"
openocd -f st_nucleo_l4r5.cfg
