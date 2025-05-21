#!/usr/bin/env bash

python3 ./benchmarks.py -p nucleo-l4r5zi --nosize --nohashing --nospeed -u /dev/ttyACM0 -t 30 -i 10
