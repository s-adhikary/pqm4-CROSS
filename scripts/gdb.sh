#!/usr/bin/env bash

arm-none-eabi-gdb -ex "target extended-remote :3333" $1
