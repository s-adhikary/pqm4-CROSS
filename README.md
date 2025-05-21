# LightCROSS

This is a project focusing on optimising the CROSS signature scheme. The framework is a modified fork
of pqm4, reduced to just the CROSS schemes.

It includes some quality of life scripts in `./scripts`, they all assume you are using the nucleo-l4r5zi
board.

## To Compile

```
./scrips/make.sh
```

## To Run

```
./scripts/load.sh <hex file path>
```

For example

```
./scripts/load.sh bin/mupq_crypto_sign_crossv2.0-sha3-r-sdpg-1-small_light_test.hex
```

## To Debug

Same as above but with `./scripts/debug.sh` then you can use `./scripts/gdb.sh` with the corresponding
elf file to connect to it.
