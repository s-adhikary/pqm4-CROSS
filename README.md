This repository contains two folders, pqm4-CROSS-balanced-small and pqm4-CROSS-fast. Our paper "LightCROSS: A Secure and Memory Optimized Post-Quantum Digital Signature CROSS" describes the implementation.  

  

## Setup 

Our code uses the [pqm4](https://github.com/mupq/pqm4) framework to test and benchmark on the [NUCLEO-L4R5ZI](https://www.st.com/en/evaluation-tools/nucleo-l4r5zi.html) board. So, we refer to the [pqm4](https://github.com/mupq/pqm4) documentation for the required essentials. 

  

All the `fast` (or `balance` and `small`) parameters of CROSS can be run using the following comments: 

Enter in the folder "pqm4-CROSS-fast" (or pqm4-CROSS-balanced-small) 

```c 

		cd pqm4-CROSS-fast (or cd pqm4-CROSS-balanced-small) 

		``` 

Compile the codes 

```c 

		sudo make clean  

		``` 

```c 

		sudo make -j4 PLATFORM=nucleo-l4r5zi 

		``` 

Benchmark on the NUCLEO-L4R5ZI board 

```c 

		sudo python3 benchmarks.py --platform nucleo-l4r5zi 

		``` 

```c 

		sudo python3 convert_benchmarks.py md 

		``` 
