## Update 2025-05-03

Memory is down to about 39% of reference. Now we need speed. We are losing reference in about
10% in signing sdp-1-small. Ideas:

1. DSP instructions for matrix/vector multiplication
  - Because we only have 32bit registers and we want 16 bit precision for the multiplication, we could do at most 2 at a time with parrallel. Not convinced there would be any speedup over O3 optim compile which is already using smulbb.
2. Packing unpacking DSP?





### sdp-5-small

==========================
keypair stack usage:
1392
sign stack usage:
573664
verify stack usage:
209224
Signature valid!

## MERKLE OPTIMISING

### flags as separate bytes vs bit optimisation

#### BITS

==========================
keypair cycles:
1674360
sign cycles:
506292504
verify cycles:
90492549


==========================
keypair stack usage:
1216
sign stack usage:
185288
verify stack usage:
83588
Signature valid!

#### BYTES

==========================
keypair cycles:
1674359
sign cycles:
506231851
verify cycles:
90489095

==========================
keypair stack usage:
1216
sign stack usage:
185288
verify stack usage:
83588
Signature valid!

### REF

==========================
keypair cycles:
1830358
sign cycles:
500320787
verify cycles:
90568481


==========================
keypair stack usage:
8632
sign stack usage:
424568
verify stack usage:
223928
Signature valid!

## Investigating CROSS_sign local variables

V_tr = 3876 bytes
e_bar = 127 bytes
root_seed = <16 bytes
seed_tree = 16624 bytes
round_seeds = 8320 bytes
e_bar_prime_i = 127 bytes
v_bar = 66040 bytes
u_prime = 66040 bytes
s_prime = 51 bytes
cmt_0_i_input = 125 bytes
offset_salt = <16 bytes
cmt_1_i_input = 48 bytes
merkle_tree_0 = 33248 bytes
csprng_state_cmt_1 = 208 bytes
cmt_1_i = 32 bytes
csprng_state_y = 208 bytes
dsc_ordered = <16 bytes
csprng_state = 208 bytes
digest_cmt0_cmt1 = 64 bytes
digest_msg_cmt_salt = 96 bytes
digest_chall_1 = 32 bytes
dsc_csprng_chall_1 = <16 bytes
chall_1 = 520 bytes
chall_2 = 520 bytes
published_rsps = <16 bytes



nucleo-l4r5zi details:
- 2Mb of flash memory

An improvement for benchmarking script could be using the built in MPU to
limit the stack region and put guards around it. Then you could detect when
the stack grows outside this region and exit.

To do this you would:
- Modify the linking script nucleo-l4r5zi.ld to define the stack region
- Use libopencm3 functions such as:
  - `mpu_enable()`
  - `mpu_disable()`
  - `mpu_set_region()`
  - `mpu_set_region_base_address()`
  - `mpu_set_region_attribute_size()`
- Define variables MPU defines like `MPU_RASR_ATTR_XN`, `MPU_RASR_AP_NO_ACCESS`, `MPU_RASR_SIZE_32B`, `MPU_CTRL_PRIVDEFENA`.
- Enable the fault with `scb_enable_memfault()`
- Implement fault handler `memmanage_handler()`
- Used `SCB_CFSR`, `SCB_MMFAR`, `SCB_CFSR_MMARVALID` from `scb.h` inside the handler.

Putting this off because it is low priority and just makes testing and benchmarking a bit faster/smoother.

Generated preliminary linker script to give an idea, see:

```ld
/* Linker script modified to explicitly define stack size */

/* Specify the minimum stack size */
/* !!! ADJUST THIS VALUE based on your application's actual requirements !!! */
/* Common starting points are 0x1000 (4KB), 0x2000 (8KB), or 0x4000 (16KB) */
_Min_Stack_Size = 0x4000; /* Example: 16KB - CHANGE AS NEEDED */

EXTERN(vector_table)
ENTRY(reset_handler)

MEMORY
{
  rom (rx)  : ORIGIN = 0x08000000, LENGTH = 2048K
  ram (rwx) : ORIGIN = 0x20000000, LENGTH = 640K
}

SECTIONS
{
  .text :
  {
    *(.vectors)
    . = ALIGN(448); /* Alignment specific to vector table handling */
    *(.text*)       /* .text sections (code) */
    *(.glue_7)      /* glue arm to thumb */
    *(.glue_7t)     /* glue thumb to arm */
    *(.eh_frame)    /* Required for C++ exceptions if enabled */

    KEEP (*(.init))
    KEEP (*(.fini))

    . = ALIGN(4);
    *(.rodata*)     /* .rodata sections (constants, strings, etc.) */
    . = ALIGN(4);
  } >rom

  .preinit_array :
  {
    . = ALIGN(4);
    __preinit_array_start = .;
    KEEP (*(.preinit_array))
    __preinit_array_end = .;
  } >rom

  .init_array :
  {
    . = ALIGN(4);
    __init_array_start = .;
    KEEP (*(SORT(.init_array.*)))
    KEEP (*(.init_array))
    __init_array_end = .;
  } >rom

  .fini_array :
  {
    . = ALIGN(4);
    __fini_array_start = .;
    KEEP (*(.fini_array))
    KEEP (*(SORT(.fini_array.*)))
    __fini_array_end = .;
  } >rom

  .ARM.extab : { *(.ARM.extab*) } >rom
  .ARM.exidx :
  {
    __exidx_start = .;
    *(.ARM.exidx*)
    __exidx_end = .;
  } >rom

  . = ALIGN(4);
  _etext = .; /* End address of code/read-only data in ROM */

  .data : /* Initialized data will be loaded from ROM to RAM */
  {
    _data = .; /* Start address of .data section in RAM */
    *(.data*)  /* .data sections */
    . = ALIGN(4);
    _edata = .; /* End address of .data section in RAM */
  } >ram AT>rom /* Place in RAM, Load from ROM */

  _data_loadaddr = LOADADDR(.data); /* Address where .data is stored in ROM */

  .bss : /* Uninitialized data */
  {
    _bss = .;  /* Start address of .bss section */
    *(.bss*)
    *(COMMON)
    . = ALIGN(4);
    _ebss = .; /* End address of .bss section */
  } >ram

  /* .heap section definition (optional but good practice) */
  /* Heap starts after .bss and grows towards the stack */
  . = ALIGN(8); /* Ensure heap is 8-byte aligned */
  _heap_start = .;
  /* The space available for heap is between _heap_start and _sstack */
  /* Malloc will manage this space. No explicit size needed here unless */
  /* using a static heap implementation. */

  /* User stack section */
  /* This section reserves space for the stack at the top of RAM */
  /* It defines _sstack (bottom) and _estack (top, initial SP) */
  .stack (NOLOAD) : ALIGN(8)
  {
    . = ALIGN(8); /* Ensure stack base is 8-byte aligned */
    _sstack = .;  /* Symbol for the bottom of the stack */
    . = . + _Min_Stack_Size; /* Reserve the stack space */
    . = ALIGN(8); /* Ensure stack top is 8-byte aligned */
    _estack = .;  /* Symbol for the top of the stack (initial SP value) */
  } >ram

  /* Check if stack overlaps with end of bss/start of heap */
  /* This helps catch configuration errors during linking */
  ASSERT(_sstack >= _ebss, "Error: Stack overlaps with .bss or static data!")
  ASSERT(_estack <= ORIGIN(ram) + LENGTH(ram), "Error: Stack extends beyond RAM!")

  end = _ebss; /* 'end' usually refers to end of static data for heap start */
  PROVIDE(_end = end);
  PROVIDE(end = .); /* Provide 'end' symbol used by some runtimes */

}

/* Remove the old PROVIDE(_stack = ...) line */
/* PROVIDE(_stack = ORIGIN(ram) + LENGTH(ram)); */ /* This is now handled by the .stack section */
```
