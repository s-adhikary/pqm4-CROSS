2025-03-18

- Removed asserts because
  1. This bricked qemu (not actually but made it hang)
  2. Other crypto sign implementations in pqm4 seem to avoid them
  3. They were superfluous, why not just early return?
- Made CROSS_verify return 1 as error and 0 as success explicitly, because you assume those are the case in sign.c:crytpo_sign_open
