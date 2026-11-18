# Ascon ineffective-fault Section 3 codes using C 

Files:
- `ascon_common.h`: shared Ascon-128 v1.2 implementation and state helpers.
- `ascon_aead.c`: AEAD/KAT checker.
- `tables.c`: exhaustive S-box differential signatures and ineffective-fault distributions.

Build with GCC or Clang:
```sh
gcc ascon_aead.c -o ascon_aead
gcc tables.c -lm -o tables
gcc combined_analysis.c -o combined_analysis
```

Run:
```sh
./ascon_aead kat_ascon128v12.txt
./tables
./combined_analysis
```
