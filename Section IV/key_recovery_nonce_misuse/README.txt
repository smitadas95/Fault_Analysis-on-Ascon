Ascon-128 v1.2 key recovery nonce-misuse software fault-injection experiment

Files
-----
key_recovery_nonce_misuse.c  Attack experiment and target-side oracle.
ascon_common.h                   Ascon-128 v1.2 primitive and AEAD code.

Build
---------------
gcc  key_recovery_nonce_misuse.c -o attack

Run 100 trials
--------------
./attack 100
