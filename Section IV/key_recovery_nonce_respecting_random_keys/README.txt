Ascon-128 v1.2 nonce-respecting key recovery (random keys) using software fault-injection experiment

Files
-----
key_recovery_nonce_respecting.c  Attack experiment and target-side oracle.
ascon_common.h                   Local Ascon-128 v1.2 primitive and AEAD code.

Build
---------------------------
gcc key_recovery_nonce_respecting.c -o attack

Run 100 trials
--------------
./attack 100