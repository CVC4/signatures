#!/bin/bash

echo "=== Generate with CVC4 $@" 
cvc4 --dump-proofs --proof-format=lfsc $@ > temp.txt
tail -n +2 "temp.txt" > proof.plf
echo "=== End generate with CVC4" 

./lfsc_check.sh proof.plf
