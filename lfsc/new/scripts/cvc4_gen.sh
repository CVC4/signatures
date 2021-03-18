#!/bin/bash

echo "=== Generate with CVC4 $@" 
cvc4 --dump-proofs --proof-format=lfsc $@
