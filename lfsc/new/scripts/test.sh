#!/bin/bash
MY_DIR="`dirname \"$0\"`"
MY_DIR=`realpath $MY_DIR`
$MY_DIR/./simple.sh 
$MY_DIR/./simple.sh $MY_DIR/../proofs/equality_proofs.plf
$MY_DIR/./simple.sh $MY_DIR/../proofs/quantifiers_proofs.plf
$MY_DIR/./simple.sh $MY_DIR/../proofs/boolean_proofs.plf
