#!/bin/bash
MY_DIR="`dirname \"$0\"`"
MY_DIR=`realpath $MY_DIR`

echo %%%%%%%%%%%%%%%%%%%
echo % only signatures %
echo %%%%%%%%%%%%%%%%%%%
$MY_DIR/./simple.sh 

echo
echo %%%%%%%%%%%%%%%%%%%
echo % equality proofs %
echo %%%%%%%%%%%%%%%%%%%
$MY_DIR/./simple.sh $MY_DIR/../proofs/equality_proofs.plf

echo
echo %%%%%%%%%%%%%%%%%%%%%%
echo % quantifiers proofs %
echo %%%%%%%%%%%%%%%%%%%%%%
$MY_DIR/./simple.sh $MY_DIR/../proofs/quantifiers_proofs.plf

echo
echo %%%%%%%%%%%%%%%%%%%
echo % Booleans proofs %
echo %%%%%%%%%%%%%%%%%%%
$MY_DIR/./simple.sh $MY_DIR/../proofs/boolean_proofs.plf
