#!/bin/bash
MY_DIR="`dirname \"$0\"`"
INPUT_PATH=`realpath $1`
cd $MY_DIR
cd ../signatures
lfscc \
  core_defs.plf \
  theory_def.plf \
  type_checking_programs.plf \
  boolean_programs.plf \
  boolean_rules.plf \
  cnf_rules.plf \
  equality_rules.plf \
  quantifiers_rules.plf \
  $INPUT_PATH

rlfsc \
  core_defs.plf \
  theory_def.plf \
  type_checking_programs.plf \
  boolean_programs.plf \
  boolean_rules.plf \
  cnf_rules.plf \
  equality_rules.plf \
  quantifiers_rules.plf \
  $INPUT_PATH


cd -
