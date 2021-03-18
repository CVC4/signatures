#!/bin/bash

echo "=== Check with lfsc $@"

SIGDIR=../signatures
LFSCDIR=~/lfsc/git/cmake/src

cat $@ | grep WARNING

CHECK=$(cat $@ | grep check)

[ -z "$CHECK" ] && echo "; WARNING: Empty proof!!!"

$LFSCDIR/lfscc $SIGDIR/core_defs.plf $SIGDIR/util_defs.plf $SIGDIR/theory_def.plf $SIGDIR/type_checking_programs.plf $SIGDIR/nary_programs.plf $SIGDIR/boolean_programs.plf 
$SIGDIR/boolean_rules.plf $SIGDIR/cnf_rules.plf $SIGDIR/equality_rules.plf $SIGDIR/arith_programs.plf $SIGDIR/arith_rules.plf $SIGDIR/strings_programs.plf $SIGDIR/strings_rules.plf $SIGDIR/quantifiers_rules.plf $@ >& temp-lfsc.txt

# recover macros for applications of arity 1,2,3, and simplify builtin syntax for constants
#sed -i 's/(f_ite [^ \)]*)/f_ite/g' temp-lfsc.txt
sed -i 's/(\\ [^ ]* (\\ [^ ]* (\\ [^ ]* (apply (apply (apply f_\([^ ]*\) [^ ]*) [^ ]*) [^ ]*))))/\1/g; s/(\\ [^ ]* (\\ [^ ]* (apply (apply f_\([^ ]*\) [^ ]*) [^ ]*)))/\1/g; s/(\\ [^ ]* (apply f_\([^ ]*\) [^ ]*))/\1/g; s/(var \([^ ]*\) [^ \)]*)/var_\1/g; s/(int \([^ \)]*\))/\1/g; s/emptystr/""/g; s/int\.//g' temp-lfsc.txt

cat temp-lfsc.txt

rm temp-lfsc.txt

echo "=== Finshed check with lfsc"
