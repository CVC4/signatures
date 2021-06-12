# Lean checker

## Build

Run

```
leanpkg configure
leanpkg build bin LINK_OPTS=-rdynamic
```

## Check

For example:

$ time ./build/bin/Cdclt Cdclt/examples/tmpResult.lean

(this has the path to lean library harcoded and also required copying the directory of the siganuter olean files to root dir of the lean library)

## Lean File Structure
`Term.lean` contains the term structure.

`Boolean.lean` contains the Boolean rules including the resolution calculus and the CNF calculus.

`Euf.lean` contains the EUF (equality over uninterpreted functions) rules.

`BV.lean` contains the bit-vector proof calculus.

`Quant.lean` contains the quantifier rules.

`examples/` contains some small test files for the signatures.
