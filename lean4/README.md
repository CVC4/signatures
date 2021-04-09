# Lean checker

## Build

Run

```
leanpkg build
```

## Lean File Structure
`Term.lean` contains the term structure.

`Boolean.lean` contains the Boolean rules including the resolution calculus and the CNF calculus.

`Euf.lean` contains the EUF (equality over uninterpreted functions) rules.

`BV.lean` contains the bit-vector proof calculus.

`Quant.lean` contains the quantifier rules.

`examples/` contains some small test files for the signatures.