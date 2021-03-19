# Lean checker

## Build

Run

```
leanpkg build
```

## Lean File Structure
`term.lean` contains the term structure.

`cdclt.lean` contains the Boolean rules including the resolution calculus and the CNF calculus.

`bv.lean` contains the bit-vector proof calculus.

`aux.lean` contains auxilary functions used by other files.

`examples.lean` contains some small test files for the signatures.