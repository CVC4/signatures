# Lean checker

## Mathlib dependencies

Run

```
leanpkg add leanprover/mathlib
```

Note that you should have the Lean version from the [community
fork](https://github.com/leanprover-community/mathlib) in your path.

## Lean File Structure
`term.lean` contains the term structure.

`cdclt.lean` contains the Boolean rules including the resolution calculus and the CNF calculus.

`bv.lean` contains the bit-vector proof calculus.

`aux.lean` contains auxilary functions used by other files.

`examples.lean` contains some small test files for the signatures.