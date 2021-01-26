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

`aux.lean` contains auxilary functions used by other files.

`smt.lean` contains the Boolean rules including the resolution calculus and the CNF calculus.

`examples.lean` contains some small test files for the signatures.