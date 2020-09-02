# Proof Signatures

This repository contains the proof signatures for CVC4.

## Testing

### Testing LFSC Signatures

#### Running Tests

`make test` runs all LFSC tests. `make <test name>` runs a single test, for
example `make drat_test`.

#### Adding a New Signature Test

To add a new signature test file, create a new file in `test/lfsc` and add it
to git, for example:

```
git add test/lfsc/new_signature_test.plf
```

Also add it to the `LFSC_TESTS` variable in [Makefile](Makefile) in the root
directory and declare the dependencies of the test as explained below.

Tests can declare the signature files that they depend on using the `; Deps:`
directive followed by a space-separated list of files. For example:

```
; Deps: sat.plf smt.plf
```

indicates that the test depends on `sat.plf` and `smt.plf`. The run script
automatically searches for the listed files in `lfsc` as well as the directory
of the test input.
