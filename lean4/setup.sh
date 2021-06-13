#!/bin/bash

leanpkg configure
leanpkg build bin LINK_OPTS=-rdynamic
rm -rf ~/.elan/toolchains/leanprover-lean4-nightly-2021-04-27/lib/lean/Cdclt/
cp -r build/Cdclt ~/.elan/toolchains/leanprover-lean4-nightly-2021-04-27/lib/lean/
