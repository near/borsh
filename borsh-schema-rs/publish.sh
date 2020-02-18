#!/usr/bin/env bash
set -ex
for p in borsh-schema-derive-internal borsh-schema-derive borsh-schema
do
pushd ./${p}
cargo publish
popd
# Sleep a bit to let the previous package upload to crates.io. Otherwise we fail publishing checks.
sleep 10
done

