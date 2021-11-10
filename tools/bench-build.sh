#!/bin/sh

if [ ! -d '.git' ]; then
    echo "ERROR: must be run from repository root" 1>&2
    exit 1
fi

time sh -c 'for i in $(seq 1 25); do rm -rf target/ && cargo build -q || exit 1; done'