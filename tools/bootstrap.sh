#!/bin/bash

# bootstrap a Cocoon network

set -x
set -e
THIS_DIR=$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )

source $THIS_DIR/../env.sh

filename=$(basename "$1")
specname="${filename%.*}"
dir=$(dirname "$1")
workdir=$dir/$specname

echo "Compiling $specname"

# kill cocoon controller and CLI (if any)
set +e
killall -qw -9 cocoon
set -e

(set +x; echo Generating  SQL schema)
$COCOON_PATH -i $1 --action=sql

(set +x; echo Generating Datalog rules)
$COCOON_PATH -i $1 --action=dl

(set +x; echo Initializing SQL DB)
psql -f $workdir/$specname.schema

(set +x; echo Compiling Datalog rules)
pushd $workdir
cargo build
pushd $popd

(set +x; echo Starting Cocoon controller)
$COCOON_PATH -i $1 --action=controller +RTS -xc -RTS


