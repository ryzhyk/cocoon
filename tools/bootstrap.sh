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

(set +x; echo Generating  SQL schema)
$COCOON_PATH -i $1 --action=sql

(set +x; echo Generating Datalog rules)
$COCOON_PATH -i $1 --action=dl

if (( $# > 1 )) && [ $2 = "nodl" ];
then
    (set +x; echo Skipping Datalog compilation)
else
    (set +x; echo Compiling Datalog rules)
    pushd $workdir
    cargo build
    pushd $popd
fi

# kill cocoon controller and CLI (if any)
set +e
sudo killall -qw -9 cocoon
set -e

(set +x; echo Initializing SQL DB)
set +e
sudo sudo -u postgres createuser -d root
set -e

sudo psql postgres -f $workdir/$specname.schema

(set +x; echo Starting Cocoon controller)
sudo $COCOON_PATH -i $1 --action=controller
