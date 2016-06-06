#!/bin/bash

THIS_DIR=$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )

source $THIS_DIR/env.sh

TESTS=(convergence b4 f10)

for t in ${TESTS[@]}; do
        ${COCOON_PATH} examples/${t}.ccn 10
        $THISDIR/tools/run_corral.sh examples/${t}/boogie
done
