#!/bin/bash

set -e
THIS_DIR=$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )

source $THIS_DIR/../../env.sh

COCOON_PATH=$COCOON_PATH ./run_network.py
