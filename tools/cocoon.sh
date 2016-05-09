#!/bin/bash

THIS_DIR=$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )

source $THIS_DIR/../env.sh

P4C_BM_SCRIPT=$P4C_BM_PATH/p4c_bm/__main__.py

SWITCH_PATH=$BMV2_PATH/targets/simple_switch/simple_switch

CLI_PATH=$BMV2_PATH/tools/runtime_CLI.py

sudo mn -c

sudo PYTHONPATH=$PYTHONPATH:$BMV2_PATH/mininet/ python $THIS_DIR/run_network.py \
    --behavioral-exe $SWITCH_PATH \
    --cocoon $COCOON_PATH \
    --spec $1 \
    --cfg $2 \
    --cli $CLI_PATH \
    --p4c $P4C_BM_SCRIPT \
    --miniedit $MINIEDIT_PATH
