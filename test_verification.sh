#!/bin/bash

THIS_DIR=$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )

source $THIS_DIR/env.sh

RED='\033[0;31m'
GREEN='\033[0;32m'
NC='\033[0m' # No Color

if [ $# -eq 0 ]
  then
    TESTS=(corporate.m4 nsdi_example simple-fat-tree vlan_virt.m4 vxlan_virt.m4 isdx.m4 stags b4 f10)
  else
    TESTS=($1)
fi


for t in ${TESTS[@]}; do
        printf "${GREEN}Starting test: ${t}${NC}\n"
        if [[ ${t} == *.m4 ]]
        then
            m4 -I examples examples/${t}.ccn > examples/${t%%.*}.ccn
        fi
        ${COCOON_PATH} -i examples/${t%%.*}.ccn -b 30 --boogie $2
        if [ $? -eq 0 ]
        then
            $THISDIR/tools/run_corral.sh examples/${t%%.*}/boogie
        fi
        printf "\n"
done
