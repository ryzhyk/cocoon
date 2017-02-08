#!/bin/sh

GREEN='\033[0;32m'
NC='\033[0m' # No Color


echo "method n time" > cocoon.txt
for n in $(seq 1 40)
do
    printf "${GREEN}Testing for n=${n}${NC}\n"
    python tools/gen_purdue.py  --export_cocoon examples/corporate.cfg.ccn  3 $n $n $n $n
    begin=$(date +%s)
    time ./test_assumptions.sh corporate.m4
    end=$(date +%s)
    tottime=$(expr $end - $begin)
    echo "cocoon $n $tottime" >> cocoon.txt
done
