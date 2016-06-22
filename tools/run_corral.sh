#!/bin/bash

RED='\033[0;31m'
GREEN='\033[0;32m'
NC='\033[0m' # No Color


for file in $1/*.bpl
do
    printf "Verifying $file "
    start=`date +%s`
    corral.exe "$file" /main:main /k:100 /recursionBound:10 /explainQuantifiers:${file}.smt2 &> "$file".log  
    #/proverLog:log 
    #/staticInlining
    #/z3opt:SMT.MBQI=true 
    ERR=$?
    end=`date +%s`
    runtime=$((end-start))
    if [ $ERR -eq 0 ]
    then
      if grep -q "Program has no bugs" "$file".log; then
          printf "${GREEN}OK (${runtime}s)${NC}\n"
      else
          printf "${RED}Bug found${NC}\n"
          cat "$file".log
          exit 1
      fi
    else
      printf "${RED}Failed (error code $?)${NC}\n" >&2
      cat "$file".log
      exit $ERR
    fi
done
