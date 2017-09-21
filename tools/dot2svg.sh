#!/bin/bash

# convert all dot files in a directory to svg

for f in $1/*.dot
do
    base="${f%.*}"
    dot -Tsvg $f > $base.svg
done
