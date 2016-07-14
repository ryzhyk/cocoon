#!/bin/bash

ovs-vsctl --if-exists del-br cocoon
ovs-vsctl  add-br cocoon

for id in $(docker ps -q); do
    docker stop $id
done

for id in $(docker ps -a -q); do
    docker rm $id
done
