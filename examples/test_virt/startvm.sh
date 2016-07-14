#!/bin/bash

VM=vm${1}
CONTAINER_ID=`docker run -dti --net=none --name=$VM testvm /bin/bash`
PID=`docker inspect -f {{.State.Pid}} ${CONTAINER_ID}`
mkdir -p /var/run/netns
ln -s /proc/$PID/ns/net /var/run/netns/$PID

ip link add ${VM}_ovs type veth peer name ${VM}_vm
ip link set ${VM}_vm netns $PID
ip netns exec $PID ip link set dev ${VM}_vm name eth0
ip netns exec $PID ip link set eth0 up
ip netns exec $PID ip addr add 192.168.${1}.${2}/16 dev eth0
ip netns exec $PID ip route add default via 192.168.${1}.${2}
ovs-vsctl add-port cocoon ${VM}_ovs
