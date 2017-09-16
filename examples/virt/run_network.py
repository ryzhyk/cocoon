#!/usr/bin/python

# Based on the topo.py script from the P4 tutorial

# Copyright 2013-present Barefoot Networks, Inc. 
# 
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
# 
#    http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

from mininet.net import Mininet
from mininet.topo import Topo
from mininet.log import setLogLevel, info
from mininet.cli import CLI
from mininet.link import TCLink
from mininet.node import Node
from mininet.node import OVSKernelSwitch
import json

import argparse
from time import sleep
import os
import signal
import subprocess
import time
import sys

#_THIS_DIR = os.path.dirname(os.path.realpath(__file__))

#print os.environ

cocoon_path = os.environ["COCOON_PATH"]

parser = argparse.ArgumentParser(description='Mininet demo')
parser.add_argument('--topology', help='MiniEdit topology file',
                    type=str, action="store", required=False)

args = parser.parse_args()

class LinuxRouter( Node ):
    "A Node with IP forwarding enabled."

    def config( self, **params ):
        super( LinuxRouter, self).config( **params )
        # Enable forwarding on the router
        self.cmd( 'sysctl net.ipv4.ip_forward=1' )

    def terminate( self ):
        self.cmd( 'sysctl net.ipv4.ip_forward=0' )
        super( LinuxRouter, self ).terminate()

#class MyTopo(Topo):
#    def __init__(self, topology, **opts):
#        # Initialize topology and default options
#        Topo.__init__(self, **opts)
#
#        router = LinuxRouter( Node )
#
#        for sw in topology['switches']:
#            hostname = sw['opts']['hostname']
#            switch = self.addSwitch(hostname)
#
#        for h in topology['hosts']:
#            host = self.addHost(h['opts']['hostname'])
#
#        for link in topology['links']:
#            self.addLink(link['src'], link['dest'], port1 = link['srcport'], port2 = link['destport'])

#def updateConfig(cocoon, loadedTopology):
#    # send signal to the cocoon process
#    cocoon.stdin.write("update\n")
#
#    # read output until magic line appears
#    while cocoon.poll() == None:
#        line = cocoon.stdout.readline()
#        sys.stdout.write("cocoon: " + line)
#        if line == "Network configuration complete\n":
#            break
#
#    if cocoon.poll() != None:
#        raise Exception(args.cocoon + " terminated with error code " + str(cocoon.returncode))
#
#def applyConfig(loadedTopology, netdir, netname, oldts):
#    # re-apply switch configuration files whose timestamps are newer than the previous timestamp
#    for sw in loadedTopology['switches']:
#        hostname = sw['opts']['hostname']
#        sleep(1)
#        cmd = [args.cli, "--json", os.path.join(netdir, netname) + '.' + hostname + '.' + 'json',
#               "--thrift-port", str(_THRIFT_BASE_PORT + sw['opts']['nodeNum'])]
#        swcfgpath = os.path.join(netdir, netname) + '.' + hostname + '.' + 'txt'
#        if os.path.getmtime(swcfgpath) > oldts:
#            with open(swcfgpath, "r") as f:
#                print " ".join(cmd)
#                try:
#                    p = subprocess.Popen(cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
#                    output, err = p.communicate("reset_state")
#                    print output
#                    output = subprocess.check_output(cmd, stdin = f)
#                    print output
#                except subprocess.CalledProcessError as e:
#                    print e
#                    print e.output
#    sleep(1)


def cocoon(cmd):
    ccn_cmd = [cocoon_path, "-i", "virt.ccn", "--action=cmd"]
    print " ".join(ccn_cmd) + " " + cmd
    try:
        p = subprocess.Popen(ccn_cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        output, err = p.communicate(cmd)
        print output
    except subprocess.CalledProcessError as e:
        print e
        print e.output


class VNet (Mininet):

    def addHV(self, hostid, hostip):
        hostname = "h" + str(hostid)
        s = self.addSwitch(hostname)
        s.start([])
        s.cmd(["ovs-vsctl", "set", "bridge", hostname, "protocols=OpenFlow15"])
        cocoon("Hypervisor.put(Hypervisor{" + str(hostid) + ", false, \"" + hostname + "\", \"\"})")
        return

    def delHost(self, hostid):
        return

    def addVM(self, vmid, host, mac, ip):
        vmname = "vm" + str(vmid)
        hostname = "h" + str(host)
        h = self.addHost(vmname)
        ifname = hostname + "-" + vmname
        self.addLink(vmname, hostname, intfName2=ifname)
        self.get(hostname).attach(ifname)
        portnum = self.get(hostname).cmd(["ovs-vsctl", "get", "Interface", ifname, "ofport"])
        for off in ["rx", "tx", "sg"]:
            cmd = "/sbin/ethtool --offload eth0 %s off" % off
            print cmd
            h.cmd(cmd)
        print hostname + ": set IP address " + ip
        h.cmd("ifconfig eth0 " + ip)
        print hostname + ": set MAC address " + mac
        h.cmd("sudo ifconfig eth0 hw ether " + mac)
        print "disable ipv6"
        h.cmd("sysctl -w net.ipv6.conf.all.disable_ipv6=1")
        h.cmd("sysctl -w net.ipv6.conf.default.disable_ipv6=1")
        h.cmd("sysctl -w net.ipv6.conf.lo.disable_ipv6=1")
        h.cmd("sysctl -w net.ipv4.tcp_congestion_control=reno")
        h.cmd("ifconfig eth0 promisc")
        h.cmd("iptables -I OUTPUT -p icmp --icmp-type destination-unreachable -j DROP")
        cocoon("HypervisorPort.put(HypervisorPort{" + str(vmid) + "," + str(portnum) + "," + str(host) + "})")
        return

    def delVM(self, vmid):
        return

def main():

    cocoon(":connect")
    # Create empty topology with Linux router
    topo = Topo()
    router = topo.addNode('r0', cls=LinuxRouter)
    net = VNet(topo=topo, controller = None)
    net.start()

    CLI(net)

    net.stop()

    # configure hosts
#    for n in loadedTopology['hosts']:
#        hostname = n['opts']['hostname']
#        h = net.get(hostname)
#        for off in ["rx", "tx", "sg"]:
#            cmd = "/sbin/ethtool --offload eth0 %s off" % off
#            print cmd
#            h.cmd(cmd)
#        if 'ip4' in n['opts']:
#            ip = n['opts']['ip4']
#            print hostname + ": set IP address " + ip
#            h.cmd("ifconfig eth0 " + ip)
#        if 'mac' in n['opts']:
#            mac = n['opts']['mac']
#            print hostname + ": set MAC address " + mac
#            h.cmd("sudo ifconfig eth0 hw ether " + mac)
#        print "disable ipv6"
#        h.cmd("sysctl -w net.ipv6.conf.all.disable_ipv6=1")
#        h.cmd("sysctl -w net.ipv6.conf.default.disable_ipv6=1")
#        h.cmd("sysctl -w net.ipv6.conf.lo.disable_ipv6=1")
#        h.cmd("sysctl -w net.ipv4.tcp_congestion_control=reno")
#        h.cmd("ifconfig eth0 promisc")
#        h.cmd("iptables -I OUTPUT -p icmp --icmp-type destination-unreachable -j DROP")

if __name__ == '__main__':
    setLogLevel( 'info' )
    main()
