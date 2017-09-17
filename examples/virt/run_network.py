#!/usr/bin/python

#Copyrights (c) 2017. VMware, Inc. All right reserved. 
#
#Licensed under the Apache License, Version 2.0 (the "License");
#you may not use this file except in compliance with the License.
#You may obtain a copy of the License at
#
#    http://www.apache.org/licenses/LICENSE-2.0
#
#Unless required by applicable law or agreed to in writing, software
#distributed under the License is distributed on an "AS IS" BASIS,
#WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
#See the License for the specific language governing permissions and
#limitations under the License.

from mininet.net import Mininet
from mininet.topo import Topo
from mininet.log import setLogLevel, info
from mininet.cli import CLI
from mininet.link import TCLink
from mininet.node import Node

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
        self.addLink(vmname, hostname, intfName1='eth0',intfName2=ifname)
        self.get(hostname).attach(ifname)
        portnum = self.get(hostname).cmd(["ovs-vsctl", "get", "Interface", ifname, "ofport"])
        for off in ["rx", "tx", "sg"]:
            cmd = "/sbin/ethtool --offload eth0 %s off" % off
            print cmd
            h.cmd(cmd)
        print vmname + ": set IP address " + ip
        h.cmd("ifconfig eth0 " + ip)
        print vmname + ": set MAC address " + mac
        h.cmd("sudo ifconfig eth0 hw ether " + mac)
        h.cmd("sudo ifconfig lo up")
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

    cocoon("LogicalSwitch.put(LogicalSwitch{0})")
    net.addHV(1, "10.10.10.101")

    net.addVM(1, 1, '00:00:c6:e2:a3:01', "192.168.0.1")
    cocoon("LogicalPort.put(LogicalPort{0,0,1,48'h112233445566})")

    net.addVM(2, 1, '00:00:c6:e2:a3:02', "192.168.0.2")
    cocoon("LogicalPort.put(LogicalPort{1,0,2,48'h112233445577})")

    CLI(net)

    net.stop()


if __name__ == '__main__':
    setLogLevel( 'info' )
    main()
