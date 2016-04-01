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
import json

from p4_mininet import P4Switch, P4Host

import argparse
from time import sleep
import os
import signal
import subprocess
import time
import sys

_THIS_DIR = os.path.dirname(os.path.realpath(__file__))
_THRIFT_BASE_PORT = 22222

parser = argparse.ArgumentParser(description='Mininet demo')
parser.add_argument('--behavioral-exe', help='Path to behavioral executable',
                    type=str, action="store", required=True)
parser.add_argument('--spec', help='Path to NetKAT+ spec file',
                    type=str, action="store", required=True)
parser.add_argument('--cfg', help='Path to NetKAT+ config file',
                    type=str, action="store", required=True)
parser.add_argument('--cli', help='Path to BM CLI',
                    type=str, action="store", required=True)
parser.add_argument('--nkp', help='Path to NetKAT+ compiler',
                    type=str, action="store", required=True)
parser.add_argument('--miniedit', help='Path to the MiniEdit tool',
                    type=str, action="store", required=False)
parser.add_argument('--p4c', help='Path to P4C-to-json compiler',
                    type=str, action="store", required=True)

args = parser.parse_args()

class MyTopo(Topo):
    def __init__(self, sw_path, topology, netname, netdir, **opts):
        # Initialize topology and default options
        Topo.__init__(self, **opts)

        thrift_port = _THRIFT_BASE_PORT

        for sw in topology['switches']:
            hostname = sw['opts']['hostname']
            switch = self.addSwitch(hostname,
                                    sw_path     = " ".join([sw_path, "-L", "trace", "--log-file", os.path.join("/tmp", netname) + '.' + hostname + '.' + 'log']),
                                    json_path   = os.path.join(netdir, netname) + '.' + hostname + '.' + 'json',
                                    thrift_port = _THRIFT_BASE_PORT + sw['opts']['nodeNum'],
                                    log_file    = os.path.join("/tmp", netname) + '.' + hostname + '.' + 'log',
                                    pcap_dump   = False,
                                    device_id   = sw['opts']['nodeNum'])

        for h in topology['hosts']:
            host = self.addHost(h['opts']['hostname'])

        for link in topology['links']:
            self.addLink(link['src'], link['dest'], port1 = link['srcport'], port2 = link['destport'])

def updateConfig(nkp, loadedTopology):
    # send signal to the netkat+ process
    nkp.stdin.write("update\n")

    # read output until magic line appears
    while nkp.poll() == None:
        line = nkp.stdout.readline()
        sys.stdout.write("netkat+: " + line)
        if line == "Network configuration complete\n":
            break

    if nkp.poll() != None:
        raise Exception(args.nkp + " terminated with error code " + str(nkp.returncode))

def applyConfig(loadedTopology, netdir, netname, oldts):
    # re-apply switch configuration files whose timestamps are newer than the previous timestamp
    for sw in loadedTopology['switches']:
        hostname = sw['opts']['hostname']
        sleep(1)
        cmd = [args.cli, "--json", os.path.join(netdir, netname) + '.' + hostname + '.' + 'json',
               "--thrift-port", str(_THRIFT_BASE_PORT + sw['opts']['nodeNum'])]
        swcfgpath = os.path.join(netdir, netname) + '.' + hostname + '.' + 'txt'
        if os.path.getmtime(swcfgpath) > oldts:
            with open(swcfgpath, "r") as f:
                print " ".join(cmd)
                try:
                    p = subprocess.Popen(cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
                    output, err = p.communicate("reset_state")
                    print output
                    output = subprocess.check_output(cmd, stdin = f)
                    print output
                except subprocess.CalledProcessError as e:
                    print e
                    print e.output
    sleep(1)

def main():

    oldts = time.time()

    # Start the NetKAT+ process.  Wait for it to generate network topology,
    # and leave it running for future network updates
    cmd = [args.nkp, args.spec, args.cfg]
    print " ".join(cmd)
    nkp = subprocess.Popen(cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    while nkp.poll() == None:
        line = nkp.stdout.readline() # This blocks until it receives a newline.
        sys.stdout.write("netkat+: " + line)
        if line == "Network configuration complete\n":
            break

    if nkp.poll() != None:
        raise Exception(args.nkp + " terminated with error code " + str(nkp.returncode))


    specdir, specfname = os.path.split(args.spec)
    netname, specext = os.path.splitext(specfname)
    netdir = os.path.join(specdir, netname)
    mnfname = os.path.join(netdir, netname+".mn")

    with open(mnfname, 'r') as handle:
        parsed = json.load(handle)
        indented = json.dumps(parsed, indent=4)

    with open(mnfname, 'w') as handle:
        handle.write(indented)

    if args.miniedit != None:
        cmd = [args.miniedit, "-f", mnfname]
    subprocess.Popen(cmd)

    print "Loading network topology from " + mnfname 
    mnfile = open(mnfname, "r")
    loadedTopology = json.load(mnfile)

    # convert .p4 switches to json
    for sw in loadedTopology['switches']:
        hostname = sw['opts']['hostname']
        cmd = [args.p4c, 
               os.path.join(netdir, netname) + '.' + hostname + '.' + 'p4', 
               "--json", os.path.join(netdir, netname) + '.' + hostname + '.' + 'json']
        print " ".join(cmd)
        subprocess.check_call(cmd)

    # build mininet topology
    topo = MyTopo(args.behavioral_exe, loadedTopology, netname, netdir)

    net = Mininet(topo = topo,
                  host = P4Host,
                  switch = P4Switch,
                  controller = None )
    net.start()

    # configure hosts
    for n in loadedTopology['hosts']:
        hostname = n['opts']['hostname']
        h = net.get(hostname)
        ip = n['opts']['ip4']
        for off in ["rx", "tx", "sg"]:
            cmd = "/sbin/ethtool --offload eth0 %s off" % off
            print cmd
            h.cmd(cmd)
        print hostname + ": set IP address " + ip
        h.cmd("ifconfig eth0 " + ip)
        print "disable ipv6"
        h.cmd("sysctl -w net.ipv6.conf.all.disable_ipv6=1")
        h.cmd("sysctl -w net.ipv6.conf.default.disable_ipv6=1")
        h.cmd("sysctl -w net.ipv6.conf.lo.disable_ipv6=1")
        h.cmd("sysctl -w net.ipv4.tcp_congestion_control=reno")
        h.cmd("iptables -I OUTPUT -p icmp --icmp-type destination-unreachable -j DROP")

    sleep(1)

    newts = oldts
    applyConfig(loadedTopology, netdir, netname, oldts)
    oldts = newts
    while True:
        CLI( net )
        updateConfig(nkp, loadedTopology)
        newts = time.time()
        applyConfig(loadedTopology, netdir, netname, oldts)
        oldts = newts

    net.stop()

if __name__ == '__main__':
    setLogLevel( 'info' )
    main()
