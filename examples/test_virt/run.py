#!/usr/bin/python

import subprocess 
import argparse
import re
import os
import sys

parser = argparse.ArgumentParser(description='Start virtual network testbed')
parser.add_argument('--prefix', help='IP4 prefix of the private vagrant network',
                    type=str, default="192.168", action="store", required=False)
parser.add_argument('--hostvms', help='VMs per host',
                    type=int, default=2, action="store", required=False)

args = parser.parse_args()



def cmd(c):
    print c
    res = subprocess.check_output(c, shell=True).strip()
    print res
    return res

def cmd_async(c):
    print c
    p = subprocess.Popen(c, shell=True)
    if p.poll() != None:
        raise Exception(c + " terminated with error code " + str(p.returncode))
    return p


def vmcmd(h, c):
    return cmd("vagrant ssh " + h + " -- sudo -s -- " + c)

def vmcmd_async(h, c):
    return cmd_async("vagrant ssh " + h + " -- sudo -s -- " + c)


def ovs_portnum(h, pname):
    port_desc = filter(lambda k: pname in k, vmcmd(h, "ovs-ofctl dump-ports-desc cocoon").split("\n"))
    if len(port_desc) != 1:
        print "Unexpected number of OVS port descriptors found: " + str(len(port_desc))
        sys.exit(-1)
    # Obtain OVS port numbers docker's are attached to
    return int(re.findall(r"[\w']+", port_desc[0])[0])

def cocoon_config(hosts, tunnels, vms):
    iL2VNet    = "function iL2VNet(VNetId id): bool = id == 16'd1"
    iHost      = "function iHost(HostId hst): bool = " + " or ".join(map(lambda (i,(h,a,swid)): "hst == 48'd" + str(swid), enumerate(hosts)))
    iVHost     = "function iVHost(VHostId id): bool = " + " or ".join(map(lambda (i,_): "id == 32'd" + str(i), enumerate(vms)))
    iVHostPort = "function iVHostPort(VHPortId port): bool = iVHost(port.vhost) and port.vport == 8'd0"
    vHPortVNet = "function vHPortVNet(VHPortId port): VNetId = 16'd1"
    vHPort2Mac = "function vHPort2Mac(VHPortId port): MAC = case {\n" + \
                 "\n".join(map(lambda (i,(h,p,mac)): "        port.vhost == 32'd" + str(i) + " and port.vport == 8'd0: 48'h" + "".join(mac.split(":")) + ";", enumerate(vms))) + \
                 "\n        default: 48'h0;\n    }"
    mac2VHPort = "function mac2VHPort(VNetId vnet, MAC mac): VHPortId = case {\n" + \
                 "\n".join(map(lambda (i,(h,p,mac)): "        vnet == 16'd1 and mac == 48'h" + "".join(mac.split(":")) + ": VHPortId{32'd" + str(i) + ", 8'd0};", enumerate(vms))) + \
                 "\n        default: VHPortId{32'hffffffff, 8'hff};\n    }"
    hostIP     = "function hostIP(HostId hst): IP4 = case {\n" + \
                 "\n".join(map(lambda (_,(h,addr,swid)): "        hst == 48'd" + str(swid) + ": 32'h" + "".join(map(lambda x: "{0:0{1}x}".format(int(x),2), addr.split("."))) + ";", enumerate(hosts))) + \
                 "\n        default: 32'h0;\n    }"
    iVSwitchPort = "function iVSwitchPort(HostId hst, uint<16> swport): bool = " + \
                 " or ".join(map(lambda (i,(h,p,mac)): "(hst == 48'd" + str(h) + " and swport == 16'd" + str(p) + ")", enumerate(vms)))
    vHostLocation = "function vHostLocation(VHostId vhost): HostId = case {\n" + \
                    "\n".join(map(lambda (i,(h,p,mac)): "        vhost == 32'd" + str(i) + ": 48'd" + str(h) + ";", enumerate(vms))) + \
                    "\n        default: 48'd0;\n    }"
    vH2SwLink  = "function vH2SwLink(VHPortId hport): uint<16> = case {\n" + \
                 "\n".join(map(lambda (i,(h,p,mac)): "        hport == VHPortId{32'd" + str(i) + ", 8'd0}: 16'd" + str(p) + ";", enumerate(vms))) + \
                 "\n        default: 16'd0;\n    }"
    vSw2HLink  = "function vSw2HLink(HostId hst, uint<16> swport): VHPortId = case {\n" + \
                 "\n".join(map(lambda (i,(h,p,mac)): "        hst == 48'd" + str(h) + " and swport == 16'd" + str(p) + ": VHPortId{32'd" + str(i) + ", 8'd0};", enumerate(vms))) + \
                 "\n        default: VHPortId{32'd0, 8'd0};\n    }"
    iVHostPPort = "function iVHostPPort(VHPortId port): bool = false"
    iVSwitchPPort = "function iVSwitchPPort(HostId hst, uint<16> swport): bool = false"
    iTunPort    = "function iTunPort(HostId hst, uint<16> port): bool = " +\
                  " or ".join(map(lambda (hst, htunnels): " or ".join(map(lambda (rhst, port): "(hst == 48'd" + str(hst) + " and port == 16'd" + str(port) + ")", htunnels.iteritems())), tunnels.iteritems()))
    tunPort     = "function tunPort(HostId hst, HostId rhst): uint<16> = case {\n" + \
                  "\n".join(map(lambda (hst, htunnels): "\n".join(map(lambda (rhst, port): "        hst == 48'd" + str(hst) + " and rhst == 48'd" + str(rhst) + ": 16'd" + str(port) + ";", htunnels.iteritems())), tunnels.iteritems())) + \
                  "\n        default: 16'd0;\n    }"
    portTun     = "function portTun(HostId hst, uint<16> port): HostId = case {\n" + \
                  "\n".join(map(lambda (hst, htunnels): "\n".join(map(lambda (rhst, port): "        hst == 48'd" + str(hst) + " and port == 16'd" + str(port) + ": 48'd" + str(rhst) + ";", htunnels.iteritems())), tunnels.iteritems())) + \
                  "\n        default: 48'd0;\n    }"
    hHostsVNet = "function hHostsVNet(HostId hst, VNetId vnet): bool = true"
    connection = "function connection(VHPortId from, VHPortId to): bool = true"
    return "\n".join([iL2VNet, iHost, iVHost, iVHostPort, vHPortVNet,  \
                      vHPort2Mac, mac2VHPort, hostIP, iVSwitchPort,  \
                      vHostLocation, vH2SwLink, vSw2HLink, iVHostPPort,  \
                      iVSwitchPPort, iTunPort, tunPort, portTun, hHostsVNet, connection])

try:
    curdir = os.path.dirname(os.path.realpath(sys.argv[0]))

    res = cmd("vagrant up")
    #list vagrant vm's => Generate the list of hosts.
    res = cmd("vagrant status")
    hosts = map(lambda k: k.split()[0], filter(lambda k: 'running' in k, res.split('\n')))
    print "Vagrant hosts:" + str(hosts)

    #get vagrant VM IP addresses and switch id's
    host_addr = dict()
    host_swid = dict()
    for h in hosts:
        vmcmd(h, "/vagrant/cleanvms.sh")
        print "Querying IP address of " + h
        res = vmcmd(h, "ifconfig | awk '/inet addr/{print substr($2,6)}' | grep " + args.prefix)
        ips = res.split()
        if len(ips) == 0:
            print "No IP addresses starting with " + args.prefix + " found"
            sys.exit(-1)
        print "Address found: " + ips[0]
        host_addr[h] = ips[0]
        res = vmcmd(h, "ovs-ofctl show cocoon")
        host_swid[h] = int(re.search('dpid:(.+?)\n', res).group(1), 16)
        print "Switch ID: " + str(host_swid[h])
        

    # Start frenetic controller on the first host
    vmcmd_async(hosts[0], "/frenetic/_build/frenetic/frenetic.native  http-controller --verbosity debug --openflow-port 6653")

    #print "Address dictionary:" + str(host_addr)

    tunnels = dict()
    vms = []
    for hidx, h in enumerate(hosts):
        #start docker VM's inside vagrant VMs 
        for i in range(1,args.hostvms+1):
            print "Starting VM " + str(i) + " on " + h
            pid = vmcmd(h, "/vagrant/startvm.sh " + str(hidx) + " " + str(i))
            vm = "vm" + str(i)
            port = ovs_portnum(h, vm + "_ovs")
            #mac = re.findall(r"\w\w:\w\w:\w\w:\w\w:\w\w:\w\w$", port_desc[0])[0]
            print "OVS port number: " + str(port)
            mac = re.findall(r"\w\w:\w\w:\w\w:\w\w:\w\w:\w\w", vmcmd(h, "ip netns exec " + pid + " ip link show eth0"))[0]
            print "Container's MAC address: " + mac
            vms.append((host_swid[h],port,mac))
        # build vxlan tunnels
        tunnels[host_swid[h]] = dict()
        for rhidx, rhst in enumerate(hosts):
            if rhst == h:
                continue
            iface = "vx" + rhst
            vmcmd(h, "ovs-vsctl add-port cocoon " + iface + " -- set interface " + iface + " type=vxlan options:remote_ip=" + host_addr[rhst])
            port = ovs_portnum(h, iface)
            print "OVS tunnel port number: " + str(port)
            tunnels[host_swid[h]][host_swid[rhst]] = port
        vmcmd(h, "ovs-vsctl set-controller cocoon tcp:" + host_addr[hosts[0]] + ":6653")

    cfg = cocoon_config(map(lambda h: (h, host_addr[h], host_swid[h]), hosts), tunnels, vms)
    print "Writing cocoon configuration file"
    f = open(curdir + '/../vlan_virt.cfg.ccn', 'w')
    f.write(cfg)

    # generate NetKAT policy

    # verify generated configuration

    # Feed NetKAT policy to controller
except subprocess.CalledProcessError as e:
    print e
    print e.output
