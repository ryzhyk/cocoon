#!/usr/bin/python

import subprocess 
import argparse
import re


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

def vmcmd(h, c):
    return cmd("vagrant ssh " + h + " -- sudo -s -- " + c)

def ovs_portnum(h, pname):
    port_desc = filter(lambda k: pname in k, vmcmd(h, "ovs-ofctl dump-ports-desc cocoon").split("\n"))
    if len(port_desc) != 1:
        print "Unexpected number of OVS port descriptors found: " + str(len(port_desc))
        sys.exit(-1)
    # Obtain OVS port numbers docker's are attached to
    return int(re.findall(r"[\w']+", port_desc[0])[0])

def cocoon_config(hosts, tunnels, vms):
    iL2VNet    = "function iL2VNet(VNetId id): bool = id == 16'd1"
    iHost      = "function iHost(HostId hst): bool = " + " or ".join(map(lambda (i,_): "hst == 48'd" + str(i), enumerate(hosts)))
    iVHost     = "function iVHost(VHostId id): bool = " + " or ".join(map(lambda (i,_): "id == 32'd" + str(i), enumerate(vms)))
    iVHostPort = "function iVHostPort(VHPortId port): bool = iVHost(port.vhost) and port.vport == 8'd0"
    vHPortVNet = "function vHPortVNet(VHPortId port): VNetId = 16'd1"
    vHPort2Mac = "function vHPort2Mac(VHPortId port): MAC = case {\n" + \
                 "\n".join(map(lambda (i,(h,p,mac)): "        port.vhost == 32'd" + str(i) + " and port.vport == 8'd0: 48'h" + "".join(mac.split(":")[::-1]) + ";", enumerate(vms))) + \
                 "\n        default: 48'h0;\n    }"
    mac2VHPort = "function mac2VHPort(VNetId vnet, MAC mac): VHPortId = case {\n" + \
                 "\n".join(map(lambda (i,(h,p,mac)): "        vnet == 16'd1 and mac == 48'h" + "".join(mac.split(":")) + ": VHPortId{32'd" + str(i) + ", 8'd0};", enumerate(vms))) + \
                 "\n        default: VHPortId{32'hffffffff, 8'hff};\n    }"
    hostIP     = "function hostIP(HostId hst): IP4 = case {\n" + \
                 "\n".join(map(lambda (i,(h,addr)): "        hst == 48'd" + str(i) + ": 32'h" + "".join(addr.split(".")) + ";", enumerate(hosts))) + \
                 "\n        default: 32'h0;\n    }"
    iVSwitchPort = "function iVSwitchPort(HostId hst, uint<16> swport): bool = " + \
                 " or ".join(map(lambda (i,(h,p,mac)): "(hst == 48'd" + str(h) + " and swport == 16'd" + str(p) + ")", enumerate(vms)))
    vHostLocation = "function vHostLocation(VHostId vhost): HostId = case {\n" + \
                    "\n".join(map(lambda (i,(h,p,mac)): "        vhost == 16'd" + str(i) + ": 48'd" + str(h) + ";", enumerate(vms))) + \
                    "\n        default: 48'd0;\n    }"
    vH2SwLink  = "function vH2SwLink(VHPortId hport): uint<16> = case {\n" + \
                 "\n".join(map(lambda (i,(h,p,mac)): "        hport == VHPortId{32'd" + str(i) + ", 8'd0}: 16'd" + str(p) + ";", enumerate(vms))) + \
                 "\n        default: 16'd0;\n    }"
    vSw2HLink  = "function vSw2HLink(HostId hst, uint<16> swport): VHPortId = case {\n" + \
                 "\n".join(map(lambda (i,(h,p,mac)): "        hst == 48'd" + str(h) + " and swport == 16'd" + str(p) + ": VHPortId{32'd" + str(i) + ", 8'd0};", enumerate(vms))) + \
                 "\n        default: VHPortId{32'd0, 8'd0};\n    }"
    iVHostPPort = "function iVHostPPort(VHPortId port): bool = false"
    iVSwitchPPort = "function iVSwitchPPort(HostId hst, uint<16> swport): bool = false "
    return "\n".join([iL2VNet, iHost, iVHost, iVHostPort, vHPortVNet, vHPort2Mac, mac2VHPort, hostIP, iVSwitchPort, vHostLocation, vH2SwLink, vSw2HLink, iVHostPPort, iVSwitchPPort])

try:
    res = cmd("vagrant up")

    #list vagrant vm's => Generate the list of hosts.
    res = cmd("vagrant status")
    hosts = map(lambda k: k.split()[0], filter(lambda k: 'running' in k, res.split('\n')))
    print "Vagrant hosts:" + str(hosts)

    #get vagrant VM IP addresses
    host_addr = dict()
    for h in hosts:
        print "Querying IP address of " + h
        res = vmcmd(h, "ifconfig | awk '/inet addr/{print substr($2,6)}' | grep " + args.prefix)
        ips = res.split()
        if len(ips) == 0:
            print "No IP addresses starting with " + args.prefix + " found"
            sys.exit(-1)
        print "Address found:" + ips[0]
        host_addr[h] = ips[0]

    #print "Address dictionary:" + str(host_addr)

    tunnels = dict()
    vms = []
    for hidx, h in enumerate(hosts):
        vmcmd(h, "/vagrant/cleanvms.sh")
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
            vms.append((hidx,port,mac))
        # build vxlan tunnels
        tunnels[h] = dict()
        for rhidx, rhst in enumerate(hosts):
            if rhst == h:
                continue
            iface = "vx" + rhst
            vmcmd(h, "ovs-vsctl add-port cocoon " + iface + " -- set interface " + iface + " type=vxlan options:remote_ip=" + host_addr[rhst])
            port = ovs_portnum(h, iface)
            print "OVS tunnel port number: " + str(port)
            tunnels[h][rhst] = port
    cfg = cocoon_config(map(lambda h: (h, host_addr[h]), hosts), tunnels, vms)
    print cfg
except subprocess.CalledProcessError as e:
    print e
    print e.output


