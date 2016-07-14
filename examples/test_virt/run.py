#!/usr/bin/python

import subprocess 
import argparse


parser = argparse.ArgumentParser(description='Start virtual network testbed')
parser.add_argument('--prefix', help='IP4 prefix of the private vagrant network',
                    type=str, default="192.168", action="store", required=False)
parser.add_argument('--hostvms', help='VMs per host',
                    type=int, default=2, action="store", required=False)

args = parser.parse_args()



def cmd(c):
    print c
    res = subprocess.check_output(c, shell=True)
    print res
    return res

def vmcmd(h, c):
    return cmd("vagrant ssh " + h + " -- sudo -s -- " + c)


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

    #start docker VM's inside vagrant VMs 
    for hidx, h in enumerate(hosts):
        vmcmd(h, "/vagrant/cleanvms.sh")
        for i in range(1,args.hostvms):
            print "Starting VM " + str(i) + " on " + h
            vmcmd(h, "/vagrant/startvm.sh " + str(hidx) + " " + str(i))
            vm = "vm" + str(i)

    #enumerate docker containers

    #identify OVS port numbers connected to VMs

    #build vxlan tunnels
except subprocess.CalledProcessError as e:
    print e
    print e.output
