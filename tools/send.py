#!/usr/bin/python

from scapy.all import sendp
from scapy.all import Ether, IP, Dot1Q

import networkx as nx

import sys

def main():
    if len(sys.argv) < 2 or len(sys.argv) > 4:
        print "Usage: send.py <target_ip> [<target_mac>] [<vlan_id>]"
        sys.exit(1)

    dstip = sys.argv[1]
    if len(sys.argv) > 2:
        dstmac = sys.argv[2]
    else:
        dstmac = "FF:FF:FF:FF:FF:FF"

    if len(sys.argv) > 3:
        vid = long(sys.argv[3])
    else:
        vid = None


    while(1):
        msg = raw_input("What do you want to send: ")
        if vid is None:
            sendp(Ether(dst=dstmac)/IP(dst=dstip)/msg)
        else:
            sendp(Ether(dst=dstmac)/Dot1Q(vlan=vid)/IP(dst=dstip)/msg)


if __name__ == '__main__':
    main()
