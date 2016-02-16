#!/usr/bin/python

from scapy.all import sendp
from scapy.all import Ether, IP

import networkx as nx

import sys

def main():
    if len(sys.argv) != 2:
        print "Usage: send.py [target_host]"
        sys.exit(1)

    dst = sys.argv[1]

    while(1):
        msg = raw_input("What do you want to send: ")
        sendp(Ether(dst="FF:FF:FF:FF:FF:FF")/IP(dst=dst)/msg)

if __name__ == '__main__':
    main()
