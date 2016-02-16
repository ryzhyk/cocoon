#!/usr/bin/python

from scapy.all import sniff, sendp
from scapy.all import Packet
from scapy.all import ShortField, IntField, LongField, BitField

import sys
import struct

def handle_pkt(pkt):
    pkt.show()

def main():
    sniff(filter="ip", iface = "eth0",
          prn = lambda x: handle_pkt(x))

if __name__ == '__main__':
    main()
