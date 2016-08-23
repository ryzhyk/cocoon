#!/usr/bin/python

import random

# Each host has PROB_NONLOCAL_HOST chance to be in a subnet different from its
# physical location.
PROB_NONLOCAL_HOST = 0.1

class Host:
    # mac (int):    host mac address
    # ip (string):  host ip address
    def __init__(self, mac, ip):
        self.mac = mac
        self.ip = ip

class LAN:
    # LAN objects are initialized with their subnet, eg. "192.168.1" and a list
    # of host IDs.  NB: Each host is assumed to have a MAC address equal to its
    # ID.
    def __init__(self, subnet, router, switches, hosts):
        assert(len(hosts) <= 256)
        self.subnet = subnet
        self.router = router
        self.switches = switches
        self.hosts = hosts

    def __str__(self):
        return '<LAN %s: %s>' % (self.subnet, ', '.join(map(lambda h: 'Host %d (%s)' % (h.mac, h.ip), self.hosts)))

    def get_local_hosts(self):
        return filter(lambda h: h.ip.startswith(self.subnet), self.hosts)

    def get_nonlocal_hosts(self):
        return filter(lambda h: not h.ip.startswith(self.subnet), self.hosts)

# Given a LAN number, convert to "X.Y.Z" such that
# n = X * (256 * 256) + Y * 256 + Z.
def convert_to_subnet(lan):
    assert(lan <= 16777216)
    part_1 = (int)(lan / 65536)
    part_2 = (int)((lan % 65536) / 256)
    part_3 = (int)(lan % 256)
    assert(part_1 * 65536 + part_2 * 256 + part_3 == lan)
    return '%d.%d.%d' % (part_1, part_2, part_3)

# Given a LAN number n and host ID h (i.e. MAC address), return an IP address
# "X.Y.Z.M" such that "X.Y.Z" = convert_to_subnet(n) and M = h % 256.
def convert_to_ip(lan, host):
    return '%s.%d' % (convert_to_subnet(lan), host % 256)

def int_of_ip(ip):
    parts = ip.split('.')
    return ( int (parts[0]) * 256 * 256 * 256
           + int (parts[1]) * 256 * 256
           + int (parts[2]) * 256
           + int (parts[3]) )

class PurdueNetwork:

    def __init__(self, num_lans, num_hosts_per_lan, num_acl_rules, num_routers, num_switches_per_lan):
        self.num_lans = num_lans
        self.num_hosts_per_lan = num_hosts_per_lan
        self.num_acl_rules = num_acl_rules
        self.num_routers = num_routers
        self.num_switches_per_lan = num_switches_per_lan
        self.next_switch = num_lans * num_hosts_per_lan + 1

        assert(0 < num_hosts_per_lan <= 256)
        assert(1 < num_lans <= 16777216)

        # Build virtual LANs.
        def mkHost(lan_num, host_num):
        # TODO: move this to spec 4.
        #         if (random.random() < PROB_NONLOCAL_HOST):
        #             ip = convert_to_ip(random.randrange(lan_num), host_num)
        #         else:
        #             ip = convert_to_ip(lan_num, host_num)
            ip = convert_to_ip(lan_num, host_num)
            return Host(host_num, ip)

        def mkLAN(lan_num):
            subnet = convert_to_subnet(lan_num)
            hosts = map(lambda i: mkHost(lan_num, lan_num * num_hosts_per_lan + i), range(num_hosts_per_lan))
            return LAN(subnet, self.get_next_switch(), [], hosts)

        self.lans = map(mkLAN, range(num_lans))
        self.subnet_to_lan = {self.lans[i].subnet : i for i in xrange(len(self.lans)) }

        # Build ACL.
        self.acl_pairs = []
        for i in xrange(num_acl_rules):
            lan1idx = random.randrange(len(self.lans))
            lan2idx = random.randrange(len(self.lans))
            while lan1idx == lan2idx:
                lan2idx = random.randrange(len(self.lans))
            lan1 = self.lans[lan1idx]
            lan2 = self.lans[lan2idx]
            h1 = lan1.hosts[random.randrange(len(lan1.hosts))]
            h2 = lan2.hosts[random.randrange(len(lan2.hosts))]
            self.acl_pairs.append((h1, h2))

    def lan_of_subnet(self, subnet):
        return self.lans[self.subnet_to_lan[subnet]]

    def lan_of_ip(self, ip):
        parts = ip.split('.')
        return self.lan_of_subnet('%s.%s.%s' % (parts[0], parts[1], parts[2]))

    def get_next_switch(self):
        rv = self.next_switch
        self.next_switch += 1
        return rv

    def gen_local_forwarding(self):
        local_forwarding = []

        for lan in self.lans:
            
            # Build local forwarding.
            local_pred = '\n+ '.join(
                map(lambda h: 'sw = %s; port = 0' % h.mac, lan.hosts))
            local_forwarding_act = '\n+ '.join(
                map(lambda h: 'ip4Dst = %d; switch := %s; port := 1' % (int_of_ip(h.ip), h.mac), lan.hosts))
            local_forwarding.append('( %s )\n\n;\n\n( %s )' % (local_pred, local_forwarding_act))

        return local_forwarding

    def gen_spec_0(self):
        # Local forwarding.
        local_forwarding = self.gen_local_forwarding()

        # Non-local forwarding.
        nonlocal_forwarding = []
        for lan in self.lans:
            local_pred = '\n+ '.join(map(lambda h: 'sw = %s; port = 0' % h.mac, lan.hosts))
            local_ip = '\n+ '.join(map(lambda h: 'ip4Dst = %d' % int_of_ip(h.ip), lan.hosts))
            nonlocal_forwarding.append('(%s); ~(%s)' % (local_pred, local_ip))

        # Build ACL forwarding.
        all_hosts = [h for lan in self.lans for h in lan.hosts]
        acl_forwarding = '\n+ '.join(map(lambda h: 'ip4Dst = %d; switch := %s; port := 1' % (int_of_ip(h.ip), h.mac), all_hosts))
        acl = '\n+ '.join(['ip4Src = %d; ip4Dst = %d; drop' % (int_of_ip(h1.ip), int_of_ip(h2.ip)) for (h1, h2) in self.acl_pairs])

        spec_0 = '( %s )\n\n+\n\n( %s )\n\n;\n\n( %s )\n\n;\n\n( %s )' % ('\n\n+\n\n'.join(local_forwarding),
                                            '\n+ '.join(nonlocal_forwarding),
                                            acl,
                                            acl_forwarding)
        return spec_0

    def gen_spec_1(self):
        # Local forwarding.
        local_forwarding = self.gen_local_forwarding()

        # Non-local forwarding.
        nonlocal_forwarding_to_router = []
        local_forwarding_from_router = []
        router_forwarding_to_router = []
        for lan in self.lans:
            # From host to router.
            local_pred = '\n+ '.join(map(lambda h: 'sw = %s; port = 0' % h.mac, lan.hosts))
            local_ip = '\n+ '.join(map(lambda h: 'ip4Dst = %d' % int_of_ip(h.ip), lan.hosts))
            nonlocal_forwarding_to_router.append('(%s); ~(%s); sw := %d' % (local_pred, local_ip, lan.router))

            # From router to host.
            local_forwarding_act = '\n+ '.join(
                map(lambda h: 'ip4Dst = %d; switch := %s; port := 1' % (int_of_ip(h.ip), h.mac), lan.hosts))
            local_acl_pairs = filter(lambda (h1, h2): self.lan_of_ip(h2.ip) == lan, self.acl_pairs)
            local_acl = '\n+ '.join(['ip4Src = %d; drop' % int_of_ip(h1.ip) for (h1, h2) in local_acl_pairs])
            if len(local_acl) > 0:
                local_forwarding_from_router.append(
                    'sw = %d; port = 1; (%s); (%s)' % (lan.router, local_acl, local_forwarding_act))
            else:
                local_forwarding_from_router.append(
                    'sw = %d; port = 1; (%s)' % (lan.router, local_forwarding_act))

            # From router to router.
            router_forwarding_to_router.append(
              '\n+ '.join(
                ['ip4Dst = %d; sw := %d; port := 1' % (
                    int_of_ip(host.ip), self.lan_of_ip(host.ip).router) for host in lan.hosts]))

        # From router to router.
        router_to_router = '( %s )\n\n;\n\n( %s )' % (
            '\n+ '.join(['sw = %d; port = 0' % lan.router for lan in self.lans]),
            '\n+ '.join(router_forwarding_to_router))

        return '''
( {local} )

+ 

( {host_switches} );
port = 0;
(
( {host_to_router} )

+

( {router_to_router} )

+

( {router_to_host} )
)* ;
( {host_switches} );
port = 1
'''.format( local='\n\n+\n\n'.join(local_forwarding)
          , host_to_router='\n+ '.join(nonlocal_forwarding_to_router)
          , router_to_router=router_to_router
          , router_to_host='\n+ '.join(local_forwarding_from_router)
          , host_switches='\n+ '.join(['sw = %d' % h.mac for lan in self.lans for h in lan.hosts]))

        # TODO: put into "t; (p; t)*" form.


p = PurdueNetwork(64, 4, 2, 1, 1)
print p.gen_spec_0()
print '\n==\n'
print p.gen_spec_1()
