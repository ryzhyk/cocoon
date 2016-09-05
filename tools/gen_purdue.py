#!/usr/bin/python

import argparse
import networkx
import random
import sys

debug = False

# Each host has PROB_NONLOCAL_HOST chance to be in a subnet different from its
# physical location.
PROB_NONLOCAL_HOST = 0.1

class Host:
    # mac (int):    host mac address
    # ip (string):  host ip address
    # vlan (int):   vlan
    def __init__(self, mac, ip, vlan):
        self.mac = mac
        self.ip = ip
        self.vlan = vlan

class LAN:
    # LAN objects are initialized with their subnet, eg. "192.168.1" and a list
    # of host IDs.  NB: Each host is assumed to have a MAC address equal to its
    # ID.
    def __init__(self, subnet, router, switches, hosts, vlan):
        assert(len(hosts) <= 256)
        self.subnet = subnet
        self.router = router
        self.switches = switches
        self.hosts = hosts
        self.vlan = vlan

    def __str__(self):
        return '<LAN %s: %s>' % (self.subnet, ', '.join(map(lambda h: 'Host %d (%s)' % (h.mac, h.ip), self.hosts)))

    def get_local_hosts(self):
        return filter(lambda h: h.ip.startswith(self.subnet), self.hosts)

    def get_nonlocal_hosts(self):
        return filter(lambda h: not h.ip.startswith(self.subnet), self.hosts)

# Produce a Waxman graph with edges added between unconnected components.
def connected_waxman_graph(n):
    g = networkx.waxman_graph(n)

    if networkx.is_connected(g):
        return g

    ccs = [x for x in networkx.connected_components(g)]
    while len(ccs) > 1:
        cc1 = random.choice(ccs)
        cc2 = random.choice(ccs)
        while cc1 == cc2:
            cc2 = random.choice(ccs)
        g.add_edge(random.sample(cc1, 1)[0], random.sample(cc2, 1)[0])
        ccs.remove(cc2)
    if not networkx.is_connected(g):
        sys.stderr.write('%s\n' % g.edges())
    assert(networkx.is_connected(g))
    return g
            

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

# Generate a NetKAT topology from a networkx graph.
def topology_of_networkx(g):
    t = []
    for n in g:
        if not g.node[n]['type'] == 'host':
            for (neighbor, port) in g.node[n]['ports'].iteritems():
                t.append('sw = %d; port = %d; sw := %d; port := %d' % (
                    n, port, neighbor, g.node[neighbor]['ports'][n]))
    return '\n+ '.join(t)

# Will return '' for a path of length 1 (i.e. a self loop).
def policy_of_path(g, path, target):
    assert(len(path) > 0)
    switch_pols = []
    current = path[0]
    for n in path[1:]:
        if 'host' in g.node[target]:
            switch_pols.append('sw = %d; ethDst = %d; ip4Dst = %d; port := %d' % (
                current,
                target,
                int_of_ip(g.node[target]['host'].ip),
                g.node[current]['ports'][n]))
        else:
            switch_pols.append('sw = %d; ethDst = %d; port := %d' % (
                current,
                target,
                g.node[current]['ports'][n]))
        current = n
    return '\n+ '.join(switch_pols)

# Generate a NetKAT policy encoding shortest path L2 forwarding for a networkx
# graph where nodes are annotated with type='switch' | 'router' | 'host'  and port
# dictionaries.  Routers are assumed to be the edges of the network and have
# MAC addresses equal to their node ID.
def spp_of_networkx(g):
    routers = [n for (n, data) in filter(
        lambda (n, data): data['type'] == 'router' or data['type'] == 'host',
        g.nodes(data=True))]

    # TODO: switch this to compute shortest path from all nodes to each router.
    # Then, for each node for each target router, compute a policy for the next
    # hop.

    paths = []
    for r1 in routers:
        for r2 in routers:
            if r1 == r2:
                continue
            path = networkx.shortest_path(g, source=r1, target=r2)
            if g.node[path[0]]['type'] == 'host':
                path = path[1:]
            p = policy_of_path(g, path, r2)
            if len(p) > 0:
                paths.append(p)
    return '\n+ '.join(paths)

# Add a dictionary to each node mapping neighboring nodes to port numbers.
# Port numbers start at 2.
def add_ports_to_networkx(g):
    for n in g:
        d = {}
        p = 2
        for neighbor in g[n].keys():
            d[neighbor] = p
            p += 1
        g.node[n]['ports'] = d

# Sanity check on port assignments.
def check_networkx(g):
    for n in g:
        for neighbor in g[n].keys():
            if neighbor not in g.node[n]['ports']:
                print '%s %d not in ports for neighbor %s %d' % (
                    g.node[neighbor]['type'], neighbor, g.node[n]['type'], n)
                assert(neighbor in g.node[n]['ports'])

# High-level spec for the Purdue network: All hosts are grouped by subnet, can
# communicate within the subnet, and inter-subnet traffic goes through an ACL.
class Spec0:
    def __init__(self, local, remote):
        self.local = local
        self.remote = remote
    def __str__(self):
        return '%s\n\n+\n\n%s' % (self.local, self.remote)

# Spec0 refactored into an OpenFlow-friendly format of policy; topology for one
# big switch.
class Spec0_1:
    def __init__(self, local, remote, host_topo, router_topo, host_switches):
        self.local = local
        self.remote = remote
        self.host_topo = host_topo
        self.router_topo = router_topo
        self.host_switches = host_switches
    def __str__(self):
        return '''
( {host_topo} );
(
(( {local} )
+ 
( {remote} ))
;
( {router_topo} ))*
;
( {host_switches} ); port = 1
'''.format( host_switches=self.host_switches
          , host_topo=self.host_topo
          , router_topo=self.router_topo
          , local=self.local
          , remote=self.remote )

# Distribute access control to each LAN gateway.
class Spec1:
    def __init__(self, local, host_to_router, router_to_router, router_to_host, host_switches):
        self.local = local
        self.host_to_router = host_to_router
        self.router_to_router = router_to_router
        self.router_to_host = router_to_host
        self.host_switches = host_switches
    def __str__(self):
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
'''.format( local=self.local
          , host_to_router=self.host_to_router
          , router_to_router=self.router_to_router
          , router_to_host=self.router_to_host
          , host_switches=self.host_switches )

# Add L2 switching between routers.
class Spec2:
    def __init__(self, local, host_to_router, router_to_router_topo, router_to_router_pol, router_to_host, host_switches):
        self.local = local
        self.host_to_router = host_to_router
        self.router_to_router_topo = router_to_router_topo
        self.router_to_router_pol = router_to_router_pol
        self.router_to_host = router_to_host
        self.host_switches = host_switches
    def __str__(self):
        return '''
( {local} )

+ 

( {host_switches} );
port = 0;
(
( {host_to_router} )

+

( {router_to_router_pol}; {router_to_router_topo}; {router_to_router_pol} )*

+

( {router_to_host} )
)* ;
( {host_switches} );
port = 1
'''.format( local=self.local
          , host_to_router=self.host_to_router
          , router_to_router_topo=self.router_to_router_topo
          , router_to_router_pol=self.router_to_router_pol
          , router_to_host=self.router_to_host
          , host_switches=self.host_switches )

# Add L2 switching between hosts and their gateways, randomly move some hosts
# out of their subnet LANs, and add VLANs.
class Spec3:
    def __init__(self, preface, local_topos, local_pols, router_to_router_topo, router_to_router_pol, host_switches):
        self.preface = preface
        self.local_topos = local_topos
        self.local_pols = local_pols
        self.router_to_router_topo = router_to_router_topo
        self.router_to_router_pol = router_to_router_pol
        self.host_switches = host_switches
    def __str__(self):
        return '''
( {host_switches} );
port = 0;
( {preface} );
(
(
( {local_pols} )

+

( {router_to_router_pol} )

) ; (

( {local_topos} )

+

( {router_to_router_topo} )

)
)* ;
( {host_switches} );
port = 1
'''.format( preface=self.preface
          , local_topos=self.local_topos
          , local_pols=self.local_pols
          , router_to_router_topo=self.router_to_router_topo
          , router_to_router_pol=self.router_to_router_pol
          , host_switches=self.host_switches )

# TODO: split router_to_router as well?

class PurdueNetwork:

    def __init__(self, num_lans, num_hosts_per_lan, num_acl_rules, num_routers, num_switches_per_lan):
        self.num_lans = num_lans
        self.num_hosts_per_lan = num_hosts_per_lan
        self.num_acl_rules = num_acl_rules
        self.num_routers = num_routers
        self.num_switches_per_lan = num_switches_per_lan
        self.next_switch = num_lans * num_hosts_per_lan

        assert(0 < num_hosts_per_lan <= 256)
        assert(1 < num_lans <= 16777216)

        # Build virtual LANs.
        def mkHost(lan_num, host_num, vlan):
            ip = convert_to_ip(lan_num, host_num)
            return Host(host_num, ip, vlan)

        def mkLAN(lan_num):
            subnet = convert_to_subnet(lan_num)
            hosts = map(lambda i: mkHost(lan_num, lan_num * num_hosts_per_lan + i, lan_num), range(num_hosts_per_lan))
            return LAN(subnet, self.get_next_switch(), [], hosts, lan_num)

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
                map(lambda h: 'ip4Dst = %d; sw := %s; port := 1' % (int_of_ip(h.ip), h.mac), lan.hosts))
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
        acl_forwarding = '\n+ '.join(map(lambda h: 'ip4Dst = %d; sw := %s; port := 1' % (int_of_ip(h.ip), h.mac), all_hosts))
        acl = ';\n'.join(['~(ip4Src = %d; ip4Dst = %d)' % (int_of_ip(h1.ip), int_of_ip(h2.ip)) for (h1, h2) in self.acl_pairs])

        spec_0 = Spec0(
            '( %s )' % '\n\n+\n\n'.join(local_forwarding),
            '( %s )\n\n;\n\n( %s )\n\n;\n\n( %s )' % ( '\n+ '.join(nonlocal_forwarding),
                                            acl,
                                            acl_forwarding))
        return spec_0

    def gen_spec_0_1(self):
        switch = self.get_next_switch()

        # Local forwarding.
        local_forwarding = []
        for lan in self.lans:
            local_forwarding.append('\n+ '.join(['port = %d; ip4Dst = %d; port := %d' % (
                h1.mac, int_of_ip(h2.ip), h2.mac) for h1 in lan.hosts for h2 in lan.hosts]))

        # Topology connecting each host to the single big switch.
        host_topo = '\n+ '.join(['sw = %d; port = 0; sw := %d; port := %d' % (
            h.mac, switch, h.mac) for lan in self.lans for h in lan.hosts])
        router_topo = '\n+ '.join(['sw = %d; port = %d; sw := %d; port := 1' % (
            switch, h.mac, h.mac) for lan in self.lans for h in lan.hosts])

        # Non-local forwarding filter.
        nonlocal_predicate = []
        for lan in self.lans:
            local_pred = '\n+ '.join(map(lambda h: 'port = %d' % h.mac, lan.hosts))
            local_ip = '\n+ '.join(map(lambda h: 'ip4Dst = %d' % int_of_ip(h.ip), lan.hosts))
            nonlocal_predicate.append('sw = %d; (%s); ~(%s)' % (switch, local_pred, local_ip))

        # Build ACL forwarding.
        all_hosts = [h for lan in self.lans for h in lan.hosts]
        acl_forwarding = '\n+ '.join(map(lambda h: 'ip4Dst = %d; port := %d' % (int_of_ip(h.ip), h.mac), all_hosts))
        acl = ';\n'.join(['~(ip4Src = %d; ip4Dst = %d)' % (int_of_ip(h1.ip), int_of_ip(h2.ip)) for (h1, h2) in self.acl_pairs])

        spec_0 = Spec0_1(
            '( %s )' % '\n\n+\n\n'.join(local_forwarding),
            '( %s )\n\n;\n\n( %s )\n\n;\n\n( %s )' % ( '\n+ '.join(nonlocal_predicate),
                                            acl,
                                            acl_forwarding),
            host_topo,
            router_topo,
            '\n+ '.join(['sw = %d' % h.mac for lan in self.lans for h in lan.hosts]))

        return spec_0

    def gen_spec_1(self, spec0):

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
                map(lambda h: 'ip4Dst = %d; sw := %s; port := 1' % (int_of_ip(h.ip), h.mac), lan.hosts))
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

        return Spec1(
              spec0.local
            , '\n+ '.join(nonlocal_forwarding_to_router)
            , router_to_router
            , '\n+ '.join(local_forwarding_from_router)
            , '\n+ '.join(['sw = %d' % h.mac for lan in self.lans for h in lan.hosts]))

    def gen_spec_2(self, spec1):
        # Local and host-to-router are unchanged from spec1.  Router-to-router
        # now replaces the ethDst with the target gateway router at the source
        # gateway router, and router-to-host reconstitutes the appropriate
        # ethDst.

        # Build router-to-router network.
        g = connected_waxman_graph(self.num_routers)
        relabel = {i:self.get_next_switch() for i in xrange(self.num_routers)}
        for n in g:
            g.node[n]['type'] = 'switch'
        networkx.relabel_nodes(g, relabel, copy=False)
        for lan in self.lans:
            g.add_node(lan.router, type='router')
            g.add_edge(lan.router, relabel[random.randrange(self.num_routers)])
        add_ports_to_networkx(g)
        self.routers = g

        router_to_host_preface = []
        for lan in self.lans:
            p = '\n+ '.join(['ip4Dst = %d; ethDst := %d' % (int_of_ip(h.ip), h.mac) for h in lan.hosts])
            router_to_host_preface.append(
                'sw = %d; ethDst = %d; ( %s ); port := 1' % (lan.router, lan.router, p))
        router_to_host = '( %s )\n\n+\n\n( %s )' % ('\n+ '.join(router_to_host_preface), spec1.router_to_host)

        router_to_router_topo = topology_of_networkx(self.routers)
        router_to_router_pol = spp_of_networkx(self.routers)

        return Spec2(spec1.local, spec1.host_to_router, router_to_router_topo, router_to_router_pol, router_to_host, spec1.host_switches)

    def gen_spec_3(self, spec2):
        # Router-to-router remains the same, but host-to-router and
        # router-to-host change to acount for (a) local L2 switching and (b)
        # adding VLAN and moving some subnet hosts to different physical LANs.

        # Permute hosts.
        host_to_lan = {}
        host_to_vrouter = {}
        remote_hosts = {lan.vlan:set([]) for lan in self.lans}
        vlan_to_hosts = {lan.vlan:set([]) for lan in self.lans}
        for lan in self.lans:
            for h in lan.hosts:
                host_to_vrouter[h] = lan.router
                vlan_to_hosts[h.vlan].add(h)
                if (random.random() < PROB_NONLOCAL_HOST):
                    lan.hosts.remove(h)
                    choice = random.choice(self.lans)
                    choice.hosts.append(h)
                    host_to_lan[h] = choice
                    remote_hosts[h.vlan].add(h)
                else:
                    host_to_lan[h] = lan

        # Generate random L2 topologies for each LAN.
        for lan in self.lans:
            g = connected_waxman_graph(self.num_switches_per_lan)
            relabel = {i:self.get_next_switch() for i in xrange(self.num_switches_per_lan)}
            for n in g:
                g.node[n]['type'] = 'switch'
            networkx.relabel_nodes(g, relabel, copy=False)
            add_ports_to_networkx(g)

            # Attach router.
            attach_point = random.randrange(self.num_switches_per_lan)
            g.add_node(lan.router, type='router', ports={relabel[attach_point]:1})
            g.add_edge(lan.router, relabel[attach_point])
            ports_d = g.node[relabel[attach_point]]['ports']
            ports = ports_d.values()
            if len(ports) > 0:
                ports.sort()
                ports_d[lan.router] = ports[-1] + 1
            else:
                ports_d[lan.router] = 2

            # Attach hosts.
            for h in lan.hosts:
                attach_point = random.randrange(self.num_switches_per_lan)
                g.add_node(h.mac, type='host', ports={relabel[attach_point]:1}, host=h)
                g.add_edge(h.mac, relabel[attach_point])
                ports_d = g.node[relabel[attach_point]]['ports']
                ports = ports_d.values()
                if len(ports) > 0:
                    ports.sort()
                    ports_d[h.mac] = ports[-1] + 1
                else:
                    ports_d[h.mac] = 2

            check_networkx(g)

            lan.g = g

        if debug:
            for lan in self.lans:
                for n in lan.g:
                    d = lan.g.node[n]
                    sys.stderr.write('%s %d: %s\n' % (d['type'], n, d['ports']))
                sys.stderr.write('\n')

        preface = []
        topo = []
        pol = []
        for lan in self.lans:

            # Generate host preface:
            #   sw = h.id; port = 0; ip4Src = h.ip; vlan := h.vlan; sw := neighbor(h); port := neighbor(h)
            for h in lan.hosts:
                neighbor = lan.g[h.mac].keys()[0]
                neighbor_port = lan.g.node[neighbor]['ports'][h.mac]
                preface.append(
                    'sw = %d; port = 0; ip4Src = %d; vlan := %d; sw := %d; port := %d' % (
                        h.mac, int_of_ip(h.ip), h.vlan, neighbor, neighbor_port
                    ))

            # Generate intra-LAN L2 forwarding.
            t = topology_of_networkx(lan.g)
            p = spp_of_networkx(lan.g)

            # Attach VLANs at the hosts.
            attach_vlan = ['sw = %d; ~(ethDst = %d); vlan := %d' % (h.mac, h.mac, h.vlan) for h in lan.hosts]

            # For outgoing traffic, if the packet VLAN is the same as the
            # router VLAN:

            # ... and the destination host is part of THE SAME VLAN, then write
            # the ethDst to be the router associated with the target host.
            if len(remote_hosts[lan.vlan]) > 0:
                p1 = 'sw = %d; port = 1; vlan = %d; ( %s )' % (
                    lan.router, lan.vlan, 
                    '\n+ '.join(['ip4Dst = %d; ethDst := %d' % (
                        int_of_ip(h.ip), host_to_lan[h].router)
                        for h in remote_hosts[lan.vlan]]))
            else:
                p1 = 'drop'

            # ... and the destination host is part of a DIFFERENT VLAN, then
            # write the ethDst to be the router associated with the target
            # VLAN.
            #
            # NB: The NetKAT decision procedure doesn't support IP masks, so we
            # need to enumerate every other host.
            p2 = 'sw = %d; port = 1; vlan = %d;\n( %s )' % (
                  lan.router,
                  lan.vlan, 
                  '\n+ '.join(['ip4Dst = %d; ethDst := %d' % (
                          int_of_ip(h.ip),
                          host_to_vrouter[h])
                      for h in host_to_vrouter if h.vlan != lan.vlan]))

            # For outgoing traffic, if the packet VLAN is NOT the same as the
            # router VLAN, then send it to the router associated with its VLAN.
            p3 = 'sw = %d; port = 1; ( %s )' % (lan.router,
                 '\n+ '.join(['vlan = %d; ethDst := %d' % (lan2.vlan, lan2.router)
                 for lan2 in filter(lambda l: l != lan, self.lans)]))


            # For incoming traffic, if the packet VLAN is the same as the
            # router VLAN, then:

            # ... if the target host is in the LAN, write the ethDst of the
            # target host.
            hosts_in_lan_and_vlan = filter(lambda h: h.vlan == lan.vlan, lan.hosts)
            if len(hosts_in_lan_and_vlan) > 0:
                p4 = 'sw = %d; ~(port = 1); vlan = %d; ( %s )' % (
                        lan.router, lan.vlan,
                        '\n+ '.join(['ip4Dst = %d; ethDst := %d' % (
                            int_of_ip(h.ip), h.mac)
                            for h in hosts_in_lan_and_vlan]))
            else:
                p4 = 'drop'

            # ... if the target host is remote, write the ethDst of the router
            # associated with this host.
            if len(remote_hosts[lan.vlan]) > 0:
                p5 = 'sw = %d; ~(port = 1); vlan = %d; ( %s )' % (
                        lan.router, lan.vlan,
                        '\n+ '.join(['ip4Dst = %d; ethDst := %d' % (
                            int_of_ip(h.ip), host_to_lan[h].router)
                            for h in remote_hosts[lan.vlan]]))
            else:
                p5 = 'drop'

            # For incoming traffic, if the packet VLAN is NOT the same as the
            # router VLAN, then:

            # The packet is intra-VLAN traffic, but its LAN houses a remote
            # host for that VLAN.
            nonlocal_hosts = filter(lambda h: h.vlan != lan.vlan, lan.hosts)
            if len(nonlocal_hosts) > 0:
                p6 = 'sw = %d; ~(port = 1); ( %s )' % (lan.router,
                        '\n+ '.join(['vlan = %d; ip4Dst = %d; ethDst := %d' % (
                            h.vlan, int_of_ip(h.ip), h.mac)
                            for h in nonlocal_hosts]))
            else:
                p6 = 'drop'

            # The packet is inter-VLAN traffic destined for a host in this
            # router's VLAN, and:

            # ... the target host is in this LAN.
            acl = ';\n '.join(['~(ip4Src = %d; ip4Dst = %d)' % (int_of_ip(src.ip), int_of_ip(dst.ip))
                        for (src, dst) in filter(lambda (src, dst): dst in vlan_to_hosts[lan.vlan], self.acl_pairs)])
            if acl == '':
                acl = 'pass'
            p7 = 'sw = %d; ~(port = 1); ~(vlan = %d);\n( %s );\n( %s ); vlan := %d' % (
                    lan.router,
                    lan.vlan,
                    '\n+ '.join(['ip4Dst = %d; ethDst := %d' % (
                        int_of_ip(h.ip), h.mac)
                        for h in filter(lambda h: h.vlan == lan.vlan, lan.hosts)]),
                        acl, lan.vlan)

            # ... the target host is elsewhere.
            if len(remote_hosts[lan.vlan]) > 0:
                p8 = 'sw = %d; ~(port = 1); ~(vlan = %d); \n( %s );\n( %s ); vlan := %d' % (
                        lan.router,
                        lan.vlan,
                        '\n+ '.join(
                            ['ip4Dst = %d; ethDst := %d' % (int_of_ip(h.ip), host_to_lan[h].router)
                                for h in remote_hosts[lan.vlan]]),
                        acl, lan.vlan)
            else:
                p8 = 'drop'

            topo.append(t)
            pol.append("""
            ( {l2} )

            +
            ((
                ( {p1} )
                +
                ( {p2} )
                +
                ( {p3} )
            ) ; (
                {router_to_router_pol}
            ))

            +

            ((
                ( {p4} )
                +
                ( {p6} )
                +
                ( {p7} )
            ) ; (
                {l2}
            ))
 
            +

            ( {p5} )
           
            +

            ( {p8} )
            """.format(
                l2=p,
                p1=p1,
                p2=p2,
                p3=p3,
                p4=p4,
                p5=p5,
                p6=p6,
                p7=p7,
                p8=p8,
                router_to_router_pol=spec2.router_to_router_pol))

        return Spec3(
            '\n+ '.join(preface),
            '\n\n+\n\n'.join(topo),
            '\n\n+\n\n'.join(pol),
            spec2.router_to_router_topo,
            spec2.router_to_router_pol,
            spec2.host_switches)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument( "num_lans"
                       , help="number of LANs"
                       , type=int)
    parser.add_argument( "num_lan_hosts"
                       , help="number of hosts per LAN"
                       , type=int)
    parser.add_argument( "num_acl_rules"
                       , help="number of (hostIP, dstIP) blacklist ACL rules"
                       , type=int)
    parser.add_argument( "num_fabric_switches"
                       , help="number of switches connecting gateway routers"
                       , type=int)
    parser.add_argument( "num_lan_switches"
                       , help="number of switches per LAN"
                       , type=int)
    parser.add_argument( "--source_spec"
                       , help="higher-level spec"
                       , default=0
                       , type=int
                       , choices=[0, 1, 2, 3] )
    parser.add_argument( "--target_spec"
                       , help="lower-level spec"
                       , default=3
                       , type=int
                       , choices=[0, 1, 2, 3] )

    args = parser.parse_args()

    if args.num_lans < 2:
        sys.stderr.write('must have at least 2 LANs')
        sys.exit(1)
    if args.num_lan_hosts < 1:
        sys.stderr.write('must have at least 1 host per LAN')
        sys.exit(1)
    if args.num_acl_rules < 1:
        sys.stderr.write('must have at least 1 ACL rule')
        sys.exit(1)
    if args.num_fabric_switches < 1:
        sys.stderr.write('must have at least 1 fabric switch')
        sys.exit(1)
    if args.num_lan_switches < 1:
        sys.stderr.write('must have at least 1 switch per LAN')
        sys.exit(1)
    if args.source_spec >= args.target_spec:
        sys.stderr.write('source spec must be less than target spec')
        sys.exit(1)

    p = PurdueNetwork( args.num_lans
                     , args.num_lan_hosts
                     , args.num_acl_rules
                     , args.num_fabric_switches
                     , args.num_lan_switches )

    spec0 = p.gen_spec_0()
    spec01 = p.gen_spec_0_1()
    spec1 = p.gen_spec_1(spec0)
    spec2 = p.gen_spec_2(spec1)
    spec3 = p.gen_spec_3(spec2)

    def num_to_spec(n):
        if n == 0:
            return spec01
        if n == 1:
            return spec1
        if n == 2:
            return spec2
        if n == 3:
            return spec3

    print '\n(\n%s\n)\nvlan := 0; ethDst := 0' % num_to_spec(args.target_spec)
    print '\n<=\n'
    print '\n(\n%s\n)\nvlan := 0; ethDst := 0' % num_to_spec(args.source_spec)

