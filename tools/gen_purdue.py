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

def export_topology_of_networkx(g, out):
    for n in g:
        for (neighbor, port) in g.node[n]['ports'].iteritems():
            out.write('(%s %d, %d)--(%s %d, %d)\n' % (
                g.node[n]['type'].upper(), n, port,
                g.node[neighbor]['type'].upper(), neighbor,
                g.node[neighbor]['ports'][n]))


# Will return '' for a path of length 1 (i.e. a self loop).
def policy_of_path(g, path, target, ethDst_of_target):
    assert(len(path) > 0)
    switch_pols = []
    current = path[0]
    for n in path[1:]:
        if 'host' in g.node[target]:
            switch_pols.append('sw = %d; ethDst = %d; ip4Dst = %d; vlan = %d; port := %d' % (
                current,
                ethDst_of_target(target),
                int_of_ip(g.node[target]['host'].ip),
                g.node[target]['host'].vlan,
                g.node[current]['ports'][n]))
        else:
            switch_pols.append('sw = %d; ethDst = %d; port := %d' % (
                current,
                ethDst_of_target(target),
                g.node[current]['ports'][n]))
        current = n
    return '\n+ '.join(switch_pols)

# Generate a NetKAT policy encoding shortest path L2 forwarding for a networkx
# graph where nodes are annotated with type='switch' | 'router' | 'host'  and port
# dictionaries.  Routers are assumed to be the edges of the network and have
# MAC addresses equal to their node ID.
def spp_of_networkx(g, ethDst_of_target=(lambda x: x)):
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
            p = policy_of_path(g, path, r2, ethDst_of_target)
            if len(p) > 0:
                paths.append(p)
    return '\n+ '.join(paths)

def cocoon_of_networkx(g):
    targets = [n for (n, data) in filter(
        lambda (n, data): data['type'] == 'router' or data['type'] == 'host',
        g.nodes(data=True))]

    # TODO: switch this to compute shortest path from all nodes to each router.
    # Then, for each node for each target router, compute a policy for the next
    # hop.

    distances = {}
    out_ports = {}
    for sw in g:
        if g.node[sw]['type'] == 'host':
            continue
        distances[sw] = {}
        out_ports[sw] = {}
        for r in targets:
            if sw == r:
                continue

            # TODO: it's grossly inefficient to recompute the path for every
            # switch.

            path = networkx.shortest_path(g, source=sw, target=r)
            distances[sw][r] = len(path) - 1
            out_ports[sw][r] = g.node[sw]['ports'][path[1]]

    return (distances, out_ports)

# Produce a new graph composing g1 and g2.  Copy dictionary attributes.
def copy_compose(g1, g2):
    g = networkx.Graph()
    for n in g1.nodes() + g2.nodes():
        g.add_node(n)
    for (n1, n2) in g1.edges() + g2.edges():
        g.add_edge(n1, n2)
    for n in g1:
        for k in g1.node[n]:
            if type(g1.node[n][k]) == dict:
                g.node[n][k] = dict(g1.node[n][k])
            else:
                g.node[n][k] = g1.node[n][k]
    for n in g2:
        for k in g2.node[n]:
            if type(g2.node[n][k]) == dict:
                g.node[n][k] = dict(g2.node[n][k])
            else:
                g.node[n][k] = g2.node[n][k]
    return g


# Add a dictionary to each node mapping neighboring nodes to port numbers.
# Port numbers start at 2.
def add_ports_to_networkx(g, starting_port):
    for n in g:
        d = {}
        p = starting_port
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

class Spec1_1:
    def __init__( self
                , preface
                , router_to_host_topo
                , router_to_host_pol
                , router_to_router_topo
                , router_to_router_pol
                , hosts):
        self.preface = preface
        self.router_to_host_topo = router_to_host_topo
        self.router_to_host_pol = router_to_host_pol
        self.router_to_router_topo = router_to_router_topo
        self.router_to_router_pol = router_to_router_pol
        self.hosts = hosts

    def __str__(self):
        return '''
( {hosts} ); port = 0;
( {preface} );
(
( ( {router_to_host_pol} )
+
( {router_to_router_pol} ) )
; 
( ( {router_to_host_topo} )
+
( {router_to_router_topo} ) )
)*;
( {hosts} ); port = 1
'''.format( preface=self.preface
          , router_to_host_topo = self.router_to_host_topo
          , router_to_host_pol = self.router_to_host_pol
          , router_to_router_topo = self.router_to_router_topo
          , router_to_router_pol = self.router_to_router_pol
          , hosts = self.hosts )

class Spec2_1:
    def __init__( self
                , preface
                , router_to_host_topo
                , router_to_host_pol
                , router_to_router_topo
                , router_to_router_pol
                , router_to_router_preface
                , router_to_router_tail
                , hosts):
        self.preface = preface
        self.router_to_host_topo = router_to_host_topo
        self.router_to_host_pol = router_to_host_pol
        self.router_to_router_topo = router_to_router_topo
        self.router_to_router_pol = router_to_router_pol
        self.router_to_router_preface = router_to_router_preface
        self.router_to_router_tail = router_to_router_tail
        self.hosts = hosts

    def __str__(self):
        return '''
( {hosts} ); port = 0;
( {preface} );
(
(
( {router_to_router_tail} )
;
( {router_to_host_pol} )
+
( {router_to_router_preface} )
;
( {router_to_router_pol} )
) ; (
( {router_to_host_topo} )
+
( {router_to_router_topo} )
)
)*;
( {hosts} ); port = 1
'''.format( preface=self.preface
          , router_to_host_topo = self.router_to_host_topo
          , router_to_host_pol = self.router_to_host_pol
          , router_to_router_topo = self.router_to_router_topo
          , router_to_router_pol = self.router_to_router_pol
          , router_to_router_preface = self.router_to_router_preface
          , router_to_router_tail = self.router_to_router_tail
          , hosts = self.hosts )


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

({router_to_router_pol});
( ({router_to_router_topo}); ({router_to_router_pol}) )*

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

    def __init__(self, args):
        self.num_lans = args.num_lans
        self.num_hosts_per_lan = args.num_lan_hosts
        self.num_acl_rules = args.num_acl_rules
        self.num_routers = args.num_fabric_switches
        self.num_switches_per_lan = args.num_lan_switches
        self.args = args

        self.next_id = 1

        assert(0 < self.num_hosts_per_lan <= 256)
        assert(1 < self.num_lans <= 16777216)

        # Build virtual LANs.
        def mkHost(lan_num, host_num, vlan):
            ip = convert_to_ip(lan_num, host_num)
            return Host(host_num, ip, vlan)

        def mkLAN(lan_num):
            subnet = convert_to_subnet(lan_num)
            hosts = map(lambda i: mkHost(lan_num, self.get_next_id(), lan_num), range(self.num_hosts_per_lan))
            return LAN(subnet, self.get_next_id(), [], hosts, lan_num)

        self.lans = map(mkLAN, range(1,self.num_lans+1))
        self.subnet_to_lan = {self.lans[i].subnet : i for i in xrange(len(self.lans)) }

        # Build ACL.
        self.acl_pairs = []
        for i in xrange(self.num_acl_rules):
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

    def get_next_id(self):
        rv = self.next_id
        self.next_id += 1
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
        switch = self.get_next_id()

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
            '( %s )' % '\n+\n'.join(local_forwarding),
            '( %s )\n;\n( %s )\n;\n( %s )' % ( '\n+ '.join(nonlocal_predicate),
                                            acl,
                                            acl_forwarding),
            host_topo,
            router_topo,
            '\n+ '.join(['sw = %d' % h.mac for lan in self.lans for h in lan.hosts]))

        if self.args.export_hsa:
            out = self.args.export_hsa

            out.write('### SPEC 0 ###')
            out.write('--- NETKAT SWITCH FUNCTION ---\n')
            out.write('%s\n+\n%s\n' % (spec_0.local, spec_0.remote))
            out.write('\n')
    
            out.write('--- TOPOLOGY ---\n')
            for lan in self.lans:
                for h in lan.hosts:
                    out.write('(HOST %d, %d)--(SWITCH %d, %d)\n' % (h.mac, 1, switch, h.mac))
            out.write('\n')
    
            out.write('--- HOSTS ---\n')
            for lan in self.lans:
                for h in lan.hosts:
                    out.write('HOST %d, %s\n' % (h.mac, h.ip))
            out.write('\n')
    
            out.write('--- ACL (BLACKLIST IP PAIRS) ---\n')
            for (src, dst) in self.acl_pairs:
                out.write('(%s, %s)\n' % (src.ip, dst.ip))
            out.write('\n')

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

    def gen_spec_1_1(self):

        # Preface: Move packets emitted from hosts to the router.
        preface = []
        for lan in self.lans:
            for h in lan.hosts:
                preface.append('sw = %d; sw := %d; port := %d' % (h.mac, lan.router, h.mac))
        preface = 'port = 0; ( %s )' % ('\n+ '.join(preface))

        router_to_host_topo = []
        for lan in self.lans:
            for h in lan.hosts:
                router_to_host_topo.append('sw = %d; port = %d; sw := %d; port := 1' % (lan.router, h.mac, h.mac))
        router_to_host_topo = '\n+ '.join(router_to_host_topo)
 
        acl = '; '.join(['~(ip4Src = %d; ip4Dst = %d)' % (
                    int_of_ip(src.ip), int_of_ip(dst.ip))
                    for (src, dst) in self.acl_pairs])
           
        router_to_host_pol = []
        for lan in self.lans:
            local_action = ' + '.join(['ip4Dst = %d; port := %d' % (int_of_ip(h.ip), h.mac) for h in lan.hosts])
            local_pred = ' + '.join(['port = %d' % h2.mac for h2 in lan.hosts])
            router_to_host_pol.append('sw = %d; ( %s ); ( %s )' % (
                lan.router, local_pred, local_action))
            router_to_host_pol.append('sw = %d; ~( %s ); ( %s ); ( %s )' % (
                lan.router, local_pred, acl, local_action))
        router_to_host_pol = '\n+ '.join(router_to_host_pol)

        router_to_router_topo = []
        for lan in self.lans:
            for other_lan in filter(lambda x: x != lan, self.lans):
                router_to_router_topo.append('sw = %d; port = %d; sw := %d; port := %d' % (
                    lan.router, other_lan.router,
                    other_lan.router, lan.router))
        router_to_router_topo = '\n+ '.join(router_to_router_topo)

        router_to_router_pol = []
        for lan in self.lans:
            tmp = []
            for h in lan.hosts:
                tmp.append('ip4Dst = %d' % (int_of_ip(h.ip)))
            other_routers = ['sw = %d' % other_lan.router for other_lan in filter(lambda x: x != lan, self.lans)]
            router_to_router_pol.append('( %s );\n( %s );\nport := %d' % (
                '\n+ '.join(other_routers),
                '\n+ '.join(tmp),
                lan.router))
        router_to_router_pol = '\n\n+\n\n'.join(router_to_router_pol)

        hosts = '\n+ '.join(['sw = %d' % h.mac for lan in self.lans for h in lan.hosts])
        return Spec1_1( preface
                      , router_to_host_topo
                      , router_to_host_pol
                      , router_to_router_topo
                      , router_to_router_pol
                      , hosts)

    def gen_spec_2_1(self, spec11):
        # Local and host-to-router are unchanged from spec1.  Router-to-router
        # now replaces the ethDst with the target gateway router at the source
        # gateway router, and router-to-host reconstitutes the appropriate
        # ethDst.

        # Build router-to-router network.
        g = connected_waxman_graph(self.num_routers)
        relabel = {i:self.get_next_id() for i in xrange(self.num_routers)}
        for n in g:
            g.node[n]['type'] = 'switch'
        networkx.relabel_nodes(g, relabel, copy=False)
        for lan in self.lans:
            g.add_node(lan.router, type='router')
            g.add_edge(lan.router, relabel[random.randrange(self.num_routers)])
        add_ports_to_networkx(g, self.next_id)
        self.routers = g

        router_to_router_preface = []
        for lan in self.lans:
            tmp = []
            for h in lan.hosts:
                tmp.append('ip4Dst = %d' % (int_of_ip(h.ip)))
            other_routers = ['sw = %d' % other_lan.router for other_lan in filter(lambda x: x != lan, self.lans)]
            router_to_router_preface.append('( %s );\n( %s );\nethDst := %d' % (
                '\n+ '.join(other_routers),
                '\n+ '.join(tmp),
                lan.router))
        router_to_router_preface = '\n\n+\n\n'.join(router_to_router_preface + ['pass'])

        router_to_router_tail = '\n+ '.join(['sw = %d; ip4Dst = %d; ethDst := %d' % (
            lan.router, int_of_ip(h.ip), h.mac) for lan in self.lans for h in lan.hosts]
            + ['pass'])

        router_to_router_pol = spp_of_networkx(self.routers)
        router_to_router_topo = topology_of_networkx(self.routers)

        return Spec2_1( spec11.preface
                      , spec11.router_to_host_topo
                      , spec11.router_to_host_pol
                      , router_to_router_topo
                      , router_to_router_pol
                      , router_to_router_preface
                      , router_to_router_tail
                      , spec11.hosts)

    def gen_spec_2(self, spec1):
        # Local and host-to-router are unchanged from spec1.  Router-to-router
        # now replaces the ethDst with the target gateway router at the source
        # gateway router, and router-to-host reconstitutes the appropriate
        # ethDst.

        # Build router-to-router network.
        g = connected_waxman_graph(self.num_routers)
        relabel = {i:self.get_next_id() for i in xrange(self.num_routers)}
        for n in g:
            g.node[n]['type'] = 'switch'
        networkx.relabel_nodes(g, relabel, copy=False)
        for lan in self.lans:
            g.add_node(lan.router, type='router')
            g.add_edge(lan.router, relabel[random.randrange(self.num_routers)])
        add_ports_to_networkx(g, self.next_id)
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
            relabel = {i:self.get_next_id() for i in xrange(self.num_switches_per_lan)}
            for n in g:
                g.node[n]['type'] = 'switch'
            networkx.relabel_nodes(g, relabel, copy=False)
            add_ports_to_networkx(g, 2)

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

        if args.debug:
            for lan in self.lans:
                for n in lan.g:
                    d = lan.g.node[n]
                    sys.stderr.write('%s %d: %s\n' % (d['type'], n, d['ports']))
                sys.stderr.write('\n')

        # Each gateway router has two ports: One connected to the
        # router-to-router fabric, and another connected to its LAN.  Generate
        # a distinct MAC address for LAN-facing router ports.
        extra_router_macs = {}
        for lan in self.lans:
            extra_router_macs[lan.router] = self.get_next_id()
        def relabel_macs(mac):
            if mac in extra_router_macs:
                return extra_router_macs[mac]
            else:
                return mac

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
            l2 = spp_of_networkx(lan.g, relabel_macs)
            assert(l2)

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
                l2=l2,
                p1=p1,
                p2=p2,
                p3=p3,
                p4=p4,
                p5=p5,
                p6=p6,
                p7=p7,
                p8=p8,
                router_to_router_pol=spec2.router_to_router_pol))
        
        spec3 = Spec3(
            '\n+ '.join(preface),
            '\n\n+\n\n'.join(topo),
            '\n\n+\n\n'.join(pol),
            spec2.router_to_router_topo,
            spec2.router_to_router_pol,
            spec2.hosts)

        if self.args.export_hsa:
            out = self.args.export_hsa

            out.write('### SPEC 3 ###')
            out.write('--- NETKAT SWITCH FUNCTION ---\n')
            out.write('%s\n+\n%s\n' % (spec3.local_pols, spec3.router_to_router_pol))
            out.write('\n')
    
            out.write('--- TOPOLOGY ---\n')
            for lan in self.lans:
                for h in lan.hosts:
                    for g in [lan.g for lan in self.lans] + [self.routers]:
                        export_topology_of_networkx(g, out)
            out.write('\n')
    
            out.write('--- HOSTS ---\n')
            for lan in self.lans:
                for h in lan.hosts:
                    out.write('HOST %d, %s\n' % (h.mac, h.ip))
            out.write('\n')
    
            out.write('--- ACL (BLACKLIST IP PAIRS) ---\n')
            for (src, dst) in self.acl_pairs:
                out.write('(%s, %s)\n' % (src.ip, dst.ip))
            out.write('\n')

        return spec3

    def export_cocoon(self):
        out = self.args.export_cocoon
        
        # Make a new graph that connects the zones to the router fabric.
        g = self.routers
        for lan in self.lans:
            g = copy_compose(lan.g, g)
            for n in lan.g:
                for neighbor in lan.g.node[n]['ports']:
                    g.node[n]['ports'][neighbor] = lan.g.node[n]['ports'][neighbor]



        # FUNCTION cHost
        out.write('function cHost(hid_t hid): bool =\n')
        out.write(' or\n'.join(["    hid == 64'd%d" % h.mac for lan in self.lans for h in lan.hosts]))
        out.write('\n')

        # FUNCTION cVlan
        out.write('function cVlan(vid_t vid): bool =\n')
        out.write(' or\n'.join(["    vid == 12'd%d" % lan.vlan for lan in self.lans]))
        out.write('\n')

        # FUNCTION vidRouterMAC
        vid_map = ["vid == 12'd%d: 48'h%x;" % (lan.vlan, lan.router)
                    for lan in self.lans]
        vid_map = '\n        '.join(vid_map)
        out.write('''
function vidRouterMAC(vid_t vid): MAC =
    case {{
        {vid_map}
        default: 48'h0;
    }}
'''.format(vid_map = vid_map))

        # FUNCTION ip2vid
        ip_map = ["ip == 32'h%x: 12'd%d;" % (int_of_ip(h.ip), h.vlan) for lan in self.lans for h in lan.hosts]
        ip_map = '\n        '.join(ip_map)
        out.write('''
function ip2vlan(IP4 ip): vid_t =
    case {{
        {ip_map}
        default: 12'd0;
    }}
'''.format(ip_map = ip_map))

        # FUNCTION hid2ip
        m = ["hid == 64'd%d: 32'h%x;" % (h.mac, int_of_ip(h.ip)) for lan in self.lans for h in lan.hosts]
        m = '\n        '.join(m)
        out.write('''
function hid2ip(hid_t hid): IP4 =
    case {{
        {m}
        default: 32'd0;
    }}
'''.format(m = m))

        # FUNCTION ip2hid
        m = ["ip == 32'h%x: 64'd%d;" % (int_of_ip(h.ip), h.mac) for lan in self.lans for h in lan.hosts]
        m = '\n        '.join(m)
        out.write('''
function ip2hid(IP4 ip): hid_t =
    case {{
        {m}
        default: 64'd0;
    }}
'''.format(m = m))

        # FUNCTION acl
        m = ["(ip.src == 32'h%x and ip.dst == 32'h%x)" % (
                int_of_ip(src.ip), int_of_ip(dst.ip))
                for (src, dst) in self.acl_pairs]
        m = ' or \n    '.join(m)
        out.write('''
function acl(vid_t srcvlan, vid_t dstvlan, ip4_t ip): bool =
    {m}
'''.format(m = m))

        # FUNCTION aclSrc, aclDst (derived)
        out.write('''
function aclSrc(vid_t srcvlan, vid_t dstvlan, ip4_t ip): bool = acl(srcvlan, dstvlan, ip)
function aclDst(vid_t srcvlan, vid_t dstvlan, ip4_t ip): bool = true
''')

        # FUNCTION cZone
        m = ["zid == 32'd%d" % lan.vlan for lan in self.lans] + ["zid == 32'd0"]
        m = ' or \n    '.join(m)
        out.write('''
function cZone(zid_t zid): bool =
    {m}
'''.format(m = m))

        # FUNCTION cRouter
        m = ["rid == 64'd%d" % lan.router for lan in self.lans]
        m = ' or \n    '.join(m)
        out.write('''
function cRouter(hid_t rid): bool =
    {m}
'''.format(m = m))

        # FUNCTION portConnected
        out.write('function portConnected(pid_t pid): bool = true (* assume all ports are connected *)\n')

        # FUNCTION routerPortZone
        zone_router_ports = []
        for lan in self.lans:
            zone_router_ports += ["pid == pid_t{64'd%d, 16'd%d}: 32'd%d;" % (
                lan.router, port, lan.vlan)
                for port in lan.g.node[lan.router]['ports'].values()]
        zone_router_ports = '\n        '.join(zone_router_ports)
        out.write('''
function routerPortZone(pid_t pid): zid_t =
    case {{
        {zone_router_ports}
        default: 32'd0;
    }}
'''.format( zone_router_ports = zone_router_ports ))

        # FUNCTION pid2mac
        hosts = ["pid == pid_t{64'd%d, 16'd1}: 48'h%x;" % ( h.mac, h.mac)
                 for lan in self.lans for h in lan.hosts]
        hosts = '\n        '.join(hosts)
        routers = ["pid == pid_t{64'd%d, 16'd%d}: 48'h%x;" % (lan.router, port, lan.router)
                    for lan in self.lans for port in g.node[lan.router]['ports'].values()]
        routers = '\n        '.join(routers)
        out.write('''
function pid2mac(pid_t pid): MAC =
    case {{
        {hosts}
        {routers}
        default: 48'd0;
    }}
'''.format(hosts=hosts, routers=routers))

        # FUNCTION mac2pid
        # Note the following assumptions on gateway routers:
        # - all gateway routers have exactly two ports
        # - port 1 connects to the gateway's zone
        # - the other port is > 1 and connects to the router-to-router fabric
        #   (i.e. zone 0)

        # NB: turns out this only needs to be defined for gateway router ports
        # on the interior router fabric.

        routers = []
        for lan in self.lans:
            assert(len(self.routers.node[lan.router]['ports']) == 1)
            routers.append("mac == 48'h%x: pid_t{64'd%d, 16'd%d};" % (
                lan.router, lan.router, self.routers.node[lan.router]['ports'].values()[0]))
        routers = '\n        '.join(routers)
        out.write('''
function mac2pid(MAC mac): pid_t =
    case {{
        {routers}
        default: pid_t{{64'd0, 16'd0}};
    }}
'''.format(hosts=hosts, routers=routers))
        
        # FUNCTION l3NextHop
        m = []
        for src_lan in self.lans:
            for dst_lan in self.lans:
                if src_lan == dst_lan:
                    continue
                m.append("rid == 64'd%d and vid == 12'd%d: nexthop_t{48'h%x, 16'd%d};" % (
                    src_lan.router,
                    dst_lan.vlan,
                    dst_lan.router,
                    self.routers.node[src_lan.router]['ports'].values()[0] ))
        m = '\n        '.join(m)
        out.write('''
function l3NextHop(hid_t rid, vid_t vid): nexthop_t =
    case {{
        {m}
        default: nexthop_t{{48'd0, 16'd0}};
    }}
'''.format(m=m))

        # FUNCTION cSwitch
        local_switches = ["sid == 64'd%d" % n
                          for lan in self.lans
                          for n in lan.g
                          if lan.g.node[n]['type'] == 'switch']
        router_switches = ["sid == 64'd%d" % n
                           for n in self.routers
                           if self.routers.node[n]['type'] == 'switch']
        routers = ["sid == 64'd%d" % lan.router for lan in self.lans]
        switches = ' or\n    '.join(local_switches + router_switches + routers)
        out.write('''
function cSwitch(hid_t sid): bool =
    {switches}
'''.format( switches=switches ))

        # FUNCTION link
        local_links = ["pid == pid_t{64'd%d, 16'd%d}: pid_t{64'd%d, 16'd%d};" % (
            n, lan.g.node[n]['ports'][neighbor], neighbor, lan.g.node[neighbor]['ports'][n])
            for lan in self.lans for n in lan.g for neighbor in lan.g.node[n]['ports']]
        local_links = '\n        '.join(local_links)
        router_links = ["pid == pid_t{64'd%d, 16'd%d}: pid_t{64'd%d, 16'd%d};" % (
            n, self.routers.node[n]['ports'][neighbor], neighbor, self.routers.node[neighbor]['ports'][n])
            for n in self.routers for neighbor in self.routers.node[n]['ports']]
        router_links = '\n        '.join(router_links)
        out.write('''
function link(pid_t pid): pid_t =
    case {{
        {local_links}
        {router_links}
        default: pid_t{{64'd0, 16'd0}};
    }}
'''.format( local_links = local_links
          , router_links = router_links ))

        # FUNCTION l2distance
        distances, out_ports = cocoon_of_networkx(g)

        distances_to_hosts = []
        ports_to_hosts = []
        for switch in g:
            if g.node[switch]['type'] == 'host':
                continue
            assert(switch in distances)
            for lan in self.lans:
                for h in lan.hosts:
                    if h.mac == switch:
                        continue
                    distances_to_hosts += ["hid == 64'd%d and vid == 12'd%d and dstaddr == 48'h%x: 8'd%d;" % (
                        switch, h.vlan, h.mac, distances[switch][h.mac])]
                    ports_to_hosts += ["hid == 64'd%d and vid == 12'd%d and dstaddr == 48'h%x: 16'd%d;" % (
                        switch, h.vlan, h.mac, out_ports[switch][h.mac])]
        distances_to_hosts = '\n        '.join(distances_to_hosts)
        ports_to_hosts = '\n        '.join(ports_to_hosts)

        distances_to_routers = []
        ports_to_routers = []
        for switch in g:
            for lan in self.lans:
                if switch == lan.router:
                    continue
                distances_to_routers += ["hid == 64'd%d and vid == 12'd0 and dstaddr == 48'h%x: 8'd%d;" % (
                    switch, lan.router, distances[switch][lan.router])]
                ports_to_routers += ["hid == 64'd%d and vid == 12'd0 and dstaddr == 48'h%x: 16'd%d;" % (
                    switch, lan.router, out_ports[switch][lan.router])]
        distances_to_routers = '\n        '.join(distances_to_routers)
        ports_to_routers = '\n        '.join(ports_to_routers)

        out.write('''
function l2distance(hid_t hid, vid_t vid, MAC dstaddr): uint<8> =
    case {{
        {distances_to_hosts}
        {distances_to_routers}
        default: 8'd0;
    }}
'''.format( distances_to_hosts = distances_to_hosts
          , distances_to_routers = distances_to_routers ))


        # FUNCTION l2NextHop
        out.write('''
function l2NextHop(hid_t hid, vid_t vid, MAC dstaddr): uint<16> =
    case {{
        {ports_to_hosts}
        {ports_to_routers}
        default: 16'd0;
    }}
'''.format( ports_to_hosts = ports_to_hosts
          , ports_to_routers = ports_to_routers ))

        # FUNCTION cPort
        pids = ["pid == pid_t{64'd%d, 16'd%d}" % (n, port)
                for n in g
                for port in g.node[n]['ports'].values()
                if g.node[n]['type'] == 'switch' or g.node[n]['type'] == 'router']
        pids = ' or\n    '.join(pids)
        out.write('''
function cSwitchPort(pid_t pid): bool = 
    {pids}
'''.format(pids=pids))

        # FUNCTION cPort
        pids = ["pid == pid_t{64'd%d, 16'd%d}" % (n, port)
                for n in g
                for port in g.node[n]['ports'].values()
                if g.node[n]['type'] == 'router' and port != 1]
        pids = ' or\n    '.join(pids)
        out.write('''
function cRouterPort(pid_t pid): bool = 
    {pids}
'''.format(pids=pids))

        # FUNCTION mac2hid
        m = ["mac == 48'h%x: 64'd%d;" % (h.mac, h.mac) for lan in self.lans for h in lan.hosts]
        m = '\n        '.join(m)
        out.write('''
function mac2hid(MAC mac): hid_t =
    case {{
        {m}
        default: 64'd0;
    }}
'''.format(m=m))

        # FUNCTION hid2mac
        m = ["hid == 64'd%d: 48'h%x;" % (h.mac, h.mac) for lan in self.lans for h in lan.hosts]
        m = '\n        '.join(m)
        out.write('''
function hid2mac(hid_t hid): MAC =
    case {{
        {m}
        default: 48'h0;
    }}
'''.format(m=m))

        # FUNCTION ip2vid
        m = ["ip == 32'd%d: 12'd%d;" % (int_of_ip(h.ip), h.vlan) for lan in self.lans for h in lan.hosts]
        m = '\n        '.join(m)
        out.write('''
function ip2vid(IP4 ip): vid_t =
    case {{
        {m}
        default: 12'd0;
    }}
'''.format(m=m))

        # FUNCTION vidRouter
        m = ["vid == 12'd%d: 64'd%d;" % (lan.vlan, lan.router) for lan in self.lans]
        m = '\n        '.join(m)
        out.write('''
function vidRouter(vid_t vid): hid_t =
    case {{
        {m}
        default: 64'd0;
    }}
'''.format(m=m))



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

    parser.add_argument( "--export_hsa"
                       , help="Export the configuration information for Spec0 and Spec3 to apply header space analysis."
                       , type=argparse.FileType('w') )
    parser.add_argument( "--export_cocoon"
                       , help="Export the configuration information for Spec0 and Spec3 to apply Cocoon. (Not yet implemented.)"
                       , type=argparse.FileType('w') )

    parser.add_argument( "--debug"
                       , help="print debug info"
                       , action="store_true" )

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

    p = PurdueNetwork( args )

#     spec0 = p.gen_spec_0()
#     spec1 = p.gen_spec_1(spec0)
#     spec2 = p.gen_spec_2(spec1)
#     spec3 = p.gen_spec_3(spec2)

    spec01 = p.gen_spec_0_1()
    spec11 = p.gen_spec_1_1()
    spec21 = p.gen_spec_2_1(spec11)
    spec3 = p.gen_spec_3(spec21)

    if args.export_cocoon:
        p.export_cocoon()

    def num_to_spec(n):
        if n == 0:
            return spec01
        if n == 1:
            return spec11
        if n == 2:
            return spec21
        if n == 3:
            return spec3

    for i in xrange(3):
        out_file = 'cmp%s%s.prd' % (i, i+1)
        print 'Writing Spec%s vs. Spec%s to %s' % (i, i+1, out_file)

        out = file(out_file, 'w')
        out.write('\n(\n%s\n)\nvlan := 0; ethDst := 0\n' % num_to_spec(i+1))
        out.write('\n<=\n\n')
        out.write('\n(\n%s\n)\nvlan := 0; ethDst := 0\n' % num_to_spec(i))
        out.close()

    # Clean up.
    if args.export_hsa:
        args.export_hsa.close()
    if args.export_cocoon:
        args.export_cocoon.close()
