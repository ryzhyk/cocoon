import argparse
import random
import sys
import numpy
from itertools import chain

def mktid(args, src, dst, f):
    return args.num_classes*(args.num_dcs*src + dst) + f

if __name__ == '__main__':
    random.seed(0)
    parser = argparse.ArgumentParser()
    parser.add_argument( "num_dcs"
                       , help="number of DCs"
                       , type=int)
    parser.add_argument( "num_classes"
                       , help="number of traffic classes"
                       , type=int)
    parser.add_argument( "max_tun"
                       , help="maximal tunnel length"
                       , type=int)
    parser.add_argument( "k"
                       , help="fat tree parameter k"
                       , type=int)

    args = parser.parse_args()

    if args.num_dcs < 3:
        sys.stderr.write('must have at least 3 DCs')
        sys.exit(1)
    if args.max_tun < 1:
        sys.stderr.write('max tunnel length must have at least 1')
        sys.exit(1)
    if args.k < 2:
        sys.stderr.write('k must be at least 2')
        sys.exit(1)

    out = file("b4_bench.cfg.ccn", 'w')

    out.write("function isite(SiteId site): bool = site < 8'd{}\n".format(args.num_dcs))
    out.write("function iwanPort(SiteId site, uint<8> port): bool = isite(site) and port != site and port<8'd{}\n".format(args.num_dcs))
    out.write("function wanLink(SiteId site, uint<8> port): WANPort = WANPort{port, site}\n")
    out.write("function k(): uint<8> = 8'd{}\n".format(args.k))
    out.write("function tunnel(SiteId src, SiteId dst, ClassId f): TunnelId = case {\n")
    for src in range(0, args.num_dcs):
        out.write("    src==8'd{}: case {{\n".format(src))
        dsts = range(0, args.num_dcs)
        dsts.remove(src)
        for dst in dsts:
            out.write("        dst==8'd{}: case {{\n".format(dst))
            for cls in range(0, args.num_classes - 1):
                out.write("            f==ClassId{{16'd{0}}}: 16'd{1};\n".format(cls, mktid(args, src, dst, cls)))
            out.write("            default: 16'd{};\n".format(mktid(args, src, dst, args.num_classes - 1)))
            out.write("        };\n")
        out.write("        default: 16'hffff;\n")
        out.write("    };\n")
    out.write("    default: 16'hffff;\n")
    out.write("}\n")
               

    nexthop = dict()
    for src in range(0, args.num_dcs):
        dsts = range(0, args.num_dcs)
        dsts.remove(src)
        for dst in dsts:
            for cls in range(0, args.num_classes):
                tid = mktid(args, src, dst, cls)
                tunnel_len = random.randrange(1, min(args.num_dcs - 1, args.max_tun) + 1)
                dcs = range(0,args.num_dcs)
                dcs.remove(src)
                dcs.remove(dst)
                waypoints = [src]+random.sample(dcs, tunnel_len - 1)+[dst]
                for (wp, wpnext) in zip(waypoints[0::], waypoints[1::]):
                    if not (wp in nexthop.keys()):
                       nexthop[wp] = dict()
                    nexthop[wp][tid] = wpnext
    out.write("function nexthop(TunnelId tun, SiteId site): uint<8> = case {\n")
    for site in nexthop.keys():
        out.write("    site==8'd{}: case {{\n".format(site))
        tids = sorted(nexthop[site].keys())
        ranges = numpy.array_split(tids, args.num_dcs)
        for r in ranges:
            out.write("        tun>=16'd{} and tun<=16'd{}: case {{\n".format(r[0], r[len(r)-1]))
            for tid in r:
                out.write("            tun==16'd{}: 8'd{};\n".format(tid, nexthop[site][tid]))
            out.write("            default: 8'd255;\n")
            out.write("        };\n")
        out.write("        default: 8'd255;\n")
        out.write("    };\n")
    out.write("    default: 8'd255;\n")
    out.write("}\n")

    out.write("function coreLinkUp(SiteId site, uint<8> hash, uint<8> hash2, uint<8> port): bool = true\n")
    out.write("function podLinkUp(SiteId site, uint<8> subnet, uint<8> subsubnet, uint<8> port): bool = case {\n")
    for site in range(0, args.num_dcs):
        out.write("    site==8'd{}: case {{\n".format(site))
        for subnet in range(0, 2*args.k):
            out.write("        subnet==8'd{}: case {{\n".format(subnet))
            subsubnet = random.randrange(0, args.k)
            port      = random.randrange(0, args.k)
            out.write("            subsubnet==8'd{} and port==8'd{}: false;\n".format(subsubnet, port))
            out.write("            default: true;\n")
            out.write("        };\n")
        out.write("        default: true;\n")
        out.write("    };\n")
    out.write("    default: true;\n")
    out.write("}\n")
