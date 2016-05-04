type {:datatype} IP4;
function {:constructor} IP4(ip3: int, ip2: int, ip1: int, ip0: int): IP4;
type {:datatype} HEth;
function {:constructor} HEth(dstAddr: int, srcAddr: int): HEth;
type {:datatype} Packet;
function {:constructor} Packet(eth: HEth): Packet;
type {:datatype} _Location;
function {:constructor} L0Out(tree: bool, i1: int, i0: int, port: int): _Location;
function {:constructor} L0In(tree: bool, i1: int, i0: int, port: int): _Location;
function {:constructor} L01Out(tree: bool, i1: int, i0: int, port: int): _Location;
function {:constructor} L01In(tree: bool, i1: int, i0: int, port: int): _Location;
function {:constructor} L10Out(tree: bool, i1: int, r: int, port: int): _Location;
function {:constructor} L10In(tree: bool, i1: int, r: int, port: int): _Location;
function {:constructor} L12Out(tree: bool, i1: int, r: int, port: int): _Location;
function {:constructor} L2In(x: int, y: int, port: int): _Location;
function {:constructor} L2Out(x: int, y: int, port: int): _Location;
function {:constructor} L12In(tree: bool, i1: int, r: int, port: int): _Location;
type {:datatype} _Output;
function {:constructor} _Output(pkt: Packet, loc: _Location): _Output;
function {:constructor} Dropped(): _Output;
var _outp: _Output;
function p(): int;
function k(): int {
    (p() + p())
}
function incmodp(v: int): int {
    if (v+1 < p()) then v+1 else v+1-p()
}

function tree(addr: int): bool;
function i1(addr: int): int;
function i0(addr: int): int;
function port(addr: int): int;
function iL0Port(i1: int, i0: int, port: int): bool {
    (((i1 < p()) && (i0< p())) && (port < p()))
}
function goodPacket(p: Packet): bool {
    iL0Port(i1(dstAddr#HEth(eth#Packet(p))), i0(dstAddr#HEth(eth#Packet(p))), port(dstAddr#HEth(eth#Packet(p))))
}
function hash(eth: HEth): int;
function l1SwitchUp(tree: bool, i1: int, r: int): bool;
function iL1Port(i1: int, r: int, port: int): bool {
    (((i1 < p()) && (r < p())) && (port < p()))
}
function l2SwitchUp(x: int, y: int): bool;
function pick12port(tree: bool, i1: int, r: int, p: Packet): int {
    (if((tree == false)) then (if(l2SwitchUp(r, hash(eth#Packet(p)))) then hash(eth#Packet(p)) else incmodp(hash(eth#Packet(p)))) else (if(l2SwitchUp(hash(eth#Packet(p)), r)) then hash(eth#Packet(p)) else incmodp(hash(eth#Packet(p)))))
}
function iL2Port(x: int, y: int, port: int): bool {
    (((x < p()) && (y < p())) && (port < k()))
}
procedure a_L10In(tree: bool, i1: int, r: int, port: int, _pkt: Packet)
requires iL1Port(i1, r, port);
requires goodPacket(_pkt);
{
    assert !is#Dropped(_outp);
    assert is#L10Out(loc#_Output(_outp));
    assert ((((tree#L10Out(loc#_Output(_outp)) == tree(dstAddr#HEth(eth#Packet(_pkt)))) && (i1#L10Out(loc#_Output(_outp)) == i1(dstAddr#HEth(eth#Packet(_pkt))))) && (r#L10Out(loc#_Output(_outp)) < p())) && (port#L10Out(loc#_Output(_outp)) == i0(dstAddr#HEth(eth#Packet(_pkt)))));
    assert pkt#_Output(_outp) == _pkt;
    return;
    assert is#Dropped(_outp);
}
procedure c_L10In(tree: bool, i1: int, r: int, port: int, _pkt: Packet)
requires iL1Port(i1, r, port);
requires goodPacket(_pkt);
modifies _outp;
{
    var _loc: _Location;
    var pkt: Packet;
    pkt := _pkt;
    if(((tree(dstAddr#HEth(eth#Packet(pkt))) == tree) && (i1(dstAddr#HEth(eth#Packet(pkt))) == i1))) {
        if((i0(dstAddr#HEth(eth#Packet(pkt))) < p())) {
            _outp := _Output(pkt, L10Out(tree, i1, r, i0(dstAddr#HEth(eth#Packet(pkt)))));
        }
    } else {
        call c_L12Out(tree, i1, r, pick12port(tree, i1, r, pkt), pkt);
    }
}
procedure c_L12Out(tree: bool, i1: int, r: int, port: int, _pkt: Packet)
requires iL1Port(i1, r, port);
requires goodPacket(_pkt);
modifies _outp;
{
    var _loc: _Location;
    var pkt: Packet;
    pkt := _pkt;
    if((tree == false)) {
        if(l2SwitchUp(r, port)) {
            call c_L2In(r, port, i1, pkt);
        }
    } else {
        if(l2SwitchUp(port, r)) {
            call c_L2In(port, r, (p() + i1), pkt);
        }
    }
}
procedure c_L2In(x: int, y: int, port: int, _pkt: Packet)
requires iL2Port(x, y, port);
requires goodPacket(_pkt);
modifies _outp;
{
    var _loc: _Location;
    var pkt: Packet;
    pkt := _pkt;
    if((tree(dstAddr#HEth(eth#Packet(pkt))) == false)) {
        if(l1SwitchUp(false, i1(dstAddr#HEth(eth#Packet(pkt))), x)) {
            call c_L2Out(x, y, i1(dstAddr#HEth(eth#Packet(pkt))), pkt);
        } else {
            if(l1SwitchUp(true, hash(eth#Packet(pkt)), y)) {
                call c_L2Out(x, y, (p() + hash(eth#Packet(pkt))), pkt);
            } else {
                call c_L2Out(x, y, (p() + incmodp(hash(eth#Packet(pkt)))), pkt);
            }
        }
    } else {
        if(l1SwitchUp(true, i1(dstAddr#HEth(eth#Packet(pkt))), y)) {
            call c_L2Out(x, y, (p() + i1(dstAddr#HEth(eth#Packet(pkt)))), pkt);
        } else {
            if(l1SwitchUp(false, hash(eth#Packet(pkt)), x)) {
                call c_L2Out(x, y, hash(eth#Packet(pkt)), pkt);
            } else {
                call c_L2Out(x, y, incmodp(hash(eth#Packet(pkt))), pkt);
            }
        }
    }
}
procedure c_L2Out(x: int, y: int, port: int, _pkt: Packet)
requires iL2Port(x, y, port);
requires goodPacket(_pkt);
modifies _outp;
{
    var _loc: _Location;
    var pkt: Packet;
    pkt := _pkt;
    if((port < p())) {
        if(l1SwitchUp(false, port, x)) {
            call c_L12In(false, port, x, y, pkt);
        }
    } else {
        if(l1SwitchUp(true, (port - p()), y)) {
            call c_L12In(true, (port - p()), y, x, pkt);
        }
    }
}
procedure c_L12In(tree: bool, i1: int, r: int, port: int, _pkt: Packet)
requires iL1Port(i1, r, port);
requires goodPacket(_pkt);
modifies _outp;
{
    var _loc: _Location;
    var pkt: Packet;
    pkt := _pkt;
    if(((tree == tree(dstAddr#HEth(eth#Packet(pkt)))) && (i1 == i1(dstAddr#HEth(eth#Packet(pkt)))))) {
        _outp := _Output(pkt, L10Out(tree, i1, r, i0(dstAddr#HEth(eth#Packet(pkt)))));
    } else {
        call c_L12Out(tree, i1, r, pick12port(tree, i1, r, pkt), pkt);
    }
}
axiom (((p() < 128) && (p() > 2)));
axiom (forall v: int :: ((!(incmodp(v) == v)) && (incmodp(v) <p())) && (incmodp(v) >= 0)  );
axiom (forall e: HEth :: (hash(e) < p()) &&  (hash(e) >= 0));
axiom (forall tree: bool, i1: int, r1: int, r2: int :: (((!(r1 == r2)) && (!l1SwitchUp(tree, i1, r1))) ==> l1SwitchUp(tree, i1, r2)));
axiom (forall tree: bool, i1_1: int, i1_2: int, r: int :: (((!(i1_1 == i1_2)) && (!l1SwitchUp(tree, i1_1, r))) ==> l1SwitchUp(tree, i1_2, r)));
axiom (forall x1: int, y1: int, x2: int, y2: int :: (((!l2SwitchUp(x1, y1)) && (!((x1 == x2) && (y1 == y2)))) ==> l2SwitchUp(x2, y2)));
axiom (forall v: int :: (i0(v) > 0) && (i1(v) > 0) && (port(v) > 0));
procedure main ()
modifies _outp;
{   var tree: bool;
    var i1: int;
    var r: int;
    var port: int;
    var inppkt: Packet;
    havoc tree;
    havoc i1;
    havoc r;
    havoc port;
    assume iL1Port(i1, r, port);
    havoc inppkt;
    assume goodPacket(inppkt);
    _outp := Dropped();
    call c_L10In(tree, i1, r, port, inppkt);
    call a_L10In(tree, i1, r, port, inppkt);
}
