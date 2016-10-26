// TODO: try yields annotations

procedure corral_atomic_begin();
procedure corral_atomic_end();
procedure corral_thread_join_all();

// model flow ids as mathematical integers
type FlowId = int;

// packet: flow id + payload
type {:datatype} Packet;
function {:constructor} Packet(flow: FlowId, payload: int): Packet;

// (per-flow state, packet) pair, used as output type for functions that take a packet, 
// return a modified packet and modified flow state
type {:datatype} StatePacket;
function {:constructor} StatePacket(state: int, packet: Packet): StatePacket;

// int or Nothing
type {:datatype} MaybeInt;
function {:constructor} Just(v: int): MaybeInt;
function {:constructor} Nothing(): MaybeInt;

// abstract state: per-flow state modeled as integer
type AbsState = [FlowId] MaybeInt;

// middlebox behavior: uninterpreted function: M: (state, pkt)->(state, pkt)
function M(state: int, pkt: Packet): StatePacket;

// initial state for a flow
const MInitState: int;

var absState: AbsState;

var absRes: Packet;

// abstract behavior: yield; apply M()
procedure AbsRole(packet: Packet)
modifies absState;
{
    var res: StatePacket;
    if (absState[flow#Packet(packet)] == Nothing()) {
        absState[flow#Packet(packet)] := Just(MInitState);
    } 
    res := M(v#Just(absState[flow#Packet(packet)]), packet);
    absState[flow#Packet(packet)] := Just(state#StatePacket(res));
    absRes := packet#StatePacket(res);
}

type ServerId = int;

// concrete state: 
// - controller state: flow's current location
var flowmap: [FlowId] ServerId;

// - per-flow routing rule
var routingTable: [FlowId] ServerId;

// - per-flow, per-server state
var serverFlows: [ServerId, FlowId] MaybeInt;

// - per-flow, per-server forwarding table
var serverForward: [ServerId, FlowId] MaybeInt;

// - per-flow, per-server buffering flag
var serverBuffer: [ServerId, FlowId] bool;

// state invariant:
// - flow's current location stores its correct state (i.e., equivalent to its abstract state)



// additional controller invariants (do not hold in the middle of controller execution)
// - the routing table either stores correct location of the flow
// - buffering flag is false

// packet thread
// - start at the switch
// - forward according to the routing table
// - at the server: forward or process locally
var concRes: Packet;

procedure ConcRole(packet: Packet)
modifies serverFlows;
{
    var server: ServerId;
    call corral_atomic_begin();
    call assumeStateRefinement();
    server := routingTable[flow#Packet(packet)];
    call corral_atomic_end();
    havoc serverFlows;

    call concRes := ConcServer(server, packet);
}

procedure {:inline} assumeStateRefinement() {
    assume (forall flow: FlowId :: absState[flow] == serverFlows[flowmap[flow], flow] || serverBuffer[flowmap[flow], flow]);
}

procedure {:inline} assertStateRefinement() {
    assert (forall flow: FlowId :: absState[flow] == serverFlows[flowmap[flow], flow] || serverBuffer[flowmap[flow], flow]);
}

procedure {:inline} assumeControllerInvariant() {
    assume (forall flow: FlowId :: routingTable[flow] == flowmap[flow]);
    assume (forall server: ServerId, flow: FlowId :: serverBuffer[server, flow] == false);
}

procedure {:inline} assertControllerInvariant() {
    assert (forall flow: FlowId :: routingTable[flow] == flowmap[flow]);
}

procedure ConcServer(server: ServerId, packet: Packet) returns (packet': Packet)
{
    var server': ServerId;
    var res: StatePacket;

    call corral_atomic_begin();
    call assumeStateRefinement();

    assume !serverBuffer[server, flow#Packet(packet)];
    if (serverForward[server, flow#Packet(packet)] != Nothing()) {
        server' := v#Just(serverForward[server, flow#Packet(packet)]);

        call corral_atomic_end();
        havoc serverFlows;

        call packet' := ConcServer(server', packet);
    } else {
        if (serverFlows[server, flow#Packet(packet)] == Nothing()) {
            serverFlows[server, flow#Packet(packet)] := Just(MInitState);
        } 
        res := M(v#Just(serverFlows[server, flow#Packet(packet)]), packet);
        serverFlows[server, flow#Packet(packet)] := Just(state#StatePacket(res));
        packet' := packet#StatePacket(res);
        call AbsRole(inpPkt);

        call assertStateRefinement();
        call corral_atomic_end();
    }
}


// controller thread:
procedure controller()
{
    var flowstate : MaybeInt;
    var flow: FlowId;
    var dst: ServerId;
    var src: ServerId;

    // pick a flow
    havoc flow;
    src := flowmap[flow];

    // pick a new destination
    havoc dst;
    assume dst != src;

    // - start buffering at the destination
    call corral_atomic_begin();
    call assumeStateRefinement();
    serverBuffer[dst, flow] := true;
    call assertStateRefinement();
    call corral_atomic_end();

    // - start redirecting at the source; remove state at the source
    call corral_atomic_begin();
    call assumeStateRefinement();
    serverForward[src, flow] := Just(dst);
    flowstate := serverFlows[src, flow];
    serverFlows[src, flow] := Nothing();
    flowmap[flow] := dst;
    call assertStateRefinement();
    call corral_atomic_end();

    // - install state on the destination
    call corral_atomic_begin();
    call assumeStateRefinement();
    serverFlows[dst, flow] := flowstate;
    call assertStateRefinement();
    call corral_atomic_end();

    // - redirect in the switch
    call corral_atomic_begin();
    call assumeStateRefinement();
    routingTable[flow] := dst;
    call assertStateRefinement();
    call corral_atomic_end();

    // - wait for all buffered packets to be delivered, remove redirect
    call corral_atomic_begin();
    call assumeStateRefinement();
    assume concRunning == false;
    serverForward[src, flow] := Nothing();
    call assertStateRefinement();
    call corral_atomic_end();
    
    call assertControllerInvariant();
    
}


var absJoin: bool;
var concJoin: bool;
var concRunning: bool;

procedure conc_thread(p: Packet)
{
    concRunning := true;
    call ConcRole(p);
    concRunning := false;
    concJoin := true;
}

var inpPkt: Packet;

procedure {:entrypoint} main() 
{
    var ap': Packet;
    var cp': Packet;
    havoc inpPkt;
    
    call assumeControllerInvariant();

    //absJoin := false;
    concJoin := false;
    concRunning := false;
    async call conc_thread(inpPkt);
    async call controller();
    //assume absJoin;
    assume concJoin;

    call assertStateRefinement();
    assert absRes == concRes;
}

