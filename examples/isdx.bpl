function {:bvbuiltin "bvxor"} BV32_XOR(x:bv32, y:bv32) returns (bv32);
function {:bvbuiltin "bvlshr"} BV32_SHR(x:bv32, y:bv32) returns (bv32);
function {:bvbuiltin "bvshl"} BV64_SHL(x:bv64, y:bv64) returns (bv64);
function {:bvbuiltin "bvsub"} BV32_SUB(x:bv32, y:bv32) returns (bv32);
function {:bvbuiltin "bvand"} BV64_AND(x:bv64, y:bv64) returns (bv64);
function {:bvbuiltin "bvor"} BV64_OR(x:bv64, y:bv64) returns (bv64);
function {:bvbuiltin "bvult"} BV32_ULT(x:bv32, y:bv32) returns (bool);
function {:bvbuiltin "bvult"} BV16_ULT(x:bv16, y:bv16) returns (bool);

type AS = bv16;
type IP = bv32;

type {:datatype} NetMask;
function {:constructor} NetMask(mask: bv32, len: bv32): NetMask;

type {:datatype} NetMasks;
function {:constructor} nilNetMasks(): NetMasks;
function {:constructor} consNetMasks(head: NetMask, tail: NetMasks): NetMasks;

//type {:datatype} NetMasks;
//function {:constructor} NetMasks(len: int, masks: [int] NetMask): NetMasks;

type {:datatype} ASMasks;
function {:constructor} ASMasks(as: AS, masks: NetMasks): ASMasks;

type {:datatype} BGPDB;
function {:constructor} nilBGPDB(): BGPDB;
function {:constructor} consBGPDB(head: ASMasks, tail: BGPDB): BGPDB;

type {:datatype} ASList;
function {:constructor} nilASList(): ASList;
function {:constructor} consASList(head: AS, tail: ASList): ASList;

//function elemASList(as:AS, lst: ASList): bool {
//    if is#nilASList(lst) then
//        false 
//    else 
//        ((head#consASList(lst) == as) || elemASList(as, tail#consASList(lst)))
//}
//
//function prefix_match(ip: IP, mask: NetMask): bool {
//    BV32_SHR((BV32_XOR(ip, mask#NetMask(mask))), BV32_SUB(32bv32, len#NetMask(mask))) == 0bv32
//}
//
//function prefix_match_many(ip: IP, masks: NetMasks): bool {
//    if is#nilNetMasks(masks) then (
//        false
//    ) else (
//        if prefix_match(ip, head#consNetMasks(masks)) then
//            true
//        else
//            prefix_match_many(ip, tail#consNetMasks(masks))
//    )
//}
//
//function bgp_match(ip: IP, db: BGPDB): ASList {
//    if is#nilBGPDB(db) then (
//        nilASList()
//    ) else (
//        if (prefix_match_many(ip, masks#ASMasks(head#consBGPDB(db)))) then 
//            consASList(as#ASMasks(head#consBGPDB(db)), bgp_match(ip, tail#consBGPDB(db)))
//        else
//            bgp_match(ip, tail#consBGPDB(db))
//    )
//}
//
//function check_bgp_match(ip: IP, as: AS, db:BGPDB): bool {
//    if is#nilBGPDB(db) then (
//        false
//    ) else (
//        if as#ASMasks(head#consBGPDB(db)) == as then
//            (prefix_match_many(ip, masks#ASMasks(head#consBGPDB(db))) || check_bgp_match(ip, as, tail#consBGPDB(db)))
//        else 
//            check_bgp_match(ip, as, tail#consBGPDB(db))
//    )
//}

procedure elemASList(as:AS, lst: ASList) returns (ret: bool) {
    if (is#nilASList(lst)) {
        ret := false;
    } else {
        if (head#consASList(lst) == as) {
            ret := true;
        } else {
            call ret := elemASList(as, tail#consASList(lst));
        }
    }
}

procedure prefix_match(ip: IP, mask: NetMask) returns (ret: bool) {
    ret := BV32_SHR((BV32_XOR(ip, mask#NetMask(mask))), BV32_SUB(32bv32, len#NetMask(mask))) == 0bv32;
}

procedure prefix_match_many(ip: IP, masks: NetMasks) returns (ret: bool) {
//    var i: int;
//    i := 0;
//    while (i < len#NetMasks(masks)) {
//        if (prefix_match(ip, masks#NetMasks(masks)[i])) {
//            ret := true;
//            return;
//        }
//        i := i+1;
//    }
//    ret := false;

    var match : bool;
    if (is#nilNetMasks(masks)) {
        ret := false;
        return;
    } else {
        call match := prefix_match(ip, head#consNetMasks(masks));
        if (match) {
            ret := true;
        } else {
            call ret := prefix_match_many(ip, tail#consNetMasks(masks));
        }
    }
}

procedure bgp_match(ip: IP, db: BGPDB) returns (ret: ASList) {
    var match : bool;
    var rest : ASList;
    if (is#nilBGPDB(db)) {
        ret := nilASList();
        return;
    } else {
        call match := prefix_match_many(ip, masks#ASMasks(head#consBGPDB(db)));
        if (match) {
            call rest := bgp_match(ip, tail#consBGPDB(db));
            ret := consASList(as#ASMasks(head#consBGPDB(db)), rest);
        } else {
            call ret := bgp_match(ip, tail#consBGPDB(db));
        }
    }
}

procedure check_bgp_match(ip: IP, as: AS, db:BGPDB) returns (ret: bool) {
    if (is#nilBGPDB(db)) {
        ret := false;
    } else {
        if (as#ASMasks(head#consBGPDB(db)) == as) {
            call ret := prefix_match_many(ip, masks#ASMasks(head#consBGPDB(db)));
            if (ret) {return;}
            call ret := check_bgp_match(ip, as, tail#consBGPDB(db));
        } else {
            call ret := check_bgp_match(ip, as, tail#consBGPDB(db));
        }
    }
}

function encode1(as: AS) : bv64 {
    BV64_SHL(1bv64, 0bv48 ++ as)
}

procedure encode(ass: ASList, mask: bv64) returns (ret: bv64) {
    var enchead : bv64;
    if (is#nilASList(ass)) {
        ret := mask;
    } else {
        assume BV16_ULT(head#consASList(ass), 64bv16);
        enchead := encode1(head#consASList(ass));
        call ret := encode(tail#consASList(ass), BV64_OR(mask, enchead));
    }
}



procedure main() {
    var db: BGPDB;
    var ip: IP;
    var as: AS;
    var matches : ASList;
    var encoded1 : bv64;
    var encoded2 : bv64;
    var correct_answer : bool;

    assume BV16_ULT(as, 64bv16);
 
    call matches := bgp_match(ip, db);
    call encoded1 := encode(matches, 0bv64);
    encoded2 := encode1(as);

    call correct_answer := check_bgp_match(ip, as, db);

    assert  correct_answer == (!(BV64_AND(encoded1, encoded2) == 0bv64));
}

//apply mask

//decode result
