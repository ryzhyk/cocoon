{-# LANGUAGE QuasiQuotes, OverloadedStrings #-}

module Datalog.DataflogTemplate where

import Text.RawString.QQ
import Text.PrettyPrint

import PP

dataflogTemplate :: Doc -> Doc -> Doc -> Doc -> Doc -> Doc -> Doc -> Doc -> Doc -> Doc -> Doc
dataflogTemplate decls facts relations sets rules advance delta cleanup undo handlers = [r|#![allow(non_snake_case)]
#![allow(non_camel_case_types)]
#![allow(non_shorthand_field_patterns)]
#![allow(unused_variables)]
extern crate timely;
#[macro_use]
extern crate abomonation;
extern crate differential_dataflow;
extern crate num;

use num::bigint::BigUint;
use abomonation::Abomonation;

#[macro_use] 
extern crate serde_derive;
extern crate serde;
extern crate serde_json;
use std::ops::*;
use serde::ser::*;
use serde::de::*;
use std::str::FromStr;
use serde::de::Error;
use std::collections::HashSet;
use std::collections::HashMap;
use std::io::{stdin, stdout, Write};
use std::cell::RefCell;
use std::rc::Rc;
use std::hash::Hash;
use std::fmt::Debug;
use serde_json as json;

use timely::progress::nested::product::Product;
use timely::dataflow::*;
use timely::dataflow::scopes::Child;
use timely::dataflow::operators::*;
use timely::dataflow::operators::feedback::Handle;

use differential_dataflow::input::Input;
use differential_dataflow::{Data, Collection, Hashable};
use differential_dataflow::operators::*;
use differential_dataflow::lattice::Lattice;

/// A collection defined by multiple mutually recursive rules.
///
/// A `Variable` names a collection that may be used in mutually recursive rules. This implementation
/// is like the `Variable` defined in `iterate.rs` optimized for Datalog rules: it supports repeated
/// addition of collections, and a final `distinct` operator applied before connecting the definition.
pub struct Variable<'a, G: Scope, D: Default+Data+Hashable>
where G::Timestamp: Lattice+Ord {
    feedback: Option<Handle<G::Timestamp, u64,(D, Product<G::Timestamp, u64>, isize)>>,
    current: Collection<Child<'a, G, u64>, D>,
    cycle: Collection<Child<'a, G, u64>, D>,
}

impl<'a, G: Scope, D: Default+Data+Hashable> Variable<'a, G, D> where G::Timestamp: Lattice+Ord {
    /// Creates a new `Variable` from a supplied `source` stream.
    pub fn from(source: &Collection<Child<'a, G, u64>, D>) -> Variable<'a, G, D> {
        let (feedback, cycle) = source.inner.scope().loop_variable(u64::max_value(), 1);
        let cycle = Collection::new(cycle);
        let mut result = Variable { feedback: Some(feedback), current: cycle.clone(), cycle: cycle };
        result.add(source);
        result
    }
    /// Adds a new source of data to the `Variable`.
    pub fn add(&mut self, source: &Collection<Child<'a, G, u64>, D>) {
        self.current = self.current.concat(source);
    }
}

impl<'a, G: Scope, D: Default+Data+Hashable> ::std::ops::Deref for Variable<'a, G, D> where G::Timestamp: Lattice+Ord {
    type Target = Collection<Child<'a, G, u64>, D>;
    fn deref(&self) -> &Self::Target {
        &self.cycle
    }
}

impl<'a, G: Scope, D: Default+Data+Hashable> Drop for Variable<'a, G, D> where G::Timestamp: Lattice+Ord {
    fn drop(&mut self) {
        if let Some(feedback) = self.feedback.take() {
            self.current.distinct()
                        .inner
                        .connect_loop(feedback);
        }
    }
}

#[derive(Eq, PartialOrd, PartialEq, Ord, Debug, Clone, Hash)]
struct Uint{x:BigUint}

impl Default for Uint {
    fn default() -> Uint {Uint{x: BigUint::default()}}
}
unsafe_abomonate!(Uint);

impl Serialize for Uint {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where S: Serializer
    {
        serializer.serialize_str(&self.x.to_str_radix(10))
    }
}

impl<'de> Deserialize<'de> for Uint {
    fn deserialize<D>(deserializer: D) -> Result<Uint, D::Error>
        where D: Deserializer<'de>
    {
        match String::deserialize(deserializer) {
            Ok(s) => match BigUint::from_str(&s) {
                        Ok(i)  => Ok(Uint{x:i}),
                        Err(_) => Err(D::Error::custom(format!("invalid integer value: {}", s)))
                     },
            Err(e) => Err(e)
        }
    }
}

impl Uint {
    #[inline]
    pub fn parse_bytes(buf: &[u8], radix: u32) -> Uint {
        Uint{x: BigUint::parse_bytes(buf, radix).unwrap()}
    }
}

impl Shr<usize> for Uint {
    type Output = Uint;

    #[inline]
    fn shr(self, rhs: usize) -> Uint {
        Uint{x: self.x.shr(rhs)}
    }
}

impl Shl<usize> for Uint {
    type Output = Uint;

    #[inline]
    fn shl(self, rhs: usize) -> Uint {
        Uint{x: self.x.shl(rhs)}
    }
}

macro_rules! forward_binop {
    (impl $imp:ident for $res:ty, $method:ident) => {
        impl $imp<$res> for $res {
            type Output = $res;

            #[inline]
            fn $method(self, other: $res) -> $res {
                // forward to val-ref
                Uint{x: $imp::$method(self.x, other.x)}
            }
        }
    }
}

forward_binop!(impl Add for Uint, add);
forward_binop!(impl Sub for Uint, sub);
forward_binop!(impl Div for Uint, div);
forward_binop!(impl Rem for Uint, rem);|]
    $$
    decls
    $$
    facts
    $$
    relations
    $$ [r|

#[derive(Serialize, Deserialize, Debug)]
enum Request {
    start,
    rollback,
    commit,
    add(Fact),
    del(Fact),
    chk(Relation),
    enm(Relation)
}

#[derive(Serialize, Deserialize, Debug)]
enum Response<T> {
    err(String),
    ok(T)
}

fn xupd<T>(s: &Rc<RefCell<HashSet<T>>>, ds: &Rc<RefCell<HashMap<T, i8>>>, x:&T, w: isize) 
where T: Eq + Hash + Clone + Debug {
    if w > 0 {
        let new = s.borrow_mut().insert(x.clone());
        if new {
            let f = |e: &mut i8| if *e == -1 {*e = 0;} else if *e == 0 {*e = 1};
            f(ds.borrow_mut().entry(x.clone()).or_insert(0));
        };
    } else if w < 0 {
        let present = s.borrow_mut().remove(x);
        if present {
            let f = |e: &mut i8| if *e == 1 {*e = 0;} else if *e == 0 {*e = -1;};
            f(ds.borrow_mut().entry(x.clone()).or_insert(0));
        };
    }
}

fn upd<T>(s: &Rc<RefCell<HashSet<T>>>, x:&T, w: isize) 
where T: Eq + Hash + Clone + Debug {
    if w > 0 {
        s.borrow_mut().insert(x.clone());
    } else if w < 0 {
        s.borrow_mut().remove(x);
    }
}

fn main() {

    // start up timely computation
    timely::execute_from_args(std::env::args(), |worker| {
        let probe = probe::Handle::new();
        let mut probe1 = probe.clone();

        let mut xaction : bool = false;
|]
    $$
    (nest' $ nest' sets)
    $$
    (nest' $ nest' rules)
    $$ [r|
        let mut epoch = 0;
        let stream = json::Deserializer::from_reader(stdin()).into_iter::<Request>();

        for val in stream {
            //print!("epoch: {}\n", epoch);
            let req = match val {
                            Ok(r)  => {
                                //print!("r: {:?}\n", r);
                                r
                            },
                            Err(e) => {
                                print!("{}\n", e);
                                std::process::exit(-1);
                            }
                        };|]
    $$
    (nest' $ nest' $ nest' advance)
    $$ [r|
            macro_rules! insert {
                ($rel:ident, $set:ident, $args:expr) => {{
                    let v = $args;
                    if !$set.borrow().contains(&v) {
                        $rel.insert(v);
                        epoch = epoch+1;
                        advance!();
                        while probe.less_than($rel.time()) {
                            worker.step();
                        };
                    };
                }}
            }

            macro_rules! insert_resp {
                ($rel:ident, $set:ident, $args:expr) => {{
                    insert!($rel, $set, $args);
                    let resp: Response<()> = Response::ok(());
                    serde_json::to_writer(stdout(), &resp).unwrap();
                    stdout().flush().unwrap();
                }}
            }

            macro_rules! remove {
                ($rel:ident, $set:ident, $args:expr) => {{
                    let v = $args;
                    if $set.borrow().contains(&v) {
                        $rel.remove(v);
                        epoch = epoch+1;
                        advance!();
                        while probe.less_than($rel.time()) {
                            worker.step();
                        };
                    };
                }}
            }

            macro_rules! remove_resp {
                ($rel:ident, $set:ident, $args:expr) => {{
                    remove!($rel, $set, $args);
                    let resp: Response<()> = Response::ok(());
                    serde_json::to_writer(stdout(), &resp).unwrap();
                    stdout().flush().unwrap();
                }}
            }

            macro_rules! check {
                ($set:expr) => {{
                    let resp = Response::ok(!$set.borrow().is_empty());
                    serde_json::to_writer(stdout(), &resp).unwrap();
                    stdout().flush().unwrap();
                }}
            }

            macro_rules! enm {
                ($set:expr) => {{
                    let resp = Response::ok((*$set).clone());
                    serde_json::to_writer(stdout(), &resp).unwrap();
                    stdout().flush().unwrap();
                }}
            }|]
    $$
    (nest' $ nest' $ nest' delta)
    $$ 
    (nest' $ nest' $ nest' cleanup)
    $$
    (nest' $ nest' $ nest' undo)
    $$ [r|
            match req {
                Request::start                       => {
                    let resp = if xaction {
                                   Response::err(format!("transaction already in progress"))
                               } else {
                                   delta_cleanup!();
                                   xaction = true;
                                   Response::ok(())
                               };
                    serde_json::to_writer(stdout(), &resp).unwrap();
                    stdout().flush().unwrap();
                },
                Request::rollback                    => {
                    let resp = if !xaction {
                                   Response::err(format!("no transaction in progress"))
                               } else {
                                   delta_undo!();
                                   delta_cleanup!();
                                   xaction = false;
                                   Response::ok(())
                               };
                    serde_json::to_writer(stdout(), &resp).unwrap();
                    stdout().flush().unwrap();
                },
                Request::commit                      => {
                    let resp = if !xaction {
                                   Response::err(format!("no transaction in progress"))
                               } else {
                                   let mut delta = HashSet::new();
                                   delta!(delta);
                                   delta_cleanup!();
                                   xaction = false;
                                   Response::ok(delta)
                               };
                    serde_json::to_writer(stdout(), &resp).unwrap();
                    stdout().flush().unwrap();
                },|]
    $$
    (nest' $ nest' $ nest' $ nest' handlers)
{-    $$ [r|
                    _ => {
                        let resp: Response<()> = Response::err(format!("unknown request: {:?}", req));
                        serde_json::to_writer(stdout(), &resp).unwrap();
                    }
                };-}
    $$ [r|
            };
        };
    }).unwrap();
}|]

cargoTemplate :: String -> Doc
cargoTemplate specname  = [r|[package]
name = "|]
    <> pp specname <> [r|"
version = "0.1.0"

[dependencies.graph_map]
git="https://github.com/frankmcsherry/graph-map.git"

[dependencies.timely]
git="https://github.com/frankmcsherry/timely-dataflow"

[dependencies.differential-dataflow]
git="https://github.com/frankmcsherry/differential-dataflow.git"


[dev-dependencies]
getopts="0.2.14"
rand="0.3.13"
byteorder="0.4.2"
itertools="^0.6"

[dependencies]
abomonation="0.4.4"
timely_sort="0.1.6"
timely_communication="0.1.5"
fnv="1.0.2"
num = "0.1"
serde = "1.0"
serde_derive = "1.0"
serde_json = "1.0.2"

[features]
default = []
logging = ["timely/logging"]

[profile.release]
opt-level = 3
debug = true
rpath = false
lto = false
debug-assertions = false

[[bin]]
name = "|] <> pp specname <> [r|"
path = "./|] <> pp specname <> [r|.rs"|]
