{-# LANGUAGE QuasiQuotes, OverloadedStrings #-}

module Datalog.DataflogTemplate where

import Text.RawString.QQ
import Text.PrettyPrint

import PP

dataflogTemplate :: Doc -> Doc -> Doc
dataflogTemplate decls rules = [r|extern crate timely;
#[macro_use]
extern crate abomonation;
extern crate differential_dataflow;
extern crate num;
use std::ops::*;

use num::bigint::BigUint;
use abomonation::Abomonation;

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
struct uint{x:BigUint}

impl Default for uint {
    fn default() -> uint {uint{x: BigUint::default()}}
}
unsafe_abomonate!(uint);

impl uint {
    #[inline]
    pub fn parse_bytes(buf: &[u8], radix: u32) -> uint {
        uint{x: BigUint::parse_bytes(buf, radix).unwrap()}
    }
}

impl Shr<usize> for uint {
    type Output = uint;

    #[inline]
    fn shr(self, rhs: usize) -> uint {
        uint{x: self.x.shr(rhs)}
    }
}

impl Shl<usize> for uint {
    type Output = uint;

    #[inline]
    fn shl(self, rhs: usize) -> uint {
        uint{x: self.x.shl(rhs)}
    }
}

macro_rules! forward_binop {
    (impl $imp:ident for $res:ty, $method:ident) => {
        impl $imp<$res> for $res {
            type Output = $res;

            #[inline]
            fn $method(self, other: $res) -> $res {
                // forward to val-ref
                uint{x: $imp::$method(self.x, other.x)}
            }
        }
    }
}

forward_binop!(impl Add for uint, add);
forward_binop!(impl Sub for uint, sub);
forward_binop!(impl Div for uint, div);
forward_binop!(impl Rem for uint, rem);|]
    $$
    decls
    $$ [r|

fn main() {

    // start up timely computation
    timely::execute_from_args(std::env::args(), |worker| {
|]
    $$
    (nest' $ nest' rules)
    $$ [r|        //path.insert(Edge::Edge{f: 1, t: 2});
        //path.insert(Edge::Edge{f: 2, t: 3});
        //let e = *path.epoch();
        //println!("path time: {}", e);
        //path.advance_to(e+1);
        //path.flush();

        //while probe.less_than(path.time()) {
        //    worker.step();
        //};
    }).unwrap();
}|]
