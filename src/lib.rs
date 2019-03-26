#![feature(optin_builtin_traits, specialization, box_patterns)]

use std::collections::HashSet;
use std::hash::Hash;

pub mod builder;
pub use self::builder::*;

mod check;

pub trait Predicate: Clone + Hash + Eq {
    type Item: Clone + Hash + Eq;
    type Iter: Iterator<Item = Self::Item>;

    fn items(&self) -> Self::Iter;
    fn unify(&self, i: InfVar, item: &Self::Item) -> Self;
}

pub trait TypeConstraint: Hash + Eq {}
impl<T: Hash + Eq> TypeConstraint for T {}

#[derive(Debug)]
pub struct Solver<P: Predicate> {
    rules: HashSet<Rule<P>>,
}

pub struct Context(usize);

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub enum Quant {
    ForAll,
    Exists
}

#[derive(PartialEq, Eq, Hash, Clone, Copy)]
struct InfVarInner(usize);

#[derive(PartialEq, Eq, Hash, Clone, Copy)]
pub struct InfVar(usize);

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum Rule<P: Predicate> {
    True(P),
    False(P),

    Quantifier(Quant, InfVar, Box<Rule<P>>), // forall / exists

    Implication(Box<[Self; 2]>), // a -> b
    And(Box<[Self; 2]>),         // a and b
    // Or(Box<[Self; 2]>),       // a or b === ~a -> b
}

impl Default for Context {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl Context {
    pub fn new() -> Self { Self(0) }
}

impl std::fmt::Debug for InfVar {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "${}", self.0)
    }
}

impl<P: Predicate> Default for Solver<P> {
    fn default() -> Self {
        Self::new()
    }
}

impl<P: Predicate> Solver<P> {
    pub fn new() -> Self {
        Self {
            rules: HashSet::new(),
        }
    }

    pub fn add_rule<R: RuleAdder<P>>(&mut self, r: R) {
        r.add_rule(self)
    }
}

pub trait RuleAdder<P: Predicate> {
    fn add_rule(self, solver: &mut Solver<P>);
}

impl<I: Into<Rule<P>>, P: Predicate> RuleAdder<P> for I {
    default fn add_rule(self, solver: &mut Solver<P>) {
        solver.rules.insert(self.into());
    }
}

impl<P: Predicate, A, B> RuleAdder<P> for And<A, B>
where A: RuleBuilder<Predicate = P> + RuleAdder<P>,
      B: RuleBuilder<Predicate = P> + RuleAdder<P>,
      Self: Into<Rule<P>> {
    fn add_rule(self, solver: &mut Solver<P>) {
        self.0.add_rule(solver);
        self.1.add_rule(solver);
    }
}

#[macro_export]
macro_rules! rule {
    ($ctx:ident cons $pred:expr)
        => { $crate::builder::Constraint($pred) };
    ($ctx:ident not ($($rule:tt)*))
        => { $crate::builder::Not(rule!($ctx $($rule)*)) };
    ($ctx:ident if ($($a:tt)*) { $($b:tt)* })
        => { $crate::builder::Implication(rule!($ctx $($a)*), rule!($ctx $($b)*)) };
    (@internal forall) => { $crate::builder::ForAll };
    (@internal exists) => { $crate::builder::Exists };
    ($ctx:ident $quant:ident $a:ident { $($rule:tt)* })
        => {
            $crate::builder::Quantifier(rule!(@internal $quant), $crate::builder::Binder::new(
                &mut $ctx,
                #[allow(unused_mut, unused_variables)]
                |mut $ctx, $a| rule!($ctx $($rule)*))
            )
        };
    (@internal and $a:expr, $b:expr) => { $crate::builder::And($a, $b) };
    (@internal or $a:expr, $b:expr) => { $crate::builder::Or($a, $b) };
    (
        $ctx:ident
        $conj:ident
        ($($first:tt)*)
        ($($second:tt)*)
    ) => {
        rule!(@internal $conj rule!($ctx $($first)*), rule!($ctx $($second)*))
    };
    (
        $ctx:ident
        $conj:ident
        $( ($($a:tt)*) ($($b:tt)*) )+
    ) => {
        rule!(@internal $conj rule!($ctx $conj $(($($a)*))+), rule!($ctx $conj $(($($b)*))+))
    };
    (
        $ctx:ident
        $conj:ident
        ($($first:tt)*)
        $( ($($term:tt)*) )+
    ) => {
        rule!(@internal $conj rule!($ctx $($first)*), rule!($ctx $conj $(($($term)*))+))
    };
}

#[macro_export]
macro_rules! add_rules {
    ($ctx:ident in $solver:ident;) => {};
    (
        $ctx:ident in $solver:ident;

        cons $pred:expr;

        $($rest:tt)*
    ) => {
        $solver.add_rule(rule!($ctx cons $pred));

        add_rules! { $ctx in $solver; $($rest)* }
    };
    (
        $ctx:ident in $solver:ident;

        not ($($rule:tt)*);

        $($rest:tt)*
    ) => {
        $solver.add_rule(rule!($ctx not($($rule)*)));

        add_rules! { $ctx in $solver; $($rest)* }
    };
    (
        $ctx:ident in $solver:ident;

        if ($($rule:tt)*) { $($out:tt)* }

        $($rest:tt)*
    ) => {
        $solver.add_rule(rule!($ctx ($($rule)*) => ($($out)*)));

        add_rules! { $ctx in $solver; $($rest)* }
    };
    (
        $ctx:ident in $solver:ident;

        $conj:ident $(($($rule:tt)*))*;

        $($rest:tt)*
    ) => {
        $solver.add_rule(rule!($ctx $conj $(($($rule)*))*));

        add_rules! { $ctx in $solver; $($rest)* }
    };
    (
        $ctx:ident in $solver:ident;

        $quant:ident $a:ident {
            $($rule:tt)*
        }

        $($rest:tt)*
    ) => {
        $solver.add_rule(rule!($ctx $quant $a { $($rule)* } ));

        add_rules! { $ctx in $solver; $($rest)* }
    };
}
