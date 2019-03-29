#![feature(optin_builtin_traits, specialization, box_patterns)]

use std::collections::HashSet;
use std::hash::Hash;

pub mod builder;
pub use self::builder::*;

mod check;

use std::fmt::Debug;

pub trait Predicate: Clone + Hash + Eq + Debug {
    type Item: Clone + Hash + Eq + Debug;
    type Iter: Iterator<Item = Self::Item>;

    fn not(&self) -> Self;
    fn items(&self) -> Self::Iter;
    fn apply(&self, i: InfVar, item: &Self::Item) -> Self;
    // fn unify(
    //     &self,
    //     i: &Self,
    // ) -> Option<std::collections::HashMap<InfVar, Result<Self::Item, InfVar>>>;
}

pub trait TypeConstraint: Hash + Eq {}
impl<T: Hash + Eq> TypeConstraint for T {}

#[derive(Debug)]
pub struct Solver<P: Predicate> {
    rules: HashSet<Rule<P>>,
}

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub enum Quant {
    ForAll,
    Exists,
}

#[derive(PartialEq, Eq, Hash, Clone, Copy)]
struct InfVarInner(usize);

#[derive(PartialEq, Eq, Hash, Clone, Copy)]
pub struct InfVar(usize);

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum Rule<P: Predicate> {
    Axiom(P),

    Quantifier(Quant, InfVar, Box<Rule<P>>), // forall / exists

    Implication(Box<[Self; 2]>), // a -> b
    And(Box<[Self; 2]>),         // a and b
                                 // Or(Box<[Self; 2]>),       // a or b === ~a -> b
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
where
    A: RuleBuilder<Predicate = P> + RuleAdder<P>,
    B: RuleBuilder<Predicate = P> + RuleAdder<P>,
    Self: Into<Rule<P>>,
{
    fn add_rule(self, solver: &mut Solver<P>) {
        self.0.add_rule(solver);
        self.1.add_rule(solver);
    }
}

#[macro_export]
macro_rules! rule {
    (cons $pred:expr)
        => { $crate::builder::Constraint($pred) };
    (not ($($rule:tt)*))
        => { $crate::builder::Not(rule!($($rule)*)) };
    (if ($($a:tt)*) { $($b:tt)* })
        => { $crate::builder::Implication(rule!($($a)*), rule!($($b)*)) };
    (@internal forall) => { $crate::builder::ForAll };
    (@internal exists) => { $crate::builder::Exists };
    ($quant:ident $a:ident { $($rule:tt)* })
        => {
            $crate::builder::Quantifier(rule!(@internal $quant), $crate::builder::Binder::new(
                #[allow(unused_mut, unused_variables)]
                |$a| rule!($($rule)*))
            )
        };
    (@internal and $a:expr, $b:expr) => { $crate::builder::And($a, $b) };
    (@internal or $a:expr, $b:expr) => { $crate::builder::Or($a, $b) };
    (
        $conj:ident
        ($($first:tt)*)
        ($($second:tt)*)
    ) => {
        rule!(@internal $conj rule!($($first)*), rule!($($second)*))
    };
    (
        $conj:ident
        $( ($($a:tt)*) ($($b:tt)*) )+
    ) => {
        rule!(@internal $conj rule!($conj $(($($a)*))+), rule!($conj $(($($b)*))+))
    };
    (
        $conj:ident
        ($($first:tt)*)
        $( ($($term:tt)*) )+
    ) => {
        rule!(@internal $conj rule!($($first)*), rule!($conj $(($($term)*))+))
    };
}

#[macro_export]
macro_rules! add_rules {
    (in $solver:ident;) => {};
    (
        in $solver:ident;

        cons $pred:expr;

        $($rest:tt)*
    ) => {
        $solver.add_rule(rule!(cons $pred));

        add_rules! { in $solver; $($rest)* }
    };
    (
        in $solver:ident;

        not ($($rule:tt)*);

        $($rest:tt)*
    ) => {
        $solver.add_rule(rule!(not($($rule)*)));

        add_rules! { in $solver; $($rest)* }
    };
    (
        in $solver:ident;

        if ($($rule:tt)*) { $($out:tt)* }

        $($rest:tt)*
    ) => {
        $solver.add_rule(rule!( if ($($rule)*) { $($out)* } ));

        add_rules! { in $solver; $($rest)* }
    };
    (
        in $solver:ident;

        $conj:ident $(($($rule:tt)*))*;

        $($rest:tt)*
    ) => {
        $solver.add_rule(rule!($conj $(($($rule)*))*));

        add_rules! { in $solver; $($rest)* }
    };
    (
        in $solver:ident;

        $quant:ident $a:ident {
            $($rule:tt)*
        }

        $($rest:tt)*
    ) => {
        $solver.add_rule(rule!($quant $a { $($rule)* } ));

        add_rules! { in $solver; $($rest)* }
    };
}
