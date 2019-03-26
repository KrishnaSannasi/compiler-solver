
use super::{Predicate, Rule, InfVar, Quant, Context};

pub struct ForAll;
pub struct Exists;

pub struct Constraint<P: Predicate>(pub P);
pub struct Quantifier<Q, R: RuleBuilder>(pub Q, pub Binder<R>);

pub struct Implication<A: RuleBuilder, B: RuleBuilder>(pub A, pub B);
pub struct And<A: RuleBuilder, B: RuleBuilder>(pub A, pub B);
pub struct Or<A: RuleBuilder, B: RuleBuilder>(pub A, pub B);

pub struct Not<A: RuleBuilder>(pub A);
pub struct Binder<R: RuleBuilder>(InfVar, R);

impl<R: RuleBuilder> Binder<R> {
    pub fn new<F: for<'a> FnOnce(&'a mut Context, InfVar) -> R>(ctx: &mut Context, f: F) -> Self {
        use std::sync::atomic::{AtomicUsize, Ordering};

        static VAR: AtomicUsize = AtomicUsize::new(0);

        ctx.0 += 1;
        let var = InfVar(VAR.fetch_add(1, Ordering::Relaxed));

        let rule = f(ctx, var);

        ctx.0 -= 1;

        // QUANT_ID.fetch_add(1, Ordering::SeqCst)

        Binder(var, rule)
    }
}

pub trait RuleBuilder: Sized {
    type Predicate: Predicate;

    fn not(self) -> Not<Self> { Not(self) }
    fn implies<R: RuleBuilder>(self, other: R) -> Implication<Self, R> { Implication(self, other) }
    fn and<R: RuleBuilder>(self, other: R) -> And<Self, R> { And(self, other) }
    fn or<R: RuleBuilder>(self, other: R) -> Or<Self, R> { Or(self, other) }
}

#[allow(type_alias_bounds, dead_code)]
type RuleOf<R: RuleBuilder> = super::Rule<R::Predicate>;

impl<R: RuleBuilder> RuleBuilder for Not<R> {
    type Predicate = R::Predicate;
}

impl<P: Predicate> RuleBuilder for Constraint<P> {
    type Predicate = P;
}

impl<R: RuleBuilder> RuleBuilder for Quantifier<ForAll, R> {
    type Predicate = R::Predicate;
}

impl<R: RuleBuilder> RuleBuilder for Quantifier<Exists, R> {
    type Predicate = R::Predicate;
}

impl<A: RuleBuilder, B: RuleBuilder> RuleBuilder for Implication<A, B> {
    type Predicate = A::Predicate;
}

impl<A: RuleBuilder, B: RuleBuilder> RuleBuilder for And<A, B> {
    type Predicate = A::Predicate;
}

impl<A: RuleBuilder, B: RuleBuilder> RuleBuilder for Or<A, B> {
    type Predicate = A::Predicate;
}

// Not(Not($R)) -> $R (rule)
impl<R: RuleBuilder + Into<RuleOf<R>>> From<Not<Not<R>>> for RuleOf<R> {
    fn from(Not(Not(r)): Not<Not<R>>) -> Self {
        r.into()
    }
}

// Not(Cons($T, $C, $V)) (rule)
impl<P: Predicate> From<Not<Constraint<P>>> for Rule<P> {
    fn from(Not(Constraint(p)): Not<Constraint<P>>) -> Self {
        Rule::False(p)
    }
}

// Cons($T, $C, $V) (rule)
impl<P: Predicate>From<Constraint<P>> for Rule<P> {
    fn from(Constraint(p): Constraint<P>) -> Self {
        Rule::True(p)
    }
}

// Not(Quant(ForAll, $R)) -> Quant(Exists, Not($R)) (rule)
impl<R: RuleBuilder> From<Not<Quantifier<ForAll, R>>> for RuleOf<R>
where Not<R>: Into<Self> {
    fn from(Not(Quantifier(_, Binder(t, c))): Not<Quantifier<ForAll, R>>) -> Self {
        Rule::Quantifier(
            Quant::Exists, t,
            Box::new(Not(c).into())
        )
    }
}

// Quant(ForAll, $R) (rule)
impl<R: RuleBuilder + Into<Self>> From<Quantifier<ForAll, R>> for RuleOf<R> {
    fn from(Quantifier(_, Binder(t, c)): Quantifier<ForAll, R>) -> Self {
        Rule::Quantifier(
            Quant::ForAll, t,
            Box::new(c.into())
        )
    }
}

// Not(Quant(Exists, $R)) -> Quant(ForAll, Not($R)) (rule)
impl<R: RuleBuilder> From<Not<Quantifier<Exists, R>>> for RuleOf<R>
where Not<R>: Into<Self> {
    fn from(Not(Quantifier(_, Binder(t, c))): Not<Quantifier<Exists, R>>) -> Self {
        Rule::Quantifier(
            Quant::ForAll, t,
            Box::new(Not(c).into())
        )
    }
}

// Quant(Exists, $R) (rule)
impl<R: RuleBuilder + Into<Self>> From<Quantifier<Exists, R>> for RuleOf<R> {
    fn from(Quantifier(_, Binder(t, c)): Quantifier<Exists, R>) -> Self {
        Rule::Quantifier(
            Quant::Exists, t,
            Box::new(c.into())
        )
    }
}

// Not(Implies($a, $b)) -> And($a, Not($b)) (rule)
impl<A: RuleBuilder + Into<Self>, B: RuleBuilder + Into<Self>> From<Not<Implication<A, B>>> for RuleOf<A>
where And<A, Not<B>>: Into<Self> {
    fn from(Not(Implication(a, b)): Not<Implication<A, B>>) -> Self {
        And(
            a,
            b.not()
        ).into()
    }
}

// Implies($a, $b) (rule)
impl<A: RuleBuilder + Into<Self>, B: RuleBuilder + Into<Self>> From<Implication<A, B>> for RuleOf<A> {
    fn from(Implication(a, b): Implication<A, B>) -> Self {
        Rule::Implication(Box::new([
            a.into(),
            b.into()
        ]))
    }
}

// Not(And($a, $b)) -> Or(Not($a), Not($b)) (rule)
impl<A: RuleBuilder + Into<Self>, B: RuleBuilder + Into<Self>> From<Not<And<A, B>>> for RuleOf<A>
where Or<Not<A>, Not<B>>: Into<Self> {
    fn from(Not(And(a, b)): Not<And<A, B>>) -> Self {
        Or(
            Not(a),
            Not(b)
        ).into()
    }
}

// And($a, $b) (rule)
impl<A: RuleBuilder + Into<Self>, B: RuleBuilder + Into<Self>> From<And<A, B>> for RuleOf<A> {
    fn from(r: And<A, B>) -> Self {
        Rule::And(Box::new([
            r.0.into(),
            r.1.into()
        ]))
    }
}

// Not(Or($a, $b)) -> And(Not($a), Not($b)) (rule)
impl<A: RuleBuilder + Into<Self>, B: RuleBuilder + Into<Self>> From<Not<Or<A, B>>> for RuleOf<A>
where And<Not<A>, Not<B>>: Into<Self> {
    fn from(Not(Or(a, b)): Not<Or<A, B>>) -> Self {
        And(
            Not(a),
            Not(b)
        ).into()
    }
}

// Or($a, $b) -> Implies(Not($a), $b) (rule)
impl<A: RuleBuilder + Into<Self>, B: RuleBuilder + Into<Self>> From<Or<A, B>> for RuleOf<A>
where Implication<Not<A>, B>: Into<Self> {
    fn from(Or(a, b): Or<A, B>) -> Self {
        // Rule::Or(Box::new([
        //     r.0.into(),
        //     r.1.into()
        // ]))

        Implication(
            Not(a),
            b
        ).into()
    }
}

// Or(Not($a), $b) -> Implies($a, $b)
impl<A: RuleBuilder, B: RuleBuilder> From<Or<Not<A>, B>> for Implication<A, B>
where Or<Not<A>, B>: RuleBuilder, Implication<A, B>: RuleBuilder {
    fn from(or: Or<Not<A>, B>) -> Self {
        Implication((or.0).0, or.1)
    }
}

// Implies($a, $b) -> Or(Not($a), $b)
impl<A: RuleBuilder, B: RuleBuilder> From<Implication<A, B>> for Or<Not<A>, B>
where Or<Not<A>, B>: RuleBuilder, Implication<A, B>: RuleBuilder {
    fn from(im: Implication<A, B>) -> Self {
        Self(Not(im.0), im.1)
    }
}
