use super::{InfVar, Predicate, Quant, Rule, Solver};

use std::collections::HashSet;

trait COpt<T>: Sized {
    fn call_with<F: FnOnce(T)>(self, _: F) {}
}

struct CSome<T>(T);
struct CNone;

impl<T> COpt<T> for CSome<T> {
    fn call_with<F: FnOnce(T)>(self, f: F) {
        f(self.0)
    }
}
impl<T> COpt<T> for CNone {}

pub struct Token<'a>(&'a ());

impl<P: Predicate> Solver<P> {
    pub fn is_consistent(&self) -> Option<Token<'_>> {
        if self.is_consistent_raw(CNone) {
            Some(Token(&()))
        } else {
            None
        }
    }

    pub fn is_consistent_with_rule(&self, rule: Rule<P>, _: &Token<'_>) -> bool {
        self.is_consistent_raw(CSome(rule))
    }

    fn is_consistent_raw<O: COpt<Rule<P>>>(&self, new_rule: O) -> bool {
        struct Existential;
        struct NotExistential;

        trait HandleImplicationUndetermined {
            fn handle() -> Option<()>;
        }

        impl HandleImplicationUndetermined for Existential {
            #[inline(always)]
            fn handle() -> Option<()> {
                None
            }
        }

        impl HandleImplicationUndetermined for NotExistential {
            #[inline(always)]
            fn handle() -> Option<()> {
                Some(())
            }
        }

        fn is_consistent_inner<H: HandleImplicationUndetermined, P: Predicate>(
            rules: &mut Vec<Rule<P>>,
            axioms: &mut HashSet<P>,
            known_variables: &HashSet<P::Item>
        ) -> Option<()> {
            while let Some(rule) = rules.pop() {
                match rule {
                    Rule::Axiom(x) => {
                        if axioms.contains(&x.not()) {
                            return None
                        } else {
                            axioms.insert(x);
                        }
                    },
                    Rule::And(box [a, b]) => {
                        rules.push(a);
                        rules.push(b);
                    },
                    Rule::Implication(box [a, b]) => {
                        if let Some(true) = a.eval(&axioms) {
                            match b.eval(&axioms) {
                                // if guaranteed false, then return false
                                Some(false) => return None,

                                // if guaranteed true , then return true
                                Some(true) => (),

                                // if undetermined    , then return false if existential
                                // if undetermined    , then return true if !existential
                                None => H::handle()?,
                            }
                        }
                    },
                    Rule::Quantifier(Quant::ForAll, t, box rule) => {
                        for var in known_variables {
                            rules.push(rule.apply(t, var));
                            // This needs to be tested.
                            // The trade off of this line is
                            // will the number of variables or
                            // the number of forall quantifiers
                            // dominate performance?
                            is_consistent_inner::<H, _>(rules, axioms, known_variables)?;
                        }
                    },
                    Rule::Quantifier(Quant::Exists, t, box rule) => {
                        let mut iter = known_variables.iter();

                        loop {
                            let var = iter.next()?;

                            rules.push(rule.apply(t, var));

                            if is_consistent_inner::<Existential, _>(rules, axioms, known_variables).is_some() {
                                break
                            }
                        }
                    }
                }
            }

            Some(())
        }

        let mut rules = self.rules.iter().cloned().collect::<Vec<_>>();

        new_rule.call_with(|x| rules.push(x));

        let known_variables = rules.iter().flat_map(Rule::items).collect::<HashSet<_>>();

        rules.sort_by_key(|x| match x {
            Rule::Axiom(..) => 3,
            Rule::And(_) => 2,
            Rule::Implication(..) => 1,
            Rule::Quantifier(..) => 0,
        });

        match rules.last() {
            | Some(Rule::Implication(..))
            | Some(Rule::Quantifier(..)) => {
                for i in rules.iter() {
                    if let Rule::Quantifier(Quant::Exists, ..) = i {
                        return false
                    }
                }
            },
            _ => ()
        }

        is_consistent_inner::<NotExistential, _>(&mut rules, &mut Default::default(), &known_variables).is_some()
    }
}

impl<P: Predicate> Rule<P> {
    fn apply(&self, v: InfVar, i: &P::Item) -> Self {
        match self {
            &Rule::Axiom(ref x) => Rule::Axiom(x.apply(v, i)),
            Rule::Implication(box [a, b]) => {
                Rule::Implication(Box::new([a.apply(v, i), b.apply(v, i)]))
            }
            Rule::And(box [a, b]) => Rule::And(Box::new([a.apply(v, i), b.apply(v, i)])),
            &Rule::Quantifier(q, qv, ref rule) => Rule::Quantifier(q, qv, Box::new(rule.apply(v, i))),
        }
    }

    fn eval(&self, axioms: &HashSet<P>) -> Option<bool> {
        match self {
            &Rule::Axiom(ref x) => if axioms.contains(x) {
                Some(true)
            } else if axioms.contains(&x.not()) {
                Some(false)
            } else {
                None
            },
            Rule::Implication(box [a, b]) => Some(!a.eval(axioms)? || b.eval(axioms)?),
            Rule::And(box [a, b]) => Some(a.eval(axioms)? && b.eval(axioms)?),
            Rule::Quantifier(..) => unimplemented!(),
        }
    }

    fn items<'a>(&'a self) -> Box<dyn 'a + Iterator<Item = P::Item>> {
        match self {
            Rule::Axiom(x) => Box::new(x.items()),

            Rule::Implication(box [a, b]) | Rule::And(box [a, b]) => {
                Box::new(a.items().chain(b.items()))
            }

            Rule::Quantifier(_, _, box rule) => rule.items(),
        }
    }
}
