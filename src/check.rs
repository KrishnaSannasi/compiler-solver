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

impl<P: Predicate> Solver<P>
where
    P: std::fmt::Debug,
    P::Item: std::fmt::Debug,
{
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
        fn is_consistent_inner<P: Predicate + std::fmt::Debug>(
            rules: &mut Vec<Rule<P>>,
            axioms: &mut HashSet<P>,
            known_variables: &HashSet<P::Item>,
            existential: bool,
        ) -> Option<()> where P::Item: std::fmt::Debug {
            struct OnDrop;

            impl Drop for OnDrop {
                fn drop(&mut self) {
                    println!("}}-");
                }
            }

            while let Some(rule) = rules.pop() {
                println!("-{{");
                dbg!(&axioms);
                let _x = OnDrop;

                match dbg!(rule) {
                    Rule::Axiom(x) => {
                        dbg!("axiom");
                        if axioms.contains(&x.not()) {
                            dbg!(axioms);
                            return None
                        } else {
                            axioms.insert(x);
                        }
                    },
                    Rule::And(box [a, b]) => {
                        dbg!("and");
                        rules.push(a);
                        is_consistent_inner(rules, axioms, known_variables, existential)?;
                        rules.push(b);
                        is_consistent_inner(rules, axioms, known_variables, existential)?;
                    },
                    Rule::Implication(box [a, b]) => {
                        dbg!("implication");

                        if let Some(true) = dbg!(a.eval(&axioms)) {
                            match b.eval(&axioms) {
                                // if guaranteed false, then return false
                                Some(false) => return None,

                                // if undetermined    , then return false if existential
                                None if existential => return None,

                                // if guaranteed true , then return true
                                | Some(true)
                                // if undetermined    , then return true if !existential
                                | None => (),
                            }
                        }
                    },
                    Rule::Quantifier(Quant::ForAll, t, box rule) => {
                        dbg!("quant forall");
                        
                        known_variables.iter().fold(Some(()), |is_true, var| {
                            rules.push(dbg!(rule.apply(t, var)));
                            is_true.and_then(|()| dbg!(is_consistent_inner(rules, axioms, known_variables, existential)))
                        })?
                    },
                    Rule::Quantifier(Quant::Exists, t, box rule) => {
                        dbg!("quant exists");

                        known_variables.iter().fold(None, |is_true, var| {
                            rules.push(dbg!(rule.apply(t, var)));
                            is_true.or_else(|| dbg!(is_consistent_inner(rules, axioms, known_variables, true)))
                        })?
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

        dbg!(&rules);

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

        is_consistent_inner(&mut rules, &mut Default::default(), dbg!(&known_variables), false).is_some()
    }
}

impl<P: Predicate> Rule<P>
where
    P: std::fmt::Debug,
    P::Item: std::fmt::Debug,
{
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
