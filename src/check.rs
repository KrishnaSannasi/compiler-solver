use super::{InfVar, Predicate, Quant, Rule, Solver};

use std::collections::{HashMap, HashSet, VecDeque};
use std::hash::Hash;

#[derive(Debug)]
struct RuleSet<T: Hash + Eq> {
    t: HashSet<T>,
    f: HashSet<T>,
    has_changed_existential: HashSet<InfVar>,
}

impl<T: Hash + Eq> RuleSet<T> {
    fn clear(&mut self) {
        self.has_changed_existential.clear();
    }
}

impl<T: Hash + Eq> std::ops::Index<bool> for RuleSet<T> {
    type Output = HashSet<T>;

    fn index(&self, a: bool) -> &HashSet<T> {
        if a {
            &self.t
        } else {
            &self.f
        }
    }
}

impl<T: Hash + Eq> std::ops::IndexMut<bool> for RuleSet<T> {
    fn index_mut(&mut self, a: bool) -> &mut HashSet<T> {
        if a {
            &mut self.t
        } else {
            &mut self.f
        }
    }
}

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
        if self.is_consistent_inner(CNone) {
            Some(Token(&()))
        } else {
            None
        }
    }

    pub fn is_consistent_with_rule(&self, rule: Rule<P>, _: &Token<'_>) -> bool {
        self.is_consistent_inner(CSome(rule))
    }

    fn is_consistent_inner<O: COpt<Rule<P>>>(&self, new_rule: O) -> bool {
        dbg!(self);

        let mut rules: VecDeque<_> = self.rules.iter().map(|x| (x.clone(), 1)).collect();

        if rules.len() == 1 {
            // lone existential quantifiers are always false,
            // this is because they are equivilent to `or` and
            // the base case for `or` is false
            return match rules[0].0 {
                Rule::Quantifier(Quant::Exists, ..) => false,
                Rule::And(..) => unreachable!(),
                _ => true,
            };
        }

        new_rule.call_with(|x| rules.push_back((x, 1)));

        let mut concrete_rules = RuleSet {
            t: HashSet::new(),
            f: HashSet::new(),
            has_changed_existential: HashSet::new(),
        };

        let mut quantifier_forall = HashMap::new();
        // let mut quantifier_exists = HashMap::new();

        let mut registered_items = HashSet::new();

        for (rule, _) in rules.iter() {
            registered_items.extend(rule.items());
        }

        // let registered_items = dbg!(registered_items);

        while let Some((rule, count)) = rules.pop_front() {
            if count > 1000 {
                dbg!(rules.len());
                dbg!(self);
                panic!();
            } // for terminating outdated rules

            println!("=================================================================\n");
            match dbg!(rule) {
                Rule::True(x) => {
                    dbg!("true");

                    if concrete_rules[false].contains(&x) {
                        dbg!(concrete_rules);
                        return false;
                    }

                    concrete_rules[true].insert(x);
                    concrete_rules.clear();
                }

                Rule::False(x) => {
                    dbg!("false");
                    if concrete_rules[true].contains(&x) {
                        dbg!(concrete_rules);
                        return false;
                    }

                    concrete_rules[false].insert(x);
                    concrete_rules.clear();
                }

                Rule::And(box [x, y]) => {
                    dbg!("and");

                    rules.push_back((x, 1));
                    rules.push_back((y, 1));
                }

                Rule::Quantifier(Quant::ForAll, t, box rule) => {
                    dbg!("quantifier forall");

                    let iter = if let Some(iter) = quantifier_forall.get_mut(&rule) {
                        iter
                    } else {
                        quantifier_forall
                            .entry(rule.clone())
                            .or_insert_with(|| registered_items.clone().into_iter())
                    };

                    if let Some(item) = iter.next() {
                        rules.push_back((rule.apply(t, &item), 1));

                        rules
                            .push_back((Rule::Quantifier(Quant::ForAll, t, Box::new(rule)), count));
                    } else {
                        quantifier_forall.remove(&rule);
                    }
                }

                Rule::Quantifier(Quant::Exists, t, box rule) => {
                    dbg!("quantifier exists");

                    unimplemented!()
                }

                Rule::Implication(box [a, b]) => {
                    dbg!("implication");
                    if a.eval(&concrete_rules).unwrap_or(false) {
                        // ~(a -> b) === a and ~b
                        if !b.eval(&concrete_rules).unwrap_or(true) {
                            dbg!(concrete_rules);
                            return false;
                        }
                        // If it is true, then push the implication onto
                        // the queue, to be processed later
                        rules.push_back((b, 1))
                    } else if !a.eval(&concrete_rules).unwrap_or(true) {
                        // If it is false, then it doesn't matter what b is
                    } else if rules.iter().any(|x| match x.0 {
                        Rule::Implication(_) => false,
                        _ => true,
                    }) {
                        dbg!(&rules);
                        // If a is not determined (some unknown variables)
                        // then kick it down the queue, only if
                        // there are other rules to process (non-implication rules)
                        // if there are no other rules, this there will be
                        // no progress to be made, as it is impossible to
                        // prove or disprove, so assume it is true
                        rules.push_back((Rule::Implication(Box::new([a, b])), count + 1));
                    }
                }
            }
            concrete_rules = dbg!(concrete_rules);
        }

        true
    }
}

impl<P: Predicate> Rule<P>
where
    P: std::fmt::Debug,
    P::Item: std::fmt::Debug,
{
    fn apply(&self, v: InfVar, i: &P::Item) -> Self {
        match self {
            Rule::True(x) => Rule::True(x.apply(v, i)),
            Rule::False(x) => Rule::False(x.apply(v, i)),
            Rule::Implication(box [a, b]) => {
                Rule::Implication(Box::new([a.apply(v, i), b.apply(v, i)]))
            }
            Rule::And(box [a, b]) => Rule::And(Box::new([a.apply(v, i), b.apply(v, i)])),
            Rule::Quantifier(..) => unimplemented!(),
        }
    }

    fn unify(&self, other: &Self) -> Option<HashMap<InfVar, Result<P::Item, InfVar>>> {
        match (self, other) {
            (Rule::True(x), Rule::True(y)) => P::unify(x, y),
            (Rule::False(x), Rule::False(y)) => P::unify(x, y),
            (Rule::And(box [a, b]), Rule::And(box [c, d]))
            | (Rule::Implication(box [a, b]), Rule::Implication(box [c, d])) => {
                let mut first = Self::unify(a, c)?;
                let second = Self::unify(b, d)?;

                for (k, v) in second {
                    let value = first.entry(k).or_insert_with(|| v.clone());

                    if *value != v {
                        return None;
                    }
                }

                Some(first)
            }
            (Rule::Quantifier(qa, _, binder_a), Rule::Quantifier(qb, _, binder_b)) => {
                if qa != qb {
                    None
                } else {
                    binder_a.unify(binder_b)
                }
            }
            _ => None,
        }
    }

    // fn is_true(&self, set: &RuleSet<P>) -> bool {
    //     self.eval(set).unwrap_or(false)
    // }

    // fn is_false(&self, set: &RuleSet<P>) -> bool {
    //     !self.eval(set).unwrap_or(true)
    // }

    fn eval(&self, set: &RuleSet<P>) -> Option<bool> {
        match self {
            Rule::True(x) => if set[true].contains(x) {
                Some(true)
            } else if set[false].contains(x) {
                Some(false)
            } else {
                None
            },
            Rule::False(x) => if set[false].contains(x) {
                Some(true)
            } else if set[true].contains(x) {
                Some(false)
            } else {
                None
            },
            Rule::Implication(box [a, b]) => Some(!a.eval(set)? || b.eval(set)?),
            Rule::And(box [a, b]) => Some(a.eval(set)? && b.eval(set)?),
            Rule::Quantifier(..) => unimplemented!(),
        }
    }

    fn items<'a>(&'a self) -> Box<dyn 'a + Iterator<Item = P::Item>> {
        match self {
            Rule::True(x) | Rule::False(x) => Box::new(x.items()),

            Rule::Implication(box [a, b]) | Rule::And(box [a, b]) => {
                Box::new(a.items().chain(b.items()))
            }

            Rule::Quantifier(_, _, box rule) => rule.items(),
        }
    }
}
