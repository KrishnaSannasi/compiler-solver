use super::{InfVar, Predicate, Quant, Rule, Solver};

use std::cell::Cell;
use std::sync::RwLock;

use std::collections::{HashSet, HashMap};

struct OnDrop;
impl Drop for OnDrop {
    fn drop(&mut self) {
        println!("}}--", );
    }
}

type Iter<'a, T> = std::iter::Cloned<std::collections::hash_set::Iter<'a, T>>;

trait COpt<'a, T, P>: Sized {
    fn call_with<F: FnOnce(T, Iter<'a, P>)>(self, _: F)
        where P: 'a {}
}

struct CSome<'a, T, P>(T, &'a HashSet<P>);
struct CNone;

impl<'a, T, P: Clone> COpt<'a, T, P> for CSome<'a, T, P> {
    fn call_with<F: FnOnce(T, Iter<'a, P>)>(self, f: F) {
        f(self.0, self.1.iter().cloned())
    }
}
impl<T, P> COpt<'_, T, P> for CNone {}

pub struct Token<'a, P: Predicate>(&'a Solver<P>, Cell<HashSet<P>>, Cell<HashMap<InfVar, Vec<P::Item>>>);
pub struct SyncToken<'a, P: Predicate>(&'a Solver<P>, RwLock<HashSet<P>>, RwLock<HashMap<InfVar, Vec<P::Item>>>);

impl<'a, P: Predicate + std::fmt::Debug> std::fmt::Debug for Token<'a, P> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let axioms = self.1.take();
        let existential_assignments = self.2.take();

        f.debug_struct("Token")
            .field("axioms", &axioms)
            .field("existential_assignments", &existential_assignments)
            .finish()?;

        self.1.set(axioms);
        self.2.set(existential_assignments);

        Ok(())
    }
}

impl<'a, P: Predicate + std::fmt::Debug> std::fmt::Debug for SyncToken<'a, P> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match (self.1.try_read(), self.2.try_read()) {
            (Ok(axioms), Ok(existential_assignments)) => 
                f.debug_struct("SyncToken")
                    .field("axioms", &*axioms)
                    .field("existential_assignments", &*existential_assignments)
                    .finish(),
            _ => write!(f, "<SyncToken read failed>")
        }
    }
}

impl<'a, P: Predicate> From<Token<'a, P>> for SyncToken<'a, P> {
    fn from(Token(solver, axioms, existential_assignments): Token<'a, P>) -> Self {
        Self(
            solver,
            RwLock::new(axioms.into_inner()),
            RwLock::new(existential_assignments.into_inner())
        )
    }
}

impl<P: Predicate> Token<'_, P> {
    pub fn is_consistent_with_rule(&self, rule: Rule<P>) -> bool {
        let mut axioms = self.1.take();
        let mut existential_assignments = self.2.take();

        let ret = match self.0.is_consistent_raw(CSome(rule, &axioms)) {
            Some((new_axioms, new_existential_assignments)) => {
                axioms.extend(new_axioms);
                existential_assignments.extend(new_existential_assignments);

                true
            },
            None => false
        };
        
        self.1.set(axioms);
        self.2.set(existential_assignments);
        
        ret
    }
}

impl<P: Predicate> SyncToken<'_, P> {
    pub fn is_consistent_with_rule(&self, rule: Rule<P>) -> bool {
        let maybe_axioms = {
            let axioms = self.1.read().unwrap();

            self.0.is_consistent_raw(CSome(rule, &axioms))
        };

        if let Some((new_axioms, new_existential_assignments)) = maybe_axioms {
            if let Ok(mut axioms) = self.1.try_write() {
                axioms.extend(new_axioms);
            }

            if let Ok(mut existential_assignments) = self.2.try_write() {
                existential_assignments.extend(new_existential_assignments);
            }

            true
        } else {
            false
        }
    }
}

impl<P: Predicate> Solver<P> {
    pub fn is_consistent(&self) -> Option<Token<'_, P>> {
        let (axioms, existential_assignments) = self.is_consistent_raw(CNone)?;
        
        Some(Token(self, Cell::new(axioms), Cell::new(existential_assignments)))
    }

    fn is_consistent_raw<'a, O: COpt<'a, Rule<P>, P>>(&self, new_rule: O) -> Option<(HashSet<P>, HashMap<InfVar, Vec<P::Item>>)> where P: 'a {
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
            known_variables: &mut HashSet<P::Item>,
            existential_assignments: &mut HashMap<InfVar, Vec<P::Item>>
        ) -> Option<()> {
            while let Some(rule) = rules.pop() {
                println!("--{{", );
                let _on_drop = OnDrop;
                dbg!(&axioms);

                match dbg!(rule) {
                    Rule::Axiom(x) => {
                        dbg!("axiom");
                        
                        if axioms.contains(&x.not()) {
                            return None;
                        } else if H::handle().is_some() {
                            axioms.insert(dbg!(x));
                        } else if !axioms.contains(&x) {
                            return None;
                        }
                    }
                    Rule::And(box [a, b]) => {
                        dbg!("and");

                        rules.push(a);
                        rules.push(b);
                    }
                    Rule::Implication(box [a, b]) => {
                        dbg!("implication");

                        fn add_to_axioms<P: Predicate>(axioms: &mut HashSet<P>, known_variables: &HashSet<P::Item>, add_axiom: Rule<P>, truthy: bool) {
                            match dbg!(add_axiom) {
                                Rule::Axiom(x) => if truthy {
                                    axioms.insert(x);
                                } else {
                                    axioms.insert(x.not());
                                },
                                Rule::And(box [a, b]) => {
                                    add_to_axioms(axioms, known_variables, a, truthy);
                                    add_to_axioms(axioms, known_variables, b, truthy);
                                },
                                Rule::Implication(box [a, b]) => {
                                    if let Some(true) = a.eval(&axioms, known_variables) {
                                        add_to_axioms(axioms, known_variables, b, truthy)
                                    }
                                },
                                Rule::Quantifier(..) => ()
                            }
                        }

                        let a_eval = a.eval(&axioms, known_variables);
                        let b_eval = b.eval(&axioms, known_variables);

                        match (a_eval, b_eval) {
                            // if cond guaranteed false, then return doesn't matter
                            (Some(false), _) => (),
                            
                            // if impl guaranteed false, then return false
                            (Some(true), Some(false)) => return None,
                            
                            // if impl guaranteed true , then return true
                            (Some(true), Some(true)) => if H::handle().is_some() {
                                add_to_axioms(axioms, known_variables, b, true)
                            },
                            
                            // if impl undetermined, then return false if existential
                            // if impl undetermined, then return true if !existential
                            (Some(true), None) => {
                                H::handle()?;

                                add_to_axioms(axioms, known_variables, b, true);
                            }

                            (None, Some(false)) => {
                                H::handle()?;

                                add_to_axioms(axioms, known_variables, b, false);
                            },
                            (None, _) => (),
                        }
                    }
                    Rule::Quantifier(Quant::ForAll, inf_var, rule) => {
                        dbg!("forall");
                        dbg!(inf_var);

                        let mut rule_buffer = Vec::with_capacity(1);

                        for var in known_variables.clone().iter() {
                            let rule = dbg!(rule.apply(inf_var, dbg!(var)));
                            known_variables.extend(rule.items());

                            rule_buffer.clear();
                            rule_buffer.push(rule);

                            dbg!(is_consistent_inner::<H, _>(
                                &mut rule_buffer,
                                axioms,
                                known_variables,
                                existential_assignments
                            ))?;
                        }
                    }
                    Rule::Quantifier(Quant::Exists, inf_var, rule) => {
                        dbg!("exists");
                        dbg!(inf_var);

                        let kv = known_variables.clone();
                        let mut iter = kv.iter();
                        let mut rule_buffer = Vec::with_capacity(1);

                        loop {
                            let var = match iter.next() {
                                Some(var) => var,
                                None => if existential_assignments.contains_key(&inf_var) {
                                    dbg!("break");
                                    break
                                } else {
                                    dbg!("return");
                                    return None
                                }
                            };

                            let rule = dbg!(rule.apply(inf_var, dbg!(var)));

                            rule_buffer.clear();
                            rule_buffer.push(rule);

                            let is_inner_consistent = is_consistent_inner::<Existential, _>(
                                &mut rule_buffer,
                                axioms,
                                known_variables,
                                existential_assignments
                            );

                            if is_inner_consistent.is_some() {
                                existential_assignments.entry(inf_var)
                                    .and_modify(|x| x.push(var.clone()))
                                    .or_insert_with(|| vec![var.clone()]);
                                
                                dbg!("store");
                            }
                        }
                    }
                }
            }

            Some(())
        }
        
        type Tree<P> = HashMap<Rule<P>, (HashSet<Rule<P>>, HashSet<usize>)>;

        fn find_cycles<P: Predicate>(rules: &[Rule<P>]) -> Option<Tree<P>> {
            fn build_deps_tree<P: Predicate>(rules: &[Rule<P>]) -> Tree<P> {
                let mut tree: Tree<P> = HashMap::default();

                for (i, ri) in rules.iter().enumerate() {
                    let mut entry = Err(tree.entry(ri.clone()));
                    for (j, rj) in rules.iter().enumerate() {
                        if i == j {
                            continue
                        }
                        if ri.is_dep(rj) {
                            let vec = match entry {
                                Ok(vec) => vec,
                                Err(entry) => entry.or_default()
                            };
                            
                            vec.0.insert(rj.clone());
                            vec.1.insert(j);
                            entry = Ok(vec);
                        }
                    }
                }

                tree
            }

            fn util<P: Predicate>(rules: &[Rule<P>], tree: &Tree<P>, v: usize, visited: &mut [bool], rec_stack: &mut [bool]) -> bool {
                dbg!(&visited);
                dbg!(&rec_stack);
                if !visited[v] {
                    // Mark the current node as visited and part of recursion stack 
                    visited[v] = true; 
                    rec_stack[v] = true;

                    if let Some(rows) = tree.get(&rules[v]) {
                        // Recur for all the vertices adjacent to this vertex 
                        for &i in &rows.1 {
                            if rec_stack[i] || (!visited[i] && util(rules, tree, i, visited, rec_stack)) {
                                return true
                            }
                        }
                    }
                }

                rec_stack[v] = false;  // remove the vertex from recursion stack 
                false
            }

            let tree = build_deps_tree(rules);

            let mut visited = vec![false; rules.len()];
            let mut rec_stack = vec![false; rules.len()];

            for i in 0..rules.len() {
                if util(rules, &tree, i, &mut visited, &mut rec_stack) {
                    return None
                }
            }

            Some(tree)
        }

        let mut rules = self.rules.iter().cloned().collect::<Vec<_>>();
        let mut axioms = HashSet::default();

        new_rule.call_with(|x, old_axioms| {
            rules.push(x);
            axioms.extend(old_axioms);
        });

        let tree = find_cycles(&rules)?;

        println!("TREE");

        for (i, (r, _)) in &tree {
            println!("{:?}", i);
            for r in r {
                println!("\t{:?}", r);
            }
        }

        let to_key = |x: &Rule<P>| match x {
            Rule::Axiom(..) => 4,
            Rule::And(_) => 3,
            Rule::Implication(..) => 2,
            Rule::Quantifier(Quant::ForAll, ..) => 1,
            Rule::Quantifier(Quant::Exists, ..) => 0,
        };

        rules.sort_unstable_by(|x, y| {
            let (kx, ky) = (to_key(x), to_key(y));
            use std::cmp::Ordering;

            match std::cmp::Ord::cmp(&kx, &ky) {
                Ordering::Equal => (),
                x => return x
            }

            dbg!((x, y));

            match dbg!((
                tree.get(x).map(|x| x.0.contains(&y)).unwrap_or(false),
                tree.get(y).map(|y| y.0.contains(&x)).unwrap_or(false),
            )) {
                (true, true) => unreachable!(),
                (false, false) => Ordering::Equal,
                (true, false) => Ordering::Less,
                (false, true) => Ordering::Greater,
            }
        });

        dbg!("-----------------------------------------------------------------------------------");

        dbg!(&rules);
        let old_rules = rules.clone();
        
        match rules.last() {
            Some(Rule::Implication(..)) | Some(Rule::Quantifier(..)) => {
                for i in rules.iter() {
                    if let Rule::Quantifier(Quant::Exists, ..) = i {
                        return None;
                    }
                }
            }
            _ => (),
        }

        let mut known_variables = rules.iter().flat_map(Rule::items).collect();
        let mut existential_assignments = HashMap::default();

        println!("**********************************************************************************************");
        println!("**********************************************************************************************");

        dbg!(&rules);
        dbg!(&known_variables);
        
        println!("**********************************************************************************************");
        println!("**********************************************************************************************");

        let ici = is_consistent_inner::<NotExistential, _>(
            &mut rules,
            &mut axioms,
            &mut known_variables,
            &mut existential_assignments,
        );

        dbg!(&old_rules);
        dbg!(&known_variables);

        ici?;

        Some(dbg!((axioms, existential_assignments)))
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
            &Rule::Quantifier(q, qv, ref rule) => {
                Rule::Quantifier(q, qv, Box::new(rule.apply(v, i)))
            }
        }
    }

    fn eval(&self, axioms: &HashSet<P>, known_variables: &HashSet<P::Item>) -> Option<bool> {
        match self {
            &Rule::Axiom(ref x) => {
                if axioms.contains(x) {
                    Some(true)
                } else if axioms.contains(&x.not()) {
                    Some(false)
                } else {
                    None
                }
            }
            Rule::Implication(box [a, b]) => Some(!a.eval(axioms, known_variables)? || b.eval(axioms, known_variables)?),
            Rule::And(box [a, b]) => Some(a.eval(axioms, known_variables)? && b.eval(axioms, known_variables)?),
            &Rule::Quantifier(Quant::Exists, t, ref rule) => {
                for i in known_variables {
                    if let Some(true) = rule.apply(t, i).eval(axioms, known_variables) {
                        return Some(true)
                    }
                }
                
                Some(false)
            },
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

impl<P: Predicate> Rule<P> {
    fn is_dep(&self, rule: &Self) -> bool {
        dbg!((self, rule));
        let output = match self {
            Rule::And(box [a, b]) => a.is_dep(rule) || b.is_dep(rule),
            Rule::Axiom(s) => {
                match rule {
                    Rule::Axiom(r) => s.matches(r),
                    Rule::Quantifier(_, _, r) => self.is_dep(r),
                    Rule::Implication(box [a, b]) => self.is_dep(a),
                    Rule::And(box [a, b]) => self.is_dep(a) || self.is_dep(b)
                }
            },
            Rule::Quantifier(_, _, s) => match rule {
                | Rule::Axiom(..)
                | Rule::Implication(..) => s.is_dep(rule),

                Rule::Quantifier(_, _, r) => s.is_dep(r),
                Rule::And(box [a, b]) => s.is_dep(a) || s.is_dep(b)
            },
            Rule::Implication(box [a, b]) => match rule {
                Rule::Axiom(..) => a.is_dep(rule),
                Rule::And(box [c, d]) => a.is_dep(c) || a.is_dep(d),
                Rule::Implication(box [c, d]) => a.is_dep(d) && !c.is_dep(b),
                Rule::Quantifier(_, _, r) => self.is_dep(r)
            },
        };
        dbg!((output, self, rule));

        output
    }
}