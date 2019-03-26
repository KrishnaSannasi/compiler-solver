
use solver::*;
use std::collections::HashMap;

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum Type {
    Concrete(&'static str),
    Infer(InfVar),
    App(&'static str, Vec<Type>),
}

impl Type {
    fn is_concrete(&self) -> bool {
        match self {
            Type::Infer(..) => false,
            Type::Concrete(..) => true,
            Type::App(_, x) => x.iter().fold(true, |acc, x| acc && x.is_concrete())
        }
    }
    fn get_concrete(&self) -> Box<dyn Iterator<Item = Type>> {
        match self {
            Type::Infer(..) => Box::new(None.into_iter()),
            Type::Concrete(..) => Box::new(Some(self.clone()).into_iter()),
            Type::App(_, x) => Box::new(
                x.clone()
                    .into_iter()
                    .flat_map(|x| x.get_concrete())
                    .chain(
                        if self.is_concrete() {
                            Some(self.clone())
                        } else {
                            None
                        }
                    )
            ),
        }
    }
}

#[allow(non_camel_case_types)]
#[derive(Clone, PartialEq, Eq, Hash)]
struct tc(Type, Type);

impl std::fmt::Debug for tc {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{:?}: {:?}", self.0, self.1)
    }
}

impl std::fmt::Debug for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match &self {
            Type::Concrete(x) => write!(f, "{}", x),
            Type::Infer(x) => write!(f, "{:?}", x),
            Type::App(x, rest) => write!(f, "{} {:?}", x, rest),
        }
    }
}

macro_rules! Type {
    ($name:ident) => {
        Type::Concrete(stringify!($name))
    };
    (@$name:ident) => {
        Type::Infer($name)
    };
    ($name:ident $( $rest:tt )*) => {
        Type::App(stringify!($name), Type![#vec new $($rest)*])
    };
    (#vec new $($rest:tt)*) => {{
        let mut vec = Vec::new();

        Type! { #vec vec $($rest)* }

        vec
    }};
    (#vec $vec:ident) => {};
    (#vec $vec:ident $a:ident $($rest:tt)*) => {
        $vec.push( Type![ $a ] );
        Type! { #vec $vec $($rest)* }
    };
    (#vec $vec:ident @$a:ident $($rest:tt)*) => {
        $vec.push( Type![ @$a ] );
        Type! { #vec $vec $($rest)* }
    };
    (#vec $vec:ident ($($inner:tt)*) $($rest:tt)*) => {
        $vec.push( Type![ $($inner)* ] );
        Type! { #vec $vec $($rest)* }
    };
}

macro_rules! tc {
    (@first [$($stack:tt)*] $first:ident $($rest:tt)*) => {
        tc! { @first [$($stack)* $first ] $($rest)* }
    };
    (@first [$($stack:tt)*] @$first:ident $($rest:tt)*) => {
        tc! { @first [$($stack)* @$first ] $($rest)* }
    };
    (@first [$($stack:tt)*] ($($inner:tt)*) $($rest:tt)*) => {
        tc! { @first [$($stack)* ($($inner)*) ] $($rest)* }
    };
    (@first [$($stack:tt)*] : $($rest:tt)*) => {
        tc! { @second [$($stack)*] [] $($rest)* }
    };
    (@second [$($f_stack:tt)*] [$($stack:tt)*] $first:ident $($rest:tt)*) => {
        tc! { @second [$($f_stack)*] [$($stack)* $first] $($rest)* }
    };
    (@second [$($f_stack:tt)*] [$($stack:tt)*] @$first:ident $($rest:tt)*) => {
        tc! { @second [$($f_stack)*] [$($stack)* @$first] $($rest)* }
    };
    (@second [$($f_stack:tt)*] [$($stack:tt)*] ($($inner:tt)*) $($rest:tt)*) => {
        tc! { @second [$($f_stack)*] [$($stack)* ($($inner)*)] $($rest)* }
    };
    (@second [$($f_stack:tt)*] [$($stack:tt)*]) => {
        tc(Type![$($f_stack)*], Type![$($stack)*])
    };
    (@first $($rest:tt)*) => { compile_error!("invalid parse options!") };
    ($($rest:tt)*) => { tc! { @first [] $($rest)* } };
}

macro_rules! count {
    () => { 0 };
    ($($a:expr, $_:expr),*) => {
        count!($($a),*) << 1
    };
    ($_:expr $(,$a:expr)*) => {
        1 + count!($($a),*)
    };
}

macro_rules! hm {
    (
        $( ($key:expr, $value:expr) )*
    ) => {{
        let mut map = std::collections::HashMap::with_capacity(count!($($key),*));

        $(
            map.insert($key, $value);
        )*

        map
    }}
}

#[cfg(test)]
mod tests;

impl Predicate for tc {
    type Item = Type;
    type Iter = Box<dyn Iterator<Item = Type>>;

    fn items(&self) -> Self::Iter {
        self.0.get_concrete()
    }

    fn apply(&self, i: InfVar, r: &Self::Item) -> Self {
        tc(
            self.0.apply(i, r),
            self.1.apply(i, r)
        )
    }

    fn unify(&self, other: &Self) -> Option<HashMap<InfVar, Result<Self::Item, InfVar>>> {
        let mut first = Type::unify(&self.0, &other.0)?;
        let second = Type::unify(&self.0, &other.0)?;

        for (k, v) in second {
            let value = first.entry(k).or_insert_with(|| v.clone());

            if *value != v {
                return None;
            }
        }

        Some(first)
    }
}

impl Type {
    fn apply(&self, i: InfVar, r: &Self) -> Self {
        match self {
            &Type::Concrete(x)
                => Type::Concrete(x),
            &Type::App(x, ref rest)
                => Type::App(x, rest.iter().map(|rule| rule.apply(i, r)).collect() ),
            &Type::Infer(x)
                => if x == i { r.clone() } else { Type::Infer(x) },
        }
    }

    fn unify(&self, other: &Self) -> Option<HashMap<InfVar, Result<Self, InfVar>>> {
        match (self, other) {
            (&Type::Infer(x), &Type::Infer(y)) => Some(hm!(
                (x, Err(y))
            )),
            (&Type::Infer(x), y) => Some(hm!(
                (x, Ok(y.clone()))
            )),
            (Type::Concrete(x), Type::Concrete(y)) if x == y => Some(Default::default()),
            (Type::App(x, rest_x), Type::App(y, rest_y)) if x == y => {
                let mut map = HashMap::new();

                if rest_x.len() != rest_y.len() {
                    return None;
                }

                for (x, y) in rest_x.iter().zip(rest_y) {
                    for (k, v) in x.unify(y)? {
                        let value = map.entry(k).or_insert_with(|| v.clone());

                        if *value != v {
                            return None;
                        }
                    }
                }

                Some(map)
            },
            _ => None
        }
    }
}

fn main() {
    let mut solver = Solver::<tc>::new();

    add_rules! {
        in solver;

        forall t {
            if ( cons tc!(@t: Foo) ) {
                cons tc!(@t: Bar)
            }
        }

        forall t {
            if ( and (cons tc!(@t: Bar))
                     (cons tc!(@t: Control)) ) {
                cons tc!(@t: Tak)
            }
        }

        // cons tc!(bool: Foo);
        cons tc!(bool: Control);

        not(cons tc!(bool: Tak));
    }

    println!("{}", solver.is_consistent().is_some());
}
