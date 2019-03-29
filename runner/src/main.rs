use solver::*;

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
            Type::App(_, x) => x.iter().fold(true, |acc, x| acc && x.is_concrete()),
        }
    }
    fn get_concrete(&self) -> Box<dyn Iterator<Item = Type>> {
        match self {
            Type::Infer(..) => Box::new(None.into_iter()),
            Type::Concrete(..) => Box::new(Some(self.clone()).into_iter()),
            Type::App(_, x) => {
                Box::new(x.clone().into_iter().flat_map(|x| x.get_concrete()).chain(
                    if self.is_concrete() {
                        Some(self.clone())
                    } else {
                        None
                    },
                ))
            }
        }
    }
}

#[allow(non_camel_case_types)]
#[derive(Clone, PartialEq, Eq, Hash)]
struct tc(Type, Type, bool);

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
        tc(Type![$($f_stack)*], Type![$($stack)*], true)
    };
    (@first $($rest:tt)*) => { compile_error!("invalid parse options!") };
    ($($rest:tt)*) => { tc! { @first [] $($rest)* } };
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
        tc(self.0.apply(i, r), self.1.apply(i, r), self.2)
    }

    fn not(&self) -> Self {
        tc(self.0.clone(), self.1.clone(), !self.2)
    }
}

impl Type {
    fn apply(&self, i: InfVar, r: &Self) -> Self {
        match self {
            &Type::Concrete(x) => Type::Concrete(x),
            &Type::App(x, ref rest) => {
                Type::App(x, rest.iter().map(|rule| rule.apply(i, r)).collect())
            }
            &Type::Infer(x) => {
                if x == i {
                    r.clone()
                } else {
                    Type::Infer(x)
                }
            }
        }
    }
}

fn main() {
    let mut solver = Solver::<tc>::new();

    add_rules! {
        in solver;

        cons tc!(u32: Copy);

        not(cons tc!(Vec u32: Clone));

        forall t {
            if (cons tc!(@t: Clone)) {
                cons tc!(Vec @t: Clone)
            }
        }

        forall t {
            if (cons tc!(@t: Copy)) {
                cons tc!(@t: Clone)
            }
        }
    }

    println!("{}", solver.is_consistent().is_some());
}
