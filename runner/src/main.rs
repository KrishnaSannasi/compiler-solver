
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
}

fn main() -> Result<(), ()> {
    let mut solver = Solver::<tc>::new();
    let mut ctx = Context::new();

    add_rules! {
        ctx in solver;

        // Transitivity
        // forall t {
        //     forall u {
        //         forall v {
        //             (and ((cons t) => (cons u))
        //                  ((cons u) => (cons v))) =>
        //             ((cons t) => (cons u))
        //         }
        //     }
        // }

        // cons "u32: Copy".to_string();
        
        // cons "bool: Copy".parse::<tc>().unwrap();
        // not (cons "bool: Clone".parse::<tc>().unwrap());

        // forall t {
        //     (cons format!("{:?}: Copy", t).parse::<tc>().unwrap()) =>
        //     (cons format!("{:?}: Clone", t).parse::<tc>().unwrap())
        // }

        // not (cons tc(Type![Vec u32], Type![Default]));
        // cons tc(Type![u32], Type![Sized]);
        // cons tc(Type![f32], Type![Sized]);

        // cons tc(Type![Vec u32], Type![Default]);
        not(cons tc(Type![Vec f32], Type![Default]));

        exists t {
            cons tc(Type![Vec @t], Type![Default])
        }

        exists t {
            not(cons tc(Type![Vec @t], Type![Default]))
        }

        // forall t {
        //     if (cons tc(Type![@t], Type![DynSized])) {
        //         not(cons tc(Type![@t], Type![Sized]))
        //     }
        // }

        // forall t {
        //     if (cons tc(Type![@t], Type![Sized])) {
        //         not(cons tc(Type![@t], Type![DynSized]))
        //     }
        // }

        // forall t {
        //     if (cons tc(Type![@t], Type![Sized])) {
        //         cons tc(Type![Vec @t], Type![Sized])
        //     }
        // }

        // forall t {
        //     if (cons tc(Type![@t], Type![Sized])) {
        //         not (cons tc(Type![Vec @t], Type![Copy]))
        //         // and (not (cons tc(Type![Vec @t], Type![Copy])))
        //         //     (cons tc(Type![Vec @t], Type![Sized]))
        //     }
        // }

        // cons tc(Type![u32], Type![Sized]);
        // cons tc(Type![f32], Type![Sized]);
        // cons tc(Type![bool], Type![Sized]);
        // cons tc(Type![char], Type![Sized]);

        // not(cons tc(Type![Vec (Vec (Vec bool))], Type![Sized]));
        // not(cons tc(Type![Vec u32], Type![Sized]));
        
        // not(cons tc(Type![Vec (Vec u32)], Type![Default]))

        // not(cons tc(Type![Vec char], Type![Sized]));

        // forall t {
        //     (cons format!("{:?}: Clone", t)) => (cons format!("Vec {:?}: Clone", t))
        // }

        // not(
        //     exists t {
        //         cons format!("Vec {:?}: Copy", t)
        //     }
        // )
    }

    // let check: Rule<_> = rule!(
    //     ctx cons "Vec u32: Clone".to_string()
    // ).into();
    
    println!("{:#?}", solver);
    // println!("{:#?}", check);

    if let Some(token) = solver.is_consistent() {
        // let rule = rule!(ctx cons tc(Type![u32], Type![Sized]));

        // println!("{:#?}", solver.is_consistent_with_rule(rule.into(), &token));
        println!("CONSISTENT");
    } else {
        println!("NOT CONSISTENT");
    }

    // solver.check(&check);

    Ok(())
}
