use super::*;

#[test]
fn empty_is_consistent() {
    let solver = Solver::<tc>::new();

    add_rules! { in solver; }

    println!("{:#?}", solver);

    assert!(solver.is_consistent().is_some());
}

#[test]
fn single_rule_is_consistent_1() {
    let mut solver = Solver::<tc>::new();

    add_rules! {
        in solver;

        cons tc!(u32: Copy);
    }

    println!("{:#?}", solver);

    assert!(solver.is_consistent().is_some());
}

#[test]
fn single_rule_is_consistent_2() {
    let mut solver = Solver::<tc>::new();

    add_rules! {
        in solver;

        not(cons tc!(u32: Copy));
    }

    println!("{:#?}", solver);

    assert!(solver.is_consistent().is_some());
}

#[test]
fn single_rule_is_consistent_3() {
    let mut solver = Solver::<tc>::new();

    add_rules! {
        in solver;

        forall t {
            cons tc!(u32: Copy)
        }
    }

    println!("{:#?}", solver);

    assert!(solver.is_consistent().is_some());
}

#[test]
fn single_rule_is_consistent_4() {
    let mut solver = Solver::<tc>::new();

    add_rules! {
        in solver;

        forall t {
            not(cons tc!(@t: Copy))
        }
    }

    println!("{:#?}", solver);

    assert!(solver.is_consistent().is_some());
}

#[test]
fn single_rule_is_consistent_5() {
    let mut solver = Solver::<tc>::new();

    add_rules! {
        in solver;

        if (cons tc!(u32: Copy)) {
            not(cons tc!(u32: Copy))
        }
    }

    println!("{:#?}", solver);

    assert!(solver.is_consistent().is_some());
}

#[test]
fn single_exists_is_not_consistent_1() {
    let mut solver = Solver::<tc>::new();

    add_rules! {
        in solver;

        exists t {
            cons tc!(u32: Copy)
        }
    }

    println!("{:#?}", solver);

    assert!(!solver.is_consistent().is_some());
}

#[test]
fn single_exists_is_not_consistent_2() {
    let mut solver = Solver::<tc>::new();

    add_rules! {
        in solver;

        exists t {
            cons tc!(@t: Copy)
        }
    }

    println!("{:#?}", solver);

    assert!(!solver.is_consistent().is_some());
}

#[allow(non_snake_case)]
#[test]
fn consistent_for_all_1() {
    let mut solver = Solver::<tc>::new();

    add_rules! {
        in solver;

        forall T {
            cons tc!(@T: Any)
        }

        cons tc!(u32: Any);
    }

    println!("{:#?}", solver);

    assert!(solver.is_consistent().is_some());
}

#[allow(non_snake_case)]
#[test]
fn consistent_for_all_2() {
    let mut solver = Solver::<tc>::new();

    add_rules! {
        in solver;

        forall T {
            if ( cons tc!(@T: Copy) ) {
                cons tc!(@T: Clone)
            }
        }

        cons tc!(u32: Copy);
        cons tc!(u32: Clone); // this line is optional
    }

    println!("{:#?}", solver);

    assert!(solver.is_consistent().is_some());
}

#[allow(non_snake_case)]
#[test]
fn not_consistent_for_all() {
    let mut solver = Solver::<tc>::new();

    add_rules! {
        in solver;

        forall T {
            cons tc!(@T: Any)
        }

        not(cons tc!(u32: Any));
    }

    println!("{:#?}", solver);

    assert!(!solver.is_consistent().is_some());
}

#[test]
fn consistent_multiple_implications_1() {
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
        // cons tc!(bool: Control);

        not(cons tc!(bool: Tak));
    }

    assert!(solver.is_consistent().is_some())
}

#[test]
fn consistent_multiple_implications_2() {
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

        cons tc!(bool: Foo);
        // cons tc!(bool: Control);

        not(cons tc!(bool: Tak));
    }

    assert!(solver.is_consistent().is_some())
}

#[test]
fn consistent_multiple_implications_3() {
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

    assert!(solver.is_consistent().is_some())
}

#[test]
fn not_consistent_multiple_implications() {
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

        cons tc!(bool: Foo);
        cons tc!(bool: Control);

        not(cons tc!(bool: Tak));
    }

    assert!(!solver.is_consistent().is_some())
}
