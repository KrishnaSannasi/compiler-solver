use super::*;

#[test]
fn empty_is_consistent() {
    let solver = Solver::<tc>::new();

    add_rules! { in solver; }

    println!("{:#?}", solver);

    assert!(solver.is_consistent().is_some());
}

#[test]
fn single_rule_is_consistent() {
    // 1
    
    let mut solver = Solver::<tc>::new();

    add_rules! {
        in solver;

        cons tc(Type![u32], Type![Copy]);
    }

    println!("{:#?}", solver);

    assert!(solver.is_consistent().is_some());

    // 2
    
    let mut solver = Solver::<tc>::new();

    add_rules! {
        in solver;

        not(cons tc(Type![u32], Type![Copy]));
    }

    println!("{:#?}", solver);

    assert!(solver.is_consistent().is_some());

    // 3
    
    let mut solver = Solver::<tc>::new();

    add_rules! {
        in solver;

        forall t {
            cons tc(Type![u32], Type![Copy])
        }
    }

    println!("{:#?}", solver);

    assert!(solver.is_consistent().is_some());

    // 4
    
    let mut solver = Solver::<tc>::new();

    add_rules! {
        in solver;

        forall t {
            not(cons tc(Type![@t], Type![Copy]))
        }
    }

    println!("{:#?}", solver);

    assert!(solver.is_consistent().is_some());

    // 5
    
    let mut solver = Solver::<tc>::new();

    add_rules! {
        in solver;

        if (cons tc(Type![u32], Type![Copy])) {
            not(cons tc(Type![u32], Type![Copy]))
        }
    }

    println!("{:#?}", solver);

    assert!(solver.is_consistent().is_some());
}

#[test]
fn single_exists_is_not_consistent() {
    // 1

    let mut solver = Solver::<tc>::new();

    add_rules! {
        in solver;

        exists t {
            cons tc(Type![u32], Type![Copy])
        }
    }

    println!("{:#?}", solver);

    assert!(!solver.is_consistent().is_some());
    
    // 2

    let mut solver = Solver::<tc>::new();

    add_rules! {
        in solver;

        exists t {
            cons tc(Type![@t], Type![Copy])
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
            cons tc(Type![@T], Type![Any])
        }

        cons tc(Type![u32], Type![Any]);
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
            if ( cons tc(Type![@T], Type![Copy]) ) {
                cons tc(Type![@T], Type![Clone])
            }
        }

        cons tc(Type![u32], Type![Copy]);
        cons tc(Type![u32], Type![Clone]);
    }

    println!("{:#?}", solver);

    assert!(solver.is_consistent().is_some());
}

#[allow(non_snake_case)]
#[test]
fn not_consistent_for_all() {
    // 1
    
    let mut solver = Solver::<tc>::new();

    add_rules! {
        in solver;

        forall T {
            cons tc(Type![@T], Type![Any])
        }

        not(cons tc(Type![u32], Type![Any]));
    }

    println!("{:#?}", solver);

    assert!(!solver.is_consistent().is_some());
}
