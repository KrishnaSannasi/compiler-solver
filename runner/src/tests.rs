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

#[test]
fn consistent_exists_1() {
    let mut solver = Solver::<tc>::new();

    add_rules! {
        in solver;

        exists t {
            cons tc!(@t: Copy)
        }

        cons tc!(u32: Copy);
    }

    println!("{:#?}", solver);

    assert!(solver.is_consistent().is_some());
}

#[test]
fn not_consistent_exists_1() {
    let mut solver = Solver::<tc>::new();

    add_rules! {
        in solver;

        exists t {
            cons tc!(@t: Copy)
        }

        not(cons tc!(u32: Copy));
    }

    println!("{:#?}", solver);

    assert!(!solver.is_consistent().is_some());
}

#[allow(non_snake_case)]
#[test]
fn consistent_for_all_1() {
    for _ in 0..1000 {
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
}

#[allow(non_snake_case)]
#[test]
fn consistent_for_all_2() {
    for _ in 0..1000 {
        let mut solver = Solver::<tc>::new();

        add_rules! {
            in solver;

            forall T {
                if ( cons tc!(@T: Copy) ) {
                    cons tc!(@T: Clone)
                }
            }

            cons tc!(u32: Copy);
            cons tc!(u32: Clone);
        }

        println!("{:#?}", solver);

        assert!(solver.is_consistent().is_some());
    }
}

#[allow(non_snake_case)]
#[test]
fn consistent_for_all_3() {
    for _ in 0..1000 {
        let mut solver = Solver::<tc>::new();

        add_rules! {
            in solver;

            forall T {
                if ( cons tc!(@T: Copy) ) {
                    cons tc!(@T: Clone)
                }
            }

            cons tc!(u32: Copy);
            cons tc!(u32: Clone);
        }

        println!("{:#?}", solver);

        assert!(solver.is_consistent().is_some());
    }
}

#[allow(non_snake_case)]
#[test]
fn not_consistent_for_all() {
    for _ in 0..1000 {
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
}

#[test]
fn consistent_multiple_implications_1() {
    for _ in 0..1000 {
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
        cons tc!(bool: Bar);
        // cons tc!(bool: Control);

        not(cons tc!(bool: Tak));
    }

    assert!(solver.is_consistent().is_some())
}

#[test]
fn consistent_multiple_implications_3() {
    for _ in 0..1000 {
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
}

#[test]
fn not_consistent_for_all_multiple_implications() {
    for _ in 0..1000 {
        let mut solver = Solver::<tc>::new();

        add_rules! {
            in solver;

            forall t {
                if ( cons tc!(@t: Foo) ) {
                    and (cons tc!(@t: Bar))
                        (cons tc!(@t: Yam))
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

        assert!(!solver.is_consistent().is_some());
    }
}

#[test]
fn consistent_exists_implication() {
    let mut solver = Solver::<tc>::new();

    add_rules! {
        in solver;

        /*
         * Note, this doesn't do what you would expect,
         * because implications are true if the input proposition
         * is true,
         * 
         * ```
         * if ( cons tc!(@t: Copy) ) {
         *     cons tc!(@t: Clone)
         * }
         * ```
         * 
         * is true if `cons tc!(@t: Copy)` is false, and this is false when
         * `@t \in { Copy, Clone }`
         * 
         * So this test case will pass
         */
        exists t {
            if ( cons tc!(@t: Copy) ) {
                cons tc!(@t: Clone)
            }
        }

        cons tc!(u32: Copy);
    }

    assert!(solver.is_consistent().is_some())
}

#[test]
fn consistent_forall_exists_implication_1() {
    let mut solver = Solver::<tc>::new();

    add_rules! {
        in solver;

        forall t {
            if (cons tc!(@t: Foo)) {
                exists u {
                    cons tc!(Array @t @u: Foo)
                }
            }
        }

        cons tc!(Vec u32: Clone);
    }

    assert!(solver.is_consistent().is_some())
}

#[test]
fn consistent_forall_implication() {
    let mut solver = Solver::<tc>::new();

    add_rules! {
        in solver;

        forall t {
            if (cons tc!(@t: Foo)) {
                cons tc!(Vec @t: Foo)
            }
        }

        cons tc!(u32: Foo);
    }

    assert!(solver.is_consistent().is_some())
}

#[test]
fn consistent_muti_forall_implication_2() {
    let mut solver = Solver::<tc>::new();

    add_rules! {
        in solver;

        forall t {
            forall u {
                if (cons tc!(@t: Foo)) {
                    cons tc!(Array @t @u: Foo)
                }
            }
        }

        cons tc!(u32: Foo);
    }

    assert!(solver.is_consistent().is_some())
}

#[test]
fn not_consistent_multi_forall() {
    for _ in 0..1000 {
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

        assert!(!solver.is_consistent().is_some());
    }
}

#[test]
fn consistent_multi_forall() {
    for _ in 0..1000 {
        let mut solver = Solver::<tc>::new();

        add_rules! {
            in solver;

            cons tc!(u32: Copy);

            cons tc!(Vec u32: Clone);

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

        assert!(solver.is_consistent().is_some());
    }
}

#[test]
fn not_consistent_for_all_exists() {
    let mut solver = Solver::<tc>::new();

    add_rules! {
        in solver;

        cons tc!(u32: Foo);

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
        
        exists t {
            cons tc!(Vec @t: Clone)
        }
    }

    assert!(!solver.is_consistent().is_some());
}

#[test]
fn consistent_for_all_exists_1() {
    let mut solver = Solver::<tc>::new();

    add_rules! {
        in solver;

        cons tc!(u32: Copy);

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

        exists t {
            cons tc!(Vec @t: Clone)
        }
    }

    assert!(solver.is_consistent().is_some());
}

#[test]
fn consistent_for_all_exists_2() {
    for _ in 0..1000 {
        let mut solver = Solver::<tc>::new();

        add_rules! {
            in solver;

            cons tc!(u32: Foo);

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

            not(exists t {
                cons tc!(Vec @t: Clone)
            });
        }

        assert!(solver.is_consistent().is_some());
    }
}

#[test]
fn consistent_for_all_implication_exists() {
    
    let mut solver = Solver::<tc>::new();
    
    add_rules! {
        in solver;

        cons tc!(u32: Type);
        cons tc!(bool: Type);

        cons tc!(Copy: Trait);

        cons tc!(u32: Copy);
        cons tc!(bool: Copy);

        forall t {
            if (cons tc!(@t: Type)) {
                exists c {
                    cons tc!(@c: Trait);
                    cons tc!(@t: @c);
                }
            }
        }
    }
    
    assert!(solver.is_consistent().is_some());
}

#[test]
fn not_consistent_for_all_implication_exists() {
    for _ in 0..1000 {
        let mut solver = Solver::<tc>::new();
    
        add_rules! {
            in solver;

            cons tc!(u32: Type 0);
            cons tc!(bool: Type 0);

            cons tc!(Copy: Trait);

            cons tc!(u32: Copy);
            // cons tc!(bool: Copy);

            forall t {
                if (cons tc!(@t: Type 0)) {
                    exists c {
                        cons tc!(@c: Trait);
                        cons tc!(@t: @c);
                    }
                }
            }
        }

        assert!(!solver.is_consistent().is_some());
    }
}
