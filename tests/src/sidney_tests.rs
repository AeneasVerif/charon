
#![allow(dead_code)]

mod btree;

use crate::btree::BTree;

/*use crate::avl_tree::AvlTree;

fn test_small_avl_tree() {
    let mut tree = AvlTree::<i32>::new();
    tree.check_integrity();

    assert_eq!(tree.insert(10, 1), None);
    assert_eq!(tree.insert(20, 2), None);
    assert_eq!(tree.insert(30, 3), None);
    assert_eq!(tree.insert(0,  0), None);
    tree.check_integrity();

    assert_eq!(tree.insert(0,   99), Some(0));
    assert_eq!(tree.insert(10, 199), Some(1));
    assert_eq!(tree.insert(20, 299), Some(2));
    assert_eq!(tree.insert(30, 399), Some(3));
    tree.check_integrity();

    assert_eq!(tree.get(&0),  Some(&99));
    assert_eq!(tree.get(&10), Some(&199));
    assert_eq!(tree.get(&20), Some(&299));
    assert_eq!(tree.get(&30), Some(&399));
    
    assert_eq!(tree.get(&-5), None);
    assert_eq!(tree.get(&5),  None);
    assert_eq!(tree.get(&15), None);
    assert_eq!(tree.get(&25), None);
    assert_eq!(tree.get(&35), None);
    
    let zero = tree.get_mut(&0).unwrap();
    *zero = 42;
    assert_eq!(tree.get(&0), Some(&42));
    tree.check_integrity();
    
    assert_eq!(tree.remove(&0),  Some(42));
    assert_eq!(tree.remove(&10), Some(199));
    tree.check_integrity();

    assert_eq!(tree.remove(&-5), None);
    assert_eq!(tree.remove(&0),  None);
    assert_eq!(tree.remove(&5),  None);
    assert_eq!(tree.remove(&10), None);
    assert_eq!(tree.remove(&15), None);
}

fn test_compare_avl_tree_to_map() {
    let mut tree = AvlTree::<i32>::new();
    let mut map = std::collections::BTreeMap::<i32, i32>::new();

    [6, 1, 0, 4, 4, 3, 9, 12, 13, 4, 2, 1, 30, 40, 2, 7].map(|n| {
        assert_eq!(tree.insert(n, n * 10), map.insert(n, n * 10), "While inserting {}", n);
        tree.check_integrity();
    });

    [6, 1, 0, 7, 3, 9, 12, 13, 14, 1, 30, 40, 2, 7].map(|n| {
        assert_eq!(tree.get(&n), map.get(&n), "While searching {}", n);
        tree.check_integrity();
        if !map.contains_key(&n) { return; };

        let t = tree.get_mut(&n).unwrap();
        let m = map.get_mut(&n).unwrap();
        *t += 1;
        *m += 1;
        assert_eq!(tree.get(&n), map.get(&n), "While searching {}", n);
        tree.check_integrity();
    });
     
    [7, 30, 20, 13, 12, 9, 5, 0, 1, 2].map(|n| {
        assert_eq!(tree.remove(&n), map.remove(&n), "While removing {}", n);
        tree.check_integrity();
    });
    
    [30, 40, 50, 60, 45, 35, 25].map(|n| {
        assert_eq!(tree.insert(n, n * 10), map.insert(n, n * 10), "While inserting {}", n);
        tree.check_integrity();
    });

    /*let mut it = tree.into_iter();
    for (k, v) in &mut map {
        assert_eq!((k, v), it.next().expect("Should yield value"));
    }
    assert_eq!(it.next(), None);
    assert_eq!(it.next(), None);*/
} */
