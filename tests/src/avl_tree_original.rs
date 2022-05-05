
#![allow(dead_code)]
/*
use std::cmp::{Ordering, max};

struct AvlNode<K: Ord, V> {
    key:    K,
    value:  V,
    height: u32,
    left:   Option<Box<AvlNode<K, V>>>, 
    right:  Option<Box<AvlNode<K, V>>>,
}

// Height
// ''''''

fn get_height<K: Ord, V>(node: &Option<Box<AvlNode<K, V>>>) -> u32 {
    match node {
        None => 0,
        Some(n) => n.height
    }
}
// Compute height based on child nodes height.
fn compute_height<K: Ord, V>(node: &AvlNode<K, V>) -> u32 {
    1 + max(get_height(&node.left), get_height(&node.right))
}
fn recache_height<K: Ord, V>(node: &mut AvlNode<K, V>) {
    node.height = compute_height(node);
}

// Balance
// '''''''

#[derive(PartialEq, Clone, Copy)]
enum AvlBalance {
    TooMuchLeft,
    LeftHeavy,
    IsBalanced,
    RightHeavy,
    TooMuchRight
}
impl AvlBalance {
    fn is_balanced(self) -> bool {
        self != AvlBalance::TooMuchLeft && self != AvlBalance::TooMuchRight
    }
    fn lean_left(self) -> bool {
        self == AvlBalance::LeftHeavy || self == AvlBalance::TooMuchLeft
    }
    fn lean_right(self) -> bool {
        self == AvlBalance::RightHeavy || self == AvlBalance::TooMuchRight
    }
}

fn get_balance<K: Ord, V>(node: &Option<Box<AvlNode<K, V>>>) -> AvlBalance {
    match node {
        None => AvlBalance::IsBalanced,
        Some(n) => {
            match get_height(&n.right) as i64 - get_height(&n.left) as i64 {
                -2 => AvlBalance::TooMuchLeft,
                -1 => AvlBalance::LeftHeavy,
                 0 => AvlBalance::IsBalanced,
                 1 => AvlBalance::RightHeavy,
                 2 => AvlBalance::TooMuchRight,
                 _ => panic!("Broken AVL node balance")
            }
        }
    }
}

// Invariants
// ''''''''''

fn check_integrity<K: Ord, V>(node: &Option<Box<AvlNode<K, V>>>) {
    if node.is_none() { return; };
    let n = node.as_ref().unwrap();

    check_integrity(&n.left);
    check_integrity(&n.right);

    if let Some(left) = n.left.as_ref() {
        assert!(left.key < n.key);
    }
    if let Some(right) = n.right.as_ref() {
        assert!(right.key > n.key);
    }
    
    assert_eq!(n.height, compute_height(n));
    assert!(get_balance(node).is_balanced());
}

// Accessors
// '''''''''

fn get<'a, K: Ord, V>(node: &'a Option<Box<AvlNode<K, V>>>, k: &K) -> Option<&'a V> {
    node.as_ref().and_then(|n| match k.cmp(&n.key) {
        Ordering::Equal   => Some(&n.value),
        Ordering::Less    => get(&n.left, k),
        Ordering::Greater => get(&n.right, k)
    })
}
fn get_mut<'a, K: Ord, V>(node: &'a mut Option<Box<AvlNode<K, V>>>, k: &K) -> Option<&'a mut V> {
    node.as_mut().and_then(|n| match k.cmp(&n.key) {
        Ordering::Equal   => Some    (&mut n.value),
        Ordering::Less    => get_mut(&mut n.left, k),
        Ordering::Greater => get_mut(&mut n.right, k)
    })
}

// Shape modifiers
// '''''''''''''''

fn push_to_left<K: Ord, V>(mut node: Box<AvlNode<K, V>>) -> Box<AvlNode<K, V>> {
    let mut new_left = node.right.expect("Should have a right child");
    std::mem::swap(&mut node.key,   &mut new_left.key);
    std::mem::swap(&mut node.value, &mut new_left.value);
    node.right = new_left.right;

    new_left.right = new_left.left;
    new_left.left  = node.left;
    recache_height(new_left.as_mut());

    node.left = Some(new_left);
    recache_height(node.as_mut()); node
}

fn push_to_right<K: Ord, V>(mut node: Box<AvlNode<K, V>>) -> Box<AvlNode<K, V>> {
    let mut new_right = node.left.expect("Should have a left child");
    std::mem::swap(&mut node.key,   &mut new_right.key);
    std::mem::swap(&mut node.value, &mut new_right.value);
    node.left = new_right.left;

    new_right.left = new_right.right;
    new_right.right  = node.right;
    recache_height(new_right.as_mut());

    node.right = Some(new_right);
    recache_height(node.as_mut()); node
}

// Only function callable when the node is unbalanced. Children must be balanced.
fn rebalance<K: Ord, V>(node: &mut Option<Box<AvlNode<K, V>>>) {
    let b = get_balance(node);
    if b.is_balanced() { return; };

    let mut parent = std::mem::replace(node, None).unwrap();
    match b {
        AvlBalance::TooMuchLeft => {
            let cb = get_balance(&parent.left);
            debug_assert!(cb.is_balanced());

            let mut child = parent.left.unwrap();
            if cb.lean_right() {
                child = push_to_left(child);
            }
            parent.left = Some(child);
            parent = push_to_right(parent);
        },
        AvlBalance::TooMuchRight => {
            let cb = get_balance(&parent.right);
            debug_assert!(cb.is_balanced());

            let mut child = parent.right.unwrap();
            if cb.lean_left() {
                child = push_to_right(child);
            }
            parent.right = Some(child);
            parent = push_to_left(parent);
        },
        _ => panic!("Returned early for other cases")
    }
    *node = Some(parent);
}

// Insertions
// ''''''''''

// Returns the old value at the given key.
fn insert<'a, K: Ord, V>(node: &'a mut Option<Box<AvlNode<K, V>>>, k: K, v: V) -> Option<V> {
    match node {
        None => {
            let n = AvlNode{ key: k, value: v, height: 1, left: None, right: None };
            *node = Some(Box::new(n));
            None
        },
        Some(n) => {
            let old_v = match k.cmp(&n.key) {
                Ordering::Equal   => Some(std::mem::replace(&mut n.value, v)),
                Ordering::Less    => insert(&mut n.left,  k, v),
                Ordering::Greater => insert(&mut n.right, k, v)
            };
            if old_v.is_none() { recache_height(n); rebalance(node); };
            old_v
        }
    }
}

// Removals
// ''''''''

// Writes the leftmost node found key & value at the given borrows,
// then replace it with its right child.
fn remove_leftmost<K: Ord, V>(key: &mut K, value: &mut V, node: &mut Option<Box<AvlNode<K, V>>>) -> V {
    let mut n = std::mem::replace(node, None).unwrap();

    let v;
    match n.left {
        Some(_) => {
            v = remove_leftmost(key, value, &mut n.left);
            *node = Some(n);
        }
        None => {
            std::mem::swap(key,   &mut n.key);
            std::mem::swap(value, &mut n.value);
            v = n.value;
            *node = std::mem::replace(&mut n.right, None);
        }
    };
    if let Some(n) = node.as_mut() {
        recache_height(n);
        rebalance(node);
    }
    v
}

fn remove_current<K: Ord, V>(node: &mut Option<Box<AvlNode<K, V>>>) -> V {
    let mut n = std::mem::replace(node, None).unwrap();
    match (&mut n.left, &mut n.right) {
        (None,    None)    => n.value,
        (Some(_), None)    => { *node = std::mem::replace(&mut n.left, None);  n.value },
        (None,    Some(_)) => { *node = std::mem::replace(&mut n.right, None); n.value },
        (Some(_), Some(_)) => {
            let v = remove_leftmost(&mut n.key, &mut n.value, &mut n.right);
            *node = Some(n);
            v
        }
    }
}

// Returns the removed value, if any.
fn remove<K: Ord, V>(node: &mut Option<Box<AvlNode<K, V>>>, k: &K) -> Option<V> {
    if node.is_none() { return None }
    let n = node.as_mut().unwrap();
    let v = match k.cmp(&n.key) {
        Ordering::Less    => remove(&mut n.left,  k),
        Ordering::Greater => remove(&mut n.right, k),
        Ordering::Equal   => Some(remove_current(node))
    };
    if v.is_some() { if let Some(n) = node {
        recache_height(n);
        rebalance(node);
    }};
    v
}

// Iteration
// '''''''''

struct AvlIteratorNode<'a, K: Ord, V> {
    key: &'a K,
    value: &'a mut V,
    right: Option<&'a mut Box<AvlNode<K, V>>>,
}

fn go_to_leftmost<'a, K: Ord, V>(
    path: &mut std::vec::Vec<AvlIteratorNode<'a, K, V>>,
    node: Option<&'a mut Box<AvlNode<K, V>>>)
{
    node.map(|n| {
        path.push(AvlIteratorNode{
            key: &n.key,
            value: &mut n.value,
            right: n.right.as_mut()
        });
        go_to_leftmost(path, n.left.as_mut());
    });
}

fn next<'a, K: Ord, V>(path: &mut std::vec::Vec<AvlIteratorNode<'a, K, V>>) -> Option<(&'a K, &'a mut V)> {
    let mut cur = path.pop()?;
    if let Some(n) = std::mem::replace(&mut cur.right, None) {
        go_to_leftmost(path, Some(n));
    }
    Some((cur.key, cur.value))
}

// Tree API
// ''''''''

struct AvlTree<K: Ord, V> {
    root: Option<Box<AvlNode<K, V>>>
}

impl<K: Ord, V> AvlTree<K, V> {

    fn new() -> AvlTree<K, V> {
        AvlTree::<K, V>{ root: None }
    }

    fn get(&self, key: &K) -> Option<&V> {
        get(&self.root, key)
    }

    fn get_mut(&mut self, key: &K) -> Option<&mut V> {
        get_mut(&mut self.root, key)
    }

    fn insert(&mut self, key: K, value: V) -> Option<V> {
        insert(&mut self.root, key, value)
    }
    
    fn remove(&mut self, key: &K) -> Option<V> {
        remove(&mut self.root, key)
    }

    fn check_integrity(&self) {
        check_integrity(&self.root)
    }
}

// Iterator API
// ''''''''''''

struct AvlIterator<'a, K: Ord, V> {
    path: std::vec::Vec<AvlIteratorNode<'a, K, V>>
}

impl<'a, K: Ord, V> IntoIterator for &'a mut AvlTree<K, V> {

    type IntoIter = AvlIterator<'a, K, V>;

    type Item = <Self::IntoIter as Iterator>::Item;

    fn into_iter(self) -> Self::IntoIter {
        let mut path = std::vec::Vec::new();
        go_to_leftmost(&mut path, self.root.as_mut());
        AvlIterator{ path }
    }
}

impl<'a, K: Ord, V> Iterator for AvlIterator<'a, K, V> {
    
    type Item = (&'a K, &'a mut V);

    fn next(&mut self) -> Option<Self::Item> {
        next(&mut self.path)
    }
}

// Tests
// '''''

fn main() {
    let mut tree = AvlTree::<i32, i32>::new();
    tree.insert(10, 1);
    tree.get(&10);
    tree.get_mut(&10);
    tree.remove(&10);
    tree.check_integrity();

    println!("Hello AVL tree !");
}

fn test_small_tree() {
    let mut tree = AvlTree::<i32, i32>::new();
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

fn test_compare_to_map() {
    let mut tree = AvlTree::<i32, i32>::new();
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

    let t_values =       tree.into_iter().collect::<std::vec::Vec<(&i32, &mut i32)>>();
    let m_values = (&mut map).into_iter().collect::<std::vec::Vec<(&i32, &mut i32)>>();
    assert_eq!(t_values, m_values);
}
*/
