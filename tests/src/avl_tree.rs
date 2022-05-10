#![allow(dead_code)]

type Key = i32; // TODO: make this generic

use std::cmp::Ordering;

struct AvlNode<V> {
    key: Key,
    value: V,
    height: u32,
    left: Option<Box<AvlNode<V>>>,
    right: Option<Box<AvlNode<V>>>,
}

// Height
// ''''''

fn get_height<V>(node: &Option<Box<AvlNode<V>>>) -> u32 {
    match node {
        None => 0,
        Some(n) => n.height,
    }
}

// Redefining max so that we don't need the Ord trait
fn max(x: u32, y: u32) -> u32 {
    if x > y {
        x
    } else {
        y
    }
}

// Compute height based on child nodes height.
fn compute_height<V>(node: &AvlNode<V>) -> u32 {
    1 + max(get_height(&node.left), get_height(&node.right))
}

/*
fn recache_height<V>(node: &mut AvlNode<V>) {
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
    TooMuchRight,
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

fn get_balance<V>(node: &Option<Box<AvlNode<V>>>) -> AvlBalance {
    match node {
        None => AvlBalance::IsBalanced,
        Some(n) => match get_height(&n.right) as i64 - get_height(&n.left) as i64 {
            -2 => AvlBalance::TooMuchLeft,
            -1 => AvlBalance::LeftHeavy,
            0 => AvlBalance::IsBalanced,
            1 => AvlBalance::RightHeavy,
            2 => AvlBalance::TooMuchRight,
            _ => panic!("Broken AVL node balance"),
        },
    }
}

// Invariants
// ''''''''''

fn check_integrity<V>(node: &Option<Box<AvlNode<V>>>) {
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

fn get<'a, V>(node: &'a Option<Box<AvlNode<V>>>, k: &Key) -> Option<&'a V> {
    node.as_ref().and_then(|n| match k.cmp(&n.key) {
        Ordering::Equal => Some(&n.value),
        Ordering::Less => get(&n.left, k),
        Ordering::Greater => get(&n.right, k),
    })
}
fn get_mut<'a, V>(node: &'a mut Option<Box<AvlNode<V>>>, k: &Key) -> Option<&'a mut V> {
    node.as_mut().and_then(|n| match k.cmp(&n.key) {
        Ordering::Equal => Some(&mut n.value),
        Ordering::Less => get_mut(&mut n.left, k),
        Ordering::Greater => get_mut(&mut n.right, k),
    })
}

// Shape modifiers
// '''''''''''''''

fn push_to_left<V>(mut node: Box<AvlNode<V>>) -> Box<AvlNode<V>> {
    let mut new_left = node.right.expect("Should have a right child");
    std::mem::swap(&mut node.key, &mut new_left.key);
    std::mem::swap(&mut node.value, &mut new_left.value);
    node.right = new_left.right;

    new_left.right = new_left.left;
    new_left.left = node.left;
    recache_height(new_left.as_mut());

    node.left = Some(new_left);
    recache_height(node.as_mut());
    node
}

fn push_to_right<V>(mut node: Box<AvlNode<V>>) -> Box<AvlNode<V>> {
    let mut new_right = node.left.expect("Should have a left child");
    std::mem::swap(&mut node.key, &mut new_right.key);
    std::mem::swap(&mut node.value, &mut new_right.value);
    node.left = new_right.left;

    new_right.left = new_right.right;
    new_right.right = node.right;
    recache_height(new_right.as_mut());

    node.right = Some(new_right);
    recache_height(node.as_mut());
    node
}

// Only function callable when the node is unbalanced. Children must be balanced.
fn rebalance<V>(node: &mut Option<Box<AvlNode<V>>>) {
    let b = get_balance(node);
    if b.is_balanced() {
        return;
    };

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
        }
        AvlBalance::TooMuchRight => {
            let cb = get_balance(&parent.right);
            debug_assert!(cb.is_balanced());

            let mut child = parent.right.unwrap();
            if cb.lean_left() {
                child = push_to_right(child);
            }
            parent.right = Some(child);
            parent = push_to_left(parent);
        }
        _ => panic!("Returned early for other cases"),
    }
    *node = Some(parent);
}

// Insertions
// ''''''''''

// Returns the old value at the given key.
fn insert<'a, V>(node: &'a mut Option<Box<AvlNode<V>>>, k: Key, v: V) -> Option<V> {
    match node {
        None => {
            let n = AvlNode {
                key: k,
                value: v,
                height: 1,
                left: None,
                right: None,
            };
            *node = Some(Box::new(n));
            None
        }
        Some(n) => {
            let old_v = match k.cmp(&n.key) {
                Ordering::Equal => Some(std::mem::replace(&mut n.value, v)),
                Ordering::Less => insert(&mut n.left, k, v),
                Ordering::Greater => insert(&mut n.right, k, v),
            };
            if old_v.is_none() {
                recache_height(n);
                rebalance(node);
            };
            old_v
        }
    }
}

// Removals
// ''''''''

// Writes the leftmost node found key & value at the given borrows,
// then replace it with its right child.
fn remove_leftmost<V>(
    key: &mut Key,
    value: &mut V,
    node: &mut Option<Box<AvlNode<V>>>
) -> V {
    let mut n = std::mem::replace(node, None).unwrap();

    let v;
    match n.left {
        Some(_) => {
            v = remove_leftmost(key, value, &mut n.left);
            *node = Some(n);
        }
        None => {
            std::mem::swap(key, &mut n.key);
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

fn remove_current<V>(node: &mut Option<Box<AvlNode<V>>>) -> V {
    let mut n = std::mem::replace(node, None).unwrap();
    match (&mut n.left, &mut n.right) {
        (None, None) => n.value,
        (Some(_), None) => {
            *node = std::mem::replace(&mut n.left, None);
            n.value
        }
        (None, Some(_)) => {
            *node = std::mem::replace(&mut n.right, None);
            n.value
        }
        (Some(_), Some(_)) => {
            let v = remove_leftmost(&mut n.key, &mut n.value, &mut n.right);
            *node = Some(n);
            v
        }
    }
}

// Returns the removed value, if any.
fn remove<V>(node: &mut Option<Box<AvlNode<V>>>, k: &Key) -> Option<V> {
    if node.is_none() {
        return None;
    }
    let n = node.as_mut().unwrap();
    let v = match k.cmp(&n.key) {
        Ordering::Less => remove(&mut n.left, k),
        Ordering::Greater => remove(&mut n.right, k),
        Ordering::Equal => Some(remove_current(node)),
    };
    if v.is_some() {
        if let Some(n) = node {
            recache_height(n);
            rebalance(node);
        }
    };
    v
}

// Iteration
// '''''''''
/*
struct AvlIteratorNode<'a, V> {
    key: &'a Key,
    value: &'a mut V,
    right: Option<&'a mut Box<AvlNode<V>>>,
}

fn go_to_leftmost<'a, V>(
    path: &mut std::vec::Vec<AvlIteratorNode<'a, V>>,
    node: Option<&'a mut Box<AvlNode<V>>>
) {
    node.map(|n| {
        path.push(AvlIteratorNode {
            key: &n.key,
            value: &mut n.value,
            right: n.right.as_mut(),
        });
        go_to_leftmost(path, n.left.as_mut());
    });
}

fn next<'a, V>(
    path: &mut std::vec::Vec<AvlIteratorNode<'a, V>>,
) -> Option<(&'a Key, &'a mut V)> {
    let mut cur = path.pop()?;
    if let Some(n) = std::mem::replace(&mut cur.right, None) {
        go_to_leftmost(path, Some(n));
    }
    Some((cur.key, cur.value))
}
 */
// Tree API
// ''''''''

pub struct AvlTree<V> {
    root: Option<Box<AvlNode<V>>>,
}

impl<V> AvlTree<V> {

    pub fn new() -> AvlTree<V> {
        AvlTree::<V>{ root: None }
    }

    pub fn get(&self, key: &Key) -> Option<&V> {
        get(&self.root, key)
    }

    pub fn get_mut(&mut self, key: &Key) -> Option<&mut V> {
        get_mut(&mut self.root, key)
    }

    pub fn insert(&mut self, key: Key, value: V) -> Option<V> {
        insert(&mut self.root, key, value)
    }

    pub fn remove(&mut self, key: &Key) -> Option<V> {
        remove(&mut self.root, key)
    }

    /*pub fn into_iter<'a>(&'a mut self) -> AvlIterator<'a, V> {
        let mut path = std::vec::Vec::new();
        go_to_leftmost(&mut path, self.root.as_mut());
        AvlIterator{ path }
    }*/

    pub fn check_integrity(&self) {
        check_integrity(&self.root)
    }
}*/

// Iterator API
// ''''''''''''
/*
pub struct AvlIterator<'a, V> {
    path: std::vec::Vec<AvlIteratorNode<'a, V>>,
}

impl<'a, V> AvlIterator<'a, V> {

    pub fn next(&mut self) -> Option<(&'a Key, &'a mut V)> {
        next(&mut self.path)
    }
}
*/
