
#![allow(dead_code)]

use std::cmp::Ordering;

pub type Key = i32;

pub struct BNode<V> {
    key:   Key,
    value: V,
    left:  BTree<V>,
    right: BTree<V>,
}

pub enum BTree<V> {
    Leaf, Node(Box<BNode<V>>)
}

impl<V> BTree<V> {

    pub fn new() -> BTree<V> { BTree::Leaf }

    pub fn check_integrity(&self) {
        if let BTree::Node(n) = self {
            if let BTree::Node(left) = &n.left {
                n.left.check_integrity();
                assert!(left.key < n.key);
            }
            if let BTree::Node(right) = &n.right {
                n.right.check_integrity();
                assert!(right.key > n.key);
            }
        }
    }

    pub fn is_leaf(&self) -> bool {
        match self {
            BTree::Leaf    => true,
            BTree::Node(_) => false
        }
    }

    pub fn contains(&self, k: &Key) -> bool {
        match self {
            BTree::Leaf => false,
            BTree::Node(n) => match k.cmp(&n.key) {
                Ordering::Equal   => true,
                Ordering::Less    => n.left .contains(k),
                Ordering::Greater => n.right.contains(k),
            }
        }
    }

    pub fn get_mut(&mut self, k: &Key) -> &mut V {
        match self {
            BTree::Leaf => panic!("not here !"),
            BTree::Node(n) => match k.cmp(&n.key) {
                Ordering::Equal   => &mut n.value,
                Ordering::Less    => n.left .get_mut(k),
                Ordering::Greater => n.right.get_mut(k),
            }
        }
    }

    pub fn insert(&mut self, k: Key, v: V) {
        match self {
            BTree::Leaf => *self = BTree::Node(Box::new(BNode
                { key: k, value: v, left: BTree::Leaf, right: BTree::Leaf })),

            BTree::Node(n) => match k.cmp(&n.key) {
                Ordering::Equal   => n.value = v,
                Ordering::Less    => n.left .insert(k, v),
                Ordering::Greater => n.right.insert(k, v),
            }
        }
    }

    pub fn remove(&mut self, k: &Key) {
        match self {
            BTree::Leaf => (),
            BTree::Node(n) => match k.cmp(&n.key) {
                Ordering::Less    => n.left .remove(k),
                Ordering::Greater => n.right.remove(k),
                Ordering::Equal => {
                    *self = std::mem::replace(self, BTree::Leaf).remove_current()
                },
            }
        }
    }

    fn remove_current(mut self: BTree<V>) -> BTree<V> {
        match &mut self {
            BTree::Leaf    => panic!("Always called on node"),
            BTree::Node(n) => match n.right.get_leftmost() {
                None       => std::mem::replace(&mut n.left, BTree::Leaf),
                Some(succ) => match succ {
                    BTree::Leaf    => panic!("Option::Some always contains a node"),
                    BTree::Node(s) => {
                        std::mem::swap(&mut n.key,   &mut s.key);
                        std::mem::swap(&mut n.value, &mut s.value);
                        *succ = std::mem::replace(&mut s.right, BTree::Leaf);
                        self
                    }
                }
            }
        }
    }

    fn as_node_mut(&mut self) -> &mut BNode<V> {
        match self {
            BTree::Leaf => panic!("Bad node cast"),
            BTree::Node(n) => n
        }
    }

    fn get_leftmost(&mut self) -> Option<&mut BTree<V>> {
        /* Nested Polonius case
        match self {
            BTree::Leaf    => None,
            BTree::Node(n) => if n.left.is_leaf() 
                { Some(self) } else { n.left.get_leftmost() }
        } */
        if self.is_leaf() { return None }

        if self.as_node_mut().left.is_leaf() {
            Some(self)
        }
        else {
            self.as_node_mut().left.get_leftmost()
        }
    }
}

#[test]
pub fn test_small_binary_tree() {
    let mut tree = BTree::<i32>::new();
    tree.check_integrity();

    tree.insert(10, 1);
    tree.insert(20, 2);
    tree.insert(30, 3);
    tree.insert(0,  0);
    tree.check_integrity();

    tree.insert(0,   99);
    tree.insert(10, 199);
    tree.insert(20, 299);
    tree.insert(30, 399);
    tree.check_integrity();

    assert!(*tree.get_mut(&0 ) ==  99);
    assert!(*tree.get_mut(&10) == 199);
    assert!(*tree.get_mut(&20) == 299);
    assert!(*tree.get_mut(&30) == 399);

    assert!(!tree.contains(&-5));
    assert!(!tree.contains(&5));
    assert!(!tree.contains(&15));
    assert!(!tree.contains(&25));
    assert!(!tree.contains(&35));

    let zero = tree.get_mut(&0);
    *zero = 42;
    assert!(*tree.get_mut(&0) == 42);
    tree.check_integrity();

    tree.remove(&0);
    tree.remove(&10);
    tree.check_integrity();

    tree.remove(&-5);
    tree.remove(&0);
    tree.remove(&5);
    tree.remove(&10);
    tree.remove(&15);
}
