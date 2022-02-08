//! A hashmap implementation.
//! TODO: we will need function pointers/closures if we want to make the map
//! generic in the key type.
#![allow(dead_code)]

use std::vec::Vec;
pub type Key = usize; // TODO: make this generic
pub type Hash = usize;

pub enum List<T> {
    Cons(Key, T, Box<List<T>>),
    Nil,
}

/// A hash function for the keys.
/// Rk.: we use shared references because we anticipate on the generic
/// hash map version.
pub fn hash_key(k: &Key) -> Hash {
    // Do nothing for now, we might want to implement something smarter
    // in the future
    *k
}

/// A hash map from [u64] to values
pub struct HashMap<T> {
    /// The current number of values in the table
    num_values: usize,
    /// The max load factor, expressed as a fraction
    /// TODO: use
    max_load_factor: (usize, usize),
    /// The table itself
    slots: Vec<List<T>>,
}

impl<T> HashMap<T> {
    /// Allocate a vector of slots of a given size.
    /// We would need a loop, but can't use loops for now...
    fn allocate_slots(mut slots: Vec<List<T>>, n: usize) -> Vec<List<T>> {
        if n == 0 {
            slots
        } else {
            slots.push(List::Nil);
            HashMap::allocate_slots(slots, n - 1)
        }
    }

    pub fn new() -> Self {
        let slots = HashMap::allocate_slots(Vec::new(), 32);
        HashMap {
            num_values: 0,
            max_load_factor: (4, 5),
            slots,
        }
    }

    /// We need a loop here too...
    /// Also, we start with the end, so that F* sees that the function terminates.
    fn clear_slots(slots: &mut Vec<List<T>>, i: usize) {
        if i > 0 {
            let i = i - 1;
            slots[i] = List::Nil;
            HashMap::clear_slots(slots, i)
        } else {
            ()
        }
    }

    pub fn clear(&mut self) {
        self.num_values = 0;
        let len = self.slots.len();
        HashMap::clear_slots(&mut self.slots, len);
    }

    pub fn len(&self) -> usize {
        self.num_values
    }

    /// Insert in a list.
    /// Return `true` if we inserted an element, `false` if we simply updated
    /// a value.
    fn insert_in_list<'a>(key: Key, value: T, ls: &'a mut List<T>) -> bool {
        match ls {
            List::Nil => {
                *ls = List::Cons(key, value, Box::new(List::Nil));
                true
            }
            List::Cons(ckey, cvalue, ls) => {
                if *ckey == key {
                    *cvalue = value;
                    false
                } else {
                    HashMap::insert_in_list(key, value, ls)
                }
            }
        }
    }

    pub fn insert<'a>(&'a mut self, key: Key, value: T) {
        let hash = hash_key(&key);
        let hash_mod = hash % self.slots.len();
        // We may want to use slots[...] instead of get_mut...
        let inserted = HashMap::insert_in_list(key, value, &mut self.slots[hash_mod]);
        if inserted {
            self.num_values += 1;
        }
        // TODO: resize the hashmap
    }

    /// We don't support borrows inside of enumerations for now, so we
    /// can't return an option...
    fn get_in_list<'a, 'k>(key: &'k Key, ls: &'a List<T>) -> &'a T {
        match ls {
            List::Nil => panic!(),
            List::Cons(ckey, cvalue, ls) => {
                if *ckey == *key {
                    cvalue
                } else {
                    HashMap::get_in_list(key, ls)
                }
            }
        }
    }

    pub fn get<'a, 'k>(&'a self, key: &'k Key) -> &'a T {
        let hash = hash_key(key);
        let hash_mod = hash % self.slots.len();
        HashMap::get_in_list(key, &self.slots[hash_mod])
    }

    /// Same remark as for [get_in_list]
    fn get_mut_in_list<'a, 'k>(key: &'k Key, ls: &'a mut List<T>) -> &'a mut T {
        match ls {
            List::Nil => panic!(),
            List::Cons(ckey, cvalue, ls) => {
                if *ckey == *key {
                    cvalue
                } else {
                    HashMap::get_mut_in_list(key, ls)
                }
            }
        }
    }

    /// Same remark as for [get].
    pub fn get_mut<'a, 'k>(&'a mut self, key: &'k Key) -> &'a mut T {
        let hash = hash_key(key);
        let hash_mod = hash % self.slots.len();
        HashMap::get_mut_in_list(key, &mut self.slots[hash_mod])
    }

    /*fn get_in_list<'l, 'k>(key: &'k Key, ls: &'l List<T>) -> Option<&'l T> {
        match ls {
            List::Nil => None,
            List::Cons(ckey, cvalue, ls) => {
                if *ckey == *key {
                    Some(cvalue)
                } else {
                    HashMap::get_in_list(key, ls)
                }
            }
        }
    }

    /// The signature is not exactly the same as the one in
    /// [https://doc.rust-lang.org/std/collections/struct.HashMap.html#method.get_mut]
    /// (the region paramaters are more precise here).
    pub fn get<'l, 'k>(&'l self, key: &'k Key) -> Option<&'l T> {
        let hash = hash_key(key);
        let hash_mod = hash % self.slots.len();
        HashMap::get_in_list(key, &self.slots[hash_mod])
    }

    fn get_mut_in_list<'l, 'k>(key: &'k Key, ls: &'l mut List<T>) -> Option<&'l mut T> {
        match ls {
            List::Nil => None,
            List::Cons(ckey, cvalue, ls) => {
                if *ckey == *key {
                    Some(cvalue)
                } else {
                    HashMap::get_mut_in_list(key, ls)
                }
            }
        }
    }

    /// Same remark as for [get].
    pub fn get_mut<'l, 'k>(&'l mut self, key: &'k Key) -> Option<&'l mut T> {
        let hash = hash_key(key);
        let hash_mod = hash % self.slots.len();
        HashMap::get_mut_in_list(key, &mut self.slots[hash_mod])
    }*/

    /// Remove an element from the list.
    /// Return the removed element.
    fn remove_from_list<'a>(key: &Key, ls: &'a mut List<T>) -> Option<T> {
        match ls {
            List::Nil => None,
            List::Cons(ckey, _, tl) => {
                if *ckey == *key {
                    // We have to move under borrows, so we need to use
                    // [std::mem::replace] in several steps.
                    // Retrieve the tail
                    let mv_ls = std::mem::replace(ls, List::Nil);
                    match mv_ls {
                        List::Nil => unreachable!(),
                        List::Cons(_, cvalue, tl) => {
                            // Make the list equal to its tail
                            *ls = *tl;
                            // Returned the dropped value
                            Some(cvalue)
                        }
                    }
                } else {
                    HashMap::remove_from_list(key, tl)
                }
            }
        }
    }

    /// Same remark as for [get].
    pub fn remove<'a>(&'a mut self, key: &Key) -> Option<T> {
        let hash = hash_key(key);
        let hash_mod = hash % self.slots.len();
        let x = HashMap::remove_from_list(key, &mut self.slots[hash_mod]);
        match x {
            Option::None => Option::None,
            Option::Some(x) => {
                self.num_values -= 1;
                Option::Some(x)
            }
        }
    }
}

#[test]
fn test1() {
    let mut hm: HashMap<u64> = HashMap::new();
    hm.insert(0, 42);
    hm.insert(128, 18);
    hm.insert(1024, 138);
    hm.insert(1056, 256);
    assert!(*hm.get(&128).unwrap() == 18);
    let x = hm.get_mut(&1024).unwrap();
    *x = 56;
    assert!(*hm.get(&1024).unwrap() == 56);
    assert!(hm.get(&10).is_none());
    let x = hm.remove(&1024).unwrap();
    assert!(x == 56);
    assert!(*hm.get(&0).unwrap() == 42);
    assert!(*hm.get(&128).unwrap() == 18);
    assert!(*hm.get(&1056).unwrap() == 256);
}
