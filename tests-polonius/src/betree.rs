//! The following module implements a minimal betree.
//! We don't have loops for now, so we will need to update the code to remove
//! the recursive functions at some point.
#![allow(dead_code)]

use crate::betree_utils as utils;
use attributes::assume;

pub type Id = u64;
pub type Key = u64;
pub type Value = u64;

type Map<K, V> = List<(K, V)>;

/// Timestamps are used to identify the order in which to process the messages.
/// This is important for the updates.
/// TODO: we don't need those...
pub(crate) type Timestamp = u64;

/// We use linked lists for the maps from keys to messages/bindings
pub(crate) enum List<T> {
    Cons(T, Box<List<T>>),
    Nil,
}

/// Every node has a unique identifier (the betree has a counter).
/// Whenever we need to read/update the content of a node, we read/update
/// the whole content from disk at once.
///
/// In order to make things simple, the content of each node is saved in
/// a single file, identified by the node index. Also, we use json.
///
/// We don't reason about the content of the load/store node functions
/// (which are assumed), while the purpose of this example is to illustrate the
/// proof experience we have with Aeneas: we are not looking for performance here.
///
/// Rk.: in the future, we will directly use the functions from betree_utils
/// and setup the translation to consider this module as assumed (i.e., no
/// wrappers)
#[assume]
fn load_internal_node(id: Id) -> InternalContent {
    utils::load_internal_node(id)
}

/// See [load_internal_node].
#[assume]
fn store_internal_node(id: Id, content: InternalContent) {
    utils::store_internal_node(id, content)
}

/// See [load_internal_node].
#[assume]
fn load_leaf_node(id: Id) -> LeafContent {
    utils::load_leaf_node(id)
}

/// See [load_internal_node].
#[assume]
fn store_leaf_node(id: Id, content: LeafContent) {
    utils::store_leaf_node(id, content)
}

/// A message - note that all those messages have to be linked to a key
pub(crate) enum Message {
    /// Insert a binding from value to key
    Insert(Value),
    /// Delete a binding from value to key
    Delete,
    /// [Upsert] is "query then update" (query a value, then update the binding
    /// by using the result of the query). This is pretty expensive if we
    /// actually *do* query, *then* update: queries are expensive, because
    /// we potentially have to explore the whole tree (and every time we
    /// lookup a node, we have an expensive I/O operation).
    /// Instead, we insert this [Upsert] message in the tree, which progressively
    /// gets propagated to the children untils it gets applied (when we find an
    /// [Insert], or when we reach a leaf).
    ///
    /// In practice, [Upsert] should store a closure. For now we don't have
    /// support for function pointers and closures, so [Upsert] doesn't store
    /// a closure and always applies the same update function. Note that the
    /// [Value] stored in [Upsert] acts as a closure's state.
    ///
    /// The interest of this example is to split the proof in two:
    /// 1. a very simple refinement proof (which is made simple by the fact that
    ///    Aeneas takes care of the memory management proof obligations through
    ///    the translation)
    /// 2. a more complex functional proof.
    /// We write a very general model of the b-epsilon tree, prove that it is
    /// refined by the translated code in 1., then prove the general functional
    /// correctness case once and for all in 2.
    /// The idea is that once we add support for closures, we should be able to
    /// update the Rust code, and all we would need to do on the proof side is
    /// to update the refinement proof in 1., which should hopefully be
    /// straightforward.
    ///
    /// Also note that if we don't have [Upsert], there is no point in using
    /// b-epsilon trees: b-trees work very well.
    ///
    /// Note there is something interesting about the proofs we do for [Upsert].
    /// When we use [Insert] or [Delete], we remove the upserts which are pending
    /// for the key, because there is no point in applying them (there would be
    /// if we wanted to leverage the fact that the update functions we apply may
    /// be stateful).
    /// The consequence is that we don't observe potentially failing executions of
    /// the update functions. At the opposite, the specification of [Upsert] is
    /// "greedy": we see [Upsert] as query then update. This means that the
    /// implementation refines the specification only if we make sure that the
    /// update function used for the upsert doesn't fail on the input we give it
    /// (all this can be seen in the specification we prove about the be-tree).
    Upsert(Value),
}

/// Whenever we insert a message in the tree, we actually need to use a timestamp
/// with the key. The reason is that otherwise we don't know in which order to
/// apply the [Upsert] messages.
pub(crate) struct MessageKey {
    pub key: Key,
    pub ts: Timestamp,
}

/// Internal node content.
///
/// An internal node contains a map from keys to pending messages
///
/// Invariants:
/// - the pairs (key, message) are sorted so that the keys are in increasing order
/// - for a given key, there can be:
///   - no message
///   - one insert or delete message
///   - a list of upsert messages. In that case, the upsert message are sorted
///     from the *first* to the *last* added in the betree.
pub(crate) type InternalContent = Map<Key, Message>;

/// Leaf node content.
///
/// A leaf node contains a map from keys to values
pub(crate) type LeafContent = Map<Key, Value>;

/// A node in the BeTree.
/// Note that the node's content is stored on disk (and hence absent from the
/// node itself).
enum Node {
    /// An internal node (with children).
    ///
    /// The fields:
    /// - id
    /// - pivot
    /// - left child
    /// - right child
    ///
    /// Note that the bindings for the keys < pivot are in the left child,
    /// and the keys >= pivot are in the right child.
    Internal(Id, Key, Box<Node>, Box<Node>),
    /// A leaf node.
    ///
    /// The fields:
    /// - id
    Leaf(Id),
}

/// The BeTree itself
pub struct BeTree {
    min_flush_size: u64,
    max_node_size: u64,
    min_node_size: u64,
    root: Node,
    next_timestamp: Timestamp,
    next_node_id: Id,
}

/// The update function used for [Upsert].
/// Will be removed once we have closures (or at least function pointers).
/// This function just computes a saturated sum.
/// Also note that it takes an option as input, for the previous value:
/// we took inspiration from [https://github.com/oscarlab/Be-Tree], where
/// in case the binding is not present, the closure stored in upsert is
/// given a default value.
pub fn upsert_update(prev: Option<Value>, add: Value) -> Value {
    // We just compute the sum, until it saturates
    match prev {
        Option::None => {
            // We consider the default value is 0, so we return 0 + add -
            // or we could fail (it doesn't matter)
            add
        }
        Option::Some(prev) => {
            // Note that Aeneas is a bit conservative about the max_usize
            let margin = u64::MAX - prev;
            // Check if we saturate
            if margin >= add {
                prev + margin
            } else {
                u64::MAX
            }
        }
    }
}

impl Node {
    /// Returns the value bound to a key.
    /// Note that while looking for the binding, we might reorganize the
    /// internals of the betree to apply or flush messages: hence the mutable
    /// borrow.
    fn lookup<'a>(&'a mut self, key: Key) -> Option<Value> {
        match self {
            Node::Leaf(id) => {
                // Load the node content
                let bindings = load_leaf_node(*id);
                // Just lookup the binding in the map
                Node::lookup_in_bindings(&bindings, key)
            }
            Node::Internal(id, pivot, left, right) => {
                // Load the node content
                let mut msgs = load_internal_node(*id);
                // Check if there are pending messages for the key
                // (note that if there are upserts messages, we filter
                // them from the stack of messages, because those upserts
                // messages *must* be applied immediately).
                // TODO: would be better to do the following: lookup the first
                // message which concerns the key. If there is one, then
                //
                let pending = Node::lookup_filter_pending_messages(&mut msgs, key);
                match &pending {
                    List::Nil => {
                        // Nothing: dive into the children
                        if key < *pivot {
                            left.lookup(key)
                        } else {
                            right.lookup(key)
                        }
                    }
                    List::Cons(Message::Insert(v), _) => {
                        // Note that the tail must be Nil
                        Some(*v)
                    }
                    List::Cons(Message::Delete, _) => {
                        // Note that the tail must be Nil
                        None
                    }
                    List::Cons(Message::Upsert(_), _) => {
                        // There are pending upserts: we have no choice but to
                        // apply them.
                        // Rk.: rather than calling [lookup], we could actually
                        // go down the tree accumulating upserts. On the other
                        // hand, the key is now "hotter", so it is not a bad
                        // idea to keep it as close to the root as possible.
                        // First, lookup the value from the children
                        let v = if key < *pivot {
                            left.lookup(key)
                        } else {
                            right.lookup(key)
                        };
                        // Apply the pending updates
                        let v = Node::apply_upserts(v, pending);
                        // Add an [Insert] message in the messages stack, to
                        // account for the update
                        Node::insert_in_messages_stack(&mut msgs, key, v);
                        // Update the node content
                        store_internal_node(*id, msgs);
                        // Return the value
                        Option::Some(v)
                    }
                }
            }
        }
    }

    /// Return a mutable borrow to the first message which concerns the given key
    /// (if we reach the end of the list, we return it)
    fn lookup_first_message_for_key<'a>(
        msgs: &'a mut Map<Key, Message>,
        key: Key,
    ) -> &'a mut Map<Key, Message> {
        match msgs {
            List::Nil => msgs,
            List::Cons(x, next_msgs) => {
                // Rk.: we need Polonius here
                if x.0 == key {
                    msgs
                } else {
                    Node::lookup_first_message_for_key(next_msgs, key)
                }
            }
        }
    }

    /// Lookup a value in a list of bindings.
    fn lookup_in_bindings(bindings: &Map<Key, Value>, key: Key) -> Option<Value> {
        match bindings {
            List::Nil => Option::None,
            List::Cons(hd, tl) => {
                if hd.0 == key {
                    Option::Some(hd.1)
                } else {
                    Node::lookup_in_bindings(tl, key)
                }
            }
        }
    }

    /// Retrieve the messages pending for a key.
    /// Note that we maintain the following invariants:
    /// - if there are > 1 messages, they must be update messages only
    /// - the upsert messages we return are sorted from the *first* added to the
    ///   *last* added to the betree.
    /// We remove the pending messages from the messages stack if they are upserts:
    /// as this function is used for lookups,if we find an upsert, we need to apply
    /// it.
    fn lookup_filter_pending_messages(msgs: &mut Map<Key, Message>, key: Key) -> List<Message> {
        match msgs {
            List::Nil => List::Nil,
            List::Cons(x, next_msgs) => {
                let removed = Node::lookup_filter_pending_messages(next_msgs, key);
                if x.0 == key {
                    // Remove the message - can't move below a borrow...
                    // This is really annoying: there must be a more efficient
                    // way to do. Maybe we could move the whole list before
                    // filtering, then filter it, then move the filtered list
                    // back?
                    let x_and_next = std::mem::replace(msgs, List::Nil);
                    match x_and_next {
                        List::Nil => {
                            unreachable!()
                        }
                        List::Cons(x, next_msgs) => {
                            *msgs = *next_msgs;
                            List::Cons(x.1, Box::new(removed))
                        }
                    }
                } else {
                    removed
                }
            }
        }
    }

    /// Apply a list of upserts to a looked up value.
    /// They must be sorted from the first upsert to apply to the last upsert.
    /// Note that if the list of upserts is empty, then the value must be `Some`.
    fn apply_upserts(prev: Option<Value>, upserts: List<Message>) -> Value {
        match upserts {
            List::Nil => prev.unwrap(),
            List::Cons(Message::Upsert(s), next_upserts) => {
                let v = upsert_update(prev, s);
                Node::apply_upserts(Option::Some(v), *next_upserts)
            }
            _ => {
                // This is unreachable: we must only have [Upsert] messages
                // in the list
                panic!();
            }
        }
    }

    /// This is used by [lookup].
    ///
    /// If when looking up the value associated to a key we find pending upserts
    /// in an internal node, we apply them then insert an [Insert] message with
    /// the resulting value in the pending messages of the node.
    fn insert_in_messages_stack(mut msgs: &mut Map<Key, Message>, key: Key, v: Value) {
        match msgs {
            List::Nil => {
                let _ = std::mem::replace(
                    msgs,
                    List::Cons((key, Message::Insert(v)), Box::new(List::Nil)),
                );
            }
            List::Cons(x, next_msgs) => {
                if x.0 > key {
                    // Insert here - note that we have to do annoying swappings
                    // because we can't move out of borrows...
                    let tl = std::mem::replace(msgs, List::Nil);
                    let tl = List::Cons((key, Message::Insert(v)), Box::new(tl));
                    *msgs = tl;
                } else {
                    // Continue
                    Node::insert_in_messages_stack(next_msgs, key, v)
                }
            }
        }
    }
}

impl BeTree {
    fn add_message(&mut self, key: Key, msg: Message) {
        unimplemented!();
    }

    /// Insert a binding from [key] to [value]
    pub fn insert(&mut self, key: Key, value: Value) {
        let msg = Message::Insert(value);
        self.add_message(key, msg);
    }

    /// Delete the bindings for [key]
    pub fn delete(&mut self, key: Key) {
        let msg = Message::Delete;
        self.add_message(key, msg);
    }

    /// Apply a query-update
    pub fn upsert(&mut self, key: Key, value: Value) {
        let msg = Message::Upsert(value);
        self.add_message(key, msg);
    }

    /// Returns the value bound to a key.
    /// Note that while looking for the binding, we might reorganize the
    /// internals of the betree to apply or flush messages: hence the mutable
    /// borrow.
    pub fn lookup<'a>(&'a mut self, key: Key) -> Option<Value> {
        self.root.lookup(key)
    }

    fn fresh_timestamp(&mut self) -> Timestamp {
        let timestamp = self.next_timestamp;
        self.next_timestamp += 1;
        timestamp
    }

    fn wrap_key(&mut self, key: Key) -> MessageKey {
        let ts = self.fresh_timestamp();
        MessageKey { key, ts }
    }
}
