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
pub(crate) type InternalContent = Map<MessageKey, Message>;

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

/*
/// The update function used for [Upsert].
/// Will be removed once we have closures (or at least function pointers).
/// This function just computes a saturated sum.
/// Also note that it takes an option as input, for the previous value:
/// we took inspiration from [https://github.com/oscarlab/Be-Tree], where
/// in case the binding is not present, the closure stored in upsert is
/// given a default value.
pub fn update(prev: Option<Value>, add: Value) -> Value {
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
                // Check if there is a message for the key
                unimplemented!();
            }
        }
    }

    /// Helper function
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

    /// Retrieve the messages pending for a key (and remove them from the stack
    /// of messages).
    /// Note that we maintain the following invariants:
    /// - if there are > 1 messages, they must be update messages only
    /// - the update messages are sorted by order of timestamp (earliest first)
    fn filter_pending_messages(msgs: &mut Map<Key, Value>) -> Map<Key, Value> {
        unimplemented!();
    }
}

impl BeTree {
    fn add_message(&mut self, key: MessageKey, msg: Message) {
        unimplemented!();
    }

    /// Insert a binding from [key] to [value]
    pub fn insert(&mut self, key: Key, value: Value) {
        let key = self.wrap_key(key);
        let msg = Message::Insert(value);
        self.add_message(key, msg);
    }

    /// Delete the bindings for [key]
    pub fn delete(&mut self, key: Key) {
        let key = self.wrap_key(key);
        let msg = Message::Delete;
        self.add_message(key, msg);
    }

    /// Apply a query-update
    pub fn upsert(&mut self, key: Key, value: Value) {
        let key = self.wrap_key(key);
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
*/
