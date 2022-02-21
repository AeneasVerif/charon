//! The following module implements a minimal betree.
//! We don't have loops for now, so we will need to update the code to remove
//! the recursive functions at some point.
//! We drew a lot of inspiration from the C++ [Be-Tree](https://github.com/oscarlab/Be-Tree).
//! implementation.
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
///
/// Note that we don't have clean/dirty nodes: all nodes are immediately
/// written on disk upon being updated.
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
    ///
    /// Note that in Be-Tree the internal nodes have lists of children, which
    /// allows to do even smarter things: if an internal node has too many
    /// messages, then:
    /// - either it can transmit big batches of those messages to some of its
    ///   children, in which case it does
    /// - or it can't, in which case it splits, because otherwise we have too
    ///   many unefficient updates to perform (the aim really is to amortize
    ///   the cost of I/O)
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
/// we draw inspiration from the C++ Be-Tree implemenation, where
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

impl<T> List<T> {
    /// Push an element at the front of the list.
    fn push_front(&mut self, x: T) {
        // Move under borrows: annoying...
        let tl = std::mem::replace(self, List::Nil);
        *self = List::Cons(x, Box::new(tl));
    }

    /// Pop the element at the front of the list
    fn pop_front(&mut self) -> T {
        // Move under borrows: annoying...
        let ls = std::mem::replace(self, List::Nil);
        match ls {
            List::Nil => panic!(),
            List::Cons(x, tl) => {
                *self = *tl;
                x
            }
        }
    }
}

impl Node {
    /// Apply a message to ourselves
    ///
    /// This basically inserts a message in a messages stack. However,
    /// we may need to filter previous messages: for insert, if we insert an
    /// [Insert] in a stack which contains an [Insert] or a [Delete] for the
    /// same key, we replace this old message with the new one.
    fn apply<'a>(msgs: &'a mut Map<Key, Message>, key: Key, new_msg: Message) {
        // Lookup the first message for [key]
        let pending = Node::lookup_first_message_for_key(msgs, key);
        // What we do is not the same, depending on whether there is already
        // a message or not.
        match pending {
            List::Nil => {
                // Nothing: simply add the new message
                *pending = List::Cons((key, new_msg), Box::new(List::Nil));
            }
            List::Cons((k, msg), next_msgs) => {
                // Check if this is the same key:
                // - if not, we simply insert the new message
                // - if yes, we need to take the current message into account
                if *k != key {
                    // Simply insert
                    pending.push_front((key, new_msg));
                } else {
                    // We need to check the current message
                    match &new_msg {
                        Message::Insert(_) | Message::Delete => {
                            // If [Insert] or [Delete]: filter the current
                            // messages, and insert the new one
                            Node::filter_messages_for_key(key, pending);
                            pending.push_front((key, new_msg));
                        }
                        Message::Upsert(s) => {
                            // If [Update]: we need to take into account the
                            // previous messages.
                            match msg {
                                Message::Insert(_) => {
                                    unimplemented!()
                                }
                                Message::Delete => {
                                    // There should be exactly one message
                                    unimplemented!()
                                }
                                Message::Upsert(_) => {
                                    unimplemented!()
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    fn filter_messages_for_key<'a>(key: Key, msgs: &'a mut Map<Key, Message>) {
        unimplemented!()
    }

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
                // Look for the first message pending for the key.
                // Note that we maintain the following invariants:
                // - if there are > 1 messages, they must be upsert messages only
                // - the upsert messages are sorted from the *first* added to the
                //   *last* added to the betree.
                // Also note that if there are upsert messages, we have to apply
                // them immediately.
                //
                // Rk.: [lookup_first_message_for_key] below returns a borrow to
                // the portion of the list we will update (if we have upserts,
                // we will apply the messages, filter them while doing so,
                // insert an [Insert] message, etc.). Should be interesting
                // to see how the proof experience with the backward functions
                // is at this for this piece of code. Note that this was inpired
                // by Be-Tree.
                // Also, can't wait to see how all this will work with loops.
                let pending = Node::lookup_first_message_for_key(&mut msgs, key);
                match pending {
                    List::Nil => {
                        // Nothing: dive into the children
                        Node::lookup_in_children(*pivot, left, right, key)
                    }
                    List::Cons((k, msg), _) => {
                        // Check if the borrow which points inside the messages
                        // stack points to a message for [key]
                        if *k != key {
                            // Note the same key: dive into the children
                            Node::lookup_in_children(*pivot, left, right, key)
                        } else {
                            // Same key: match over the message for this key
                            match msg {
                                Message::Insert(v) => Some(*v),
                                Message::Delete => None,
                                Message::Upsert(_) => {
                                    // There are pending upserts: we have no choice but to
                                    // apply them.
                                    //
                                    // Rk.: rather than calling [lookup], we could actually
                                    // go down the tree accumulating upserts. On the other
                                    // hand, the key is now "hotter", so it is not a bad
                                    // idea to keep it as close to the root as possible.
                                    // Note that what we do is what Be-Tree does.
                                    //
                                    // First, lookup the value from the children.
                                    let v = Node::lookup_in_children(*pivot, left, right, key);
                                    // Apply the pending updates, and replace them with
                                    // an [Insert] containing the updated value.
                                    //
                                    // Rk.: Be-Tree doesn't seem to store the newly computed
                                    // value, which I don't understand.
                                    let v = Node::apply_upserts(pending, v, key);
                                    // Update the node content
                                    store_internal_node(*id, msgs);
                                    // Return the value
                                    Option::Some(v)
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    /// Small utility: lookup a value in the children nodes.
    fn lookup_in_children(
        pivot: Key,
        left: &mut Box<Node>,
        right: &mut Box<Node>,
        key: Key,
    ) -> Option<Value> {
        if key < pivot {
            left.lookup(key)
        } else {
            right.lookup(key)
        }
    }

    /// Return a mutable borrow to the first message whose key is <= than [key].
    /// If the key is [key], then it is the first message about [key].
    /// Otherwise, it gives us a mutable borrow to the place where we need
    /// to insert new messages (note that the borrow may point to the end
    /// of the list).
    fn lookup_first_message_for_key<'a>(
        msgs: &'a mut Map<Key, Message>,
        key: Key,
    ) -> &'a mut Map<Key, Message> {
        match msgs {
            List::Nil => msgs,
            List::Cons(x, next_msgs) => {
                // Rk.: we need Polonius here
                // We wouldn't need Polonius if directly called the proper
                // function to make the modifications here (because we wouldn't
                // need to return anything). However, it would not be very
                // idiomatic, especially with regards to the fact that we will
                // rewrite everything with loops at some point.
                if x.0 >= key {
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

    /// Apply the upserts from the current messages stack to a looked up value.
    ///
    /// The input mutable borrow must point to the first upsert message in the
    /// messages stack of the current node. We remove the messages from the stack
    /// while applying them.
    /// Note that if there are no more upserts to apply, then the value must be
    /// `Some`. Also note that we use the invariant that in the message stack,
    /// upsert messages are sorted from the first to the last to apply.
    fn apply_upserts(msgs: &mut Map<Key, Message>, prev: Option<Value>, key: Key) -> Value {
        match msgs {
            List::Nil => {
                // We reached the end of the list: we applied all the upsert
                // messages. Simply put an [Insert] message.
                let v = prev.unwrap();
                *msgs = List::Cons((key, Message::Insert(v)), Box::new(List::Nil));
                return v;
            }
            List::Cons((k, msg), next_msgs) => {
                // Check if we should stop here
                if *k == key {
                    // This message still applies to the key. Note that it
                    // *must* be an upsert message.
                    match msg {
                        Message::Upsert(s) => {
                            // Apply the update
                            let v = upsert_update(prev, *s);
                            let prev = Option::Some(v);
                            // Pop the message the message we just applied
                            let _ = msgs.pop_front();
                            // Continue
                            Node::apply_upserts(msgs, prev, key)
                        }
                        _ => {
                            // Unreachable: we can only have [Upsert] messages
                            // for the key
                            panic!();
                        }
                    }
                } else {
                    // Not the proper key: we applied all the upsert messages.
                    // Simply put an [Insert] message and return the value.
                    let v = prev.unwrap();
                    msgs.push_front((key, Message::Insert(v)));
                    return v;
                }
            }
        }
    }
}

impl BeTree {
    fn add_message(&mut self, _key: Key, _msg: Message) {
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
