//! The following module implements a minimal betree.
//! We don't have loops for now, so we will need to update the code to remove
//! the recursive functions at some point.
//! We drew a lot of inspiration from the C++ [Be-Tree](https://github.com/oscarlab/Be-Tree).
//! implementation.
#![allow(dead_code)]

use crate::betree_utils as utils;
use attributes::assume;

pub type NodeId = u64;
pub type Key = u64;
pub type Value = u64;

type Map<K, V> = List<(K, V)>;

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
fn load_internal_node(id: NodeId) -> InternalContent {
    utils::load_internal_node(id)
}

/// See [load_internal_node].
#[assume]
fn store_internal_node(id: NodeId, content: InternalContent) {
    utils::store_internal_node(id, content)
}

/// See [load_internal_node].
#[assume]
fn load_leaf_node(id: NodeId) -> LeafContent {
    utils::load_leaf_node(id)
}

/// See [load_internal_node].
#[assume]
fn store_leaf_node(id: NodeId, content: LeafContent) {
    utils::store_leaf_node(id, content)
}

/// We use this type to encode closures.
/// See [Message::Upsert] and [upsert_update]
pub enum UpsertFunState {
    Add(u64),
    Sub(u64),
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
    /// we potentially have to explore the tree in depth (and every time we
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
    /// b-epsilon trees, which have the particularity of storing messages:
    /// b-trees and their variants work very well (and don't use messages).
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
    Upsert(UpsertFunState),
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
/// A leaf node contains a map from keys to values.
/// We store the bindings in order of increasing key.
pub(crate) type LeafContent = Map<Key, Value>;

/// Internal node. See [Node].
struct Internal {
    id: NodeId,
    pivot: Key,
    left: Box<Node>,
    right: Box<Node>,
}

/// Leaf node. See [Node]
struct Leaf {
    id: NodeId,
    /// The number of bindings in the node
    size: u64,
}

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
    Internal(Internal),
    /// A leaf node.
    ///
    /// The fields:
    /// - id
    Leaf(Leaf),
}

/// Parameters and indices used in the BeTree
struct Params {
    /// The minimum number of messages we flush to the children.
    /// We wait to reach 2 * min_flush_size before flushing to children.
    /// If one of the children doesn't receive a number of
    /// messages >= min_flush_size, we keep those messages in the parent
    /// node. Of course, at least one of the two children will receive
    /// flushed messages: this gives us that an internal node has at most
    /// 2 * min_flush_size pending messages - 1.
    min_flush_size: u64,
    /// The maximum number of bindings we can store in a leaf node (if we
    /// reach this number, we split).
    split_size: u64,
    /// Every node has a unique id
    next_node_id: NodeId,
}

impl Params {
    fn fresh_node_id(&mut self) -> NodeId {
        let id = self.next_node_id;
        self.next_node_id += 1;
        id
    }
}

/// The BeTree itself
pub struct BeTree {
    params: Params,
    /// The root of the tree
    root: Node,
}

/// The update function used for [Upsert].
/// Will be removed once we have closures (or at least function pointers).
/// This function just computes a saturated sum.
/// Also note that it takes an option as input, for the previous value:
/// we draw inspiration from the C++ Be-Tree implemenation, where
/// in case the binding is not present, the closure stored in upsert is
/// given a default value.
pub fn upsert_update(prev: Option<Value>, st: UpsertFunState) -> Value {
    // We just compute the sum, until it saturates
    match prev {
        Option::None => {
            match st {
                UpsertFunState::Add(add) => {
                    // We consider the default value is 0, so we return 0 + add -
                    // or we could fail (it doesn't matter)
                    add
                }
                UpsertFunState::Sub(add) => {
                    // Same logic as for [sub], but this time we saturate at 0
                    0
                }
            }
        }
        Option::Some(prev) => {
            match st {
                UpsertFunState::Add(v) => {
                    // Note that Aeneas is a bit conservative about the max_usize
                    let margin = u64::MAX - prev;
                    // Check if we saturate
                    if margin >= v {
                        prev + margin
                    } else {
                        u64::MAX
                    }
                }
                UpsertFunState::Sub(v) => {
                    // Check if we saturate
                    if prev >= v {
                        prev - v
                    } else {
                        0
                    }
                }
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

    fn hd(&self) -> &T {
        match self {
            List::Nil => panic!(),
            List::Cons(hd, _) => hd,
        }
    }
}

impl<T> Map<Key, T> {
    fn head_has_key(&self, key: Key) -> bool {
        match self {
            List::Nil => false,
            List::Cons(hd, _) => hd.0 == key,
        }
    }
}

impl Leaf {
    /// Split a leaf into an internal node with two children.
    fn split(&self, content: Map<Key, Value>, params: &mut Params) -> Internal {
        unimplemented!();
    }
}

impl Internal {
    /// Small utility: lookup a value in the children nodes.
    fn lookup_in_children(&mut self, key: Key) -> Option<Value> {
        if key < self.pivot {
            self.left.lookup(key)
        } else {
            self.right.lookup(key)
        }
    }
}

impl Node {
    /// Apply a message to ourselves: leaf node case
    ///
    /// This simply updates the bindings.
    /// We return `true` if there was already a binding for `key`, `false`
    /// otherwise.
    fn apply_to_leaf<'a>(bindings: &'a mut Map<Key, Value>, key: Key, new_msg: Message) -> bool {
        // Retrieve a mutable borrow to the position of the binding, if there is
        // one, or to the end of the list
        let bindings = Node::lookup_mut_in_bindings(key, bindings);
        // Check if we point to a binding which has the key we are looking for
        if bindings.head_has_key(key) {
            // We need to pop the binding, and may need to reuse the
            // previous value (for an upsert)
            let hd = bindings.pop_front();
            // Match over the message
            match new_msg {
                Message::Insert(v) => {
                    bindings.push_front((key, v));
                }
                Message::Delete => {
                    // Nothing to do: we popped the binding
                    ()
                }
                Message::Upsert(s) => {
                    let v = upsert_update(Option::Some(hd.1), s);
                    bindings.push_front((key, v));
                }
            };
            return true;
        } else {
            // Key not found: simply insert
            match new_msg {
                Message::Insert(v) => {
                    bindings.push_front((key, v));
                }
                Message::Delete => {
                    // Nothing to do
                    ()
                }
                Message::Upsert(s) => {
                    let v = upsert_update(Option::None, s);
                    bindings.push_front((key, v));
                }
            };
            return false;
        }
    }

    /// Apply a message to ourselves: internal node case
    ///
    /// This basically inserts a message in a messages stack. However,
    /// we may need to filter previous messages: for insert, if we insert an
    /// [Insert] in a stack which contains an [Insert] or a [Delete] for the
    /// same key, we replace this old message with the new one.
    fn apply_to_internal<'a>(msgs: &'a mut Map<Key, Message>, key: Key, new_msg: Message) {
        // Lookup the first message for [key] (if there is no message for [key],
        // we get a mutable borrow to the position in the list where we need
        // to insert the new message).
        let msgs = Node::lookup_first_message_for_key(key, msgs);
        // What we do is not the same, depending on whether there is already
        // a message or not.
        if msgs.head_has_key(key) {
            // We need to check the current message
            match new_msg {
                Message::Insert(_) | Message::Delete => {
                    // If [Insert] or [Delete]: filter the current
                    // messages, and insert the new one
                    Node::filter_messages_for_key(key, msgs);
                    msgs.push_front((key, new_msg));
                }
                Message::Upsert(s) => {
                    // If [Update]: we need to take into account the
                    // previous messages.
                    match msgs.hd().1 {
                        Message::Insert(prev) => {
                            // There should be exactly one [Insert]:
                            // pop it, compute the result of the [Upsert]
                            // and insert this result
                            let v = upsert_update(Option::Some(prev), s);
                            let _ = msgs.pop_front();
                            msgs.push_front((key, Message::Insert(v)));
                        }
                        Message::Delete => {
                            // There should be exactly one [Delete]
                            // message : pop it, compute the result of
                            // the [Upsert], and insert this result
                            let _ = msgs.pop_front();
                            let v = upsert_update(Option::None, s);
                            msgs.push_front((key, Message::Insert(v)));
                        }
                        Message::Upsert(_) => {
                            // There may be several msgs upserts:
                            // we need to insert the new message at
                            // the end of the list of upserts (so
                            // that later we can apply them all in
                            // proper order).
                            let msgs = Node::lookup_first_message_after_key(key, msgs);
                            msgs.push_front((key, Message::Upsert(s)));
                        }
                    }
                }
            }
        } else {
            // No pending message for [key]: simply add the new message
            msgs.push_front((key, new_msg))
        }
    }

    /// Apply a message to ourselves
    fn apply(&mut self, params: &mut Params, key: Key, new_msg: Message) {
        match self {
            Node::Leaf(node) => {
                // Load the content from disk
                let mut content = load_leaf_node(node.id);
                // Insert
                let already_key = Node::apply_to_leaf(&mut content, key, new_msg);
                // Check if we need to split
                if !already_key && (node.size + 1 >= 2 * params.min_flush_size) {
                    // Split
                    let new_node = node.split(content, params);
                    // Store the content to disk
                    store_leaf_node(node.id, List::Nil);
                    // Update the node
                    *self = Node::Internal(new_node);
                } else {
                    // Update the size if necessary
                    if already_key {
                        node.size += 1;
                    }
                    // Store the content to disk
                    store_leaf_node(node.id, content);
                }
            }
            Node::Internal(node) => {
                // Load the content from disk
                let mut content = load_internal_node(node.id);
                // Insert
                Node::apply_to_internal(&mut content, key, new_msg);
                // Check if we need to flush
                unimplemented!();
                // Store the content to disk
                store_internal_node(node.id, content);
                unimplemented!()
            }
        }
    }

    /// Lookup a value in a list of bindings.
    /// Note that the values should be stored in order of increasing key.
    fn lookup_in_bindings(key: Key, bindings: &Map<Key, Value>) -> Option<Value> {
        match bindings {
            List::Nil => Option::None,
            List::Cons(hd, tl) => {
                if hd.0 == key {
                    Option::Some(hd.1)
                } else if hd.0 < key {
                    Option::None
                } else {
                    Node::lookup_in_bindings(key, tl)
                }
            }
        }
    }

    /// Lookup a value in a list of bindings, and return a borrow to the position
    /// where the value is (or should be inserted, if the key is not in the bindings).
    fn lookup_mut_in_bindings<'a>(
        key: Key,
        bindings: &'a mut Map<Key, Value>,
    ) -> &'a mut Map<Key, Value> {
        match bindings {
            List::Nil => bindings,
            List::Cons(hd, tl) => {
                // This requires Polonius
                if hd.0 <= key {
                    bindings
                } else {
                    Node::lookup_mut_in_bindings(key, tl)
                }
            }
        }
    }

    /// Filter all the messages which concern [key].
    ///
    /// Note that the stack of messages must start with a message for [key]:
    /// we stop filtering at the first message which is not about [key].
    fn filter_messages_for_key<'a>(key: Key, msgs: &'a mut Map<Key, Message>) {
        match msgs {
            List::Nil => (),
            List::Cons((k, _), _) => {
                if *k == key {
                    msgs.pop_front();
                    Node::filter_messages_for_key(key, msgs);
                } else {
                    // Stop
                    ()
                }
            }
        }
    }

    fn lookup_first_message_after_key<'a>(
        key: Key,
        msgs: &'a mut Map<Key, Message>,
    ) -> &'a mut Map<Key, Message> {
        match msgs {
            List::Nil => msgs,
            List::Cons((k, _), next_msgs) => {
                if *k == key {
                    Node::lookup_first_message_after_key(key, next_msgs)
                } else {
                    msgs
                }
            }
        }
    }

    /// Returns the value bound to a key.
    /// Note that while looking for the binding, we might reorganize the
    /// internals of the betree to apply or flush messages: hence the mutable
    /// borrow.
    fn lookup<'a>(&'a mut self, key: Key) -> Option<Value> {
        match self {
            Node::Leaf(node) => {
                // Load the node content
                let bindings = load_leaf_node(node.id);
                // Just lookup the binding in the map
                Node::lookup_in_bindings(key, &bindings)
            }
            Node::Internal(node) => {
                // Load the node content
                let mut msgs = load_internal_node(node.id);
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
                let pending = Node::lookup_first_message_for_key(key, &mut msgs);
                match pending {
                    List::Nil => {
                        // Nothing: dive into the children
                        node.lookup_in_children(key)
                    }
                    List::Cons((k, msg), _) => {
                        // Check if the borrow which points inside the messages
                        // stack points to a message for [key]
                        if *k != key {
                            // Note the same key: dive into the children
                            node.lookup_in_children(key)
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
                                    let v = node.lookup_in_children(key);
                                    // Apply the pending updates, and replace them with
                                    // an [Insert] containing the updated value.
                                    //
                                    // Rk.: Be-Tree doesn't seem to store the newly computed
                                    // value, which I don't understand.
                                    let v = Node::apply_upserts(pending, v, key);
                                    // Update the node content
                                    store_internal_node(node.id, msgs);
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

    /// Return a mutable borrow to the first message whose key is <= than [key].
    /// If the key is [key], then it is the first message about [key].
    /// Otherwise, it gives us a mutable borrow to the place where we need
    /// to insert new messages (note that the borrow may point to the end
    /// of the list).
    fn lookup_first_message_for_key<'a>(
        key: Key,
        msgs: &'a mut Map<Key, Message>,
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
                if x.0 <= key {
                    msgs
                } else {
                    Node::lookup_first_message_for_key(key, next_msgs)
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
        if msgs.head_has_key(key) {
            // Pop the front message.
            // Note that it *must* be an upsert.
            let msg = msgs.pop_front();
            match msg.1 {
                Message::Upsert(s) => {
                    // Apply the update
                    let v = upsert_update(prev, s);
                    let prev = Option::Some(v);
                    // Continue
                    Node::apply_upserts(msgs, prev, key)
                }
                _ => {
                    // Unreachable: we can only have [Upsert] messages
                    // for the key
                    unreachable!();
                }
            }
        } else {
            // We applied all the upsert messages: simply put an [Insert]
            // message and return the value.
            let v = prev.unwrap();
            msgs.push_front((key, Message::Insert(v)));
            return v;
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
    pub fn upsert(&mut self, key: Key, upd: UpsertFunState) {
        let msg = Message::Upsert(upd);
        self.add_message(key, msg);
    }

    /// Returns the value bound to a key.
    /// Note that while looking for the binding, we might reorganize the
    /// internals of the betree to apply or flush messages: hence the mutable
    /// borrow.
    pub fn lookup<'a>(&'a mut self, key: Key) -> Option<Value> {
        self.root.lookup(key)
    }

    fn fresh_node_id(&mut self) -> NodeId {
        self.params.fresh_node_id()
    }
}
