//! The following module implements a minimal betree.
#![allow(dead_code)]

use std::fs::File;

use attributes::assume;
use std::vec::Vec;

type Id = u64;
type Key = u64;
type Value = u64;
type Map<K, V> = Vec<(K, V)>;

/// Timestamps are used to identify the order in which to process the messages.
/// This is important for the updates.
type Timestamp = u64;

/// Every node has a unique identifier (the betree has a counter).
/// Whenever we need to read/update the content of a node, we read/update
/// the whole content from disk at once.
///
/// In order to make things simple, the content of each node is saved in
/// a single file, identified by the node index. Also, we use json.
///
/// We don't reason about the content of [load_node] and [store_node]
/// (which are assumed), and the purpose of this example is to illustrate the
/// proof experience we have with Aeneas: we are not looking for performance.
#[assume]
pub fn load_node(id: Id) -> Map<Key, Value> {
    // Open the file
    // Open the file
    std::fs::create_dir_all("tmp").unwrap();
    let filename = format!("tmp/node{}", id).to_string();
    // Read
    let f = File::open(filename).unwrap();
    serde_json::from_reader(&f).unwrap()
}

/// Similarly to [load_node].
#[assume]
fn store_node(id: Id, content: Map<Key, Value>) {
    // Open the file
    std::fs::create_dir_all("tmp").unwrap();
    let filename = format!("tmp/node{}", id).to_string();
    // Write
    let f = File::create(filename).unwrap();
    serde_json::to_writer(&f, &content).unwrap();
}

/// A message - note that all those messages have to be linked to a key
enum Message {
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
    Upsert(Value),
}

/// Whenever we insert a message in the tree, we actually need to use a timestamp
/// with the key. The reason is that otherwise we don't know in which order to
/// apply the [Upsert] messages.
struct MessageKey {
    key: Key,
    ts: Timestamp,
}

/// A node in the BeTree
enum Node {
    /// An internal node (with children).
    ///
    /// The fields:
    /// - id
    /// - messages (map from time-stamped keys to messages)
    /// - pivot
    /// - left child
    /// - right child
    Internal(Id, Map<MessageKey, Message>, Key, Box<Node>, Box<Node>),
    /// A leaf node.
    ///
    /// The fields:
    /// - id
    /// - map from keys to values
    Leaf(Id, Map<Key, Value>),
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

impl BeTree {
    fn add_message(&mut self, key: MessageKey, msg: Message) {
        unimplemented!();
    }

    pub fn insert(&mut self, key: Key, value: Value) {
        let key = self.wrap_key(key);
        let msg = Message::Insert(value);
        self.add_message(key, msg);
    }

    pub fn delete(&mut self, key: Key) {
        let key = self.wrap_key(key);
        let msg = Message::Delete;
        self.add_message(key, msg);
    }

    pub fn upsert(&mut self, key: Key, value: Value) {
        let key = self.wrap_key(key);
        let msg = Message::Upsert(value);
        self.add_message(key, msg);
    }

    pub fn get(&mut self, key: Key) {
        unimplemented!();
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

    // TODO: rename to lookup
    pub fn query(&mut self, k: Key) -> Value {
        unimplemented!();
    }
}
