//! The following module implements a minimal betree.x

use std::vec::Vec;

type Id = u64;
type Key = u64;
type Value = u64;
type Map<K, V> = Vec<(K, V)>;

/// Every node has a unique identifier (the betree has a counter).
/// The content of each node is saved in a file, whose name is derived from
/// the node identifier.
/// TODO: or we can identify sectors of a unique file
/// with the identifier. The only issue is that I don't want to carry a file
/// in the btree (which is why I'm ok on opening then closing every time we
/// need access).
/// TODO: I think it is better to carry a file.
///
/// Whenever we need to read the content of a node, we read the whole content
/// at once.
#[assume]
fn load_node(Id: u64) -> Map<Key, Value> {
    // TODO:
    unimplemented!();
}

/*
/// Similarly to [load_node]: whenever we need to update the content of a
/// node, we update the whole content at once.
#[assume]
fn store_node(Id: u64, content: Map<Key, Value>) {
    // TODO:
    unimplemented!();
}

/// Timestamps are used to identify the order in which to process the messages.
/// This is important for the updates.
type Timestamp = u64;

/// A message
enum Message {
    /// Insert a binding from value to key
    Insert(Key, Value),
    /// Delete a binding from value to key
    Delete(Key),
    /// TODO: remove that?
    /// If we keep that, it is better to have binary trees for the map,
    /// but we can start with vectors.
    /// TODO: rename `Upsert`
    /// fn apply()
    Update(Key, Value),
}

/// A node in the BeTree
enum Node {
    /// An internal node (with children).
    ///
    /// The fields:
    /// - id
    /// - messages
    /// - pivot
    /// - left child
    /// - right child
    /// TODO: Key -> MessageKey
    /// TODO: Map: linked list
    Internal(Id, Map<Key, Message>, Key, Box<Node>, Box<Node>),
    /// A leaf node.
    ///
    /// The fields:
    /// - id
    /// - messages
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
    // TODO: rename to update
    pub fn apply(&mut self, msg: Message) {
        unimplemented!();
    }

    // TODO: rename to lookup
    pub fn query(&mut self, k: Key) -> Value {
        unimplemented!();
    }
}
*/
