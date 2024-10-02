//@ known-failure

fn next(iter: &mut std::vec::IntoIter<u8>) -> Option<Vec<u8>> {
    Some(vec![iter.next()?])
}
