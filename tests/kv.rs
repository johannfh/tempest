use tempest::KvStore;

mod common;
extern crate tempest;

#[test]
fn test_kv_open() {
    init!();

    let kv_dir = common::get_test_dir().expect("failed to get test dir");

    let kv = KvStore::open(kv_dir).expect("failed to open db");
    kv.insert(b"key1", b"value1");
    kv.insert(b"key2", b"value2");
    kv.insert(b"key1", b"value3"); // Update key1
    let value = kv.get(b"key1").expect("key1 should exist");
    assert_eq!(value, b"value3");
}
