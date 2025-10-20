use tempest::DB;

mod common;
extern crate tempest;

#[test]
fn test_db_open() {
    init!();

    let db_dir = common::get_test_dir("test_db_open");

    let tempest = DB::open(db_dir).expect("failed to open db");
    tempest.insert(b"key1", b"value1");
    tempest.insert(b"key2", b"value2");
    tempest.insert(b"key1", b"value3"); // Update key1
    let value = tempest.get(b"key1").expect("key1 should exist");
    assert_eq!(value, b"value3");

    
}
