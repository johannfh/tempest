use tempest::Tempest;

fn main() {
    let tempest = Tempest::new();
    tempest.set(b"key1", Some(b"value1"));
    println!("Set {:?} to {:?}", b"key1", b"value1");
    if let Some(value) = tempest.get(b"key1") {
        println!("Found key1: {:?}", value);
    } else {
        println!("key1 not found");
    }
}
