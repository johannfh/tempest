use tempest::Tempest;

#[macro_use]
extern crate tracing;

fn main() {
    let tracing_level = std::env::var("TRACE_LEVEL")
        .unwrap_or_else(|_| "info".to_string())
        .parse::<tracing::Level>()
        .expect("Invalid TRACE_LEVEL");

    tracing_subscriber::fmt()
        .with_max_level(tracing_level)
        .init();

    let tempest = Tempest::new();
    tempest.insert(b"key1", b"value1");
    info!("Inserted key1 with value1");
    tempest.insert(b"key2", b"value2");
    info!("Inserted key2 with value2");
    tempest.insert(b"key1", b"value3"); // Update key1
    info!("Updated key1 with value3");
    let value = tempest.get(b"key1").expect("key1 should exist");
    info!(
        "Retrieved value for 'key1': {:?}",
        std::str::from_utf8(value).unwrap()
    );
}
