# TODO

- [ ] Implement memtable for in-memory storage of key-value pairs.
    - Use an append-only skiplist for efficient insertions and lookups.
    - This keeps the memtable sorted, thus allowing for fast flushing to disk.
- [ ] Implement write-ahead logging (WAL) to ensure durability of writes.
    - Every write operation should be logged to a WAL file before being applied to the memtable.
    - This allows recovery of the memtable in case of a crash.
- [ ] Implement flushing mechanism to write the memtable to disk as an SSTable when it reaches a certain size.
    - This involves serializing the memtable and writing it to a new SSTable file.
    - After flushing, the memtable should be cleared to make room for new writes.
- [ ] Implement Sorted String Table (SSTable) for efficient storage and retrieval of key-value pairs on disk.
- [ ] Implement efficient search algorithms to quickly locate keys in the SSTable.
- [ ] Add support for data compression in SSTable to save disk space.
- [ ] Implement a compaction process to merge multiple SSTables and remove deleted or obsolete entries.
    - This helps to reduce the number of SSTables and improve read performance.
- [ ] Implement a caching layer to store frequently accessed key-value pairs in memory for faster reads.
- [ ] Add support for range queries to retrieve all key-value pairs within a specified range.
- [ ] Implement read/write worker thread pools to handle concurrent read and write operations.
    - This improves the performance of the key-value store by allowing multiple operations to be processed in parallel.
- [ ] Implement a background thread to periodically flush the memtable to disk and perform compaction.
- [ ] Add support for snapshots to allow consistent reads of the key-value store at a specific point in time.
- [ ] Implement a monitoring system to track the performance and health of the key-value store.
- [ ] Add support for configuration options to customize the behavior of the key-value store
    - Config via flags and/or config file (yaml? what crate for parsing yaml?)
    - min/max memtable size
    - flush-interval based on time or other conditios

