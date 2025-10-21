//! # Write-Ahead Logging (WAL) Module
//!
//! This module provides functionality for write-ahead logging (WAL) to ensure data integrity and
//! durability in the event of system crashes or failures.
//! In [ACID](https://en.wikipedia.org/ACID), thats the "D" (Durability).
//!
//! ## Overview
//!
//! The WAL module allows for logging changes to a persistent log file before applying them to the
//! main data store. This ensures that in the event of a crash, the system can recover to a
//! consistent state by replaying the log entries that were committed before crashing sequentially.
//!
//! ## Data Directory Hierarchy
//!
//! - `/recycle/`: Directory for recycled WAL files. This is managed through the [`FilePool`].
//!   Recycled files can be reused to minimize file creation overhead.
//! - `/wal/`: Directory for active WAL files.
//! - `/wal/{virtual_wal_number}.log/`: Virtual WAL directories, each containing multiple files.
//! - `/wal/{virtual_wal_number}.log/.wal_manifest`: Manifest file for the virtual WAL.
//!   Stores general metadata and specifics about all the contained WAL files.
//! - `/wal/{virtual_wal_number}.log/{wal_file_number}.wal`: Individual WAL files.
//!   Block size and other parsing specifics are defined in the virtual WAL manifest file.
//!
//! ## Key Components
//!
//! NOTE: The following components will likely be changed, current work is focused on
//! async-runtime-agnostic file I/O abstraction and evaulating an io_uring based implementation.
//! 
//! --- Outdated ---
//!
//! ### WalManager
//!
//! The [`WalManager`] is the high-level interface for managing the write-ahead log. It handles log
//! file creation through the [`VirtualWal`]s, rotation, and recovery processes.
//!
//! ### VirtualWal
//!
//! The [`VirtualWal`] provides an abstraction over the physical log files, allowing for easier
//! management of log entries and their states.
//! It is an aggregate of multiple [`WalFile`]s that together represent a complete
//! write-ahead log.
//!
//! ### WalFile
//!
//! The [`WalFile`] represents an individual log file that stores the log entries. It provides
//! methods for writing log entries and reading them back during recovery.
//!
//! ### WalEntry
//!
//! The [`WalEntry`] struct defines the format of each log entry, including the operation type.
//! It is created from the following types of the [`core` module](crate::core):
//!
//! - [`KeySlice`](crate::core::KeySlice): The raw key bytes.
//! - [`KeyTrailer`](crate::core::KeyTrailer): The metadata associated with the key.
//!   - [`KeyTrailer::seqnum()`](crate::core::KeyTrailer::seqnum): The entries sequence number.
//!   - [`KeyTrailer::kind()`](crate::core::KeyTrailer::kind): The type of operation (like Set).
//! - [`ValueSlice`](crate::core::ValueSlice): The raw value bytes.
//!
//! ## Asynchronous Operations
//!
//! - File I/O operations are performed using asynchronous methods to ensure non-blocking behavior.
//!   This makes the WAL suitable for high-performance applications, but it also forces the use of
//!   async/await patterns in Rust.

