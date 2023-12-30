# bstree
A Binary Search Tree written in Rust

## Description
The implementation requires the elements to implement the
[Ord](https://doc.rust-lang.org/std/cmp/trait.Ord.html) trait,
since a binary search tree expects to contain unique elements that
can be compared.  

It should be noted that the implementation consists of both 
recursive and iterative methods,
and are most likely not the most efficient ones out there 
(at least for now).

## Getting Started
You can read the detailed documentation of the crate [here](https://crates.io/crates/bstree).

## Usage
Simply add the crate to your project's Cargo.toml: 
```toml
[dependencies]
bstree = "0.1.0"
```
Or alternatively use the command:
```
cargo add bstree
```

## Contributing 
Contributions are welcome, and greatly appreciated.
