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

A simple usage example is given below: 
```rust
use bstree::BinarySearchTree;

fn main() {

    let mut bst = BinarySearchTree::new();

    // Initial Tree Representation: 
    //       4
    //      / \
    //     2   6
    //    / \   \
    //   1   3   8
    //          /
    //         7

    bst.insert(4);
    bst.insert(2);
    bst.insert(3);
    bst.insert(1);
    bst.insert(6);
    bst.insert(8);
    bst.insert(7);

    assert_eq!(bst.height(), 4);
    assert_eq!(bst.len(), 7);

    assert_eq!(bst.min_elem(), Some(&1));
    assert_eq!(bst.max_elem(), Some(&8));
    assert_eq!(bst.predecessor(&7), Some(&6));
    assert_eq!(bst.successor(&3), Some(&4));

    assert_eq!(bst.as_pre_order_vec().into_iter().copied().collect::<Vec<_>>(), vec![4,2,1,3,6,8,7]);
    assert_eq!(bst.as_in_order_vec().into_iter().copied().collect::<Vec<_>>(), vec![1,2,3,4,6,7,8]);
    assert_eq!(bst.as_post_order_vec().into_iter().copied().collect::<Vec<_>>(), vec![1,3,2,7,8,6,4]);

    assert_eq!(bst.get(&6), Some(&6));
    assert_eq!(bst.get(&3), Some(&3));
    assert_eq!(bst.get(&5), None);

    assert_eq!(bst.replace(&2, 5), Some(2));
    assert!(bst.contains(&5));

    assert!(bst.contains(&1) && bst.contains(&8));
    bst.remove_min();
    bst.remove_max();
    assert!(!bst.contains(&1) && !bst.contains(&8));

    assert_eq!(bst.remove(&6), Some(6));
    assert_eq!(bst.remove(&5), Some(5));

    assert_eq!(bst.iter().copied().collect::<Vec<_>>(), vec![3,4,7]);

    let mut bst2 = BinarySearchTree::from(vec![5,9,10]);
    bst.append(&mut bst2);
    assert_eq!(bst.iter().copied().collect::<Vec<_>>(), vec![3,4,5,7,9,10]);
    assert!(bst2.is_empty());

    let to_ascii = bst.iter_mut().map(|number| char::from(*number as u8 + 97))
        .collect::<String>();

    assert_eq!(to_ascii, "defhjk");

    bst.clear();
    assert!(bst.is_empty());
}

```

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
