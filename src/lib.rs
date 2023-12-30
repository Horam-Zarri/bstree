//! This crate is a Rust implementation of the binary search tree data structure
//!
//! The implementation requires the elements to implement the
//! [Ord](https://doc.rust-lang.org/std/cmp/trait.Ord.html) trait,
//! since a binary search tree expects to contain unique elements that
//! can be compared.  
//!
//! It should be noted that the implementation consists of both 
//! recursive and iterative methods,
//! and most likely not the most efficient ones out there 
//! (at least for now).
//! 
#![allow(dead_code)]

use std::ptr::{NonNull, self};
use std::cmp::Ordering; 
use std::marker::PhantomData;
use std::hash::Hash;

struct TreeNode<T> {
    elem: T,
    left: Option<NonNull<TreeNode<T>>>,
    right: Option<NonNull<TreeNode<T>>>,
    parent: Option<NonNull<TreeNode<T>>>,
}

/// Binary search tree implementation
///
/// The `BinarySearchTree` type is
/// [covariant](https://doc.rust-lang.org/reference/subtyping.html).  
///
/// The implementation utilizes both recusrive and iterative algorithms 
/// as noted in the crate level documentation, so it might **blow the stack**.
///
pub struct BinarySearchTree<T: Ord> {
    root: Option<NonNull<TreeNode<T>>>,
    len: usize,
}

type Link<T> = Option<NonNull<TreeNode<T>>>;

impl<T> TreeNode<T> {

    fn new(elem: T) -> Self {
        Self { elem, left: None, right: None, parent: None }
    }

    unsafe fn new_as_ptr(elem: T, parent: Link<T>) -> NonNull<Self> {
        let mut new_node = Self::new(elem);
        new_node.parent = parent;
        NonNull::new_unchecked(Box::into_raw(Box::new(new_node)))
    }

    unsafe fn drop_tree(mut tn: Link<T>) {
        tn.take().map(|node| {
            if let Some(mut prnt) = node.as_ref().parent {
                match (prnt.as_ref().left, prnt.as_ref().right) {
                    (None, None) => unreachable!("The parent should have
                                                 a pointer to its child"),
                                                 (None, Some(_)) => {
                                                     prnt.as_mut().right = None;
                                                 }
                    (Some(_), None) => {
                        prnt.as_mut().left = None;
                    },
                    (Some(lchild), Some(rchild)) => {
                        if lchild.as_ptr() == node.as_ptr() {
                            prnt.as_mut().left = None;
                        }
                        if rchild.as_ptr() == node.as_ptr() {
                            prnt.as_mut().right = None;
                        }
                    },
                }
            }

            let boxed_node = Box::from_raw(node.as_ptr());
            Self::drop_tree(boxed_node.left);
            Self::drop_tree(boxed_node.right);

        });
    }




    unsafe fn height(&self) -> usize {
        let lheight = self.left.map_or(0, |ln| ln.as_ref().height());
        let rheight = self.right.map_or(0, |rn| rn.as_ref().height());

        lheight.max(rheight) + 1
    }


    unsafe fn successor(tn: NonNull<Self>) -> Link<T> {
        if let Some(rnode) = tn.as_ref().right {
            return Some(Self::min_helper_nr(rnode));
        }
        else {
            let mut temp = tn;
            let mut temp_parent = tn.as_ref().parent;

            while let Some(pnode) = temp_parent {
                if let Some(rchild) = pnode.as_ref().right {
                    if rchild.as_ptr() == temp.as_ptr() {
                        temp = pnode;
                        temp_parent = pnode.as_ref().parent;
                    }
                    else {
                        break;
                    }
                }
                else {
                    break;
                }
            }
            
            temp_parent
        }
    }

    unsafe fn predecessor(tn: NonNull<Self>) -> Link<T> {
        if let Some(lnode) = tn.as_ref().left {
            return Some(Self::max_helper_nr(lnode));
        }
        else {
            let mut temp = tn;
            let mut temp_parent = tn.as_ref().parent;

            while let Some(pnode) = temp_parent {
                if let Some(lchild) = pnode.as_ref().left {
                    if lchild.as_ptr() == temp.as_ptr() {
                        temp = pnode;
                        temp_parent = pnode.as_ref().parent;
                    }
                    else {
                        break;
                    }
                }
                else {
                    break;
                }
            }
            
            temp_parent
        }
    }

    unsafe fn min_helper_nr(mut tn: NonNull<TreeNode<T>>) -> NonNull<TreeNode<T>> {
        while let Some(left) = tn.as_ref().left {
            tn = left;
        }
        tn
    }

    unsafe fn max_helper_nr(mut tn: NonNull<TreeNode<T>>) -> NonNull<TreeNode<T>> {
        while let Some(right) = tn.as_ref().right {
            tn = right;
        }
        tn
    }
}



impl<T: Ord> BinarySearchTree<T> {

    /// Creates an empty `BinarySearchTree'
    ///
    /// # Examples
    /// ```
    /// use bstree::BinarySearchTree;
    ///
    /// let mut bst = BinarySearchTree::<i32>::new();
    /// assert!(bst.is_empty());
    /// ```
    pub fn new() -> Self {
        Self {
            root: None,
            len: 0,
        }
    }

    /// Insert an element into the tree and returns a reference to the inserted
    /// element. Duplicate elements are **NOT** inserted and `None` is returned
    /// instead.
    ///
    /// # Examples 
    ///
    /// ```
    /// use bstree::BinarySearchTree;
    ///
    /// let mut bst = BinarySearchTree::<i32>::new();
    ///
    /// bst.insert(5);
    /// bst.insert(2);
    /// bst.insert(7);
    /// bst.insert(8);
    ///
    /// assert_eq!(bst.len(), 4);
    /// ```
    ///
    /// ```
    /// use bstree::BinarySearchTree;
    ///
    /// let mut bst = BinarySearchTree::<i32>::new();
    ///
    /// bst.insert(3);
    /// bst.insert(6);
    /// bst.insert(3);
    ///
    /// assert_eq!(bst.len(), 2);
    /// ```
    ///
    pub fn insert(&mut self, elem: T) -> Option<&T>
    {
        unsafe {
            if self.root.is_none() {
                self.root = Some(TreeNode::new_as_ptr(elem, None));
                self.len += 1;
                return Some(&self.root.unwrap().as_ref().elem);
            }
            else {
                return insert_helper(self.root.unwrap(), elem).map(|el| {
                    self.len += 1;
                    el
                });
            }
        }

        unsafe fn insert_helper<'a, T>(mut tn: NonNull<TreeNode<T>>, elem: T) -> Option<&'a T>
            where T: Ord
            {
                match elem.cmp(&tn.as_ref().elem) {
                    Ordering::Less => {
                        if let Some(lnode) = tn.as_ref().left {
                            insert_helper(lnode, elem)
                        }
                        else {
                            let new_node = TreeNode::new_as_ptr(elem, Some(tn));
                            tn.as_mut().left = Some(new_node);
                            Some(&new_node.as_ref().elem)
                        }
                    }
                    Ordering::Equal => None,
                    Ordering::Greater => {
                        if let Some(rnode) = tn.as_ref().right {
                            insert_helper(rnode, elem)
                        }
                        else {
                            let new_node = TreeNode::new_as_ptr(elem, Some(tn));
                            tn.as_mut().right = Some(new_node);
                            Some(&new_node.as_ref().elem)
                        }
                    }
                }
            }
    }

    /// Returns the height of the tree (0 for empty tree).
    /// 
    /// # Examples
    ///
    /// ```
    /// use bstree::BinarySearchTree;
    ///
    /// // Tree representation: 
    /// //          8
    /// //         / \ 
    /// //        3   9
    /// //       / \  
    /// //      1   4
    /// //           \
    /// //            7
    /// let mut bst = BinarySearchTree::new();
    ///
    /// assert_eq!(bst.height(), 0);
    ///
    /// bst.insert(8);
    /// bst.insert(9);
    /// bst.insert(3);
    /// bst.insert(1);
    /// bst.insert(4);
    /// bst.insert(7);
    ///
    /// assert_eq!(bst.height(), 4);
    /// ```
    pub fn height(&self) -> usize {
        unsafe {
            self.root.as_ref().map_or(0, |tn| TreeNode::height(tn.as_ref()))
        }
    }

    fn search(&self, elem: &T) -> Link<T> 
        where T: Ord
        {

            return search_helper_nr(self.root, elem);

            fn search_helper_nr<T: Ord>(mut tn: Link<T>, elem: &T) -> Link<T> {
                while let Some(node) = tn {
                    unsafe {
                        match node.as_ref().elem.cmp(&elem) {
                            Ordering::Less => tn = node.as_ref().right,
                            Ordering::Equal => return tn,
                            Ordering::Greater => tn = node.as_ref().left,
                        }
                    }
                }
                None 
            }
        }

    /// Obtains a reference to the element in the tree, or `None`
    /// if it does not exist. 
    ///
    /// # Examples 
    /// ```
    /// use bstree::BinarySearchTree;
    ///
    /// let mut bst = BinarySearchTree::new();
    ///
    /// bst.insert(15);
    /// bst.insert(20);
    /// bst.insert(25);
    ///
    /// assert_eq!(bst.get(&20), Some(&20));
    /// assert_eq!(bst.get(&10), None);
    ///
    pub fn get(&self, elem: &T) -> Option<&T> {
        self.search(elem).map(|node| unsafe {&node.as_ref().elem})
    }

    /// Returns `true` if the tree contains the given element
    ///
    /// # Examples
    /// ```
    /// use bstree::BinarySearchTree;
    ///
    /// let mut bst = BinarySearchTree::new();
    ///
    /// bst.insert(4);
    /// bst.insert(9);
    /// bst.insert(1);
    /// bst.insert(2);
    ///
    /// assert!(bst.contains(&2));
    /// assert!(!bst.contains(&3));
    /// ```
    pub fn contains(&self, elem: &T) -> bool {
        self.get(elem).is_some()
    }

    /// Replaces the node that has element `old_elem` with `new_elem` and
    /// returns the previous value. Duplicate elements are **NOT** inserted and
    /// `None` is returned instead.  
    ///
    /// This method ensures that the core properties of the binary search tree
    /// structure are complied. The examples below demonstrate this.
    ///
    /// # Examples
    ///
    /// An example where the node's position need not change after mutating: 
    /// ```
    /// use bstree::BinarySearchTree;
    /// // Before Replace:      After Replace: 
    /// //       7                   7
    /// //      / \                 / \
    /// //     2   10              2   13
    /// //        /  \                /  \
    /// //       8   14              8   14
    /// //        \                   \
    /// //         9                   9
    ///
    /// let mut bst = BinarySearchTree::from(vec![7,2,10,8,9,14]);
    ///
    /// assert_eq!(bst.replace(&10, 13), Some(10));
    ///
    /// assert_eq!(bst.iter().copied().collect::<Vec<_>>(), vec![2,7,8,9,13,14]);
    ///
    /// ```
    /// An example where the node's position must change after mutating:
    /// ```
    /// use bstree::BinarySearchTree;
    ///
    /// // Before Replace:      After Replace: 
    /// //       8                   8
    /// //      / \                 / \
    /// //     5   9               6   9
    /// //    / \                 / \   \
    /// //   4   6               4   7   10
    /// //        \
    /// //         7
    /// // 
    ///
    /// let mut bst = BinarySearchTree::from(vec![8,5,9,4,6,7]);
    ///
    /// assert_eq!(bst.replace(&5, 10), Some(5));
    ///
    /// assert_eq!(bst.iter().copied().collect::<Vec<_>>(), vec![4,6,7,8,9,10]);
    /// ```
    ///
    pub fn replace(&mut self, old_elem: &T, new_elem: T) -> Option<T> {

        if new_elem.eq(old_elem) {
            return None;
        }

        self.search(old_elem).map(|mut node| unsafe {

            let suc = self.successor(old_elem);
            let pre = self.predecessor(old_elem);


            assert!(suc.is_some());
            assert!(pre.is_some());

            let mut safe_to_mutate = true;

            if let Some(prev) = pre {
                if new_elem < *prev {
                    safe_to_mutate = false;
                }
            }
            if let Some(next) = suc {
                if new_elem > *next {
                    safe_to_mutate = false;
                }
            }

            if safe_to_mutate {
                ptr::replace(&mut node.as_mut().elem, new_elem)
            }
            else {
                self.remove(old_elem);
                let old = ptr::read(&mut node.as_mut().elem);
                self.insert(new_elem);
                old
            }
        })
    }

    /// Returns an immutable reference to the minimum element in the tree, or
    /// `None` if the tree is empty.
    ///
    /// # Examples 
    /// ```
    /// use bstree::BinarySearchTree;
    ///
    /// let mut bst = BinarySearchTree::from(vec![7,5,6,3,1,2]);
    /// assert_eq!(bst.min_elem(), Some(&1));
    ///
    /// bst.clear();
    /// assert_eq!(bst.min_elem(), None);
    /// ```
    ///
    pub fn min_elem(&self) -> Option<&T> {
        self.root.map(|node| unsafe {
            &TreeNode::min_helper_nr(node).as_ref().elem
        })
    }

    /// Returns an immutable reference to the maximum element in the tree, or
    /// `None` if the tree is empty.
    ///
    /// # Examples
    /// ```
    /// use bstree::BinarySearchTree;
    ///
    /// let mut bst = BinarySearchTree::from(vec![7,5,6,3,1,2]);
    /// assert_eq!(bst.max_elem(), Some(&7));
    ///
    /// bst.clear();
    /// assert_eq!(bst.max_elem(), None);
    /// ```
    ///
    pub fn max_elem(&self) -> Option<&T> {
        self.root.map(|node| unsafe {
            &TreeNode::max_helper_nr(node).as_ref().elem
        })
    }


    /// Returns the number of elements in the tree.
    ///
    /// # Examples 
    /// ```
    /// use bstree::BinarySearchTree;
    ///
    /// let mut bst = BinarySearchTree::new();
    ///
    /// assert_eq!(bst.len(), 0);
    ///
    /// bst.insert(22);
    /// bst.insert(47);
    ///
    /// assert_eq!(bst.len(), 2);
    /// ```
    pub fn len(&self) -> usize {
        self.len 
    }

    /// Returns a reference to the predecessor of the given element, or returns
    /// `None` in the following scenarios:  
    ///
    /// - The element does not exist in the tree
    /// - The element is the minimum element in the tree, thus having no predecessor.
    ///
    /// # Examples
    /// ```
    /// use bstree::BinarySearchTree;
    ///
    /// let mut bst = BinarySearchTree::new();
    ///
    /// bst.insert(4);
    /// bst.insert(9);
    /// bst.insert(14);
    /// bst.insert(12);
    ///
    /// assert_eq!(bst.predecessor(&12), Some(&9));
    ///
    /// // The element does not exist
    /// assert_eq!(bst.predecessor(&20), None);
    ///
    /// // The element has no predecessor
    /// assert_eq!(bst.predecessor(&4), None);
    /// ```
    ///
    pub fn predecessor(&self, elem: &T) -> Option<&T> {
        self.search(elem).and_then(|node| unsafe {TreeNode::predecessor(node)
            .map(|node| &node.as_ref().elem)})
    }

    /// Returns a reference to the successor of the given element, or returns
    /// `None` in the following scenarios:  
    ///
    /// - The element does not exist in the tree
    /// - The element is the maximum element in the tree, thus having no successor.
    ///
    /// # Examples
    /// ```
    /// use bstree::BinarySearchTree;
    ///
    /// let mut bst = BinarySearchTree::new();
    ///
    /// bst.insert(4);
    /// bst.insert(9);
    /// bst.insert(14);
    /// bst.insert(12);
    ///
    /// assert_eq!(bst.successor(&9), Some(&12));
    ///
    /// // The element does not exist
    /// assert_eq!(bst.successor(&20), None);
    ///
    /// // The element has no successor
    /// assert_eq!(bst.successor(&14), None);
    /// ```
    ///
    pub fn successor(&self, elem: &T) -> Option<&T> {
        self.search(elem).and_then(|node| unsafe {TreeNode::successor(node)
            .map(|node| &node.as_ref().elem)})
    }

    unsafe fn transplant(&mut self, tns: NonNull<TreeNode<T>>, tnd: Link<T>) {

        if let Some(mut parent) = tns.as_ref().parent {

            let is_left_child = parent.as_ref().left
                .map(|ln| ln.as_ptr() == tns.as_ptr())
                .unwrap_or(false);

            if is_left_child {
                parent.as_mut().left = tnd;
            } else {
                parent.as_mut().right = tnd;
            }
        }
        else {
            self.root = tnd;
        }

        if let Some(mut tn2u) = tnd {
            tn2u.as_mut().parent = tns.as_ref().parent;
        }

    }
    

    /// Removes the given element from the tree, returning the deleted element,
    /// or `None` if it does not exist in the tree.
    ///
    /// # Examples
    /// ```
    /// use bstree::BinarySearchTree;
    ///
    /// let mut bst = BinarySearchTree::new();
    ///
    /// bst.insert(3);
    /// bst.insert(1);
    /// bst.insert(5);
    /// bst.insert(4);
    /// bst.insert(2);
    ///
    /// assert_eq!(bst.remove(&4), Some(4));
    /// assert_eq!(bst.remove(&3), Some(3));
    ///
    /// assert_eq!(bst.iter().copied().collect::<Vec<_>>(), vec![1,2,5]);
    ///
    /// assert_eq!(bst.remove(&6), None);
    /// ```
    ///
    pub fn remove(&mut self, elem: &T) -> Option<T>
        where T: Ord 
        {
            self.search(elem).map(|mut node| unsafe {
                match (node.as_ref().left, node.as_ref().right) {
                    (None, None) => {
                        self.transplant(node, None);
                        node.as_mut().parent = None;
                        let elem = ptr::read(&mut node.as_mut().elem);
                        TreeNode::drop_tree(Some(node));
                        elem
                    },
                    (None, Some(rchild)) => {
                        self.transplant(node, Some(rchild));
                        ptr::read(&mut node.as_mut().elem)
                    },
                    (Some(lchild), None) => {
                        self.transplant(node, Some(lchild));
                        ptr::read(&mut node.as_mut().elem)
                    },
                    (Some(_), Some(_)) => {
                        let mut suc = TreeNode::successor(node).expect("A node which has children
                                                                   can not be max node, therefore
                                                             it should have a successor");

                        if suc.as_ptr() != node.as_ref().right.unwrap().as_ptr() {
                            self.transplant(suc, suc.as_ref().right);
                            suc.as_mut().right = node.as_ref().right;
                            suc.as_ref().right.map(|mut rn| rn.as_mut().parent = Some(suc));
                        }

                        self.transplant(node, Some(suc));
                        suc.as_mut().left = node.as_mut().left;
                        suc.as_ref().left.map(|mut ln| ln.as_mut().parent = Some(suc));

                        ptr::read(&mut node.as_mut().elem)
                    },
                }
            })
        }

    /// Removes the minimum element in the tree and returns it, or returns `None`
    /// if the tree is empty.
    ///
    /// # Examples
    /// ```
    /// use bstree::BinarySearchTree;
    ///
    /// let mut bst = BinarySearchTree::from(vec![8,13,2,19,6,20]);
    ///
    /// assert_eq!(bst.remove_min(), Some(2));
    /// assert_eq!(bst.remove_min(), Some(6));
    ///
    /// bst.clear();
    /// assert_eq!(bst.remove_min(), None);
    /// ```
    ///
    pub fn remove_min(&mut self) -> Option<T> {
        self.root.map(|mut min_node| unsafe {

            while let Some(lnode) = min_node.as_ref().left {
                min_node = lnode;
            }

            let elem = ptr::read(&mut min_node.as_mut().elem);

            if let Some(rnode) = min_node.as_ref().right {
                self.transplant(min_node, Some(rnode));
            }
            else {
                self.transplant(min_node, None);
                min_node.as_mut().parent = None;
                TreeNode::drop_tree(Some(min_node));
            }
            
            self.len -= 1;
            elem
        })
    }

    /// Removes the maximum element in the tree and returns it, or returns `None`
    /// if the tree is empty.
    ///
    /// # Examples
    /// ```
    /// use bstree::BinarySearchTree;
    ///
    /// let mut bst = BinarySearchTree::from(vec![8,13,2,19,6,20]);
    ///
    /// assert_eq!(bst.remove_max(), Some(20));
    /// assert_eq!(bst.remove_max(), Some(19));
    ///
    /// bst.clear();
    /// assert_eq!(bst.remove_max(), None);
    /// ```
    ///
    pub fn remove_max(&mut self) -> Option<T> {
        self.root.map(|mut max_node| unsafe {

            while let Some(rnode) = max_node.as_ref().right {
                max_node = rnode;
            }
            let elem = ptr::read(&mut max_node.as_mut().elem);

            if let Some(lnode) = max_node.as_ref().left {
                self.transplant(max_node, Some(lnode));
            }
            else {
                self.transplant(max_node, None);
                max_node.as_mut().parent = None;
                TreeNode::drop_tree(Some(max_node));
            }

            self.len -= 1;
            elem
        })
    }

    /// Returns true if the tree is empty
    ///
    /// # Examples 
    /// ```
    /// use bstree::BinarySearchTree;
    ///
    /// let mut bst = BinarySearchTree::new();
    ///
    /// assert!(bst.is_empty());
    /// bst.insert(1);
    /// assert!(!bst.is_empty());
    /// ```
    ///
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Appends another `BinarySearchTree`'s elements to the current one, 
    /// leaving the other one empty. Duplicate elements are **NOT** inserted.
    ///
    /// # Examples 
    /// ```
    /// use bstree::BinarySearchTree;
    ///
    /// let mut bst1 = BinarySearchTree::from(vec![5,9,11,18]);
    /// let mut bst2 = BinarySearchTree::from(vec![3,5,11,24]);
    ///
    /// bst1.append(&mut bst2);
    ///
    /// assert_eq!(bst1.iter().copied().collect::<Vec<_>>(), vec![3,5,9,11,18,24]);
    /// assert!(bst2.is_empty());
    /// ```
    ///
    pub fn append(&mut self, other: &mut BinarySearchTree<T>) {
        for elem in other.into_iter() {
            unsafe {
                self.insert(ptr::read(elem));
            }
        }
        other.clear();
    }


    /// Clears the tree, removing all elements.
    ///
    /// # Examples
    /// ```
    /// use bstree::BinarySearchTree;
    ///
    /// let mut bst = BinarySearchTree::from(vec![1,2,3]);
    /// 
    /// bst.clear();
    ///
    /// assert!(bst.is_empty());
    /// assert_eq!(bst.len(), 0);
    /// ```
    ///
    pub fn clear(&mut self) {
        unsafe {
            TreeNode::drop_tree(self.root);
        }
        self.root = None;
        self.len = 0;
    }

    /// Extracts a [Vec] containing the tree elements, with a pre order traverse.
    ///
    /// # Examples
    /// ```
    /// use bstree::BinarySearchTree;
    ///
    /// let mut bst = BinarySearchTree::from(vec![4,2,1,3,6,7,5]);
    ///
    /// assert_eq!(bst.as_pre_order_vec(), vec![&4,&2,&1,&3,&6,&5,&7]);
    /// ```
    ///
    pub fn as_pre_order_vec(&self) -> Vec<&T> {

        let mut vec = Vec::new();
        pre_order_helper(self.root, &mut vec);
        return vec;

        fn pre_order_helper<T>(tn: Link<T>, vec: &mut Vec<&T>) {
            tn.map(|node| unsafe {
                vec.push(&node.as_ref().elem);
                pre_order_helper(node.as_ref().left, vec);
                pre_order_helper(node.as_ref().right, vec)
            });
        }
    }

    /// Extracts a [Vec] containing the tree elements, with an in order traverse.
    ///
    /// # Examples
    /// ```
    /// use bstree::BinarySearchTree;
    ///
    /// let mut bst = BinarySearchTree::from(vec![4,2,1,3,6,7,5]);
    ///
    /// assert_eq!(bst.as_in_order_vec(), vec![&1,&2,&3,&4,&5,&6,&7]);
    /// ```
    ///
    pub fn as_in_order_vec(&self) -> Vec<&T> {

        let mut vec = Vec::new();
        in_order_helper(self.root, &mut vec);
        return vec;

        fn in_order_helper<T>(tn: Link<T>, vec: &mut Vec<&T>) {
            tn.map(|node| unsafe {
                in_order_helper(node.as_ref().left, vec);
                vec.push(&node.as_ref().elem);
                in_order_helper(node.as_ref().right, vec);
            });
        }
    }

    /// Extracts a [Vec] containing the tree elements, with an in order traverse.
    ///
    /// # Examples
    /// ```
    /// use bstree::BinarySearchTree;
    ///
    /// let mut bst = BinarySearchTree::from(vec![4,2,1,3,6,7,5]);
    ///
    /// assert_eq!(bst.as_post_order_vec(), vec![&1,&3,&2,&5,&7,&6,&4]);
    /// ```
    ///
    pub fn as_post_order_vec(&self) -> Vec<&T> {

        let mut vec = Vec::new();
        post_order_helper(self.root, &mut vec);
        return vec;

        fn post_order_helper<T>(tn: Link<T>, vec: &mut Vec<&T>) {
            tn.map(|node| unsafe {
                post_order_helper(node.as_ref().left, vec);
                post_order_helper(node.as_ref().right, vec);
                vec.push(&node.as_ref().elem);
            });
        }
    }
    

    /// Returns an [IntoIter] over the tree's elements, using an in order traverse.
    ///
    /// # Examples
    /// ```
    /// use bstree::BinarySearchTree;
    ///
    /// let bst = BinarySearchTree::from(vec![7,2,4,9,1,8]);
    ///
    /// assert_eq!(bst.into_iter().collect::<Vec<_>>(), vec![1,2,4,7,8,9]);
    /// ```
    ///
    pub fn into_iter(self) -> IntoIter<T> {
        IntoIter(self)
    }

    /// Returns an [Iter] over the tree's elements, using an in order traverse.
    ///
    /// # Examples
    /// ```
    /// use bstree::BinarySearchTree;
    ///
    /// let bst = BinarySearchTree::from(vec![7,2,4,9,1,8]);
    ///
    /// assert_eq!(bst.iter().collect::<Vec<_>>(), vec![&1,&2,&4,&7,&8,&9]);
    /// ```
    ///
    pub fn iter(&self) -> Iter<T> {
        Iter { 
            min_node: self.root.map(|node| unsafe {TreeNode::min_helper_nr(node)}), 
            max_node: self.root.map(|node| unsafe {TreeNode::max_helper_nr(node)}), 
            len: self.len, 
            _phantom: PhantomData 
        }
    }


    /// Returns an [IterMut] over the tree's elements, using an in order traverse.
    ///
    /// # Examples
    /// ```
    /// use bstree::BinarySearchTree;
    ///
    /// let mut bst = BinarySearchTree::from(vec![7,2,4,9,1,8]);
    ///
    /// assert_eq!(bst.iter_mut().collect::<Vec<_>>(), vec![&1,&2,&4,&7,&8,&9]);
    /// ```
    ///
    pub fn iter_mut(&mut self) -> IterMut<T> {
        IterMut { 
            min_node: self.root.map(|node| unsafe {TreeNode::min_helper_nr(node)}), 
            max_node: self.root.map(|node| unsafe {TreeNode::max_helper_nr(node)}), 
            len: self.len, 
            _phantom: PhantomData 
        }
    }
}

impl<T: Ord> Drop for BinarySearchTree<T> {
    fn drop(&mut self) {
        unsafe {
            TreeNode::drop_tree(self.root);
        }
    }
}

/// An iterator that moves out of a binary search tree.
///
/// This `struct` is created by the `into_iter` method on [BinarySearchTree].
/// The implementation uses an in inorder traverse. If this is not desired, use
/// the `as_pre_order_vec`, `as_post_order_vec` methods on [BinarySearchTree].
pub struct IntoIter<T: Ord>(BinarySearchTree<T>);

impl<T: Ord> Iterator for IntoIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.remove_min()
    }
}

impl<T: Ord> DoubleEndedIterator for IntoIter<T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.remove_max()
    }
}

impl<T: Ord> ExactSizeIterator for IntoIter<T> {
    fn len(&self) -> usize {
        self.0.len()
    }
}

/// An iterator that iterates over the immutable references of a binary search tree elements.
///
/// This `struct` is created by the `iter` method on [BinarySearchTree].
///
/// The implementation uses an in inorder traverse. If this is not desired, use
/// the `as_pre_order_vec`, `as_post_order_vec` methods on [BinarySearchTree].
pub struct Iter<'a, T: Ord> {
    min_node: Link<T>,
    max_node: Link<T>,
    len: usize,
    _phantom: PhantomData<&'a T>,
}

impl<'a, T: Ord> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.len > 0 {
            self.min_node.map(|node| unsafe {
                self.len -= 1;
                self.min_node = TreeNode::successor(node);
                &node.as_ref().elem
            })
        }
        else {
            None
        }
    }
}

impl<'a, T:Ord> DoubleEndedIterator for Iter<'a, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.len > 0 {
            self.max_node.map(|node| unsafe {
                self.len -= 1;
                self.max_node = TreeNode::predecessor(node);
                &node.as_ref().elem
            })
        }
        else {
            None
        }
    }
}

impl<'a, T: Ord> ExactSizeIterator for Iter<'a, T> {
    fn len(&self) -> usize {
        self.len
    }
}

/// An iterator that iterates over the mutable references of a binary search tree elements.
///
/// This `struct` is created by the `iter_mut` method on [BinarySearchTree].
///
/// The implementation uses an in inorder traverse. If this is not desired, use
/// the `as_pre_order_vec`, `as_post_order_vec` methods on [BinarySearchTree].
///
/// # **CAUTION!**
///
/// It is strongly advised to avoid using this struct, as mutating the elements
/// of the tree can invalidate the core properties of a binary search tree. If 
/// you need mutation, use the `replace` method on [BinarySearchTree], which
/// ensures proper mutation of the elements.
///
/// Again, only use `iter_mut` when you exactly know what you're doing (e.g,
/// adding a constant value K to all elements of the tree does not invalidate the
/// tree's structure, while a mod K operation to all elements can).
///
pub struct IterMut<'a, T> {
    min_node: Link<T>,
    max_node: Link<T>,
    len: usize,
    _phantom: PhantomData<&'a mut T>
}

impl<'a, T> Iterator for IterMut<'a, T> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.len > 0 {
            self.min_node.map(|mut node| unsafe {
                self.len -= 1;
                self.min_node = TreeNode::successor(node);
                &mut node.as_mut().elem
            })
        }
        else {
            None
        }
    }
}

impl<'a, T> DoubleEndedIterator for IterMut<'a, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.len > 0 {
            self.max_node.map(|mut node| unsafe {
                self.len -= 1;
                self.max_node = TreeNode::predecessor(node);
                &mut node.as_mut().elem
            })
        }
        else {
            None
        }
    }
}

impl<'a, T> ExactSizeIterator for IterMut<'a, T> {
    fn len(&self) -> usize {
        self.len
    }
}


impl<T: Ord> IntoIterator for BinarySearchTree<T> {
    type Item = T;

    type IntoIter = IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        self.into_iter()
    }
}

impl<'a, T: Ord> IntoIterator for &'a BinarySearchTree<T> {
    type Item = &'a T;

    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
} 

impl<'a, T: Ord> IntoIterator for &'a mut BinarySearchTree<T> {
    type Item = &'a mut T;

    type IntoIter = IterMut<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

impl<T: Ord> Default for BinarySearchTree<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Ord + Clone> Clone for BinarySearchTree<T> {
    fn clone(&self) -> Self {
        let mut tree = BinarySearchTree::new();
        let iter = self.iter().cloned().collect::<Vec<_>>();
        for elem in iter {
            tree.insert(elem);
        }
        tree
    }
}

impl<T: Ord> Extend<T> for BinarySearchTree<T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        let mut tree = BinarySearchTree::new();
        for elem in iter {
            tree.insert(elem);
        }
    }
}

impl<'a, T: Ord + Clone> Extend<&'a T> for BinarySearchTree<T> {
    fn extend<I: IntoIterator<Item = &'a T>>(&mut self, iter: I) {
        let mut tree = BinarySearchTree::new();
        for elem in iter {
            tree.insert(elem.clone());
        }
    }
}


impl<T: Ord> FromIterator<T> for BinarySearchTree<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut tree = BinarySearchTree::new();
        for elem in iter {
            tree.insert(elem);
        }
        tree
    }
}

impl<'a, T: Ord + Clone> FromIterator<&'a T> for BinarySearchTree<T> {
    fn from_iter<I: IntoIterator<Item = &'a T>>(iter: I) -> Self {
        let mut tree: BinarySearchTree<T> = BinarySearchTree::new();
        for elem in iter {
            tree.insert(elem.clone());
        }
        tree
    }
}

impl<'a, T: Ord + Clone> FromIterator<&'a mut T> for BinarySearchTree<T> {
    fn from_iter<I: IntoIterator<Item = &'a mut T>>(iter: I) -> Self {
        let mut tree: BinarySearchTree<T> = BinarySearchTree::new();
        for elem in iter {
            tree.insert(elem.clone());
        }
        tree
    }
}

impl<T: Ord> PartialEq for BinarySearchTree<T> {
    fn eq(&self, other: &Self) -> bool {
        self.len == other.len && self.iter().eq(other)
    }
}

impl<T: Ord> Eq for BinarySearchTree<T> {}

impl<T: Ord> PartialOrd for BinarySearchTree<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.iter().partial_cmp(other)
    }
}

impl<T: Ord> Ord for BinarySearchTree<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.iter().cmp(other)
    }
}

impl<T: Ord + Hash> Hash for BinarySearchTree<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.len().hash(state);
        for elem in self {
            elem.hash(state);
        }
    }
}


impl<T: Ord + Clone> From<&[T]> for BinarySearchTree<T> {
    fn from(value: &[T]) -> Self {
        BinarySearchTree::from_iter(value)
    }
}


impl<T: Ord + Clone> From<&mut [T]> for BinarySearchTree<T> {
    fn from(value: &mut [T]) -> Self {
        BinarySearchTree::from_iter(value)
    }
}

impl<T: Ord, const N: usize> From<[T; N]> for BinarySearchTree<T> {
    fn from(value: [T; N]) -> Self {
        BinarySearchTree::from_iter(value)
    }
}

impl<T: Ord + Clone, const N: usize> From<&[T; N]> for BinarySearchTree<T> {
    fn from(value: &[T; N]) -> Self {
        BinarySearchTree::from_iter(value)
    }
}

impl<T: Ord + Clone, const N: usize> From<&mut [T; N]> for BinarySearchTree<T> {
    fn from(value: &mut [T; N]) -> Self {
        BinarySearchTree::from_iter(value)
    }
}


impl<T: Ord> From<Vec<T>> for BinarySearchTree<T> {
    fn from(value: Vec<T>) -> Self {
        BinarySearchTree::from_iter(value)
    }
}

impl<'a, T: Ord + Clone> From<&'a Vec<T>> for BinarySearchTree<T> {
    fn from(value: &'a Vec<T>) -> Self {
        BinarySearchTree::from_iter(value)
    }
}

unsafe impl<T: Ord + Send> Send for BinarySearchTree<T> {}
unsafe impl<T: Ord + Sync> Sync for BinarySearchTree<T> {}


unsafe impl<'a, T: Ord + Send> Send for Iter<'a, T> {}
unsafe impl<'a, T: Ord + Sync> Sync for Iter<'a, T> {}

unsafe impl<'a, T: Ord + Send> Send for IterMut<'a, T> {}
unsafe impl<'a, T: Ord + Sync> Sync for IterMut<'a, T> {}

#[allow(dead_code)]
fn assert_status() {
    fn accepts_send<T: Send>() {}
    fn accepts_sync<T: Sync>() {}

    accepts_send::<BinarySearchTree<usize>>();
    accepts_sync::<BinarySearchTree<usize>>();

    accepts_send::<IntoIter<usize>>();
    accepts_sync::<IntoIter<usize>>();

    accepts_send::<Iter<usize>>();
    accepts_sync::<Iter<usize>>();

    accepts_send::<IterMut<usize>>();
    accepts_sync::<IterMut<usize>>();

    fn covariant<'a, T: Ord>(tree: BinarySearchTree<&'static T>) -> BinarySearchTree<&'a T> {
        tree
    }

    fn iter_cov<'a, 'b, T: Ord>(iter: Iter<'a, &'static T>) -> Iter<'a, &'b T> {
        iter
    }
}

#[cfg(test)]
mod tests {

    use super::BinarySearchTree;

    #[test]
    fn test_insert_remove_1() {

        let mut tree = BinarySearchTree::new();

        tree.insert(3);
        tree.insert(2);
        tree.insert(4);
        tree.insert(5);
        tree.insert(1);

        assert_eq!(tree.remove_min(), Some(1));
        assert_eq!(tree.remove_min(), Some(2));

        assert_eq!(tree.len(), 3);

        assert_eq!(tree.remove_min(), Some(3));
        assert_eq!(tree.remove_min(), Some(4));
        assert_eq!(tree.remove_min(), Some(5));
        assert_eq!(tree.remove_min(), None);

        assert_eq!(tree.len(), 0);

        tree.insert(7);
        tree.insert(5);
        tree.insert(9);
        tree.insert(6);
        tree.insert(8);
        tree.insert(10);
        assert_eq!(tree.len(), 6);

        assert_eq!(tree.remove_min(), Some(5));
        assert_eq!(tree.remove_min(), Some(6));
        assert_eq!(tree.remove_min(), Some(7));
        assert_eq!(tree.remove_min(), Some(8));
        assert_eq!(tree.remove_min(), Some(9));
        assert_eq!(tree.remove_min(), Some(10));
        assert_eq!(tree.remove_min(), None);
        assert_eq!(tree.len(), 0);


        tree.insert(3);
        tree.insert(2);
        tree.insert(4);
        tree.insert(5);
        tree.insert(1);


        assert_eq!(tree.remove_max(), Some(5));
        assert_eq!(tree.remove_max(), Some(4));
        assert_eq!(tree.remove_max(), Some(3));
        assert_eq!(tree.remove_max(), Some(2));
        assert_eq!(tree.remove_max(), Some(1));
        assert_eq!(tree.remove_max(), None);



        tree.insert(7);
        tree.insert(5);
        tree.insert(9);
        tree.insert(6);
        tree.insert(8);
        tree.insert(10);
        
        assert_eq!(tree.remove_max(), Some(10));
        assert_eq!(tree.remove_max(), Some(9));
        assert_eq!(tree.remove_max(), Some(8));
        assert_eq!(tree.remove_max(), Some(7));
        assert_eq!(tree.remove_max(), Some(6));
        assert_eq!(tree.remove_max(), Some(5));
        assert_eq!(tree.remove_max(), None);

    }

    fn generate_iter_test() -> BinarySearchTree<i32> {
        BinarySearchTree::from(vec![50,30,70,20,40,80,60])
    }


    #[test]
    fn test_iter() {

        let mut tree = generate_iter_test();

        assert_eq!(tree.iter().copied().collect::<Vec<_>>(), vec![20,30,40,50,60,70,80]);
        tree.remove_min();
        assert_eq!(tree.iter().copied().collect::<Vec<_>>(), vec![30,40,50,60,70,80]);
        tree.remove_min();
        assert_eq!(tree.iter().copied().collect::<Vec<_>>(), vec![40,50,60,70,80]);
        tree.remove_max();
        assert_eq!(tree.iter().copied().collect::<Vec<_>>(), vec![40,50,60,70]);
        tree.remove_max();
        assert_eq!(tree.iter().copied().collect::<Vec<_>>(), vec![40,50,60]);
        tree.remove_max();
        assert_eq!(tree.iter().copied().collect::<Vec<_>>(), vec![40,50]);
        tree.remove_max();
        assert_eq!(tree.iter().copied().collect::<Vec<_>>(), vec![40]);
        tree.remove_min();
        assert_eq!(tree.iter().copied().collect::<Vec<_>>(), vec![]);

    }

    #[test]
    fn test_into_iter_double_ex_end() {
        let tree = generate_iter_test();

        let mut iter = tree.into_iter();

        assert_eq!(iter.len(), 7);
        assert_eq!(iter.next(), Some(20));
        assert_eq!(iter.next_back(), Some(80));
        assert_eq!(iter.next_back(), Some(70));
        assert_eq!(iter.len(), 4);
        assert_eq!(iter.next(), Some(30));
        assert_eq!(iter.next_back(), Some(60));
        assert_eq!(iter.next_back(), Some(50));
        assert_eq!(iter.next(), Some(40));
        assert_eq!(iter.len(), 0);
        assert_eq!(iter.next(), None);
    }


    #[test]
    fn test_iter_double_ex_end() {

        let tree = generate_iter_test();

        let mut iter = tree.iter().copied();

        assert_eq!(iter.len(), 7);
        assert_eq!(iter.next(), Some(20));
        assert_eq!(iter.next_back(), Some(80));
        assert_eq!(iter.next_back(), Some(70));
        assert_eq!(iter.len(), 4);
        assert_eq!(iter.next(), Some(30));
        assert_eq!(iter.next_back(), Some(60));
        assert_eq!(iter.next_back(), Some(50));
        assert_eq!(iter.next(), Some(40));
        assert_eq!(iter.len(), 0);
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn test_iter_mut_double_ex_end() {

        let mut tree = generate_iter_test();

        let mut iter = tree.iter_mut();

        *iter.next().unwrap() = 1;
        *iter.next_back().unwrap() = 7;
        *iter.next().unwrap() = 2;
        *iter.next_back().unwrap() = 6;
        *iter.next().unwrap() = 3;
        *iter.next_back().unwrap() = 5;
        *iter.next().unwrap() = 4;

        assert_eq!(iter.next(), None);

        let iter = tree.iter();

        assert_eq!(iter.copied().collect::<Vec<_>>(), vec![1,2,3,4,5,6,7]);
    }


    #[test]
    fn test_insert_remove_2() {

        let mut tree = BinarySearchTree::new();

        tree.insert(50);
        tree.insert(30);
        tree.insert(70);
        tree.insert(20);
        tree.insert(40);
        tree.insert(80);
        tree.insert(60);

        tree.remove(&&20);
        assert_eq!(tree.iter().copied().collect::<Vec<_>>(), vec![30,40,50,60,70,80]);
        tree.remove(&&30);
        assert_eq!(tree.iter().copied().collect::<Vec<_>>(), vec![40,50,60,70,80]);
        tree.remove(&&50);
        assert_eq!(tree.iter().copied().collect::<Vec<_>>(), vec![40,60,70,80]);

        let mut tree = BinarySearchTree::new();

        tree.insert(14);
        tree.insert(11);
        tree.insert(19);
        tree.insert(10);
        tree.insert(13);
        tree.insert(16);
        tree.insert(21);
        tree.insert(20);
        tree.insert(12);
        tree.insert(7);
        tree.insert(6);
        tree.insert(9);
        tree.insert(8);

        tree.remove(&11);
        assert_eq!(tree.iter().copied().collect::<Vec<_>>(), vec![6,7,8,9,10,12,13,14,16,19,20,21]);
        tree.remove(&7);
        tree.remove(&20);
        tree.remove(&14);
        assert_eq!(tree.iter().copied().collect::<Vec<_>>(), vec![6,8,9,10,12,13,16,19,21]);
        tree.remove(&12);
        tree.remove(&9);
        tree.remove(&8);
        tree.remove(&10);
        tree.remove(&6);
        assert_eq!(tree.iter().copied().collect::<Vec<_>>(), vec![13,16,19,21]);
        tree.remove(&16);
        assert_eq!(tree.iter().copied().collect::<Vec<_>>(), vec![13,19,21]);



        tree.insert(20);
        tree.insert(22);

        tree.remove(&19);
        assert_eq!(tree.iter().copied().collect::<Vec<_>>(), vec![13,20,21,22]);
    }

    #[test]
    fn test_search_elem() {
        
        let mut tree = generate_iter_test();

        assert!(tree.get(&30).is_some());
        assert!(tree.get(&80).is_some());
        assert!(tree.get(&75).is_none());

        assert!(tree.get(&60).is_some());

        tree.replace(&60, 65).unwrap();

        assert!(tree.get(&60).is_none());
        assert!(tree.get(&65).is_some());

    }


    #[test]
    fn test_eq_ord() {

        let mut tree1 = BinarySearchTree::new();
        let mut tree2 = BinarySearchTree::new();

        assert!(tree1 == tree2);
        tree1.insert(1);
        assert!(tree1 != tree2);
        tree2.insert(1);
        assert!(tree1 == tree2);

        tree1 = BinarySearchTree::from(vec![1,2,3]);
        tree2 = BinarySearchTree::from(vec![1,2,3,4]);

        assert!(tree1 < tree2);

        tree2.remove_max();

        assert!(tree1 == tree2);
    }

    #[test]
    fn test_traverse_methods() {

        let tree = generate_iter_test();

        assert_eq!(tree.as_pre_order_vec(), vec![&50,&30,&20,&40,&70,&60,&80]);
        assert_eq!(tree.as_in_order_vec(), vec![&20,&30,&40,&50,&60,&70,&80]);
        assert_eq!(tree.as_post_order_vec(), vec![&20,&40,&30,&60,&80,&70,&50]);
    }
}
