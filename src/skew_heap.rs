#![warn(unsafe_op_in_unsafe_fn)]

use std::{cell::Cell, ops::Deref, ptr::null, rc::Rc};

#[derive(Debug)]
pub struct Hook<Outer> {
    left: Cell<*const Outer>,
    right: Cell<*const Outer>,
    parent: Cell<*const Outer>,
}

impl<Outer> Default for Hook<Outer> {
    fn default() -> Self {
        Self {
            left: Cell::new(null()),
            right: Cell::new(null()),
            parent: Cell::new(null()),
        }
    }
}

pub trait Adapter {
    type Outer;
    type Key: Ord;
    fn hook(outer: &Self::Outer) -> &Hook<Self::Outer>;
    fn key(outer: &Self::Outer) -> &Self::Key;
}

// Make sure that key(p1) <= key(p2)
// p1 and p2 must not be null.
unsafe fn ensure_ordering<A: Adapter>(p1: &mut *const A::Outer, p2: &mut *const A::Outer) {
    let key1 = A::key(unsafe { &**p1 });
    let key2 = A::key(unsafe { &**p2 });
    if key1 > key2 {
        std::mem::swap(p1, p2);
    }
}

// Melds the given two heaps and returns the root of the merged heap.
// O(log n) amortized
pub unsafe fn meld<A: Adapter>(
    mut h1: *const A::Outer,
    mut h2: *const A::Outer,
) -> *const A::Outer {
    if h1.is_null() {
        return h2;
    }
    if h2.is_null() {
        return h1;
    }

    unsafe { ensure_ordering::<A>(&mut h1, &mut h2) };

    let new_root = h1;

    // skew root node
    let root_hook = A::hook(unsafe { &*new_root });
    root_hook.left.swap(&root_hook.right);

    // setup loop variables
    let mut parent = h1;
    h1 = root_hook.left.get();

    while !h1.is_null() {
        unsafe { ensure_ordering::<A>(&mut h1, &mut h2) };

        let h1_hook = A::hook(unsafe { &*h1 });
        let parent_hook = A::hook(unsafe { &*parent });

        // connect `h1` as the left child of `parent`.
        parent_hook.left.set(h1);
        h1_hook.parent.set(parent);

        // skew `h1`
        h1_hook.left.swap(&h1_hook.right);

        // update loop variables
        parent = h1;
        h1 = h1_hook.left.get();
    }

    A::hook(unsafe { &*parent }).left.set(h2);
    A::hook(unsafe { &*h2 }).parent.set(parent);

    new_root
}

// Inserts new_node into the heap and returns new root.
// O(log n) amortized
pub unsafe fn push<A: Adapter>(root: *const A::Outer, new_node: Rc<A::Outer>) -> *const A::Outer {
    let new_hook = A::hook(new_node.deref());
    assert_eq!(new_hook.left.get(), null(), "new_node.left must be null");
    assert_eq!(new_hook.right.get(), null(), "new_node.right must be null");
    assert_eq!(
        new_hook.parent.get(),
        null(),
        "new_node.parent must be null"
    );
    unsafe { meld::<A>(root, Rc::into_raw(new_node)) }
}

// Removes the minimum element of the heap and returns (new_root, min_entry).
// O(log n) amortized
pub unsafe fn pop_min<A: Adapter>(
    root: *const A::Outer,
) -> (*const A::Outer, Option<Rc<A::Outer>>) {
    if root.is_null() {
        return (null(), None);
    }

    // Meld the children of the root.
    let root_hook = A::hook(unsafe { &*root });
    debug_assert_eq!(root_hook.parent.get(), null());
    let new_root = unsafe { meld::<A>(root_hook.left.get(), root_hook.right.get()) };
    if !new_root.is_null() {
        A::hook(unsafe { &*new_root }).parent.set(null());
    }

    // Clear the hook for safety.
    root_hook.left.set(null());
    root_hook.right.set(null());
    root_hook.parent.set(null());

    // Since Rc::into_raw() was called when pushing the node to heap,
    // Rc::from_raw() need to be called when removing it from heap.
    (new_root, Some(unsafe { Rc::from_raw(root) }))
}

// Returns the minimum element of the heap without removing it from the heap.
// O(1)
pub unsafe fn peek_min<A: Adapter>(root: *const A::Outer) -> Option<Rc<A::Outer>> {
    if root.is_null() {
        return None;
    }
    unsafe {
        Rc::increment_strong_count(root);
        Some(Rc::from_raw(root))
    }
}

// Removes the given node from the heap and returns the new root and the ownership of the removed node.
// O(log n) amortized
pub unsafe fn unlink<A: Adapter>(
    root: *const A::Outer,
    node: &Rc<A::Outer>,
) -> (*const A::Outer, Rc<A::Outer>) {
    debug_assert_ne!(root, null(), "root must not be null");

    let node_hook = A::hook(node.deref());
    let parent = node_hook.parent.get();

    // Meld the children of the node.
    let subtree = unsafe { meld::<A>(node_hook.left.get(), node_hook.right.get()) };
    if !subtree.is_null() {
        A::hook(unsafe { &*subtree }).parent.set(parent);
    }

    // Connect the subtree to the parent of the node.
    if !parent.is_null() {
        let parent_hook = A::hook(unsafe { &*parent });
        if parent_hook.left.get() == Rc::as_ptr(node) {
            parent_hook.left.set(subtree);
        } else {
            parent_hook.right.set(subtree);
        }
    }

    // Clear the hook for safety.
    node_hook.left.set(null());
    node_hook.right.set(null());
    node_hook.parent.set(null());

    // Since Rc::into_raw() was called when pushing the node to heap,
    // Rc::from_raw() need to be called when removing it from heap.
    let rc = unsafe { Rc::from_raw(Rc::as_ptr(node)) };
    if Rc::as_ptr(node) == root {
        (subtree, rc)
    } else {
        (root, rc)
    }
}

pub unsafe fn visit_all<A: Adapter>(root: *const A::Outer, f: &mut impl FnMut(Rc<A::Outer>)) {
    if root.is_null() {
        return;
    }
    let rc = unsafe {
        Rc::increment_strong_count(root);
        Rc::from_raw(root)
    };
    f(rc);
    let root_hook = A::hook(unsafe { &*root });
    unsafe { visit_all::<A>(root_hook.left.get(), f) };
    unsafe { visit_all::<A>(root_hook.right.get(), f) };
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeSet;

    #[derive(Debug, Default)]
    struct Entry {
        x: i64,
        hook: Hook<Entry>,
    }

    struct EntryAdapter;
    impl Adapter for EntryAdapter {
        type Outer = Entry;
        type Key = i64;
        fn hook(outer: &Self::Outer) -> &Hook<Self::Outer> {
            &outer.hook
        }
        fn key(outer: &Self::Outer) -> &Self::Key {
            &outer.x
        }
    }

    #[derive(Debug)]
    enum Action {
        Push(i64),
        PopMin,
        Unlink(usize),
    }

    fn print_heap(root: *const Entry) {
        let mut v = Vec::new();
        unsafe {
            visit_all::<EntryAdapter>(root, &mut |entry| {
                v.push(entry.as_ref().x);
            });
        }
        println!("{:?}", v);
    }

    #[test]
    fn randomized_test() {
        let mut expected = BTreeSet::new();
        let mut root: *const Entry = null();

        for i in 0..1000 {
            let action = {
                if expected.is_empty() {
                    Action::Push(i)
                } else {
                    match rand::random::<usize>() % 10 {
                        0..5 => Action::Push(i),
                        5..8 => Action::PopMin,
                        8..10 => Action::Unlink(rand::random::<usize>() % expected.len()),
                        _ => unreachable!(),
                    }
                }
            };
            print_heap(root);
            println!("action = {:?}", action);
            match action {
                Action::Push(x) => {
                    expected.insert(x);

                    let new_entry = Rc::new(Entry {
                        x,
                        ..Default::default()
                    });
                    root = unsafe { push::<EntryAdapter>(root, new_entry) };
                }
                Action::PopMin => {
                    let expected_min = *expected.first().unwrap();
                    expected.remove(&expected_min);

                    let (new_root, min_entry) = unsafe { pop_min::<EntryAdapter>(root) };
                    root = new_root;
                    let actual_min = min_entry.unwrap().x;
                    assert_eq!(expected_min, actual_min);
                }
                Action::Unlink(idx) => {
                    let expected_x = *expected.iter().nth(idx).unwrap();
                    expected.remove(&expected_x);

                    // heap では idx 番目に小さい値が不明なので、expected_x を探して削除するということにする
                    let mut x_entry = None;
                    unsafe {
                        visit_all::<EntryAdapter>(root, &mut |entry| {
                            if entry.x == expected_x {
                                x_entry = Some(entry);
                            }
                        });
                    }
                    let (new_root, _) = unsafe { unlink::<EntryAdapter>(root, &x_entry.unwrap()) };
                    root = new_root;
                }
            }

            let actual_min = unsafe { peek_min::<EntryAdapter>(root) }.map(|p| p.x);
            let expected_min = expected.first().map(|x| *x);
            assert_eq!(expected_min, actual_min);
        }

        // deallocate
        while !root.is_null() {
            let (new_root, _) = unsafe { pop_min::<EntryAdapter>(root) };
            root = new_root;
        }
    }
}
