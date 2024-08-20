use std::{
    borrow::Borrow,
    cell::RefCell,
    mem::swap,
    ops::{Deref, DerefMut},
    ptr::null,
    rc::Rc,
};

#[derive(Debug)]
pub struct Hook<Outer> {
    left: *const Outer,
    right: *const Outer,
    parent: *const Outer,
}

impl<Outer> Default for Hook<Outer> {
    fn default() -> Self {
        Self {
            left: null(),
            right: null(),
            parent: null(),
        }
    }
}

pub trait Adapter {
    type Outer;
    type Key: Ord;
    fn hook(outer: &Self::Outer) -> &RefCell<Hook<Self::Outer>>;
    fn key(outer: &Self::Outer) -> &Self::Key;
}

// Melds the given two heaps and returns the root of the merged heap.
pub unsafe fn meld<A: Adapter>(
    root1: *const A::Outer,
    root2: *const A::Outer,
    parent: *const A::Outer,
) -> *const A::Outer {
    if root1.is_null() {
        if root2.is_null() {
            return null();
        }
        let mut hook2 = A::hook(unsafe { &*root2 }).borrow_mut();
        hook2.parent = parent;
        return root2;
    }
    if root2.is_null() {
        let mut hook1 = A::hook(unsafe { &*root1 }).borrow_mut();
        hook1.parent = parent;
        return root1;
    }

    // make sure that root1 <= root2
    let (root1, root2) = unsafe {
        // NOTE: we create shared references to Entry here.
        let key1 = A::key(&*root1).borrow();
        let key2 = A::key(&*root2).borrow();
        if key1 > key2 {
            (root2, root1)
        } else {
            (root1, root2)
        }
    };

    // do meld
    let mut hook1_borrow = A::hook(unsafe { &*root1 }).borrow_mut();
    let hook1 = hook1_borrow.deref_mut();
    hook1.right = meld::<A>(hook1.right, root2, root1);
    swap(&mut hook1.left, &mut hook1.right);
    hook1.parent = parent;
    root1
}

// Inserts new_node into the heap and returns new root.
pub unsafe fn push<A: Adapter>(root: *const A::Outer, new_node: Rc<A::Outer>) -> *const A::Outer {
    let new_hook = A::hook(new_node.deref()).borrow();
    assert_eq!(new_hook.left, null(), "new_node.left must be null");
    assert_eq!(new_hook.right, null(), "new_node.right must be null");
    assert_eq!(new_hook.parent, null(), "new_node.parent must be null");
    drop(new_hook); // unborrow
    unsafe { meld::<A>(root, Rc::into_raw(new_node), null()) }
}

// Removes minimum element of the heap and returns (new_root, min_entry).
pub unsafe fn pop_min<A: Adapter>(
    root: *const A::Outer,
) -> (*const A::Outer, Option<Rc<A::Outer>>) {
    if root.is_null() {
        return (null(), None);
    }
    let mut root_hook = A::hook(unsafe { &*root }).borrow_mut();
    assert_eq!(root_hook.parent, null(), "root.parent must be null");

    let new_root = unsafe { meld::<A>(root_hook.left, root_hook.right, null()) };

    root_hook.left = null();
    root_hook.right = null();
    drop(root_hook); // unborrow
    (new_root, Some(Rc::from_raw(root)))
}

// Removes the given node from the heap and returns the new root and the ownership of the removed node.
pub unsafe fn unlink<A: Adapter>(
    root: *const A::Outer,
    node: &Rc<A::Outer>,
) -> (*const A::Outer, Rc<A::Outer>) {
    assert_ne!(root, null(), "root must not be null");

    let mut node_hook = A::hook(node.deref()).borrow_mut();

    let subtree = meld::<A>(node_hook.left, node_hook.right, node_hook.parent);

    let parent = node_hook.parent;
    if !parent.is_null() {
        let mut parent_hook = A::hook(unsafe { &*parent }).borrow_mut();
        if parent_hook.left == Rc::as_ptr(node) {
            parent_hook.left = subtree;
        } else {
            parent_hook.right = subtree;
        }
    }

    node_hook.left = null();
    node_hook.right = null();
    node_hook.parent = null();

    let rc = Rc::from_raw(Rc::as_ptr(node));
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
    let root_hook = A::hook(unsafe { &*root }).borrow();
    visit_all::<A>(root_hook.left, f);
    visit_all::<A>(root_hook.right, f);
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::{cell::RefCell, collections::BTreeSet};

    #[derive(Debug, Default)]
    struct Entry {
        x: i64,
        hook: RefCell<Hook<Entry>>,
    }

    struct EntryAdapter;
    impl Adapter for EntryAdapter {
        type Outer = Entry;
        type Key = i64;
        fn hook(outer: &Self::Outer) -> &RefCell<Hook<Self::Outer>> {
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
        }

        // deallocate
        while !root.is_null() {
            let (new_root, _) = unsafe { pop_min::<EntryAdapter>(root)};
            root = new_root;
        }
    }
}
