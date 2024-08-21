use std::{
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
        let key1 = A::key(&*root1);
        let key2 = A::key(&*root2);
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

// make sure that key(p1) <= key(p2)
// p1 and p2 must not be null.
unsafe fn ensure_ordering<A: Adapter>(p1: &mut *const A::Outer, p2: &mut *const A::Outer) {
    let key1 = A::key(unsafe { &**p1 });
    let key2 = A::key(unsafe { &**p2 });
    if key1 > key2 {
        std::mem::swap(p1, p2);
    }
}

// Melds the given two heaps and returns the root of the merged heap.
pub unsafe fn imeld<A: Adapter>(
    mut h1: *const A::Outer,
    mut h2: *const A::Outer,
) -> *const A::Outer {
    if h1.is_null() {
        return h2;
    }
    if h2.is_null() {
        return h1;
    }

    ensure_ordering::<A>(&mut h1, &mut h2);

    let new_root = h1;
    let mut parent = h1;
    let mut h1_hook_borrow = A::hook(unsafe { &*h1 }).borrow_mut();
    let h1_hook = h1_hook_borrow.deref_mut();
    h1 = std::mem::replace(&mut h1_hook.right, h1_hook.left);
    drop(h1_hook_borrow); // unborrow

    while !h1.is_null() {
        ensure_ordering::<A>(&mut h1, &mut h2);

        let mut parent_hook = A::hook(unsafe { &*parent }).borrow_mut();
        let mut h1_hook_borrow = A::hook(unsafe { &*h1 }).borrow_mut();
        let h1_hook = h1_hook_borrow.deref_mut();

        // connect `h1` as the left child of `parent`.
        parent_hook.left = h1;
        h1_hook.parent = parent;

        // update loop variables: the next `parent` is `h1`
        parent = h1;

        // swap `h1.left` and `h1.right` and the next `h1` is old `h1.right`.
        h1 = std::mem::replace(&mut h1_hook.right, h1_hook.left);
    }

    A::hook(unsafe { &*parent }).borrow_mut().left = h2;
    A::hook(unsafe { &*h2 }).borrow_mut().parent = parent;

    new_root
}

// Inserts new_node into the heap and returns new root.
pub unsafe fn push<A: Adapter>(root: *const A::Outer, new_node: Rc<A::Outer>) -> *const A::Outer {
    let new_hook = A::hook(new_node.deref()).borrow();
    assert_eq!(new_hook.left, null(), "new_node.left must be null");
    assert_eq!(new_hook.right, null(), "new_node.right must be null");
    assert_eq!(new_hook.parent, null(), "new_node.parent must be null");
    drop(new_hook); // unborrow
    unsafe { imeld::<A>(root, Rc::into_raw(new_node)) }
}

// node must not be null
unsafe fn set_parent<A: Adapter>(node: *const A::Outer, parent: *const A::Outer) {
    let mut hook = A::hook(unsafe { &*node }).borrow_mut();
    hook.parent = parent;
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

    let new_root = unsafe { imeld::<A>(root_hook.left, root_hook.right) };

    if !new_root.is_null() {
        set_parent::<A>(new_root, null());
    }

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

    let subtree = imeld::<A>(node_hook.left, node_hook.right);

    if !subtree.is_null() {
        set_parent::<A>(subtree, node_hook.parent);
    }

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
