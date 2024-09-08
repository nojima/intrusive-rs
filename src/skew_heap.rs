#![warn(unsafe_op_in_unsafe_fn)]

use std::{cell::Cell, marker::PhantomData, ops::Deref, ptr::null, rc::Rc};

pub struct SkewHeap<A: Adapter> {
    root: *const A::Outer,
}

impl<A: Adapter> SkewHeap<A> {
    pub fn new() -> Self {
        Self { root: null() }
    }

    pub fn is_empty(&self) -> bool {
        self.root.is_null()
    }

    pub fn push(&mut self, new_node: Rc<A::Outer>) {
        // precondition check
        {
            let hook = A::hook(&new_node);
            assert_eq!(
                hook.parent.get(),
                out_of_heap_mark(),
                "You are trying to push a node that already belongs to a heap."
            );
            hook.parent.set(null());
        }

        self.root = unsafe { push::<A>(self.root, new_node) };
    }

    pub fn pop_min(&mut self) -> Option<Rc<A::Outer>> {
        let (new_root, popped_node) = unsafe { pop_min::<A>(self.root) };
        self.root = new_root;
        popped_node
    }

    pub fn peek_min(&self) -> Option<Rc<A::Outer>> {
        unsafe { peek_min::<A>(self.root) }
    }

    pub unsafe fn unlink(&mut self, node: &Rc<A::Outer>) -> Rc<A::Outer> {
        let (new_root, removed_node) = unsafe { unlink::<A>(self.root, node) };
        self.root = new_root;
        removed_node
    }

    pub fn visit_all(&self, f: &mut impl FnMut(Rc<A::Outer>)) {
        unsafe { visit_all::<A>(self.root, f) }
    }
}

impl<A: Adapter> Drop for SkewHeap<A> {
    fn drop(&mut self) {
        while !self.is_empty() {
            let _ = self.pop_min();
        }
    }
}

#[derive(Debug)]
pub struct Hook<Outer> {
    left: Cell<*const Outer>,
    right: Cell<*const Outer>,
    parent: Cell<*const Outer>,
}

// Since Rust does not have static_assert with type arguments yet,
// we emulate it with struct.
macro_rules! static_assert_with_t {
    ($t: ident, $expr: expr, $message: expr) => {{
        struct StaticAssert<$t>(PhantomData<$t>);
        impl<$t> StaticAssert<$t> {
            const ASSERT: () = if !$expr {
                panic!($message)
            };
        }
        let _ = StaticAssert::<$t>::ASSERT;
    }};
}

#[inline]
fn out_of_heap_mark<Outer>() -> *const Outer {
    static_assert_with_t!(
        Outer,
        align_of::<Outer>() >= 2,
        "align of Outer must be >= 2"
    );

    // It is safe to use address 1 as a mark.
    // Since the pointer is aligned, 1 does not conflict with a valid pointer.
    1 as *const Outer
}

impl<Outer> Default for Hook<Outer> {
    fn default() -> Self {
        Self {
            left: Cell::new(null()),
            right: Cell::new(null()),
            parent: Cell::new(out_of_heap_mark()),
        }
    }
}

impl<Outer> Hook<Outer> {
    fn reset(&self) {
        self.left.set(null());
        self.right.set(null());
        self.parent.set(out_of_heap_mark());
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
    assert_ne!(h1, h2, "h1 and h2 must be different heaps");

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
    debug_assert_eq!(new_hook.left.get(), null(), "new_node.left must be null");
    debug_assert_eq!(new_hook.right.get(), null(), "new_node.right must be null");
    debug_assert_eq!(
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

    root_hook.reset();

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

    node_hook.reset();

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

    fn print_heap(heap: &SkewHeap<EntryAdapter>) {
        let mut v = Vec::new();
        heap.visit_all(&mut |entry| {
            v.push(entry.as_ref().x);
        });
        println!("{:?}", v);
    }

    #[test]
    fn randomized_test() {
        let mut expected = BTreeSet::new();
        let mut heap = SkewHeap::<EntryAdapter>::new();

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
            print_heap(&heap);
            println!("action = {:?}", action);
            match action {
                Action::Push(x) => {
                    expected.insert(x);

                    let new_entry = Rc::new(Entry {
                        x,
                        ..Default::default()
                    });
                    heap.push(new_entry);
                }
                Action::PopMin => {
                    let expected_min = *expected.first().unwrap();
                    expected.remove(&expected_min);

                    let min_entry = heap.pop_min();
                    let actual_min = min_entry.unwrap().x;
                    assert_eq!(expected_min, actual_min);
                }
                Action::Unlink(idx) => {
                    let expected_x = *expected.iter().nth(idx).unwrap();
                    expected.remove(&expected_x);

                    // heap では idx 番目に小さい値が不明なので、expected_x を探して削除するということにする
                    let mut x_entry = None;
                    heap.visit_all(&mut |entry| {
                        if entry.x == expected_x {
                            x_entry = Some(entry);
                        }
                    });
                    let _ = unsafe { heap.unlink(&x_entry.unwrap()) };
                }
            }

            let actual_min = heap.peek_min().map(|p| p.x);
            let expected_min = expected.first().map(|x| *x);
            assert_eq!(expected_min, actual_min);
        }
    }
}
