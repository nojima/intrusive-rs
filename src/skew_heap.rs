use std::{
    mem::swap,
    ptr::{null_mut, NonNull},
};

#[derive(Debug)]
pub struct Hook {
    left: *mut Hook,
    right: *mut Hook,
    parent: *mut Hook,
}

impl Default for Hook {
    fn default() -> Self {
        Self {
            left: null_mut(),
            right: null_mut(),
            parent: null_mut(),
        }
    }
}

// Melds the given two heaps and returns the root of the merged heap.
pub unsafe fn meld<Entry: Ord, const OFFSET: usize>(
    root1: *mut Hook,
    root2: *mut Hook,
    parent: *mut Hook,
) -> *mut Hook {
    if root1.is_null() {
        if root2.is_null() {
            return null_mut();
        }
        unsafe { (*root2).parent = parent };
        return root2;
    }
    if root2.is_null() {
        unsafe { (*root1).parent = parent };
        return root1;
    }

    // make sure that root1 <= root2
    let (root1, root2) = unsafe {
        // NOTE: we create shared references to Entry here.
        let entry1 = (root1.byte_sub(OFFSET) as *mut Entry)
            .as_ref()
            .unwrap_unchecked();
        let entry2 = (root2.byte_sub(OFFSET) as *mut Entry)
            .as_ref()
            .unwrap_unchecked();
        if entry1 > entry2 {
            (root2, root1)
        } else {
            (root1, root2)
        }
    };

    // do meld
    unsafe {
        (*root1).right = meld::<Entry, OFFSET>((*root1).right, root2, root1);
        swap(&mut (*root1).left, &mut (*root1).right);
        (*root1).parent = parent;
    }
    root1
}

// Inserts new_node into the heap and returns new root.
pub unsafe fn push<Entry: Ord, const OFFSET: usize>(
    root: *mut Hook,
    new_node: *mut Hook,
) -> *mut Hook {
    unsafe {
        assert_ne!(new_node, null_mut(), "new_node must not be null");
        assert_eq!((*new_node).left, null_mut(), "new_node.left must be null");
        assert_eq!((*new_node).right, null_mut(), "new_node.right must be null");
        assert_eq!(
            (*new_node).parent,
            null_mut(),
            "new_node.parent must be null"
        );
    }
    unsafe { meld::<Entry, OFFSET>(root, new_node, null_mut()) }
}

// Removes minimum element of the heap and returns (new_root, min_entry).
pub unsafe fn pop_min<Entry: Ord, const OFFSET: usize>(
    root: *mut Hook,
) -> (*mut Hook, Option<NonNull<Entry>>) {
    if root.is_null() {
        return (null_mut(), None);
    }
    unsafe { assert_eq!((*root).parent, null_mut(), "root.parent must be null") };
    unsafe {
        let new_root = meld::<Entry, OFFSET>((*root).left, (*root).right, null_mut());
        (*root).left = null_mut();
        (*root).right = null_mut();
        let entry = NonNull::new_unchecked(root.byte_sub(OFFSET) as *mut Entry);
        (new_root, Some(entry))
    }
}

// Removes the given node from the heap.
pub unsafe fn unlink<Entry: Ord, const OFFSET: usize>(
    root: *mut Hook,
    node: *mut Hook,
) -> *mut Hook {
    assert_ne!(root, null_mut(), "root must not be null");
    assert_ne!(node, null_mut(), "node must not be null");
    assert_eq!((*root).parent, null_mut(), "root.parent must be null");

    let subtree = meld::<Entry, OFFSET>((*node).left, (*node).right, (*node).parent);

    let parent = (*node).parent;
    if !parent.is_null() {
        if (*parent).left == node {
            (*parent).left = subtree;
        } else {
            (*parent).right = subtree;
        }
    }

    (*node).left = null_mut();
    (*node).right = null_mut();
    (*node).parent = null_mut();

    if node == root {
        subtree
    } else {
        root
    }
}

pub unsafe fn visit_all<Entry: Ord, const OFFSET: usize>(
    root: *mut Hook,
    f: &mut impl FnMut(NonNull<Entry>),
) {
    if root.is_null() {
        return;
    }
    let entry = NonNull::new_unchecked(root.byte_sub(OFFSET) as *mut Entry);
    f(entry);
    visit_all::<Entry, OFFSET>((*root).left, f);
    visit_all::<Entry, OFFSET>((*root).right, f);
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::{cell::UnsafeCell, collections::BTreeSet, mem::offset_of};

    #[derive(Debug, Default)]
    struct Entry {
        x: i64,
        hook: UnsafeCell<Hook>,
    }
    impl PartialEq for Entry {
        fn eq(&self, other: &Self) -> bool {
            self.x == other.x
        }
    }
    impl Eq for Entry {}
    impl PartialOrd for Entry {
        fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
            Some(self.cmp(other))
        }
    }
    impl Ord for Entry {
        fn cmp(&self, other: &Self) -> std::cmp::Ordering {
            self.x.cmp(&other.x)
        }
    }

    const HOOK_OFFSET: usize = offset_of!(Entry, hook);

    #[derive(Debug)]
    enum Action {
        Push(i64),
        PopMin,
        Unlink(usize),
    }

    fn print_heap(root: *mut Hook) {
        let mut v = Vec::new();
        unsafe {
            visit_all::<Entry, HOOK_OFFSET>(root, &mut |entry| {
                v.push(entry.as_ref().x);
            });
        }
        println!("{:?}", v);
    }

    #[test]
    fn randomized_test() {
        let mut expected = BTreeSet::new();
        let mut root: *mut Hook = null_mut();

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

                    let new_entry = Box::leak(Box::new(Entry {
                        x,
                        ..Default::default()
                    }));
                    root = unsafe { push::<Entry, HOOK_OFFSET>(root, new_entry.hook.get_mut()) };
                }
                Action::PopMin => {
                    let expected_min = *expected.first().unwrap();
                    expected.remove(&expected_min);

                    let (new_root, min_entry) = unsafe { pop_min::<Entry, HOOK_OFFSET>(root) };
                    root = new_root;
                    let actual_min = unsafe { min_entry.unwrap().as_ref().x };
                    assert_eq!(expected_min, actual_min);
                }
                Action::Unlink(idx) => {
                    let expected_x = *expected.iter().nth(idx).unwrap();
                    expected.remove(&expected_x);

                    // heap では idx 番目に小さい値が不明なので、expected_x を探して削除するということにする
                    let mut x_entry = None;
                    unsafe {
                        visit_all::<Entry, HOOK_OFFSET>(root, &mut |entry| {
                            if entry.as_ref().x == expected_x {
                                x_entry = Some(entry);
                            }
                        })
                    }
                    let mut x_entry = x_entry.unwrap();
                    root = unsafe { unlink::<Entry, HOOK_OFFSET>(root, x_entry.as_mut().hook.get_mut()) };
                }
            }
        }
    }
}
