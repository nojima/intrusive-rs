use std::{
    marker::PhantomData,
    ptr::{null_mut, NonNull},
};

#[derive(Debug)]
pub struct Hook {
    next: *mut Hook,
    prev: *mut Hook,
}

impl Default for Hook {
    fn default() -> Self {
        Self {
            next: null_mut(),
            prev: null_mut(),
        }
    }
}

pub struct Iter<Entry, const OFFSET: usize> {
    p: *mut Hook,
    _phantom: PhantomData<fn() -> Entry>,
}

impl<Entry, const OFFSET: usize> Iterator for Iter<Entry, OFFSET> {
    type Item = NonNull<Entry>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.p.is_null() {
            return None;
        }
        unsafe {
            let entry = self.p.byte_sub(OFFSET) as *mut Entry;
            self.p = (*self.p).next;
            Some(NonNull::new_unchecked(entry))
        }
    }
}

pub unsafe fn push_front(head: *mut Hook, new_node: *mut Hook) -> *mut Hook {
    unsafe {
        if head.is_null() {
            (*new_node).next = null_mut();
            (*new_node).prev = null_mut();
            return new_node;
        }

        assert_eq!((*head).prev, null_mut());

        (*new_node).next = head;
        (*new_node).prev = null_mut();
        (*head).prev = new_node;
        new_node
    }
}

pub unsafe fn unlink(head: *mut Hook, node: *mut Hook) -> *mut Hook {
    assert_ne!(node, null_mut());
    unsafe {
        if !(*node).prev.is_null() {
            (*(*node).prev).next = (*node).next;
        }
        if !(*node).next.is_null() {
            (*(*node).next).prev = (*node).prev;
        }
        let next = (*node).next;
        (*node).next = null_mut();
        (*node).prev = null_mut();
        if node == head {
            next
        } else {
            head
        }
    }
}

pub unsafe fn iterate<Entry, const OFFSET: usize>(
    head: *mut Hook,
) -> impl Iterator<Item = NonNull<Entry>> {
    Iter::<Entry, OFFSET> {
        p: head,
        _phantom: PhantomData,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::{cell::UnsafeCell, collections::VecDeque, mem::offset_of};

    #[derive(Debug, Default)]
    struct Entry {
        x: i64,
        hook: UnsafeCell<Hook>,
    }
    const HOOK_OFFSET: usize = offset_of!(Entry, hook);

    #[test]
    fn test_linked_list() {
        let mut v = Vec::new();
        for i in 0..10 {
            v.push(Entry {
                x: i,
                ..Default::default()
            })
        }
        let mut head = null_mut();
        for i in 0..10 {
            let p = v[i].hook.get();
            head = unsafe { push_front(head, p) };
        }
        for p in unsafe { iterate::<Entry, HOOK_OFFSET>(head) } {
            let x = unsafe { p.as_ref() }.x;
            println!("{}", x);
        }
    }

    #[derive(Debug)]
    enum Action {
        PushFront(i64),
        Unlink(usize),
    }

    fn print_list(head: *mut Hook) {
        let v: Vec<_> = unsafe {
            iterate::<Entry, HOOK_OFFSET>(head).map(|p| p.as_ref().x).collect()
        };
        println!("{:?}", v);
    }

    #[test]
    fn randomized_test() {
        let mut expected = VecDeque::new();
        let mut head: *mut Hook = null_mut();

        for i in 0..1000 {
            let action = {
                if expected.is_empty() {
                    Action::PushFront(i)
                } else {
                    if rand::random::<bool>() {
                        Action::PushFront(i)
                    } else {
                        Action::Unlink(rand::random::<usize>() % expected.len())
                    }
                }
            };
            print_list(head);
            println!(
                "head = {}, action = {:?}",
                if head.is_null() {
                    "null".to_owned()
                } else {
                    format!("{:?}", unsafe { head.as_mut().unwrap() })
                },
                action
            );
            match action {
                Action::PushFront(x) => {
                    expected.push_front(x);

                    let new_entry = Box::leak(Box::new(Entry {
                        x,
                        ..Default::default()
                    }));
                    head = unsafe { push_front(head, new_entry.hook.get_mut()) }
                }
                Action::Unlink(idx) => {
                    let expected_x = expected.remove(idx).unwrap();

                    let mut entry = unsafe { iterate::<Entry, HOOK_OFFSET>(head) }
                        .nth(idx)
                        .unwrap();
                    let actual_x = unsafe { entry.as_ref().x };
                    head = unsafe { unlink(head, entry.as_mut().hook.get_mut()) };

                    assert_eq!(expected_x, actual_x);
                }
            }
        }
    }
}
