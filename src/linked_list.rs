use std::ptr::{null_mut, NonNull};

pub struct LinkedList<Outer, const OFFSET: usize> {
    head: *mut Outer,
}

impl<Outer, const OFFSET: usize> LinkedList<Outer, OFFSET> {
    pub fn new() -> Self {
        Self { head: null_mut() }
    }

    pub fn is_empty(&self) -> bool {
        self.head.is_null()
    }

    pub unsafe fn push_front(&mut self, new_node: *mut Outer) {
        self.head = push_front::<Outer, OFFSET>(self.head, new_node);
    }

    pub unsafe fn unlink(&mut self, node: *mut Outer) {
        self.head = unlink::<Outer, OFFSET>(self.head, node);
    }

    pub fn iter(&mut self) -> impl Iterator<Item = NonNull<Outer>> {
        unsafe { iterate::<Outer, OFFSET>(self.head) }
    }
}

#[derive(Debug)]
pub struct Hook<Outer> {
    next: *mut Outer,
    prev: *mut Outer,
}

impl<Outer> Default for Hook<Outer> {
    fn default() -> Self {
        Self {
            next: null_mut(),
            prev: null_mut(),
        }
    }
}

pub struct Iter<Outer, const OFFSET: usize> {
    p: *mut Outer,
}

impl<Outer, const OFFSET: usize> Iterator for Iter<Outer, OFFSET> {
    type Item = NonNull<Outer>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.p.is_null() {
            return None;
        }
        unsafe {
            let item = NonNull::new_unchecked(self.p);
            let hook = self.p.byte_add(OFFSET) as *mut Hook<Outer>;
            self.p = (*hook).next;
            Some(item)
        }
    }
}

unsafe fn get_hook<Outer, const OFFSET: usize>(p: *mut Outer) -> *mut Hook<Outer> {
    p.byte_add(OFFSET) as *mut Hook<Outer>
}

pub unsafe fn push_front<Outer, const OFFSET: usize>(
    head: *mut Outer,
    new_node: *mut Outer,
) -> *mut Outer {
    unsafe {
        let new_hook = get_hook::<_, OFFSET>(new_node);
        if head.is_null() {
            (*new_hook).next = null_mut();
            (*new_hook).prev = null_mut();
            return new_node;
        }

        let head_hook = get_hook::<_, OFFSET>(head);
        assert_eq!((*head_hook).prev, null_mut());

        (*new_hook).next = head;
        (*new_hook).prev = null_mut();
        (*head_hook).prev = new_node;
        new_node
    }
}

pub unsafe fn unlink<Outer, const OFFSET: usize>(head: *mut Outer, node: *mut Outer) -> *mut Outer {
    assert_ne!(node, null_mut());
    unsafe {
        let node_hook = get_hook::<_, OFFSET>(node);
        if !(*node_hook).prev.is_null() {
            let prev_hook = get_hook::<_, OFFSET>((*node_hook).prev);
            (*prev_hook).next = (*node_hook).next;
        }
        if !(*node_hook).next.is_null() {
            let next_hook = get_hook::<_, OFFSET>((*node_hook).next);
            (*next_hook).prev = (*node_hook).prev;
        }
        let next = (*node_hook).next;
        (*node_hook).next = null_mut();
        (*node_hook).prev = null_mut();
        if node == head {
            next
        } else {
            head
        }
    }
}

pub unsafe fn iterate<Outer, const OFFSET: usize>(
    head: *mut Outer,
) -> impl Iterator<Item = NonNull<Outer>> {
    Iter::<Outer, OFFSET> { p: head }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::{cell::UnsafeCell, collections::VecDeque, mem::offset_of};

    #[derive(Debug, Default)]
    struct Entry {
        x: i64,
        hook: UnsafeCell<Hook<Entry>>,
    }
    const HOOK_OFFSET: usize = offset_of!(Entry, hook);

    #[test]
    fn test_linked_list() {
        let mut list = LinkedList::<Entry, HOOK_OFFSET>::new();
        for i in 0..10 {
            let p = Box::into_raw(Box::new(Entry {
                x: i,
                ..Default::default()
            }));
            unsafe { list.push_front(p) };
        }
        for p in list.iter() {
            let x = unsafe { p.as_ref() }.x;
            println!("{}", x);
            // deallocate
            unsafe { drop(Box::from_raw(p.as_ptr())) };
        }
    }

    #[derive(Debug)]
    enum Action {
        PushFront(i64),
        Unlink(usize),
    }

    fn print_list(list: &mut LinkedList<Entry, HOOK_OFFSET>) {
        let v: Vec<_> = unsafe { list.iter().map(|p| p.as_ref().x).collect() };
        println!("{:?}", v);
    }

    #[test]
    fn randomized_test() {
        let mut expected = VecDeque::new();
        let mut list = LinkedList::<Entry, HOOK_OFFSET>::new();

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
            print_list(&mut list);
            println!("action = {:?}", action);
            match action {
                Action::PushFront(x) => {
                    expected.push_front(x);

                    let new_entry = Box::into_raw(Box::new(Entry {
                        x,
                        ..Default::default()
                    }));
                    unsafe { list.push_front(new_entry) };
                }
                Action::Unlink(idx) => {
                    let expected_x = expected.remove(idx).unwrap();

                    unsafe {
                        let entry = list.iter().nth(idx).unwrap();
                        let actual_x = entry.as_ref().x;
                        list.unlink(entry.as_ptr());

                        assert_eq!(expected_x, actual_x);

                        drop(Box::from_raw(entry.as_ptr()));
                    }
                }
            }
        }

        // deallocate
        for p in list.iter() {
            unsafe {
                drop(Box::from_raw(p.as_ptr()));
            }
        }
    }
}
