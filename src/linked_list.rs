use std::{
    cell::UnsafeCell,
    ptr::{null_mut, NonNull},
};

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

pub trait Adapter {
    type Outer;
    fn hook(outer: &Self::Outer) -> &UnsafeCell<Hook<Self::Outer>>;
}

pub struct LinkedList<A: Adapter> {
    head: *mut A::Outer,
}

impl<A: Adapter> LinkedList<A> {
    pub fn new() -> Self {
        Self { head: null_mut() }
    }

    pub fn is_empty(&self) -> bool {
        self.head.is_null()
    }

    pub unsafe fn push_front(&mut self, new_node: *mut A::Outer) {
        self.head = push_front::<A>(self.head, new_node);
    }

    pub unsafe fn unlink(&mut self, node: *mut A::Outer) {
        self.head = unlink::<A>(self.head, node);
    }

    pub fn iter(&mut self) -> impl Iterator<Item = NonNull<A::Outer>> {
        unsafe { iterate::<A>(self.head) }
    }
}

struct Iter<A: Adapter> {
    p: *mut A::Outer,
}

impl<A: Adapter> Iterator for Iter<A> {
    type Item = NonNull<A::Outer>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.p.is_null() {
            return None;
        }
        unsafe {
            let item = NonNull::new_unchecked(self.p);
            let hook = A::hook(&*self.p).get();
            self.p = (*hook).next;
            Some(item)
        }
    }
}

unsafe fn push_front<A: Adapter>(
    head: *mut A::Outer,
    new_node: *mut A::Outer,
) -> *mut A::Outer {
    unsafe {
        let new_hook = A::hook(&*new_node).get();
        if head.is_null() {
            (*new_hook).next = null_mut();
            (*new_hook).prev = null_mut();
            return new_node;
        }

        let head_hook = A::hook(&*head).get();
        assert_eq!((*head_hook).prev, null_mut());

        (*new_hook).next = head;
        (*new_hook).prev = null_mut();
        (*head_hook).prev = new_node;
        new_node
    }
}

unsafe fn unlink<A: Adapter>(
    head: *mut A::Outer,
    node: *mut A::Outer,
) -> *mut A::Outer {
    assert_ne!(node, null_mut());
    unsafe {
        let node_hook = A::hook(&*node).get();
        if !(*node_hook).prev.is_null() {
            let prev_hook = A::hook(&*(*node_hook).prev).get();
            (*prev_hook).next = (*node_hook).next;
        }
        if !(*node_hook).next.is_null() {
            let next_hook = A::hook(&*(*node_hook).next).get();
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

unsafe fn iterate<A: Adapter>(
    head: *mut A::Outer,
) -> impl Iterator<Item = NonNull<A::Outer>> {
    Iter::<A> { p: head }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::{cell::UnsafeCell, collections::VecDeque};

    #[derive(Debug, Default)]
    struct Entry {
        x: i64,
        hook: UnsafeCell<Hook<Entry>>,
    }

    struct EntryAdapter;
    impl Adapter for EntryAdapter {
        type Outer = Entry;
        fn hook(outer: &Self::Outer) -> &UnsafeCell<Hook<Self::Outer>> {
            &outer.hook
        }
    }

    #[test]
    fn test_linked_list() {
        let mut list = LinkedList::<EntryAdapter>::new();
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

    fn print_list(list: &mut LinkedList<EntryAdapter>) {
        let v: Vec<_> = unsafe { list.iter().map(|p| p.as_ref().x).collect() };
        println!("{:?}", v);
    }

    #[test]
    fn randomized_test() {
        let mut expected = VecDeque::new();
        let mut list = LinkedList::<EntryAdapter>::new();

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
