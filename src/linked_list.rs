use std::{cell::RefCell, ptr::null, rc::Rc};

#[derive(Debug)]
pub struct Hook<Outer> {
    next: *const Outer,
    prev: *const Outer,
}

impl<Outer> Default for Hook<Outer> {
    fn default() -> Self {
        Self {
            next: null(),
            prev: null(),
        }
    }
}

pub trait Adapter {
    type Outer;
    fn hook(outer: &Self::Outer) -> &RefCell<Hook<Self::Outer>>;
}

pub struct LinkedList<A: Adapter> {
    head: *const A::Outer,
}

impl<A: Adapter> LinkedList<A> {
    pub fn new() -> Self {
        Self { head: null() }
    }

    pub fn is_empty(&self) -> bool {
        self.head.is_null()
    }

    // Add `new_node` to the list.
    //
    // # Safety
    // * new_node must not be a member of the list.
    pub unsafe fn push_front(&mut self, new_node: Rc<A::Outer>) {
        self.head = push_front::<A>(self.head, new_node);
    }

    // Unlink `node` from the list and returns the ownership of `node`.
    //
    // # Safety
    // * `node` must be a member of the list.
    // * `node` must be obtained from Rc::into_raw or Rc::as_ptr.
    //    * Do not pass `rc.as_ref() as *const A::Outer`. It causes undefined behavior.
    #[must_use]
    pub unsafe fn unlink(&mut self, node: *const A::Outer) -> Rc<A::Outer> {
        let (new_head, unlinked_node) = unlink::<A>(self.head, node);
        self.head = new_head;
        unlinked_node
    }

    pub fn iter(&mut self) -> impl Iterator<Item = Rc<A::Outer>> {
        unsafe { iterate::<A>(self.head) }
    }
}

struct Iter<A: Adapter> {
    p: *const A::Outer,
}

impl<A: Adapter> Iterator for Iter<A> {
    type Item = Rc<A::Outer>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.p.is_null() {
            return None;
        }
        unsafe {
            // Rc::clone from self.p
            Rc::increment_strong_count(self.p);
            let rc = Rc::from_raw(self.p);

            let hook = A::hook(&*self.p).borrow();
            self.p = hook.next;

            Some(rc)
        }
    }
}

unsafe fn push_front<A: Adapter>(head: *const A::Outer, new_node: Rc<A::Outer>) -> *const A::Outer {
    let new_node = Rc::into_raw(new_node);
    unsafe {
        let mut new_hook = A::hook(&*new_node).borrow_mut();
        if head.is_null() {
            new_hook.next = null();
            new_hook.prev = null();
            return new_node;
        }

        let mut head_hook = A::hook(&*head).borrow_mut();
        assert_eq!(head_hook.prev, null());

        new_hook.next = head;
        new_hook.prev = null();
        head_hook.prev = new_node;
        new_node
    }
}

unsafe fn unlink<A: Adapter>(
    head: *const A::Outer,
    node: *const A::Outer,
) -> (*const A::Outer, Rc<A::Outer>) {
    assert_ne!(node, null());
    unsafe {
        let mut node_hook = A::hook(&*node).borrow_mut();
        if !node_hook.prev.is_null() {
            let mut prev_hook = A::hook(&*node_hook.prev).borrow_mut();
            prev_hook.next = node_hook.next;
        }
        if !node_hook.next.is_null() {
            let mut next_hook = A::hook(&*node_hook.next).borrow_mut();
            next_hook.prev = (*node_hook).prev;
        }
        let next = node_hook.next;
        node_hook.next = null();
        node_hook.prev = null();
        if node == head {
            (next, Rc::from_raw(node))
        } else {
            (head, Rc::from_raw(node))
        }
    }
}

unsafe fn iterate<A: Adapter>(head: *const A::Outer) -> impl Iterator<Item = Rc<A::Outer>> {
    Iter::<A> { p: head }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::VecDeque;

    #[derive(Debug, Default)]
    struct Entry {
        x: i64,
        hook: RefCell<Hook<Entry>>,
    }

    struct EntryAdapter;
    impl Adapter for EntryAdapter {
        type Outer = Entry;
        fn hook(outer: &Self::Outer) -> &RefCell<Hook<Self::Outer>> {
            &outer.hook
        }
    }

    #[test]
    fn test_linked_list() {
        let mut list = LinkedList::<EntryAdapter>::new();
        for i in 0..10 {
            let entry = Rc::new(Entry {
                x: i,
                ..Default::default()
            });
            unsafe { list.push_front(entry) };
        }
        for p in list.iter() {
            println!("{}", p.x);
            // deallocate
            let _ = unsafe { list.unlink(Rc::as_ptr(&p)) };
        }
    }

    #[derive(Debug)]
    enum Action {
        PushFront(i64),
        Unlink(usize),
    }

    fn print_list(list: &mut LinkedList<EntryAdapter>) {
        let v: Vec<_> = list.iter().map(|p| p.x).collect();
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

                    let new_entry = Rc::new(Entry {
                        x,
                        ..Default::default()
                    });
                    unsafe { list.push_front(new_entry) };
                }
                Action::Unlink(idx) => {
                    let expected_x = expected.remove(idx).unwrap();

                    let entry = list.iter().nth(idx).unwrap();
                    let actual_x = entry.x;

                    let _ = unsafe { list.unlink(Rc::as_ptr(&entry)) };

                    assert_eq!(expected_x, actual_x);
                }
            }
        }

        // deallocate
        for p in list.iter() {
            let _ = unsafe { list.unlink(Rc::as_ptr(&p)) };
        }
    }
}
