use std::{cell::Cell, ptr::null, rc::Rc};

#[derive(Debug)]
pub struct Hook<Outer> {
    // Invariant: next and prev are obtained from Rc::into_raw().
    next: Cell<*const Outer>,
    prev: Cell<*const Outer>,
}

impl<Outer> Default for Hook<Outer> {
    fn default() -> Self {
        Self {
            next: Cell::new(null()),
            prev: Cell::new(null()),
        }
    }
}

pub trait Adapter {
    type Outer;
    fn hook(outer: &Self::Outer) -> &Hook<Self::Outer>;
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
    // `new_node` must not be a member of the list, or push_front panics.
    pub fn push_front(&mut self, new_node: Rc<A::Outer>) {
        self.head = unsafe { push_front::<A>(self.head, new_node) };
    }

    // Unlink `node` from the list and returns the ownership of `node`.
    //
    // # Safety
    // * `node` must be a member of this list.
    #[must_use]
    pub unsafe fn unlink(&mut self, node: &Rc<A::Outer>) -> Rc<A::Outer> {
        let (new_head, unlinked_node) = unlink::<A>(self.head, node);
        self.head = new_head;
        unlinked_node
    }

    pub fn iter(&mut self) -> impl Iterator<Item = Rc<A::Outer>> {
        if self.head.is_null() {
            return Iter::<A> { p: None };
        }

        // Rc::clone(self.head)
        // Safety: self.head is obtained from Rc::into_raw().
        let rc = unsafe {
            Rc::increment_strong_count(self.head);
            Rc::from_raw(self.head)
        };
        Iter::<A> { p: Some(rc) }
    }
}

struct Iter<A: Adapter> {
    p: Option<Rc<A::Outer>>,
}

impl<A: Adapter> Iterator for Iter<A> {
    type Item = Rc<A::Outer>;

    fn next(&mut self) -> Option<Self::Item> {
        let Some(ref p) = self.p else {
            return None;
        };

        let next = A::hook(p).next.get();
        let p_next = if next.is_null() {
            None
        } else {
            // Rc::clone(hook.next)
            // Safety: next is obtained from Rc::into_raw().
            let rc = unsafe {
                Rc::increment_strong_count(next);
                Rc::from_raw(next)
            };
            Some(rc)
        };
        std::mem::replace(&mut self.p, p_next)
    }
}

unsafe fn push_front<A: Adapter>(head: *const A::Outer, new_node: Rc<A::Outer>) -> *const A::Outer {
    if Rc::as_ptr(&new_node) == head {
        panic!("`new_node` must not be a member of a list");
    }

    let new_hook = A::hook(&new_node);

    if new_hook.next.get() != null() || new_hook.prev.get() != null() {
        panic!("`new_node` must not be a member of a list.")
    }

    if head.is_null() {
        return Rc::into_raw(new_node);
    }

    let head_hook = A::hook(unsafe { &*head });
    debug_assert_eq!(head_hook.prev.get(), null());

    new_hook.next.set(head);
    new_hook.prev.set(null());

    let new_node = Rc::into_raw(new_node);
    head_hook.prev.set(new_node);
    new_node
}

unsafe fn unlink<A: Adapter>(
    head: *const A::Outer,
    node: &Rc<A::Outer>,
) -> (*const A::Outer, Rc<A::Outer>) {
    let node_hook = A::hook(node);
    let (next, prev) = (node_hook.next.get(), node_hook.prev.get());
    if !prev.is_null() {
        let prev_hook = A::hook(unsafe { &*prev });
        prev_hook.next.set(next);
    }
    if !next.is_null() {
        let next_hook = A::hook(unsafe { &*next });
        next_hook.prev.set(prev);
    }
    node_hook.next.set(null());
    node_hook.prev.set(null());

    // `let p_node = node.as_ref() as *const _` とすると
    // `Rc::from_raw(p_node)` が undefined behavior になってしまう。
    // 必ず Rc::as_ptr を使うこと。
    let p_node = Rc::as_ptr(node);
    // Safety: node を list に push するときに Rc::into_raw している。
    //         よって、unlink の際に Rc::from_raw することで釣り合いが取れる。
    let rc = unsafe { Rc::from_raw(p_node) };
    if p_node == head {
        (next, rc)
    } else {
        (head, rc)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::VecDeque;

    #[derive(Debug, Default)]
    struct Entry {
        x: i64,
        hook: Hook<Entry>,
    }

    struct EntryAdapter;
    impl Adapter for EntryAdapter {
        type Outer = Entry;
        fn hook(outer: &Self::Outer) -> &Hook<Self::Outer> {
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
            list.push_front(entry);
        }
        for p in list.iter() {
            println!("{}", p.x);
            // deallocate
            let _ = unsafe { list.unlink(&p) };
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
                    list.push_front(new_entry);
                }
                Action::Unlink(idx) => {
                    let expected_x = expected.remove(idx).unwrap();

                    let entry = list.iter().nth(idx).unwrap();
                    let actual_x = entry.x;

                    let _ = unsafe { list.unlink(&entry) };

                    assert_eq!(expected_x, actual_x);
                }
            }
        }

        // deallocate
        for p in list.iter() {
            let _ = unsafe { list.unlink(&p) };
        }
    }
}
