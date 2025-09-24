use std::ptr::NonNull;

#[derive(Debug)]
struct Node<T> {
    data: T,
    next: Option<*mut Node<T>>,
    prev: Option<*mut Node<T>>,
}

#[derive(Default, Debug)]
pub struct LinkedList<T> {
    start: Option<*mut Node<T>>,
    end: Option<*mut Node<T>>,
}

impl<T> LinkedList<T> {
    pub fn new() -> Self {
        Self {
            start: None,
            end: None,
        }
    }

    pub fn push_end(&mut self, data: T) {
        let node = Box::new(Node {
            data,
            next: None,
            prev: self.end,
        });

        let ptr = Box::into_raw(node);

        if self.start.is_none() {
            self.start = Some(ptr);
        }

        if let Some(prev) = self.end.take() {
            // SAFETY:
            // Since a `Node` is wrapped with `Option`, `Some` always contains
            // a valid `Node` pointer that can be dereferenced as expected. The
            // insertion/deletion methods guarantee this behavior.
            unsafe {
                (*prev).next = Some(ptr);
            }
        };

        self.end = Some(ptr);
    }

    pub fn pop_end(&mut self) -> Option<T> {
        self.end
            .take()
            // SAFETY:
            // Since `Some` always contains a valid `Node` pointer,
            // and the pointer was previously obtained from a `Box`,
            // it is safe to re-create the `Box` through it's raw pointer
            // to own and drop it when we're done.
            //
            // The possibility of a dangling pointer after the drop is handled
            // by setting the start and end of the list appropriately, to
            // prevent accessing the underlying memory in other parts of the
            // program.
            .map(|ptr| unsafe { Box::from_raw(ptr) })
            .map(|b| {
                match b.prev {
                    // SAFETY:
                    // Since `Some` always contains a valid `Node` pointer,
                    // it is safe to dereference the raw pointer.
                    Some(ptr) => unsafe {
                        (*ptr).next = None;
                        self.end = Some(ptr);
                    },
                    None => {
                        self.start = None;
                        self.end = None;
                    }
                }

                Some(b.data)
            })?
    }

    pub fn pop_start(&mut self) -> Option<T> {
        self.start
            .take()
            // SAFETY:
            // Since `Some` always contains a valid `Node` pointer,
            // and the pointer was previously obtained from a `Box`,
            // it is safe to re-create the `Box` through it's raw pointer
            // to own and drop it when we're done.
            //
            // The possibility of a dangling pointer after the drop is handled
            // by setting the start and end of the list appropriately, to
            // prevent accessing the underlying memory in other parts of the
            // program.
            .map(|ptr| unsafe { Box::from_raw(ptr) })
            .map(|b| {
                match b.next {
                    // SAFETY:
                    // Since `Some` always contains a valid `Node` pointer,
                    // it is safe to dereference the raw pointer.
                    Some(ptr) => unsafe {
                        (*ptr).prev = None;
                        self.start = Some(ptr);
                    },
                    None => {
                        self.start = None;
                        self.end = None;
                    }
                }
                Some(b.data)
            })?
    }

    pub fn push_start(&mut self, data: T) {
        let node = Box::new(Node {
            data,
            next: self.start,
            prev: None,
        });
        let ptr = Box::into_raw(node);

        if let Some(old_start) = self.start {
            unsafe {
                (*old_start).prev = Some(ptr);
            }
        }

        self.start = Some(ptr);

        if self.end.is_none() {
            self.end = Some(ptr);
        }
    }

    pub fn end(&self) -> Option<&T> {
        let end = self.end?;
        // SAFETY:
        // Since the end `Node` is wrapped with `Option`, `Some` always
        // contains a valid `Node`. This is guaranteed by the insertion/deletion
        // methods.
        // `.data` does not try to read from uninitialized memory.
        Some(unsafe { &(*end).data })
    }

    pub fn start(&self) -> Option<&T> {
        let start = self.start?;

        // SAFETY:
        // Since the start `Node` is wrapped with `Option`, `Some` always
        // contains a valid `Node`. This is guaranteed by the insertion/deletion
        // methods.
        // `.data` does not try to read from uninitialized memory.
        Some(unsafe { &(*start).data })
    }
}

impl<T> Drop for LinkedList<T> {
    fn drop(&mut self) {
        if let Some(start) = self.start.take() {
            let mut curr_node = start;
            loop {
                // SAFETY:
                // Since a `Node` is wrapped with `Option`, `ptr` always points
                // to a valid, non-null Node instance. This is guaranteed by
                // insertion/deletion methods.
                // `.next` does not try to read from uninitialied memory.
                let next_node = unsafe { (*curr_node).next };

                // SAFETY:
                // The pointer is dropped once and is not used after being
                // dropped, making this operation safe to execute.
                unsafe {
                    drop(Box::from_raw(curr_node));
                }

                match next_node {
                    Some(n) => curr_node = n,
                    None => break,
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::LinkedList;

    #[test]
    pub fn should_push_end() {
        let i1 = 5;
        let i2 = 10;
        let i3 = 15;

        let mut list: LinkedList<u8> = LinkedList::new();
        list.push_end(i1);
        list.push_end(i2);
        list.push_end(i3);

        let start = list.start();
        let end = list.end();

        assert!(start.is_some());
        assert!(end.is_some());
        assert_eq!(start.unwrap(), &i1);
        assert_eq!(end.unwrap(), &i3);
    }

    #[test]
    pub fn should_push_start() {
        let i1 = 5;
        let i2 = 10;
        let i3 = 15;

        let mut list: LinkedList<u8> = LinkedList::new();
        list.push_start(i1);
        list.push_start(i2);
        list.push_start(i3);

        let start = list.start();
        let end = list.end();

        assert!(start.is_some());
        assert!(end.is_some());
        assert_eq!(start.unwrap(), &i3);
        assert_eq!(end.unwrap(), &i1);
    }

    #[test]
    pub fn should_pop_end_some() {
        let i1 = 5;
        let i2 = 10;
        let i3 = 15;

        let mut list: LinkedList<u8> = LinkedList::new();
        list.push_end(i1);
        list.push_end(i2);
        list.push_end(i3);

        let end = list.pop_end();

        assert!(end.is_some());
        assert_eq!(end.unwrap(), i3);
    }

    #[test]
    pub fn should_pop_end_none() {
        let mut list: LinkedList<u8> = LinkedList::new();
        let end = list.pop_end();

        assert!(end.is_none());
    }

    #[test]
    pub fn should_pop_start_some() {
        let i1 = 5;
        let i2 = 10;
        let i3 = 15;

        let mut list: LinkedList<u8> = LinkedList::new();
        list.push_end(i1);
        list.push_end(i2);
        list.push_end(i3);

        let end = list.pop_start();

        assert!(end.is_some());
        assert_eq!(end.unwrap(), i1);
    }

    #[test]
    pub fn should_pop_start_none() {
        let mut list: LinkedList<u8> = LinkedList::new();
        let end = list.pop_start();

        assert!(end.is_none());
    }
}
