use std::ptr::NonNull;

#[derive(Debug)]
struct Node<'a, T> {
    data: &'a T,
    next: Option<NonNull<Node<'a, T>>>,
}

#[derive(Default, Debug)]
pub struct LinkedList<'a, T> {
    start: Option<NonNull<Node<'a, T>>>,
    end: Option<NonNull<Node<'a, T>>>,
}

impl<'a, T> LinkedList<'a, T> {
    pub fn new() -> Self {
        Self {
            start: None,
            end: None,
        }
    }

    pub fn end(&self) -> Option<&T> {
        let end = self.end?;
        // SAFETY:
        // Since the end `Node` is wrapped with `Option`, `Some` always
        // contains a valid `Node`.
        // `.data` does not try to read from uninitialized memory, making this
        // operation safe to execute.
        Some(unsafe { (end.as_ref()).data })
    }
}

impl<'a, T> LinkedList<'a, T> {
    pub fn push_end(&mut self, data: &'a T) {
        let node = Box::new(Node { data, next: None });
        let ptr = NonNull::from(Box::leak(node));

        if self.start.is_none() {
            self.start = Some(ptr);
        }

        if let Some(mut prev) = self.end.take() {
            // SAFETY:
            // Since a `Node` is wrapped with `Option`, `Some` always contains
            // a valid `Node` pointer that can be converted into a reference,
            // making this operation safe to execute.
            unsafe {
                let prev_ptr = prev.as_mut();
                prev_ptr.next = Some(ptr);
            }
        };

        self.end = Some(ptr);
    }
}

impl<'a, T> Drop for LinkedList<'a, T> {
    fn drop(&mut self) {
        if let Some(start) = self.start.take() {
            let mut curr_node = start;
            loop {
                let ptr = curr_node.as_ptr();

                // SAFETY:
                // Since a `Node` is wrapped with `Option`, `ptr` always points
                // to a valid, non-null Node instance.
                // `.next` does not try to read from uninitialied memory,
                // making this operation safe to execute.
                let next_node = unsafe { (*ptr).next };

                // SAFETY:
                // The pointer is dropped once and is not used after being
                // dropped, making this operation safe to execute.
                unsafe {
                    drop(Box::from_raw(ptr));
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
        list.push_end(&i1);
        list.push_end(&i2);
        list.push_end(&i3);

        let last_item = list.end();
        assert_eq!(last_item.unwrap(), &i3);
    }
}
