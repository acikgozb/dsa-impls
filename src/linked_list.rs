use std::marker::PhantomData;

/// Represents each node of a `LinkedList`.
#[derive(Debug)]
struct Node<T> {
    data: T,
    next: Option<*mut Node<T>>,
    prev: Option<*mut Node<T>>,
}

/// Represents a basic doubly linked list.
///
/// This structure is not thread-safe.
///
/// A `LinkedList` allows insertion and removal of elements
/// in constant time. However, it does not have random search capabilities of
/// container structs like `Vec`.
///
/// Therefore, prefer using `Vec` or any other container structs for search-
/// heavy logic.
/// They do not force sequential search and make better use of CPU cache.
#[derive(Default, Debug)]
pub struct LinkedList<T> {
    start: Option<*mut Node<T>>,
    end: Option<*mut Node<T>>,
}

impl<T> LinkedList<T> {
    /// Creates a new `LinkedList`.
    pub fn new() -> Self {
        Self {
            start: None,
            end: None,
        }
    }

    /// Creates an `Iterator` that can be used to traverse `LinkedList`.
    /// The provided iterator only yields references to the data from front to
    /// back.
    ///
    /// # Examples
    ///
    /// ```
    /// use dsa_impls::linked_list::LinkedList;
    ///
    /// let mut list: LinkedList<u8> = LinkedList::new();
    /// list.push_end(1);
    /// list.push_end(2);
    /// list.push_end(3);
    ///
    /// let mut iter = list.iter();
    ///
    /// assert_eq!(iter.next(), Some(&1));
    /// assert_eq!(iter.next(), Some(&2));
    /// assert_eq!(iter.next(), Some(&3));
    /// assert_eq!(iter.next(), None);
    /// ```
    pub fn iter(&self) -> Iter<'_, T> {
        Iter {
            start: self.start,
            phantom: PhantomData,
        }
    }

    /// Creates an `Iterator` that can be used to traverse `LinkedList`.
    /// The provided iterator only yields mutable borrows to the data from
    /// front to back.
    ///
    /// # Examples
    ///
    /// ```
    /// use dsa_impls::linked_list::LinkedList;
    ///
    /// let mut list: LinkedList<u8> = LinkedList::new();
    /// list.push_end(1);
    /// list.push_end(2);
    /// list.push_end(3);
    ///
    /// for item in list.iter_mut() {
    ///     *item *= 2;
    /// }
    ///
    /// let mut iter = list.iter();
    /// assert_eq!(iter.next(), Some(&2));
    /// assert_eq!(iter.next(), Some(&4));
    /// assert_eq!(iter.next(), Some(&6));
    /// assert_eq!(iter.next(), None);
    /// ```
    pub fn iter_mut(&mut self) -> IterMut<'_, T> {
        IterMut {
            start: self.start,
            phantom: PhantomData,
        }
    }

    /// Add a new element to the end of the `LinkedList`.
    ///
    /// # Examples
    ///
    /// ```
    /// use dsa_impls::linked_list::LinkedList;
    ///
    /// let mut list: LinkedList<u8> = LinkedList::new();
    /// list.push_end(1);
    /// list.push_end(2);
    /// list.push_end(3);
    ///
    /// let end = list.end();
    /// assert_eq!(end, Some(&3));
    /// ```
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

    /// Removes an element from the end of the `LinkedList`.
    ///
    /// # Examples
    ///
    /// ```
    /// use dsa_impls::linked_list::LinkedList;
    ///
    /// let mut list: LinkedList<u8> = LinkedList::new();
    /// list.push_end(1);
    /// list.push_end(2);
    /// list.push_end(3);
    ///
    /// let popped = list.pop_end();
    /// let end = list.end();
    ///
    /// assert_eq!(popped, Some(3));
    /// assert_eq!(end, Some(&2));
    /// ```
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

    /// Removes an element from the start of the `LinkedList`.
    ///
    /// # Examples
    ///
    /// ```
    /// use dsa_impls::linked_list::LinkedList;
    ///
    /// let mut list: LinkedList<u8> = LinkedList::new();
    /// list.push_end(1);
    /// list.push_end(2);
    /// list.push_end(3);
    ///
    /// let popped = list.pop_start();
    /// let start = list.start();
    ///
    /// assert_eq!(popped, Some(1));
    /// assert_eq!(start, Some(&2));
    /// ```
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

    /// Adds a new element to the beginning of the `LinkedList`.
    ///
    /// # Examples
    ///
    /// ```
    /// use dsa_impls::linked_list::LinkedList;
    ///
    /// let mut list: LinkedList<u8> = LinkedList::new();
    /// list.push_start(1);
    /// list.push_start(2);
    /// list.push_start(3);
    ///
    /// let start = list.start();
    /// assert_eq!(start, Some(&3));
    /// ```
    pub fn push_start(&mut self, data: T) {
        let node = Box::new(Node {
            data,
            next: self.start,
            prev: None,
        });
        let ptr = Box::into_raw(node);

        if let Some(old_start) = self.start {
            // SAFETY:
            // Since `Some` always contains a valid `Node` pointer,
            // it is safe to dereference the raw pointer here.
            unsafe {
                (*old_start).prev = Some(ptr);
            }
        }

        self.start = Some(ptr);

        if self.end.is_none() {
            self.end = Some(ptr);
        }
    }

    /// Provides a reference to the last item of the `LinkedList`.
    ///
    /// # Examples
    ///
    /// ```
    /// use dsa_impls::linked_list::LinkedList;
    ///
    /// let mut list: LinkedList<u8> = LinkedList::new();
    /// list.push_end(1);
    /// list.push_end(2);
    /// list.push_end(3);
    ///
    /// let end = list.end();
    /// assert_eq!(end, Some(&3));
    /// ```
    pub fn end(&self) -> Option<&T> {
        let end = self.end?;
        // SAFETY:
        // Since the end `Node` is wrapped with `Option`, `Some` always
        // contains a valid `Node`. This is guaranteed by the insertion/deletion
        // methods.
        // `.data` does not try to read from uninitialized memory.
        Some(unsafe { &(*end).data })
    }

    /// Provides a reference to the first item of the `LinkedList`.
    ///
    /// # Examples
    ///
    /// ```
    /// use dsa_impls::linked_list::LinkedList;
    ///
    /// let mut list: LinkedList<u8> = LinkedList::new();
    /// list.push_end(1);
    /// list.push_end(2);
    /// list.push_end(3);
    ///
    /// let start = list.start();
    /// assert_eq!(start, Some(&1));
    /// ```
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

impl<T> IntoIterator for LinkedList<T> {
    type Item = T;

    type IntoIter = IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter { list: self }
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

/// `Iter` provides sequential, readonly search on a `LinkedList`.
pub struct Iter<'a, T> {
    start: Option<*mut Node<T>>,
    phantom: PhantomData<&'a T>,
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        let curr = self.start?;

        // SAFETY:
        // - `curr` is a valid raw `Node` pointer if it is `Some`.
        // This is guaranteed by insertion and deletion methods.
        // - Since `Node` is allocated on the heap, and the lifetimes are
        // tied to `LinkedList` through `PhantomData`, it is safe to return a
        // reference to `.data`.
        let (data, next) = unsafe {
            let n = &(*curr);
            (&n.data, n.next)
        };
        self.start = next;

        Some(data)
    }
}

/// `IntoIter` provides sequential, owned search on a `LinkedList`.
pub struct IntoIter<T> {
    list: LinkedList<T>,
}

impl<T> Iterator for IntoIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        self.list.pop_start()
    }
}

/// `IterMut` provides sequential, mutable search on a `LinkedList`.
pub struct IterMut<'a, T> {
    start: Option<*mut Node<T>>,
    phantom: PhantomData<&'a T>,
}

impl<'a, T> Iterator for IterMut<'a, T> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<Self::Item> {
        let curr = self.start?;

        // SAFETY:
        // - `curr` is a valid raw `Node` pointer if it is `Some`.
        // This is guaranteed by insertion and deletion methods.
        // - Since `Node` is allocated on the heap, and the lifetimes are
        // tied to `LinkedList` through `PhantomData`, it is safe to return a
        // mutable borrow to `.data`.
        let (data, next) = unsafe {
            let n = &mut (*curr);
            (&mut n.data, n.next)
        };

        self.start = next;
        Some(data)
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

    #[test]
    pub fn should_be_into_iterable() {
        let items: [u8; 3] = [5, 10, 15];

        let mut list: LinkedList<u8> = LinkedList::new();
        for expected in items.into_iter() {
            list.push_end(expected);
        }

        let mut iter = items.into_iter();
        for actual in list.into_iter() {
            assert_eq!(iter.next().unwrap(), actual);
        }
    }

    #[test]
    pub fn should_be_iterable() {
        let items: [u8; 3] = [5, 10, 15];

        let mut list: LinkedList<u8> = LinkedList::new();
        for expected in items {
            list.push_end(expected);
        }

        let mut iter = items.iter();
        for actual in list.iter() {
            assert_eq!(iter.next().unwrap(), actual);
        }
    }

    #[test]
    pub fn should_be_mut_iterable() {
        let items: [u8; 3] = [5, 10, 15];

        let mut list: LinkedList<u8> = LinkedList::new();
        for expected in items {
            list.push_end(expected);
        }

        for item in list.iter_mut() {
            *item *= 2;
        }

        let mut iter = items.iter();
        for actual in list.iter() {
            assert_eq!(iter.next().unwrap() * 2, *actual);
        }
    }
}
