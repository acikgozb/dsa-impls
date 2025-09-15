use std::cmp::Ordering;

/// A basic binary search implementation.
///
/// Given a sorted `slice` and an `item`, this method returns `Some` index if the item exists in the slice. It returns `None` if item is not found.
///
/// # Examples
///
/// ```no_run
/// let vec: Vec<u8> = (1..=125).collect();
/// let mut item = 88;
/// let idx = bsearch(&vec, &item);
///
/// assert!(idx.is_some());
/// assert_eq!(vec[idx.unwrap()], item);
///
/// item = 150;
/// let idx = bsearch(&vec, item);
/// assert!(idx.is_none());
/// ```
pub fn bsearch<T>(slice: &[T], item: &T) -> Option<usize>
where
    T: Ord,
{
    let mut low = 0;
    let mut high = slice.len() - 1;

    loop {
        let mid = (low + high) / 2;
        match slice[mid].cmp(item) {
            Ordering::Equal => break Some(mid),
            Ordering::Less => {
                low = mid + 1;
            }
            Ordering::Greater => {
                high = mid - 1;
            }
        }

        if low > high {
            break None;
        }
    }
}

#[cfg(test)]
mod bsearch_tests {
    use super::*;

    #[test]
    pub fn should_return_some() {
        let vec: Vec<u8> = (1..=125).collect();
        let item = 88;
        let idx = bsearch(&vec, &item);

        assert!(idx.is_some());
        assert_eq!(vec[idx.unwrap()], item);
    }

    #[test]
    pub fn should_return_none() {
        let vec: Vec<u8> = (1..=125).collect();
        let item = 130;
        let idx = bsearch(&vec, &item);

        assert!(idx.is_none());
    }
}
