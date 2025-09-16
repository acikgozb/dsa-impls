/// Determines the order of a sort operation.
///
/// This enum is currently supported in the sort algorithms below:
///
/// - Selection sort
pub enum Order {
    Asc,
    Desc,
}

/// Sorts a slice `s` using selection sort, ordered by the given `Order`.
///
/// If there are any duplicate items, they will be put next to each other.
///
/// # Examples
///
/// Ascending sort, without any duplicates.
///
/// ```no_run
///    let items = [1, 5, 3, 2, 4];
///    let mut sorted = selection_sort(&items[..], Order::Asc).into_iter();
///
///    for item in [1, 2, 3, 4, 5] {
///        assert_eq!(*(sorted.next().unwrap()), item);
///    }
/// ```
///
/// Descending sort with duplicates.
///
/// ```no_run
///     let items = [1, 5, 3, 2, 2, 4];
///     let mut sorted = selection_sort(&items[..], Order::Desc).into_iter();
///
///     for item in [5, 4, 3, 2, 2, 1] {
///         assert_eq!(*(sorted.next().unwrap()), item);
///     }
/// ```
pub fn selection_sort<T>(s: &[T], order: Order) -> Vec<&T>
where
    T: Ord + std::fmt::Debug,
{
    let mut vec: Vec<&T> = Vec::with_capacity(s.len());
    let mut sorted_idxs: Vec<bool> = vec![false; s.len()];

    loop {
        let mut iter = s.iter().enumerate().filter(|(i, _)| !sorted_idxs[*i]);
        let next = iter.next();
        if next.is_none() {
            break;
        }

        let mut next_idx = next.unwrap().0;
        let mut next_item = next.unwrap().1;

        for (i, item) in iter {
            let should_switch = match order {
                Order::Asc => item < next_item,
                Order::Desc => item > next_item,
            };

            if should_switch {
                next_item = item;
                next_idx = i;
            }
        }

        vec.push(next_item);
        sorted_idxs[next_idx] = true;
    }

    vec
}

#[cfg(test)]
pub mod selection_sort_tests {
    use super::{Order, selection_sort};

    #[test]
    pub fn should_sort_ascending() {
        let items = [1, 5, 3, 2, 4];
        let mut sorted = selection_sort(&items[..], Order::Asc).into_iter();

        for item in [1, 2, 3, 4, 5] {
            assert_eq!(*(sorted.next().unwrap()), item);
        }
    }

    #[test]
    pub fn should_sort_ascending_with_dups() {
        let items = [1, 5, 3, 2, 2, 4];
        let mut sorted = selection_sort(&items[..], Order::Asc).into_iter();

        for item in [1, 2, 2, 3, 4, 5] {
            assert_eq!(*(sorted.next().unwrap()), item);
        }
    }

    #[test]
    pub fn should_sort_descending() {
        let items = [1, 5, 3, 2, 4];
        let mut sorted = selection_sort(&items[..], Order::Desc).into_iter();

        for item in [5, 4, 3, 2, 1] {
            assert_eq!(*(sorted.next().unwrap()), item);
        }
    }

    #[test]
    pub fn should_sort_descending_with_dups() {
        let items = [1, 5, 3, 2, 2, 4];
        let mut sorted = selection_sort(&items[..], Order::Desc).into_iter();

        for item in [5, 4, 3, 2, 2, 1] {
            assert_eq!(*(sorted.next().unwrap()), item);
        }
    }
}
