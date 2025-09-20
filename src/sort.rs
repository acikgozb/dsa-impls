/// Determines the order of a sort operation.
///
/// This enum is currently supported in the sort algorithms below:
///
/// - Selection sort
/// - Quicksort
pub enum Order {
    Asc,
    Desc,
}

/// Sorts a slice `s` using selection sort, ordered by the given `Order`.
///
/// If there are any duplicate items in `s`, they will be put next to each other.
///
/// # Examples
///
/// Ascending sort, without any duplicates.
///
/// ```no_run
/// use dsa_impls::sort::{selection_sort, Order};
///
/// let items = [1, 5, 3, 2, 4];
/// let mut sorted = selection_sort(&items[..], Order::Asc).into_iter();
///
/// for item in [1, 2, 3, 4, 5] {
///     assert_eq!(*(sorted.next().unwrap()), item);
/// }
/// ```
///
/// Descending sort with duplicates.
///
/// ```no_run
/// use dsa_impls::sort::{selection_sort, Order};
///
/// let items = [1, 5, 3, 2, 2, 4];
/// let mut sorted = selection_sort(&items[..], Order::Desc).into_iter();
///
/// for item in [5, 4, 3, 2, 2, 1] {
///     assert_eq!(*(sorted.next().unwrap()), item);
/// }
/// ```
pub fn selection_sort<T>(s: &[T], order: Order) -> Vec<&T>
where
    T: Ord,
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

/// Sorts a slice `s` using quicksort, ordered by the given `Order`.
///
/// If there are any duplicate items in `s`, they will be put next to each other.
///
/// # Examples
///
/// Ascending sort, without any duplicates.
///
/// ```no_run
/// use dsa_impls::sort::{quicksort, Order};
///
/// let items = [1, 5, 3, 2, 4];
/// let mut sorted = quicksort(&items[..], &Order::Asc).into_iter();
///
/// for item in [1, 2, 3, 4, 5] {
///     assert_eq!(sorted.next().unwrap(), item);
/// }
/// ```
///
/// Descending sort with duplicates.
///
/// ```no_run
/// use dsa_impls::sort::{quicksort, Order};
///
/// let items = [1, 5, 3, 2, 2, 4];
/// let mut sorted = quicksort(&items[..], &Order::Desc).into_iter();
///
/// for item in [5, 4, 3, 2, 2, 1] {
///     assert_eq!(sorted.next().unwrap(), item);
/// }
/// ```
pub fn quicksort<T>(s: &[T], order: &Order) -> Vec<T>
where
    T: Ord + Copy,
{
    let s = s.to_owned();
    match s.len() {
        l if l < 2 => s,
        _ => {
            let pivot = s[0];
            let (lower, higher): (Vec<_>, Vec<_>) =
                s.into_iter().skip(1).partition(|i| *i <= pivot);

            match order {
                Order::Desc => quicksort(&higher, order)
                    .into_iter()
                    .chain([pivot])
                    .chain(quicksort(&lower, order))
                    .collect(),
                Order::Asc => quicksort(&lower, order)
                    .into_iter()
                    .chain([pivot])
                    .chain(quicksort(&higher, order))
                    .collect(),
            }
        }
    }
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
#[cfg(test)]
pub mod quicksort_tests {
    use super::{Order, quicksort};

    #[test]
    pub fn should_sort_ascending() {
        let items = [1, 5, 3, 2, 4];
        let mut sorted = quicksort(&items[..], &Order::Asc).into_iter();

        for item in [1, 2, 3, 4, 5] {
            assert_eq!(sorted.next().unwrap(), item);
        }
    }

    #[test]
    pub fn should_sort_ascending_with_dups() {
        let items = [1, 5, 3, 2, 2, 4];
        let mut sorted = quicksort(&items[..], &Order::Asc).into_iter();

        for item in [1, 2, 2, 3, 4, 5] {
            assert_eq!(sorted.next().unwrap(), item);
        }
    }

    #[test]
    pub fn should_sort_descending() {
        let items = [1, 5, 3, 2, 4];
        let mut sorted = quicksort(&items[..], &Order::Desc).into_iter();

        for item in [5, 4, 3, 2, 1] {
            assert_eq!(sorted.next().unwrap(), item);
        }
    }

    #[test]
    pub fn should_sort_descending_with_dups() {
        let items = [1, 5, 3, 2, 2, 4];
        let mut sorted = quicksort(&items[..], &Order::Desc).into_iter();

        for item in [5, 4, 3, 2, 2, 1] {
            assert_eq!(sorted.next().unwrap(), item);
        }
    }
}
