use std::{
    cmp::Ordering,
    collections::{HashMap, VecDeque},
    hash::Hash,
};

/// A basic binary search implementation.
///
/// Given a sorted `slice` and an `item`, this method returns `Some` index if the item exists in the slice. It returns `None` if item is not found.
///
/// # Examples
///
/// ```no_run
/// use dsa_impls::search::bsearch;
///
/// let vec: Vec<u8> = (1..=125).collect();
/// let mut item = 88;
/// let idx = bsearch(&vec, &item);
///
/// assert!(idx.is_some());
/// assert_eq!(vec[idx.unwrap()], item);
///
/// item = 150;
/// let idx = bsearch(&vec, &item);
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

/// Searches an item in a `graph` that satisfies `cond` via breadth-first
/// search.
///
/// The `key` is used to traverse the graph, and it is expected to get a key
/// from this closure that exists in the graph. In other words, the closure
/// should return a key that represents a valid node in the graph.
///
/// If the closure fails to satisfy this requirement, `bfs` will not be able to
/// search the entire graph and will most likely output an incorrect result.
///
/// # Examples
///
/// Searching for an existing item. The closure `key` returns the entire node.
///
/// ```no_run
/// use std::collections::HashMap;
/// use dsa_impls::search::bfs;
///
/// let graph: HashMap<&str, &[&str]> = HashMap::from([
///     ("me", ["alice", "bob", "claire"].as_slice()),
///     ("alice", ["anuj", "peggy"].as_slice()),
///     ("bob", ["peggy"].as_slice()),
///     ("peggy", ["tom", "johnny"].as_slice()),
/// ]);
///
/// let exists = bfs(&graph, &"me", |x| x, |x| *x == "tom");
/// assert!(exists);
/// ```
///
/// Searching for a non-existant item. The closure `key` returns the entire node.
///
/// ```no_run
/// use std::collections::HashMap;
/// use dsa_impls::search::bfs;
///
/// let graph: HashMap<&str, &[&str]> = HashMap::from([
///     ("me", ["alice", "bob", "claire"].as_slice()),
///     ("alice", ["anuj", "peggy"].as_slice()),
///     ("bob", ["peggy"].as_slice()),
///     ("peggy", ["tom", "johnny"].as_slice()),
/// ]);
///
/// let exists = bfs(&graph, &"me", |x| x, |x| *x == "noone");
/// assert!(!exists);
/// ```
///
/// Searching for an existing item, but the initial node is given incorrectly.
/// ```no_run
/// use std::collections::HashMap;
/// use dsa_impls::search::bfs;
///
/// let graph: HashMap<&str, &[&str]> = HashMap::from([
///     ("me", ["alice", "bob", "claire"].as_slice()),
///     ("alice", ["anuj", "peggy"].as_slice()),
///     ("bob", ["peggy"].as_slice()),
///     ("peggy", ["tom", "johnny"].as_slice()),
/// ]);
/// let exists = bfs(&graph, &"noone", |x| x, |x| *x == "tom");
/// assert!(!exists);
/// ```
///
/// Searching for an existing item, but the `key` closure is given incorrectly,
/// making `bfs` fail.
/// ```no_run
/// use std::collections::HashMap;
/// use dsa_impls::search::bfs;
///
/// let graph: HashMap<&str, &[&str]> = HashMap::from([
///     ("me", ["alice", "bob", "claire"].as_slice()),
///     ("alice", ["anuj", "peggy"].as_slice()),
///     ("bob", ["peggy"].as_slice()),
///     ("peggy", ["tom", "johnny"].as_slice()),
/// ]);
/// let exists = bfs(&graph, &"me", |_| &"noone", |x| *x == "tom");
/// assert!(!exists);
/// ```
pub fn bfs<K, V, F, C>(graph: &HashMap<K, &[V]>, start: &K, key: F, cond: C) -> bool
where
    K: Eq + Hash,
    F: Fn(&V) -> &K,
    C: Fn(&V) -> bool,
{
    let Some(s) = graph.get(start) else {
        return false;
    };
    let mut queue = VecDeque::from_iter(s.iter());

    let mut checked: HashMap<&K, bool> = HashMap::new();
    let mut found = false;

    while let Some(i) = queue.pop_front() {
        let key = key(i);
        if let Some(yes) = checked.get(key)
            && *yes
        {
            continue;
        };

        if cond(i) {
            found = true;
            break;
        }

        checked.insert(key, true);
        match graph.get(key) {
            None => continue,
            Some(v) => {
                for n in *v {
                    queue.push_back(n);
                }
            }
        }
    }

    found
}

#[cfg(test)]
mod bfs_tests {
    use super::bfs;
    use std::collections::HashMap;

    #[test]
    pub fn should_return_false_for_invalid_starts() {
        let graph: HashMap<&str, &[&str]> = HashMap::from([
            ("me", ["alice", "bob", "claire"].as_slice()),
            ("alice", ["anuj", "peggy"].as_slice()),
            ("bob", ["peggy"].as_slice()),
            ("peggy", ["tom", "johnny"].as_slice()),
        ]);

        let exists = bfs(&graph, &"noone", |x| x, |x| *x == "tom");
        assert!(!exists);
    }

    #[test]
    pub fn should_return_false() {
        let graph: HashMap<&str, &[&str]> = HashMap::from([
            ("me", ["alice", "bob", "claire"].as_slice()),
            ("alice", ["anuj", "peggy"].as_slice()),
            ("bob", ["peggy"].as_slice()),
            ("peggy", ["tom", "johnny"].as_slice()),
        ]);

        let exists = bfs(&graph, &"me", |x| x, |x| *x == "noone");
        assert!(!exists);
    }

    #[test]
    pub fn should_return_false_with_incorrect_key() {
        let graph: HashMap<&str, &[&str]> = HashMap::from([
            ("me", ["alice", "bob", "claire"].as_slice()),
            ("alice", ["anuj", "peggy"].as_slice()),
            ("bob", ["peggy"].as_slice()),
            ("peggy", ["tom", "johnny"].as_slice()),
        ]);

        let exists = bfs(&graph, &"me", |_| &"noone", |x| *x == "tom");
        assert!(!exists);
    }

    #[test]
    pub fn should_return_true() {
        let graph: HashMap<&str, &[&str]> = HashMap::from([
            ("me", ["alice", "bob", "claire"].as_slice()),
            ("alice", ["anuj", "peggy"].as_slice()),
            ("bob", ["peggy"].as_slice()),
            ("peggy", ["tom", "johnny"].as_slice()),
        ]);

        let exists = bfs(&graph, &"me", |x| x, |x| *x == "tom");
        assert!(exists);
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
