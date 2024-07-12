//! Sorts are another name that SMT-LIB gives to types. They can be either ground or with un-instantiated generic parameters.

use super::KRPKGroundSort;

use std::fmt::{self, Debug, Formatter};
use std::hash::{Hash, Hasher};

/// A semantic object with a sort.
pub struct Sorted<T> {
    pub item: T,
    pub sort: Option<KRPKGroundSort>,
}

impl<T> Sorted<T> {
    pub fn new(item: T) -> Self {
        Sorted { item, sort: None }
    }

    pub fn with_sort(item: T, sort: KRPKGroundSort) -> Self {
        Sorted {
            item,
            sort: Some(sort),
        }
    }

    pub fn inner(&self) -> &T {
        &self.item
    }

    pub fn unwrap(self) -> T {
        self.item
    }

    pub fn sort(&self) -> &Option<KRPKGroundSort> {
        &self.sort
    }

    pub fn map_inner<R>(self, func: impl Fn(T) -> R) -> Sorted<R> {
        Sorted {
            item: func(self.item),
            sort: self.sort,
        }
    }
}

impl<T: Clone> Sorted<T> {
    pub(super) fn create_sorted(&self, sort: KRPKGroundSort) -> Sorted<T> {
        Self::with_sort(self.item.clone(), sort)
    }
}

impl<T: Debug> Debug for Sorted<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{:?} : {:?}", self.item, self.sort)
    }
}

impl<T: PartialEq> PartialEq for Sorted<T> {
    fn eq(&self, other: &Sorted<T>) -> bool {
        self.item == other.item && self.sort == other.sort
    }
}

impl<T: Eq> Eq for Sorted<T> {}

impl<T: fmt::Display> fmt::Display for Sorted<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.item.fmt(f)
    }
}

impl<T: Clone> Clone for Sorted<T> {
    fn clone(&self) -> Self {
        Sorted {
            item: self.item.clone(),
            sort: self.sort.clone(),
        }
    }
}

impl<T: Hash> Hash for Sorted<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.item.hash(state);
        self.sort.hash(state);
    }
}
