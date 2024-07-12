use std::fmt;
use std::hash::Hash;

/// Transform an offset to a row-column location.
pub trait HasPosition {
    fn position_at(&self, offset: usize) -> Position;
}

impl HasPosition for &str {
    fn position_at(&self, offset: usize) -> Position {
        let mut line = 1;
        let mut column = 1;
        for (i, c) in self.chars().enumerate() {
            if i == offset {
                break;
            }
            if c == '\n' {
                line += 1;
                column = 1;
            } else {
                column += 1;
            }
        }
        Position::new(line, column)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Copy, Hash)]
pub struct Position {
    pub line: usize,
    pub column: usize,
}

impl Position {
    pub fn new(line: usize, column: usize) -> Position {
        Position { line, column }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Copy, Hash)]
pub struct Span {
    pub start: Position,
    pub end: Position,
}

impl Span {
    pub fn new(start: Position, end: Position) -> Span {
        Span { start, end }
    }

    pub fn join(&self, another: &Span) -> Span {
        Span {
            start: self.start,
            end: another.end,
        }
    }
}

/// Items with a location range.
pub struct Located<T> {
    item: T,
    span: Span,
}

impl<T> Located<T> {
    pub fn new(t: T, span: Span) -> Located<T> {
        Located { item: t, span }
    }

    pub fn no_loc(t: T) -> Located<T> {
        Located {
            item: t,
            span: Span::new(Position::new(0, 0), Position::new(0, 0)),
        }
    }

    pub fn unwrap(self) -> T {
        self.item
    }

    pub fn span(&self) -> Span {
        self.span
    }

    pub fn inner(&self) -> &T {
        &self.item
    }

    pub fn map_inner<R, F: Fn(T) -> R>(self, func: F) -> Located<R> {
        Located {
            item: func(self.item),
            span: self.span,
        }
    }

    pub fn mut_inner(&mut self) -> &mut T {
        &mut self.item
    }
}

/// `Located<T>::eq` only considers the item's equality.
impl<T: PartialEq> PartialEq for Located<T> {
    fn eq(&self, other: &Located<T>) -> bool {
        self.item == other.item
    }
}

impl<T: Eq> Eq for Located<T> {}

impl<T: fmt::Display> fmt::Display for Located<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.item.fmt(f)
    }
}

impl<T: fmt::Debug> fmt::Debug for Located<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.item.fmt(f)
    }
}

impl<T: Clone> Clone for Located<T> {
    fn clone(&self) -> Self {
        Located {
            item: self.item.clone(),
            span: self.span,
        }
    }
}

/// `Located<T>::hash` only considers the item's hash.
impl<T: Hash> Hash for Located<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.item.hash(state);
    }
}
