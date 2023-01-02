use std::{convert::From, fmt};

const SQUARE_SIZE: usize = 3;
const GRID_SIZE: usize = SQUARE_SIZE * SQUARE_SIZE;
const NUM_SQUARES: usize = GRID_SIZE * GRID_SIZE;

#[derive(Clone, Copy)]
pub struct Position {
    row: usize,
    col: usize,
}

impl From<(usize, usize)> for Position {
    fn from(value: (usize, usize)) -> Self {
        Self {
            row: value.0,
            col: value.1,
        }
    }
}

impl fmt::Debug for Position {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({}, {})", self.row, self.col)
    }
}

impl Position {
    /// Get the 1D position in the grid given a 2D one
    fn normalized(&self) -> usize {
        self.row * GRID_SIZE + self.col
    }
}

#[derive(Clone, Copy, PartialEq)]
pub struct Board {
    entries: [Option<u8>; NUM_SQUARES],
}

impl From<[u8; NUM_SQUARES]> for Board {
    fn from(arr: [u8; NUM_SQUARES]) -> Self {
        let mut entries: [Option<u8>; NUM_SQUARES] = [None; NUM_SQUARES];

        for (i, x) in arr.iter().enumerate() {
            match x {
                1..=9 => entries[i] = Some(*x),
                _ => (),
            }
        }

        Board { entries }
    }
}

impl fmt::Debug for Board {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "Board:")?;
        for row in 0..GRID_SIZE {
            if row % SQUARE_SIZE == 0 {
                writeln!(f, "")?;
            }
            for col in 0..GRID_SIZE {
                if col % SQUARE_SIZE == 0 {
                    write!(f, " ")?;
                }
                match self.entry((row, col).into()) {
                    Some(x) => write!(f, "{}", x)?,
                    None => write!(f, "*")?,
                }
            }
            write!(f, "\n")?;
        }
        Ok(())
    }
}

impl Board {
    /// Get the entry at a given position
    fn entry(&self, pos: Position) -> Option<u8> {
        self.entries[pos.normalized()]
    }

    /// Insert a value at a given position
    fn insert(&mut self, pos: Position, value: u8) {
        self.entries[pos.normalized()] = Some(value);
    }

    /// Get the next empty cell, if there is one
    fn next_empty_cell(&self) -> Option<Position> {
        for row in 0..GRID_SIZE {
            for col in 0..GRID_SIZE {
                if self.entry((row, col).into()).is_none() {
                    return Some(Position { row, col });
                }
            }
        }
        None
    }

    /// Return whether the puzzle has been solved
    fn is_solved(&self) -> bool {
        self.next_empty_cell().is_none()
    }

    /// Get all the possible guesses at a given position
    fn guesses(&self, pos: Position) -> Vec<u8> {
        let mut result = vec![];
        let grid_size = GRID_SIZE as u8;
        for guess in 1..=grid_size {
            if self.valid(&pos, guess) {
                result.push(guess);
            }
        }
        result
    }

    /// Creates a new board from a string representation
    pub fn new(input: &str) -> Self {
        let mut entries: [Option<u8>; NUM_SQUARES] = [None; NUM_SQUARES];
        let chars = input.chars().filter(|c| *c != '\n').take(81);
        for (i, c) in chars.enumerate() {
            match c.to_digit(10) {
                Some(x) => entries[i] = Some(x as u8),
                None => (),
            }
        }

        Self { entries }
    }

    /// Check whether a guess is valid at a given position
    pub fn valid(&self, pos: &Position, guess: u8) -> bool {
        // Check rows and columns
        for x in 0..GRID_SIZE {
            if self.entry((pos.row, x).into()) == Some(guess)
                || self.entry((x, pos.col).into()) == Some(guess)
            {
                return false;
            }
        }

        // Check box
        let x_index: usize = pos.row / SQUARE_SIZE * SQUARE_SIZE;
        let y_index: usize = pos.col / SQUARE_SIZE * SQUARE_SIZE;

        for x in 0..SQUARE_SIZE {
            for y in 0..SQUARE_SIZE {
                if self.entry((x_index + x, y_index + y).into()) == Some(guess) {
                    return false;
                }
            }
        }

        true
    }

    /// Solve the puzzle via brute-force backtracking
    pub fn solve(&self) -> Self {
        let mut result = *self;
        let empty_cell = self.next_empty_cell();

        match empty_cell {
            None => {
                // All done!
                return result;
            }
            Some(cell) => {
                for guess in self.guesses(cell) {
                    result.insert((cell.row, cell.col).into(), guess);
                    result = result.solve();
                    if result.is_solved() {
                        return result;
                    }
                }
            }
        }
        result = *self;
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse() {
        let entries: [u8; NUM_SQUARES] = [
            1, 7, 4, 0, 9, 0, 6, 0, 0, 0, 0, 0, 0, 3, 8, 1, 5, 7, 5, 3, 0, 7, 0, 1, 0, 0, 4, 0, 0,
            7, 3, 4, 9, 8, 0, 0, 8, 4, 0, 5, 0, 0, 3, 6, 0, 3, 0, 5, 0, 0, 6, 4, 7, 0, 2, 8, 6, 9,
            0, 0, 0, 0, 1, 0, 0, 0, 6, 2, 7, 0, 3, 8, 0, 5, 3, 0, 8, 0, 0, 9, 6,
        ];
        let board: Board = entries.into();
        let parsed = Board::new(include_str!("../test/board0.txt"));
        assert_eq!(board, parsed);
    }

    #[test]
    fn test_invalid() {
        let board = Board::new(include_str!("../test/board0.txt"));
        assert!(!board.valid(&Position { row: 1, col: 0 }, 4));
        assert!(!board.valid(&Position { row: 1, col: 0 }, 1));
        assert!(!board.valid(&Position { row: 1, col: 1 }, 4));
        assert!(!board.valid(&Position { row: 1, col: 2 }, 4));
        assert!(!board.valid(&Position { row: 0, col: 3 }, 4));
        assert!(!board.valid(&Position { row: 0, col: 3 }, 3));
        assert!(!board.valid(&Position { row: 6, col: 6 }, 3));
        assert!(!board.valid(&Position { row: 8, col: 6 }, 1));
    }

    #[test]
    fn test_valid() {
        let board = Board::new(include_str!("../test/board0.txt"));
        assert!(board.valid(&Position { row: 0, col: 3 }, 2));
    }

    #[test]
    fn test_solver_0() {
        let expected = Board::new(include_str!("../test/board0s.txt"));
        let board = Board::new(include_str!("../test/board0.txt"));
        let result = board.solve();
        assert_eq!(expected, result);
    }

    #[test]
    fn test_solver_1() {
        let expected = Board::new(include_str!("../test/board1s.txt"));
        let board = Board::new(include_str!("../test/board1.txt"));
        let result = board.solve();
        assert_eq!(expected, result);
    }

    #[test]
    fn test_solver_2() {
        let expected = Board::new(include_str!("../test/board2s.txt"));
        let board = Board::new(include_str!("../test/board2.txt"));
        let result = board.solve();
        assert_eq!(expected, result);
    }

    #[test]
    fn test_solver_3() {
        let expected = Board::new(include_str!("../test/board3s.txt"));
        let board = Board::new(include_str!("../test/board3.txt"));
        let result = board.solve();
        assert_eq!(expected, result);
    }
}
