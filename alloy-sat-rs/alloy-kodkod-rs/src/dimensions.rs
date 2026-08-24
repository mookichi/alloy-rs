#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Dimensions {
    dims: Vec<u32>,
}

#[derive(Debug, thiserror::Error)]
pub enum DimsError {
    #[error("invalid dimension size {0}")]
    InvalidSize(u32),
    #[error("matrix needs at least one dimension")]
    Empty,
    #[error("matrix capacity exceeds addressable space")]
    TooLarge,
    #[error("dot product requires inner dimensions to match: {left} vs {right}")]
    DotMismatch { left: u32, right: u32 },
    #[error("dot product collapses to zero dimensions")]
    DotEmpty,
    #[error("transpose needs exactly two dimensions but got {0}")]
    TransposeNeeds2D(u32),
    #[error("index {0} out of range")]
    IndexOutOfRange(u64),
}

fn checked_capacity(dims: &[u32]) -> Result<usize, DimsError> {
    dims.iter()
        .try_fold(1usize, |acc, &d| acc.checked_mul(d as usize))
        .ok_or(DimsError::TooLarge)
}

impl Dimensions {
    pub fn square(size: u32, n: u32) -> Result<Dimensions, DimsError> {
        if n < 1 {
            return Err(DimsError::Empty);
        }
        if size < 1 {
            return Err(DimsError::InvalidSize(size));
        }
        let dims = vec![size; n as usize];
        checked_capacity(&dims)?;
        Ok(Dimensions { dims })
    }

    pub fn rectangular(dims: &[u32]) -> Result<Dimensions, DimsError> {
        if dims.is_empty() {
            return Err(DimsError::Empty);
        }
        if let Some(&d) = dims.iter().find(|&&d| d < 1) {
            return Err(DimsError::InvalidSize(d));
        }
        checked_capacity(dims)?;
        Ok(Dimensions {
            dims: dims.to_vec(),
        })
    }

    pub fn num_dimensions(&self) -> usize {
        self.dims.len()
    }

    pub fn dimension(&self, i: usize) -> Option<u32> {
        self.dims.get(i).copied()
    }

    pub fn capacity(&self) -> usize {
        self.dims.iter().map(|&d| d as usize).product()
    }

    pub fn is_square(&self) -> bool {
        self.dims.iter().all(|&d| d == self.dims[0])
    }

    pub fn dot(&self, other: &Dimensions) -> Result<Dimensions, DimsError> {
        let n0 = self.num_dimensions();
        let n1 = other.num_dimensions();
        let drop = other.dimension(0).ok_or(DimsError::DotEmpty)?;
        if n0 + n1 < 3 || self.dimension(n0 - 1) != Some(drop) {
            return Err(DimsError::DotMismatch {
                left: self.dimension(n0 - 1).unwrap_or(0),
                right: drop,
            });
        }
        let mut dims = Vec::with_capacity(n0 + n1 - 2);
        dims.extend_from_slice(&self.dims[..n0 - 1]);
        dims.extend_from_slice(&other.dims[1..]);
        checked_capacity(&dims)?;
        Ok(Dimensions { dims })
    }

    pub fn cross(&self, other: &Dimensions) -> Result<Dimensions, DimsError> {
        let mut dims = Vec::with_capacity(self.num_dimensions() + other.num_dimensions());
        dims.extend_from_slice(&self.dims);
        dims.extend_from_slice(&other.dims);
        checked_capacity(&dims)?;
        Ok(Dimensions { dims })
    }

    pub fn transpose(&self) -> Result<Dimensions, DimsError> {
        if self.num_dimensions() != 2 {
            return Err(DimsError::TransposeNeeds2D(self.num_dimensions() as u32));
        }
        Ok(Dimensions {
            dims: vec![self.dims[1], self.dims[0]],
        })
    }

    pub fn validate_flat(&self, index: usize) -> bool {
        index < self.capacity()
    }

    pub fn validate_vector(&self, index: &[u32]) -> bool {
        index.len() == self.dims.len()
            && index
                .iter()
                .zip(&self.dims)
                .all(|(&i, &d)| (i as usize) < d as usize)
    }

    pub fn vector_of(&self, index: usize) -> Option<Vec<u32>> {
        if !self.validate_flat(index) {
            return None;
        }
        let mut factor = self.capacity();
        let mut remainder = index;
        let mut out = vec![0u32; self.dims.len()];
        for (i, &d) in self.dims.iter().enumerate() {
            factor /= d as usize;
            out[i] = (remainder / factor) as u32;
            remainder %= factor;
        }
        Some(out)
    }

    pub fn flat_of(&self, vector: &[u32]) -> Option<usize> {
        if !self.validate_vector(vector) {
            return None;
        }
        let mut factor = self.capacity();
        let mut idx = 0usize;
        for (&v, &d) in vector.iter().zip(&self.dims) {
            factor /= d as usize;
            idx += factor * v as usize;
        }
        Some(idx)
    }
}
