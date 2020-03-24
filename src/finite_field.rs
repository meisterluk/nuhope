use std::cmp;
use std::fmt;
use std::usize;
use std::cell::RefCell;
use std::ops::{Add,Sub,Mul,Index,IndexMut};

#[derive(Debug, PartialEq, Eq)]
pub struct FiniteField {
    pub size: u32,
}

impl FiniteField {
    pub fn new(field_size: u32) -> FiniteField {
        FiniteField { size: field_size }
    }

    pub fn element(&self, init: u32) -> FiniteFieldElement {
        FiniteFieldElement::new(self.size, init)
    }

    pub fn polynomial(&self, init: Vec<FiniteFieldElement>) -> FiniteFieldPolynomial {
        FiniteFieldPolynomial::new(self.size, init)
    }
}

impl fmt::Display for FiniteField {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        write!(formatter, "ℤ_{}", self.size)
    }
}

#[derive(Copy,Clone,Debug,PartialEq,Eq)]
pub struct FiniteFieldElement {
    field_size: u32,
    val: u32,
}

impl FiniteFieldElement {
    pub fn new(field_size: u32, value: u32) -> FiniteFieldElement {
        FiniteFieldElement { field_size: field_size, val: value % field_size }
    }

    pub fn field(&self) -> FiniteField {
        FiniteField { size: self.field_size }
    }

    /// Modular exponentiation, based on Rob Cobb's https://rob.co.bb/posts/2019-02-10-modular-exponentiation-in-rust/
    pub fn pow(&self, mut exp: u32) -> FiniteFieldElement {
        if self.field_size == 1 { return FiniteFieldElement::new(self.field_size, 0) }
        let mut result = 1;
        let mut base = self.val;
        while exp > 0 {
            if exp % 2 == 1 {
                result = (result * base) % self.field_size;
            }
            exp = exp >> 1;
            base = base * base % self.field_size
        }
        FiniteFieldElement::new(self.field_size, result)
    }

    /// Returns the multiplicative inverse of val
    pub fn mul_inv(&self) -> Option<FiniteFieldElement> {
        for candidate in 2..self.field_size {
            if (self.val * candidate) % self.field_size == 1 {
                return Some(FiniteFieldElement::new(self.field_size, candidate));
            }
        }
        None
    }
}

impl Add for FiniteFieldElement {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        return FiniteFieldElement{
            field_size: self.field_size,
            val: (self.val + rhs.val) % self.field_size,
        };
    }
}

impl Sub for FiniteFieldElement {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        return FiniteFieldElement{
            field_size: self.field_size,
            val: (self.field_size + self.val - rhs.val) % self.field_size,
        };
    }
}

impl Mul for FiniteFieldElement {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        return FiniteFieldElement{
            field_size: self.field_size,
            val: (self.val * rhs.val) % self.field_size,
        };
    }
}

impl fmt::Display for FiniteFieldElement {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        write!(formatter, "{} in ℤ_{}", self.val, self.field_size)
    }
}

#[derive(Eq)]
pub struct FiniteFieldPolynomial {
    field_size: u32,
    coefficients: RefCell<Vec<FiniteFieldElement>>,
}

/// FiniteFieldPolynomial implements a polynomial over a finite field with interior mutability.
impl FiniteFieldPolynomial {
    // TODO use u32 not FiniteFieldPolynomial as coefficient to reduce the number of field_size elements in memory?
    pub fn new(field_size: u32, coeffs: Vec<FiniteFieldElement>) -> FiniteFieldPolynomial {
        let mut coefficients = coeffs.clone();
        while coefficients.len() > 0 && coefficients.last().unwrap().val == 0 {
            coefficients.pop();
        }

        FiniteFieldPolynomial{
            coefficients: RefCell::new(coefficients),
            field_size: field_size,
        }
    }

    pub fn field(&self) -> FiniteField {
        FiniteField { size: self.field_size }
    }

    /// BitReverse operation specified in NewHope.
    pub fn bit_rev(self: &Self, n: u32) -> FiniteFieldPolynomial {
        let bitlength = (n as f32).log2() as usize;
        let mut copy = Vec::with_capacity(n as usize);
        copy.extend_from_slice(&[FiniteFieldElement::new(self.field_size, 0)].repeat(n as usize));

        // reverses the bitmask of x w.r.t. bitlength significant bits
        let rev = |x: usize, bitlength: usize| {
            let mut result = 0usize;
            for i in 0..bitlength {
                result += ((x >> (bitlength - i - 1)) & 1) << i;
            }
            result
        };

        for (i, coeff) in self.coefficients.borrow().iter().enumerate() {
            copy[rev(i, bitlength)] = *coeff;
        }

        FiniteFieldPolynomial::new(self.field_size, copy)
    }

    pub fn get(&self, idx: usize) -> FiniteFieldElement {
        let b = self.coefficients.borrow();
        let opt_elem = b.get(idx);
        match opt_elem {
            Some(elem) => elem.clone(),
            None => FiniteFieldElement::new(self.field_size, 0),
        }
    }

    pub fn set(&mut self, idx: usize, element: FiniteFieldElement) {
        let mut coeffs = self.coefficients.borrow_mut();
        if element.val == 0 && idx >= coeffs.len() {
            return
        }
        if idx >= coeffs.len() {
            while idx >= coeffs.len() {
                coeffs.push(FiniteFieldElement::new(element.field_size, 0))
            }
        }
        coeffs[idx] = element.clone();
    }
}

impl Add for FiniteFieldPolynomial {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        if self.field_size != rhs.field_size {
            panic!("incompatible field sizes {} and {} in FiniteFieldPolynomial Add", self.field_size, rhs.field_size)
        }

        let coeffs1 = self.coefficients.borrow();
        let coeffs2 = rhs.coefficients.borrow();

        let mut coeffs = Vec::new();
        for i in 0..cmp::max(coeffs1.len(), coeffs2.len()) {
            let summand1 = match coeffs1.get(i) {
                Some(e) => e.val,
                None => 0u32,
            };
            let summand2 = match coeffs2.get(i) {
                Some(e) => e.val,
                None => 0u32,
            };
            coeffs.push(FiniteFieldElement::new(self.field_size, (summand1 + summand2) % self.field_size));
        }

        return FiniteFieldPolynomial{
            field_size: self.field_size,
            coefficients: RefCell::new(coeffs)
        };
    }
}

impl Mul for FiniteFieldPolynomial {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        if self.field_size != rhs.field_size {
            panic!("incompatible field sizes {} and {} in FiniteFieldPolynomial Add", self.field_size, rhs.field_size)
        }
        
        let zero = FiniteFieldElement::new(self.field_size, 0);
        let mut product = [zero].repeat(self.coefficients.borrow().len() + rhs.coefficients.borrow().len() - 1);
        for (i1, factor1) in self.coefficients.borrow().iter().enumerate() {
            for (i2, factor2) in rhs.coefficients.borrow().iter().enumerate() {
                if let Some(coeff) = product.get_mut(i1 + i2) {
                    *coeff = *coeff + *factor1 * *factor2;
                }
            }
        }

        FiniteFieldPolynomial::new(self.field_size, product)
    }
}
/*
impl Index<usize> for FiniteFieldPolynomial {
    type Output = Rc<FiniteFieldElement>;

    fn index(&self, idx: usize) -> &Self::Output {
        match self.coefficients.borrow().get(idx) {
            Some(&ffe) => &Rc::new(ffe),
            None => &Rc::new(FiniteFieldElement{
                val: 0,
                field_size: self.field_size
            }),
        }
    }
}

impl IndexMut<usize> for FiniteFieldPolynomial {
    fn index_mut<'a>(&'a mut self, idx: usize) -> &'a mut Self::Output {
        let field = FiniteField::new(self.field_size);
        let mut coeffs = self.coefficients.borrow_mut();
        if coeffs.len() <= idx {
            let missingItems = idx - coeffs.len();
            coeffs.extend([field.element(0)].repeat(missingItems).iter().cloned());
        }
        let element = coeffs.get_mut(idx).unwrap();
        &mut Rc::new(*element)
    }
}*/

impl PartialEq for FiniteFieldPolynomial {
    fn eq(&self, other: &Self) -> bool {
        self.field_size == other.field_size &&
        self.coefficients.borrow().len() == other.coefficients.borrow().len() &&
        self.coefficients.borrow().iter().zip(other.coefficients.borrow().iter()).all(|(&x, &y)| x == y)
    }
}

impl fmt::Debug for FiniteFieldPolynomial {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "FiniteFieldPolynomial::new({}, vec![{}])", self.field_size,
            self.coefficients.borrow().iter().map(|v| (*v).val.to_string()).collect::<Vec<String>>().join(", "))
    }
}

impl fmt::Display for FiniteFieldPolynomial {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        write!(formatter, "[")?;
        for coeff in self.coefficients.borrow().iter() {
            write!(formatter, "{} ", coeff)?;
        }
        write!(formatter, "in ℤ_{}]", self.field_size)
    }
}


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_element() {
        let ff = FiniteField::new(99);
        println!("{}", ff); // must be implemented
        assert_eq!(ff.element(100), ff.element(1));
    }

    #[test]
    fn test_element_add() {
        let ff = FiniteField::new(99);
        assert_eq!(ff.element(98) + ff.element(2), ff.element(1));
    }

    #[test]
    fn test_element_mul() {
        let ff = FiniteField::new(128);
        assert_eq!(ff.element(13) * ff.element(67), ff.element(103));
    }

    #[test]
    fn test_polynomial() {
        let ff = FiniteField::new(99);
        let poly1 = ff.polynomial(vec![ff.element(100), ff.element(1), ff.element(200)]);
        let poly2 = ff.polynomial(vec![ff.element(1), ff.element(1), ff.element(2)]);
        println!("{}", poly1); // must be implemented
        assert_eq!(poly1, poly2);
        assert_ne!(poly1, ff.polynomial(vec![ff.element(1)]));

        // omit trailing zeros
        let poly3 = ff.polynomial(vec![ff.element(1), ff.element(1), ff.element(0)]);
        let poly4 = ff.polynomial(vec![ff.element(1), ff.element(1)]);
        assert_eq!(poly3, poly4);
    }

    #[test]
    fn test_polynomial_add() {
        let ff = FiniteField::new(99);
        let o = ff.element(1);
        let z = ff.element(0);
        let poly1 = ff.polynomial(vec![o, z, o]);
        let poly2 = ff.polynomial(vec![z, o, z, o]);
        assert_eq!(poly1 + poly2, ff.polynomial(vec![o, o, o, o]));
    }

    #[test]
    fn test_polynomial_mul() {
        let ff = FiniteField::new(99);
        let t = ff.element(2);
        let o = ff.element(1);
        let poly1 = ff.polynomial(vec![t, t, t]);
        let poly2 = ff.polynomial(vec![o, o, o, t]);
        assert_eq!(poly1 * poly2, ff.polynomial(vec![ff.element(2), ff.element(4), ff.element(6), ff.element(8), ff.element(6), ff.element(4)]));
    }

    #[test]
    fn test_bit_rev() {
        let ff = FiniteField::new(12289);
        let e = |v| ff.element(v);
        let zero = vec![e(1), e(2), e(3), e(4)];
        let poly = ff.polynomial(zero);
        assert_eq!(poly.bit_rev(4), ff.polynomial(vec![e(1), e(3), e(2), e(4)]));
    }
}
