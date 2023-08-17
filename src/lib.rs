//! calculator

mod numeric;
mod operator;

use std::collections::HashMap;
use operator::*;

// Syntax
// top_exp : asn_exp
// asn_exp : eql_exp
//           var_exp [=,+=,-=,*=,/=] asn_exp
// var_exp : A-Za-z...
// eql_exp : rel_exp
//           eql_exp [==,!=] rel_exp
// rel_exp : add_sub
//           rel_exp [<,>,<=,>=] add_sub
// add_sub : mul_div
//           add_sub [+,-] mul_div
// mul_div : par_exp
//           mul_div [*,/] pa_exp
// par_exp : numeric
//           (top_exp)
// numeric : hexs
//           octs
//           digs
//           var_exp

#[allow(unused_macros)]
macro_rules! LINE { () => { println!("{}", line!()) } }

fn is_space(c: u8) -> bool {
    c <= 0x20 || c >= 0x7F
}

fn count_delim(buf: &[u8]) -> usize {
    buf.iter().position(|x| !is_space(*x)).unwrap_or(buf.len())
}

fn skip_delim(buf: &[u8]) -> (&[u8], usize) {
    let s = count_delim(buf);
    (&buf[s..], s)
}

impl Calc {
    fn top_exp(&mut self, buf: &[u8]) -> Option<(i64, usize)> {
        self.asn_exp(buf)
    }

    fn asn_exp(&mut self, buf: &[u8]) -> Option<(i64, usize)> {
        let (b, skip) = skip_delim(&buf);
        if b.len() == 0 {
            return None
        }
        let Some((var, skip2)) = try_get_var_exp(b) else {
            return self.eql_exp(buf)
        };
        let b = &b[skip2..];
        let (b, skip3) = skip_delim(&b);
        if !is_assign_token(b) {
            // maybe var_exp as numeric
            return self.eql_exp(buf)
        }
        let skip4 = if is_cmn_assign_token(b) { 1 } else { 2 };
        let (v, s) = self.asn_exp(&b[skip4..])?;
        if is_cmn_assign_token(b) {
            self.var.insert(var.to_string(), v);
        } else {
            let Some(var) = self.var.get_mut(var) else {
                return None;
            };
            if is_add_assign_token(b) {
                *var += v;
            } else if is_sub_assign_token(b) {
                *var -= v;
            } else if is_mul_assign_token(b) {
                *var *= v;
            } else {
                *var /= v;
            }
        }
        Some((*self.var.get(var)?, skip + skip2 + skip3 + skip4 + s))
    }

    fn eql_exp(&mut self, buf: &[u8]) -> Option<(i64, usize)> {
        let (lv, ls) = self.rel_exp(buf)?;
        let (v, s) = self.eql_exp_rv(lv, 0, &buf[ls..])?;
        Some((v, s + ls))
    }

    fn eql_exp_rv(&mut self, lv: i64, ls:usize, buf: &[u8]) -> Option<(i64, usize)> {
        let (buf, skip) = skip_delim(&buf);
        if buf.len() == 0 {
            Some((lv, ls + skip))
        } else if is_eq_token(buf) || is_ne_token(buf) {
            let skip2 = 2;
            let (rv, rs) = self.rel_exp(&buf[skip2..])?;
            let s = ls + rs + skip + skip2;
            let v = if is_eq_token(buf) {
                lv == rv
            } else {
                lv != rv
            } as i64;
            self.eql_exp_rv(v, s, &buf[skip2 + rs..])
        } else {
            Some((lv, ls + skip))
        }
    }

    fn rel_exp(&mut self, buf: &[u8]) -> Option<(i64, usize)> {
        let (lv, ls) = self.add_sub(buf)?;
        let (v, s) = self.rel_exp_rv(lv, 0, &buf[ls..])?;
        Some((v, s + ls))
    }

    fn rel_exp_rv(&mut self, lv: i64, ls:usize, buf: &[u8]) -> Option<(i64, usize)> {
        let (buf, skip) = skip_delim(&buf);
        if buf.len() == 0 {
            Some((lv, ls + skip))
        } else if is_gt_token(buf) || is_lt_token(buf) || is_ge_token(buf) || is_le_token(buf) {
            let skip2 = if is_gt_token(buf) || is_lt_token(buf) { 1 } else { 2 };
            let (rv, rs) = self.add_sub(&buf[skip2..])?;
            let s = ls + rs + skip + skip2;
            let v = if is_gt_token(buf) {
                lv > rv
            } else if is_lt_token(buf) {
                lv < rv
            } else if is_ge_token(buf) {
                lv >= rv
            } else {
                lv <= rv
            } as i64;
            self.rel_exp_rv(v, s, &buf[skip2 + rs..])
        } else {
            Some((lv, ls + skip))
        }
    }

    fn add_sub(&mut self, buf: &[u8]) -> Option<(i64, usize)> {
        let (lv, ls) = self.mul_div(buf)?;
        let (v, s) = self.add_sub_rv(lv, 0, &buf[ls..])?;
        Some((v, s + ls))
    }

    fn add_sub_rv(&mut self, lv: i64, ls:usize, buf: &[u8]) -> Option<(i64, usize)> {
        let (buf, skip) = skip_delim(&buf);
        if buf.len() == 0 {
            Some((lv, ls + skip))
        } else if is_add_token(buf) || is_sub_token(buf) {
            let (rv, rs) = self.mul_div(&buf[1..])?;
            let s = ls + rs + skip + 1;
            let v = if is_add_token(buf) {
                lv.wrapping_add(rv)
            } else {
                lv.wrapping_sub(rv)
            };
            self.add_sub_rv(v, s, &buf[1 + rs..])
        } else {
            Some((lv, ls + skip))
        }
    }

    fn mul_div(&mut self, buf: &[u8]) -> Option<(i64, usize)> {
        let (lv, ls) = self.par_exp(buf)?;
        let (v, s) = self.mul_div_rv(lv, 0, &buf[ls..])?;
        Some((v, s + ls))
    }

    fn mul_div_rv(&mut self, lv: i64, ls:usize, buf: &[u8]) -> Option<(i64, usize)> {
        let (buf, skip) = skip_delim(&buf);
        if buf.len() == 0 {
            Some((lv, ls + skip))
        } else if is_mul_token(buf) || is_div_token(buf) {
            let (rv, rs) = self.par_exp(&buf[1..])?;
            let s = ls + rs + skip + 1;
            let v = if is_mul_token(buf) {
                lv.wrapping_mul(rv)
            } else if rv != 0 {
                lv.wrapping_div(rv)
            } else {
                return None
            };
            self.mul_div_rv(v, s, &buf[1 + rs..])
        } else {
            Some((lv, ls + skip))
        }
    }

    fn par_exp(&mut self, buf: &[u8]) -> Option<(i64, usize)> {
        let (buf, skip) = skip_delim(buf);
        if is_lpar_token(buf) {
            let (v, s) = self.top_exp(&buf[1..])?;
            let (buf, skip2) = skip_delim(&buf[1 + s..]);
            if is_rpar_token(buf) {
                Some((v, s + skip + skip2 + LPAR.len() + RPAR.len()))
            } else {
                None
            }
        } else {
            let (v, s) = self.numeric(buf)?;
            Some((v, s + skip))
        }
    }

    fn numeric(&mut self, buf: &[u8]) -> Option<(i64, usize)> {
        let (buf, skip) = skip_delim(buf);
        let (v, s) = self.numeric_ltrimed(buf)?;
        Some((v, s + skip))
    }

    fn numeric_ltrimed(&mut self, buf: &[u8]) -> Option<(i64, usize)> {
        if buf.len() == 0 {
            None
        } else if let Some((var, skip)) = try_get_var_exp(buf) {
            Some((*self.var.get(var)?, skip))
        } else if buf.len() < 3 {
            numeric::idigits(buf)
        } else if buf[0] != '0' as u8 {
            numeric::idigits(buf)
        } else if buf[1] == 'x' as u8 || buf[1] == 'X' as u8 {
            let (v, s) = numeric::uhexes(&buf[2..])?;
            Some((v as i64, s + 2))
        } else if buf[1] == 'o' as u8 || buf[1] == 'O' as u8 {
            let (v, s) = numeric::uoctets(&buf[2..])?;
            Some((v as i64, s + 2))
        } else {
            numeric::idigits(buf)
        }
    }

    pub fn new() -> Self {
        Self { var: HashMap::<String, i64>::new() }
    }

    /// Calculate expression
    /// # Arguments
    /// * `buf` - ascii string bufer
    pub fn calc(&mut self, buf: &str) -> Option<i64> {
        let (v, s) = self.top_exp(buf.as_bytes())?;
        if buf.len() == s {
            Some(v)
        } else {
            None
        }
    }
}

pub struct Calc {
    var: HashMap<String, i64>,
}

/// Calculate expression
/// # Arguments
/// * `buf` - ascii string bufer
pub fn calc(buf: &str) -> Option<i64> {
    let mut c = Calc::new();
    c.calc(buf)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_numeric() {
        let mut c = Calc::new();
        assert_eq!(c.numeric(b""), None);
        assert_eq!(c.numeric(b" 1").unwrap(), (1, 2));
        assert_eq!(c.numeric(b"1").unwrap(), (1, 1));
        assert_eq!(c.numeric(b"10").unwrap(), (10, 2));
        assert_eq!(c.numeric(b"10").unwrap(), (10, 2));
        assert_eq!(c.numeric(b"0x10").unwrap(), (0x10, 4));
        assert_eq!(c.numeric(b"0X10").unwrap(), (0x10, 4));
        assert_eq!(c.numeric(b"0o10").unwrap(), (0o10, 4));
        assert_eq!(c.numeric(b"0O10").unwrap(), (0o10, 4));
    }

    #[test]
    fn test_par_exp() {
        let mut c = Calc::new();
        assert_eq!(c.par_exp(b"()"), None);
        assert_eq!(c.par_exp(b"(1"), None);
        assert_eq!(c.par_exp(b"(1)").unwrap(), (1, 3));
        assert_eq!(c.par_exp(b"(10)").unwrap(), (10, 4));
        assert_eq!(c.par_exp(b"(10)").unwrap(), (10, 4));
        assert_eq!(c.par_exp(b"(0x10)").unwrap(), (0x10, 6));
        assert_eq!(c.par_exp(b"(0X10)").unwrap(), (0x10, 6));
        assert_eq!(c.par_exp(b"(0o10)").unwrap(), (0o10, 6));
        assert_eq!(c.par_exp(b"(0O10)").unwrap(), (0o10, 6));
    }
    #[test]
    fn test_mul_div() {
        let mut c = Calc::new();
        assert_eq!(c.mul_div(b"12*13").unwrap(), (12*13, 5));
        assert_eq!(c.mul_div(b" 12 * 13 ").unwrap(), (12*13, 9));
        assert_eq!(c.mul_div(b"12/4").unwrap(), (12/4, 4));
        assert_eq!(c.mul_div(b"12/4*3").unwrap(), (12/4*3, 6));
    }
    #[test]
    fn test_add_sub() {
        let mut c = Calc::new();
        assert_eq!(c.add_sub(b" 12 + 13 ").unwrap(), (12+13, 9));
        assert_eq!(c.add_sub(b"12-4").unwrap(), (12-4, 4));
        assert_eq!(c.add_sub(b"12-4+3").unwrap(), (12-4+3, 6));
        assert_eq!(c.add_sub(b"12+13*2-5").unwrap(), (12+13*2-5, 9));
        assert_eq!(c.add_sub(b"12+13*2").unwrap(), (12+13*2, 7));
        assert_eq!(c.add_sub(b"12+13*(2-5)").unwrap(), (12+13*(2-5), 11));
    }
    #[test]
    fn test_ariths() {
        assert_eq!(calc("12+13*2-5").unwrap(), 12+13*2-5);
        assert_eq!(calc("12+13*2").unwrap(), 12+13*2);
        assert_eq!(calc("12+13*(2-5)").unwrap(), 12+13*(2-5));
        assert_eq!(calc("(12+13)*(2-5)").unwrap(), (12+13)*(2-5));
        assert_eq!(calc("((12+13))*(2-5)").unwrap(), (12+13)*(2-5));
        assert_eq!(calc("((12+13))*(-5)").unwrap(), (12+13)*(-5));
        assert_eq!(calc("((12+13))--5").unwrap(), (12+13)- -5);
        assert_eq!(calc("12+13*2-5-"), None);
    }
    #[test]
    fn test_rel_exp() {
        assert_eq!(calc(" 12 < 11 + 3").unwrap(), 1);
        assert_eq!(calc(" 12 - 2 > 11").unwrap(), 0);
        assert_eq!(calc(" 12 >= 3*4").unwrap(), 1);
        assert_eq!(calc(" 12 <= 3*4").unwrap(), 1);
    }
    #[test]
    fn test_eql_exp() {
        assert_eq!(calc(" 12 != 11 + 3").unwrap(), 1);
        assert_eq!(calc(" 12 - 1 != 11").unwrap(), 0);
        assert_eq!(calc(" 12 == 3*4").unwrap(), 1);
    }
    #[test]
    fn test_asn_exp() {
        assert_eq!(calc("a@ = 2"), None);
        assert_eq!(calc("a = 1").unwrap(), 1);
        assert_eq!(calc("a = 2").unwrap(), 2);
        assert_eq!(calc("(a=b=1) + (a=b)").unwrap(), 2);
        assert_eq!(calc("((a = 2) + (b = 3)) * 0 + a * b").unwrap(), 6);
        assert_eq!(calc("((a = 2) + (b = 3)) * 0 + (a += b)").unwrap(), 5);
        assert_eq!(calc("((a = 2) + (b = 3)) * 0 + (a -= b)").unwrap(), -1);
        assert_eq!(calc("((a = 2) + (b = 3)) * 0 + (a *= b)").unwrap(), 6);
        assert_eq!(calc("(a = b = 3) * 0 + (a /= b)").unwrap(), 1);
    }
    #[test]
    fn test_ctx_asn_exp() {
        let mut c = Calc::new();
        assert_eq!(c.calc("a = 1").unwrap(), 1);
        assert_eq!(c.calc("a += 2").unwrap(), 3);
    }
}
