//! calculator

mod numeric;

// Syntax
// eql_exp : rel_exp
//           eql_exp [==,!=] rel_exp
// rel_exp : add_sub
//           rel_exp [<,>,<=,>=] add_sub
// add_sub : mul_div
//           add_sub [+,-] mul_div
// mul_div : par_exp
//           mul_div [*,/] pa_exp
// par_exp : numeric
//           (add_sub)
// numeric : hexs
//           octs
//           digs

#[allow(unused_macros)]
macro_rules! LINE { () => { println!("{}", line!()) } }

const ADD: [u8; 1] = ['+' as u8];
const SUB: [u8; 1] = ['-' as u8];
const MUL: [u8; 1] = ['*' as u8];
const DIV: [u8; 1] = ['/' as u8];
const LPAR: [u8; 1] = ['(' as u8];
const RPAR: [u8; 1] = [')' as u8];

const GT: [u8; 1] = ['>' as u8];
const LT: [u8; 1] = ['<' as u8];
const GE: [u8; 2] = ['>' as u8, '=' as u8];
const LE: [u8; 2] = ['<' as u8, '=' as u8];

const EQ: [u8; 2] = ['=' as u8, '=' as u8];
const NE: [u8; 2] = ['!' as u8, '=' as u8];

const ADD_ASSIGN: [u8; 2] = ['+' as u8, '=' as u8];
const SUB_ASSIGN: [u8; 2] = ['-' as u8, '=' as u8];
const MUL_ASSIGN: [u8; 2] = ['*' as u8, '=' as u8];
const DIV_ASSIGN: [u8; 2] = ['/' as u8, '=' as u8];

fn is_add_token(buf: &[u8]) -> bool {
    buf.starts_with(&ADD) && !buf.starts_with(&ADD_ASSIGN)
}

fn is_sub_token(buf: &[u8]) -> bool {
    buf.starts_with(&SUB) && !buf.starts_with(&SUB_ASSIGN)
}

fn is_mul_token(buf: &[u8]) -> bool {
    buf.starts_with(&MUL) && !buf.starts_with(&MUL_ASSIGN)
}

fn is_div_token(buf: &[u8]) -> bool {
    buf.starts_with(&DIV) && !buf.starts_with(&DIV_ASSIGN)
}

fn is_lpar_token(buf: &[u8]) -> bool {
    buf.starts_with(&LPAR)
}

fn is_rpar_token(buf: &[u8]) -> bool {
    buf.starts_with(&RPAR)
}

fn is_gt_token(buf: &[u8]) -> bool {
    buf.starts_with(&GT) && !buf.starts_with(&GE)
}

fn is_lt_token(buf: &[u8]) -> bool {
    buf.starts_with(&LT) && !buf.starts_with(&LE)
}
fn is_ge_token(buf: &[u8]) -> bool {
    buf.starts_with(&GE)
}

fn is_le_token(buf: &[u8]) -> bool {
    buf.starts_with(&LE)
}

fn is_eq_token(buf: &[u8]) -> bool {
    buf.starts_with(&EQ)
}

fn is_ne_token(buf: &[u8]) -> bool {
    buf.starts_with(&NE)
}

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

fn root_exp(buf: &[u8]) -> Option<(i64, usize)> {
    eql_exp(buf)
}

fn eql_exp(buf: &[u8]) -> Option<(i64, usize)> {
    let (lv, ls) = rel_exp(buf)?;
    let (v, s) = eql_exp_rv(lv, 0, &buf[ls..])?;
    Some((v, s + ls))
}

fn eql_exp_rv(lv: i64, ls:usize, buf: &[u8]) -> Option<(i64, usize)> {
    let (buf, skip) = skip_delim(&buf);
    if buf.len() == 0 {
        Some((lv, ls + skip))
    } else if is_eq_token(buf) || is_ne_token(buf) {
        let skip2 = 2;
        let (rv, rs) = rel_exp(&buf[skip2..])?;
        let s = ls + rs + skip + skip2;
        let v = if is_eq_token(buf) {
            lv == rv
        } else {
            lv != rv
        } as i64;
        eql_exp_rv(v, s, &buf[skip2 + rs..])
    } else {
        Some((lv, ls + skip))
    }
}

fn rel_exp(buf: &[u8]) -> Option<(i64, usize)> {
    let (lv, ls) = add_sub(buf)?;
    let (v, s) = rel_exp_rv(lv, 0, &buf[ls..])?;
    Some((v, s + ls))
}

fn rel_exp_rv(lv: i64, ls:usize, buf: &[u8]) -> Option<(i64, usize)> {
    let (buf, skip) = skip_delim(&buf);
    if buf.len() == 0 {
        Some((lv, ls + skip))
    } else if is_gt_token(buf) || is_lt_token(buf) || is_ge_token(buf) || is_le_token(buf) {
        let skip2 = if is_gt_token(buf) || is_lt_token(buf) { 1 } else { 2 };
        let (rv, rs) = add_sub(&buf[skip2..])?;
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
        rel_exp_rv(v, s, &buf[skip2 + rs..])
    } else {
        Some((lv, ls + skip))
    }
}

fn add_sub(buf: &[u8]) -> Option<(i64, usize)> {
    let (lv, ls) = mul_div(buf)?;
    let (v, s) = add_sub_rv(lv, 0, &buf[ls..])?;
    Some((v, s + ls))
}

fn add_sub_rv(lv: i64, ls:usize, buf: &[u8]) -> Option<(i64, usize)> {
    let (buf, skip) = skip_delim(&buf);
    if buf.len() == 0 {
        Some((lv, ls + skip))
    } else if is_add_token(buf) || is_sub_token(buf) {
        let (rv, rs) = mul_div(&buf[1..])?;
        let s = ls + rs + skip + 1;
        let v = if is_add_token(buf) {
            lv.wrapping_add(rv)
        } else {
            lv.wrapping_sub(rv)
        };
        add_sub_rv(v, s, &buf[1 + rs..])
    } else {
        Some((lv, ls + skip))
    }
}

fn mul_div(buf: &[u8]) -> Option<(i64, usize)> {
    let (lv, ls) = par_exp(buf)?;
    let (v, s) = mul_div_rv(lv, 0, &buf[ls..])?;
    Some((v, s + ls))
}

fn mul_div_rv(lv: i64, ls:usize, buf: &[u8]) -> Option<(i64, usize)> {
    let (buf, skip) = skip_delim(&buf);
    if buf.len() == 0 {
        Some((lv, ls + skip))
    } else if is_mul_token(buf) || is_div_token(buf) {
        let (rv, rs) = par_exp(&buf[1..])?;
        let s = ls + rs + skip + 1;
        let v = if is_mul_token(buf) {
            lv.wrapping_mul(rv)
        } else if rv != 0 {
            lv.wrapping_div(rv)
        } else {
            return None
        };
        mul_div_rv(v, s, &buf[1 + rs..])
    } else {
        Some((lv, ls + skip))
    }
}

fn par_exp(buf: &[u8]) -> Option<(i64, usize)> {
    let (buf, skip) = skip_delim(buf);
    if is_lpar_token(buf) {
        let (v, s) = root_exp(&buf[1..])?;
        let (buf, skip2) = skip_delim(&buf[1 + s..]);
        if is_rpar_token(buf) {
            Some((v, s + skip + skip2 + LPAR.len() + RPAR.len()))
        } else {
            None
        }
    } else {
        let (v, s) = numeric(buf)?;
        Some((v, s + skip))
    }
}

fn numeric(buf: &[u8]) -> Option<(i64, usize)> {
    let (buf, skip) = skip_delim(buf);
    let (v, s) = numeric_ltrimed(buf)?;
    Some((v, s + skip))
}

fn numeric_ltrimed(buf: &[u8]) -> Option<(i64, usize)> {
    if buf.len() == 0 {
        None
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

/// Calculate expression
/// # Arguments
/// * `buf` - ascii string bufer
pub fn calc(buf: &str) -> Option<i64> {
    let (v, s) = root_exp(buf.as_bytes())?;
    if buf.len() == s {
        Some(v)
    } else {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_numeric() {
        assert_eq!(numeric(b""), None);
        assert_eq!(numeric(b" 1").unwrap(), (1, 2));
        assert_eq!(numeric(b"1").unwrap(), (1, 1));
        assert_eq!(numeric(b"10").unwrap(), (10, 2));
        assert_eq!(numeric(b"10").unwrap(), (10, 2));
        assert_eq!(numeric(b"0x10").unwrap(), (0x10, 4));
        assert_eq!(numeric(b"0X10").unwrap(), (0x10, 4));
        assert_eq!(numeric(b"0o10").unwrap(), (0o10, 4));
        assert_eq!(numeric(b"0O10").unwrap(), (0o10, 4));
    }

    #[test]
    fn test_par_exp() {
        assert_eq!(par_exp(b"()"), None);
        assert_eq!(par_exp(b"(1"), None);
        assert_eq!(par_exp(b"(1)").unwrap(), (1, 3));
        assert_eq!(par_exp(b"(10)").unwrap(), (10, 4));
        assert_eq!(par_exp(b"(10)").unwrap(), (10, 4));
        assert_eq!(par_exp(b"(0x10)").unwrap(), (0x10, 6));
        assert_eq!(par_exp(b"(0X10)").unwrap(), (0x10, 6));
        assert_eq!(par_exp(b"(0o10)").unwrap(), (0o10, 6));
        assert_eq!(par_exp(b"(0O10)").unwrap(), (0o10, 6));
    }
    #[test]
    fn test_mul_div() {
        assert_eq!(mul_div(b"12*13").unwrap(), (12*13, 5));
        assert_eq!(mul_div(b" 12 * 13 ").unwrap(), (12*13, 9));
        assert_eq!(mul_div(b"12/4").unwrap(), (12/4, 4));
        assert_eq!(mul_div(b"12/4*3").unwrap(), (12/4*3, 6));
    }
    #[test]
    fn test_add_sub() {
        assert_eq!(add_sub(b" 12 + 13 ").unwrap(), (12+13, 9));
        assert_eq!(add_sub(b"12-4").unwrap(), (12-4, 4));
        assert_eq!(add_sub(b"12-4+3").unwrap(), (12-4+3, 6));
        assert_eq!(add_sub(b"12+13*2-5").unwrap(), (12+13*2-5, 9));
        assert_eq!(add_sub(b"12+13*2").unwrap(), (12+13*2, 7));
        assert_eq!(add_sub(b"12+13*(2-5)").unwrap(), (12+13*(2-5), 11));
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
}
