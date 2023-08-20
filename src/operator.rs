pub const ADD: [u8; 1] = ['+' as u8];
pub const SUB: [u8; 1] = ['-' as u8];
pub const MUL: [u8; 1] = ['*' as u8];
pub const DIV: [u8; 1] = ['/' as u8];
pub const LPAR: [u8; 1] = ['(' as u8];
pub const RPAR: [u8; 1] = [')' as u8];

pub const GT: [u8; 1] = ['>' as u8];
pub const LT: [u8; 1] = ['<' as u8];
pub const GE: [u8; 2] = ['>' as u8, '=' as u8];
pub const LE: [u8; 2] = ['<' as u8, '=' as u8];

pub const EQ: [u8; 2] = ['=' as u8, '=' as u8];
pub const NE: [u8; 2] = ['!' as u8, '=' as u8];

pub const CMN_ASSIGN: [u8; 1] = ['=' as u8];
pub const ADD_ASSIGN: [u8; 2] = ['+' as u8, '=' as u8];
pub const SUB_ASSIGN: [u8; 2] = ['-' as u8, '=' as u8];
pub const MUL_ASSIGN: [u8; 2] = ['*' as u8, '=' as u8];
pub const DIV_ASSIGN: [u8; 2] = ['/' as u8, '=' as u8];

pub const CUSTOM1: [u8; 1] = ['@' as u8];
pub const LSQR: [u8; 1] = ['[' as u8];
pub const RSQR: [u8; 1] = [']' as u8];

pub fn is_add_token(buf: &[u8]) -> bool {
    buf.starts_with(&ADD) && !buf.starts_with(&ADD_ASSIGN)
}

pub fn is_sub_token(buf: &[u8]) -> bool {
    buf.starts_with(&SUB) && !buf.starts_with(&SUB_ASSIGN)
}

pub fn is_mul_token(buf: &[u8]) -> bool {
    buf.starts_with(&MUL) && !buf.starts_with(&MUL_ASSIGN)
}

pub fn is_div_token(buf: &[u8]) -> bool {
    buf.starts_with(&DIV) && !buf.starts_with(&DIV_ASSIGN)
}

pub fn is_lpar_token(buf: &[u8]) -> bool {
    buf.starts_with(&LPAR)
}

pub fn is_rpar_token(buf: &[u8]) -> bool {
    buf.starts_with(&RPAR)
}

pub fn is_gt_token(buf: &[u8]) -> bool {
    buf.starts_with(&GT) && !buf.starts_with(&GE)
}

pub fn is_lt_token(buf: &[u8]) -> bool {
    buf.starts_with(&LT) && !buf.starts_with(&LE)
}
pub fn is_ge_token(buf: &[u8]) -> bool {
    buf.starts_with(&GE)
}

pub fn is_le_token(buf: &[u8]) -> bool {
    buf.starts_with(&LE)
}

pub fn is_eq_token(buf: &[u8]) -> bool {
    buf.starts_with(&EQ)
}

pub fn is_ne_token(buf: &[u8]) -> bool {
    buf.starts_with(&NE)
}

pub fn is_assign_token(buf: &[u8]) -> bool {
    is_cmn_assign_token(buf) ||
        is_add_assign_token(buf) || is_sub_assign_token(buf) ||
        is_mul_assign_token(buf) || is_div_assign_token(buf)
}

pub fn is_cmn_assign_token(buf: &[u8]) -> bool {
    buf.starts_with(&CMN_ASSIGN) && !buf.starts_with(&EQ)
}

pub fn is_add_assign_token(buf: &[u8]) -> bool {
    buf.starts_with(&ADD_ASSIGN)
}

pub fn is_sub_assign_token(buf: &[u8]) -> bool {
    buf.starts_with(&SUB_ASSIGN)
}

pub fn is_mul_assign_token(buf: &[u8]) -> bool {
    buf.starts_with(&MUL_ASSIGN)
}

pub fn is_div_assign_token(buf: &[u8]) -> bool {
    buf.starts_with(&DIV_ASSIGN)
}

fn is_alphabet(c: u8) -> bool {
    (c >= 'A' as u8 && c <= 'Z' as u8) || (c >= 'a' as u8 && c <= 'z' as u8)
}

pub fn try_get_var_exp(buf: &[u8]) -> Option<(&str, usize)> {
    let o = buf.iter().position(|x| !is_alphabet(*x)).unwrap_or(buf.len());
    if o == 0 {
        None
    } else {
        Some((std::str::from_utf8(&buf[..o]).ok()?, o))
    }
}

pub fn try_get_custom1(buf: &[u8]) -> Option<(&str, usize)> {
    if buf.len() == 0 || !buf.starts_with(&CUSTOM1){
        return None
    }
    let buf = &buf[1..];
    let o = buf.iter().position(|x| !is_alphabet(*x)).unwrap_or(buf.len());
    if o == 0 {
        None
    } else {
        Some((std::str::from_utf8(&buf[..o]).ok()?, 1 + o))
    }
}

pub fn is_lsqr_token(buf: &[u8]) -> bool {
    buf.starts_with(&LSQR)
}

pub fn is_rsqr_token(buf: &[u8]) -> bool {
    buf.starts_with(&RSQR)
}
