pub const ADD: [u8; 1] = ['+' as u8];
pub const SUB: [u8; 1] = ['-' as u8];
pub const MUL: [u8; 1] = ['*' as u8];
pub const DIV: [u8; 1] = ['/' as u8];
pub const AND: [u8; 1] = ['&' as u8];
pub const XOR: [u8; 1] = ['^' as u8];
pub const IOR: [u8; 1] = ['|' as u8];
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
pub const AND_ASSIGN: [u8; 2] = ['&' as u8, '=' as u8];
pub const XOR_ASSIGN: [u8; 2] = ['^' as u8, '=' as u8];
pub const IOR_ASSIGN: [u8; 2] = ['|' as u8, '=' as u8];

pub const ARG_VAR: [u8; 1] = ['$' as u8];
pub const CUSTOM1: [u8; 1] = ['@' as u8];
pub const LSQR: [u8; 1] = ['[' as u8];
pub const RSQR: [u8; 1] = [']' as u8];

pub const RSQR_ASSIGN: [u8; 2] = [']' as u8, '=' as u8];

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

pub fn is_and_token(buf: &[u8]) -> bool {
    buf.starts_with(&AND) && !buf.starts_with(&AND_ASSIGN)
}

pub fn is_xor_token(buf: &[u8]) -> bool {
    buf.starts_with(&XOR) && !buf.starts_with(&XOR_ASSIGN)
}

pub fn is_ior_token(buf: &[u8]) -> bool {
    buf.starts_with(&IOR) && !buf.starts_with(&IOR_ASSIGN)
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
        is_mul_assign_token(buf) || is_div_assign_token(buf) ||
        is_and_assign_token(buf) || is_xor_assign_token(buf) ||
        is_ior_assign_token(buf)
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

pub fn is_and_assign_token(buf: &[u8]) -> bool {
    buf.starts_with(&AND_ASSIGN)
}

pub fn is_xor_assign_token(buf: &[u8]) -> bool {
    buf.starts_with(&XOR_ASSIGN)
}

pub fn is_ior_assign_token(buf: &[u8]) -> bool {
    buf.starts_with(&IOR_ASSIGN)
}

fn is_numeric(c: u8) -> bool {
    c >= '0' as u8 && c <= '9' as u8
}

fn is_alphabet(c: u8) -> bool {
    (c >= 'A' as u8 && c <= 'Z' as u8) || (c >= 'a' as u8 && c <= 'z' as u8)
}

fn is_alnum(c: u8) -> bool {
    is_numeric(c) || is_alphabet(c)
}

pub fn try_get_alphabet_name(buf: &[u8]) -> Option<(&str, usize)> {
    let o = buf.iter().position(|x| !is_alphabet(*x)).unwrap_or(buf.len());
    if o == 0 {
        None
    } else {
        Some((std::str::from_utf8(&buf[..o]).ok()?, o))
    }
}

pub fn try_get_alnum_name(buf: &[u8]) -> Option<(&str, usize)> {
    let o = buf.iter().position(|x| !is_alnum(*x)).unwrap_or(buf.len());
    if o == 0 {
        None
    } else {
        Some((std::str::from_utf8(&buf[..o]).ok()?, o))
    }
}

pub fn try_get_numeric_name(buf: &[u8]) -> Option<(&str, usize)> {
    let o = buf.iter().position(|x| !is_numeric(*x)).unwrap_or(buf.len());
    if o == 0 {
        None
    } else {
        Some((std::str::from_utf8(&buf[..o]).ok()?, o))
    }
}

pub fn try_get_var_exp(buf: &[u8]) -> Option<(&str, usize)> {
    try_get_alphabet_name(buf)
}

pub fn try_get_arg_var(buf: &[u8]) -> Option<(&str, usize)> {
    if buf.len() == 0 || !buf.starts_with(&ARG_VAR) {
        return None
    }
    let buf = &buf[ARG_VAR.len()..];
    let Some((n, s)) = try_get_numeric_name(buf) else {
        return None
    };
    Some((n, ARG_VAR.len() + s))
}

pub fn try_get_custom1(buf: &[u8]) -> Option<(&str, usize)> {
    if buf.len() == 0 || !buf.starts_with(&CUSTOM1) {
        return None
    }
    let buf = &buf[CUSTOM1.len()..];
    let Some((n, s)) = try_get_alnum_name(buf) else {
        return Some(("", CUSTOM1.len()))
    };
    Some((n, CUSTOM1.len() + s))
}

pub fn try_get_sqr_bra(buf: &[u8]) -> Option<(&str, usize)> {
    if buf.len() == 0 || !buf.starts_with(&LSQR) {
        return None
    }
    let buf = &buf[LSQR.len()..];
    if let Some((v, s)) = try_get_custom1(buf) {
        Some((v, s + LSQR.len()))
    } else {
        Some(("", LSQR.len()))
    }
}

pub fn try_get_cmd_name(buf: &[u8]) -> Option<(&str, usize)> {
    try_get_alnum_name(buf)
}

pub fn is_lsqr_token(buf: &[u8]) -> bool {
    buf.starts_with(&LSQR)
}

pub fn is_rsqr_token(buf: &[u8]) -> bool {
    buf.starts_with(&RSQR)
}

pub fn is_rsqr_assign_token(buf: &[u8]) -> bool {
    buf.starts_with(&RSQR_ASSIGN)
}
