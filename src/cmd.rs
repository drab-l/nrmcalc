macro_rules! to_u8 {
    ($($v:expr),*) => { {[$($v as u8,)*]} };
}

pub const STR_GET: [u8; 3] = to_u8!('s', 't', 'r');
pub const STR_SET: [u8; 7] = to_u8!('s', 'e', 't', '_', 's', 't', 'r');

pub fn is_str_get_token(buf: &[u8]) -> bool {
    buf.starts_with(&STR_GET)
}

pub fn is_str_set_token(buf: &[u8]) -> bool {
    buf.starts_with(&STR_SET)
}


