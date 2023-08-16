//! Likely strtoint in C language.

fn digit(s: u8) -> Option<u8> {
    match s {
        s if (0x30..=0x39).contains(&s) => Some(s - 0x30),
        _ => None,
    }
}

fn octet(s: u8) -> Option<u8> {
    match s {
        s if (0x30..=0x37).contains(&s) => Some(s - 0x30),
        _ => None,
    }
}

fn hex(s: u8) -> Option<u8> {
    match s {
        s if (0x30..=0x39).contains(&s) => Some(s - 0x30),
        s if ('A' as u8..='F' as u8).contains(&s) => Some(s - 'A' as u8 + 10),
        s if ('a' as u8..='f' as u8).contains(&s) => Some(s - 'a' as u8 + 10),
        _ => None,
    }
}

fn udigits_in(buf: &[u8], value: u64, offset: usize) -> (u64, usize) {
    if buf.len() <= offset { return (value, offset); }
    let Some(t) = digit(buf[offset]) else { return (value, offset); };
    udigits_in(&buf, value.wrapping_mul(10).wrapping_add(t as u64), offset + 1)
}

fn uoctets_in(buf: &[u8], value: u64, offset: usize) -> (u64, usize) {
    if buf.len() <= offset { return (value, offset); }
    let Some(t) = octet(buf[offset]) else { return (value, offset); };
    uoctets_in(&buf, value.wrapping_mul(8).wrapping_add(t as u64), offset + 1)
}

fn uhexes_in(buf: &[u8], value: u64, offset: usize) -> (u64, usize) {
    if buf.len() <= offset { return (value, offset); }
    let Some(t) = hex(buf[offset]) else { return (value, offset); };
    uhexes_in(&buf, value.wrapping_mul(16).wrapping_add(t as u64), offset + 1)
}

/// Convert digits to unsigned integer, and get convert string length
/// # Arguments
/// * `buf` - ascii string bufer
pub fn udigits(buf: &[u8]) -> Option<(u64, usize)> {
    if buf.len() == 0 { return None; }
    let Some(t) = digit(buf[0]) else { return None; };
    Some(udigits_in(&buf, t as u64, 1))
}

/// Convert digits to signed integer, and get convert string length
/// # Arguments
/// * `buf` - ascii string bufer
pub fn idigits(s: &[u8]) -> Option<(i64, usize)> {
    if s.len() == 0 { return None; }
    let b = if s.len() > 1 && (s[0] == '-' as u8 || s[0] == '+' as u8) {
        &s[1..]
    } else {
        s
    };
    match udigits(b) {
        Some((v, u)) => {
            let v = if s[0] == '-' as u8 { v.wrapping_neg() } else { v };
            Some((v as i64, u + (s[0] == '-' as u8 || s[0] == '+' as u8) as usize))
        },
        _ => None,
    }
}

/// Convert octets to unsigned integer, and get convert string length
/// # Arguments
/// * `buf` - ascii string bufer
pub fn uoctets(buf: &[u8]) -> Option<(u64, usize)> {
    if buf.len() == 0 { return None; }
    let Some(t) = octet(buf[0]) else { return None; };
    Some(uoctets_in(&buf, t as u64, 1))
}

/// Convert hexes to unsigned integer, and get convert string length
/// # Arguments
/// * `buf` - ascii string bufer
pub fn uhexes(buf: &[u8]) -> Option<(u64, usize)> {
    if buf.len() == 0 { return None; }
    let Some(t) = hex(buf[0]) else { return None; };
    Some(uhexes_in(&buf, t as u64, 1))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_digit() {
        for i in 0..('0' as u8) {
            assert!(digit(i).is_none())
        }
        for i in ('0' as u8)..('9' as u8 + 1) {
            assert!(digit(i).is_some())
        }
        for i in ('9' as u8 + 1)..255 {
            assert!(digit(i).is_none())
        }
    }
    #[test]
    fn test_udigits() {
        assert_eq!(udigits(b""), None);
        assert_eq!(udigits(b"-1"), None);
        assert_eq!(udigits(b"0").unwrap(), (0,1));
        assert_eq!(udigits(b"1").unwrap(), (1,1));
        assert_eq!(udigits(b"12").unwrap(), (12,2));
        assert_eq!(udigits(format!("{}", std::u64::MAX).as_ref()).unwrap(), (std::u64::MAX, format!("{}", std::u64::MAX).len()));
        assert_eq!(udigits(format!("{}", (std::u64::MAX as u128 + 1)).as_ref()).unwrap(), (0, format!("{}", std::u64::MAX).len()));
        assert_eq!(udigits(format!("{}", (std::u64::MAX as u128 + 2)).as_ref()).unwrap(), (1, format!("{}", std::u64::MAX).len()));
        assert_eq!(udigits(b"12 ").unwrap(), (12,2));
        assert_eq!(udigits(b"12-").unwrap(), (12,2));
        assert_eq!(udigits(b"12+").unwrap(), (12,2));
    }
    #[test]
    fn test_idigits() {
        assert_eq!(idigits(b""), None);
        assert_eq!(idigits(b"-1").unwrap(), (-1, 2));
        assert_eq!(idigits(b"0").unwrap(), (0,1));
        assert_eq!(idigits(b"1").unwrap(), (1,1));
        assert_eq!(idigits(b"12").unwrap(), (12,2));
        assert_eq!(idigits(format!("{}", std::i64::MAX).as_ref()).unwrap(), (std::i64::MAX, format!("{}", std::i64::MAX).len()));
        assert_eq!(idigits(format!("{}", std::i64::MAX as i128 + 1).as_ref()).unwrap(), (std::i64::MIN, format!("{}", std::i64::MAX).len()));
        assert_eq!(idigits(format!("{}", std::i64::MAX as i128 + 2).as_ref()).unwrap(), (std::i64::MIN + 1, format!("{}", std::i64::MAX).len()));
        assert_eq!(idigits(format!("{}", std::i64::MIN).as_ref()).unwrap(), (std::i64::MIN, format!("{}", std::i64::MIN).len()));
        assert_eq!(idigits(format!("{}", std::i64::MIN as i128 - 1).as_ref()).unwrap(), (std::i64::MAX, format!("{}", std::i64::MIN).len()));
        assert_eq!(idigits(format!("{}", std::i64::MIN as i128 - 2).as_ref()).unwrap(), (std::i64::MAX - 1, format!("{}", std::i64::MIN).len()));
    }
    #[test]
    fn test_octet() {
        for i in 0..('0' as u8) {
            assert!(octet(i).is_none())
        }
        for i in ('0' as u8)..('7' as u8 + 1) {
            assert!(octet(i).is_some())
        }
        for i in ('7' as u8 + 1)..255 {
            assert!(octet(i).is_none())
        }
    }
    #[test]
    fn test_uoctets() {
        assert_eq!(uoctets(b""), None);
        assert_eq!(uoctets(b"-1"), None);
        assert_eq!(uoctets(b"0").unwrap(), (0,1));
        assert_eq!(uoctets(b"1").unwrap(), (1,1));
        assert_eq!(uoctets(b"12").unwrap(), (0o12,2));
        assert_eq!(uoctets(format!("{:o}", std::u64::MAX).as_ref()).unwrap(), (std::u64::MAX, format!("{:o}", std::u64::MAX).len()));
        assert_eq!(uoctets(format!("{:o}", (std::u64::MAX as u128 + 1)).as_ref()).unwrap(), (0, format!("{:o}", std::u64::MAX).len()));
        assert_eq!(uoctets(format!("{:o}", (std::u64::MAX as u128 + 2)).as_ref()).unwrap(), (1, format!("{:o}", std::u64::MAX).len()));
    }
    #[test]
    fn test_hex() {
        for i in 0..('0' as u8) {
            assert!(hex(i).is_none())
        }
        for i in ('0' as u8)..('9' as u8 + 1) {
            assert!(hex(i).is_some())
        }
        for i in ('9' as u8 + 1)..('A' as u8) {
            assert!(hex(i).is_none())
        }
        for i in ('A' as u8)..('F' as u8 + 1) {
            assert!(hex(i).is_some())
        }
        for i in ('F' as u8 + 1)..('a' as u8) {
            assert!(hex(i).is_none())
        }
        for i in ('a' as u8)..('f' as u8 + 1) {
            assert!(hex(i).is_some())
        }
        for i in ('f' as u8 + 1)..255 {
            assert!(hex(i).is_none())
        }
    }
    #[test]
    fn test_uhexes() {
        assert_eq!(uhexes(b""), None);
        assert_eq!(uhexes(b"-1"), None);
        assert_eq!(uhexes(b"0").unwrap(), (0,1));
        assert_eq!(uhexes(b"1").unwrap(), (1,1));
        assert_eq!(uhexes(b"12").unwrap(), (0x12,2));
        assert_eq!(uhexes(format!("{:x}", std::u64::MAX).as_ref()).unwrap(), (std::u64::MAX, format!("{:x}", std::u64::MAX).len()));
        assert_eq!(uhexes(format!("{:x}", (std::u64::MAX as u128 + 1)).as_ref()).unwrap(), (0, format!("{:x}", std::u64::MAX).len() + 1));
        assert_eq!(uhexes(format!("{:x}", (std::u64::MAX as u128 + 2)).as_ref()).unwrap(), (1, format!("{:x}", std::u64::MAX).len() + 1));
        assert_eq!(uhexes(format!("{:X}", std::u64::MAX).as_ref()).unwrap(), (std::u64::MAX, format!("{:X}", std::u64::MAX).len()));
        assert_eq!(uhexes(format!("{:X}", (std::u64::MAX as u128 + 1)).as_ref()).unwrap(), (0, format!("{:X}", std::u64::MAX).len() + 1));
        assert_eq!(uhexes(format!("{:X}", (std::u64::MAX as u128 + 2)).as_ref()).unwrap(), (1, format!("{:X}", std::u64::MAX).len() + 1));
    }
}
