pub fn extend_with_u64(buf: &mut Vec<u8>, n: u64) {
    // TODO: can be optimized using "Three Optimization Tips for C++" talk
    let mut n = n;
    let mut s = vec![0; 20];
    let mut i = 19;
    loop {
        *s.get_mut(i).unwrap() = (n % 10) as u8 + b'0';
        if n < 10 {
            break;
        }
        n /= 10;
        i -= 1;
    }

    buf.extend_from_slice(&s.get(i..).unwrap());
}

pub fn extend_with_u32(buf: &mut Vec<u8>, n: u32) {
    // TODO: can be optimized using "Three Optimization Tips for C++" talk
    let mut n = n;
    let mut s = vec![0; 11];
    let mut i = 10;
    loop {
        *s.get_mut(i).unwrap() = (n % 10) as u8 + b'0';
        if n < 10 {
            break;
        }
        n /= 10;
        i -= 1;
    }

    buf.extend_from_slice(&s.get(i..).unwrap());
}
