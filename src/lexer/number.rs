// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use bitflags::bitflags;
use hashbrown::HashMap;
use lazy_static::lazy_static;

use super::lexer::{self, Lexer, Token};
use super::preprocessor::context::PreprocContext;

const POW_P_10: [f64; 309] = [
    1., 1e1, 1e2, 1e3, 1e4, 1e5, 1e6, 1e7, 1e8, 1e9, 1e10, 1e11, 1e12, 1e13, 1e14, 1e15, 1e16,
    1e17, 1e18, 1e19, 1e20, 1e21, 1e22, 1e23, 1e24, 1e25, 1e26, 1e27, 1e28, 1e29, 1e30, 1e31, 1e32,
    1e33, 1e34, 1e35, 1e36, 1e37, 1e38, 1e39, 1e40, 1e41, 1e42, 1e43, 1e44, 1e45, 1e46, 1e47, 1e48,
    1e49, 1e50, 1e51, 1e52, 1e53, 1e54, 1e55, 1e56, 1e57, 1e58, 1e59, 1e60, 1e61, 1e62, 1e63, 1e64,
    1e65, 1e66, 1e67, 1e68, 1e69, 1e70, 1e71, 1e72, 1e73, 1e74, 1e75, 1e76, 1e77, 1e78, 1e79, 1e80,
    1e81, 1e82, 1e83, 1e84, 1e85, 1e86, 1e87, 1e88, 1e89, 1e90, 1e91, 1e92, 1e93, 1e94, 1e95, 1e96,
    1e97, 1e98, 1e99, 1e100, 1e101, 1e102, 1e103, 1e104, 1e105, 1e106, 1e107, 1e108, 1e109, 1e110,
    1e111, 1e112, 1e113, 1e114, 1e115, 1e116, 1e117, 1e118, 1e119, 1e120, 1e121, 1e122, 1e123,
    1e124, 1e125, 1e126, 1e127, 1e128, 1e129, 1e130, 1e131, 1e132, 1e133, 1e134, 1e135, 1e136,
    1e137, 1e138, 1e139, 1e140, 1e141, 1e142, 1e143, 1e144, 1e145, 1e146, 1e147, 1e148, 1e149,
    1e150, 1e151, 1e152, 1e153, 1e154, 1e155, 1e156, 1e157, 1e158, 1e159, 1e160, 1e161, 1e162,
    1e163, 1e164, 1e165, 1e166, 1e167, 1e168, 1e169, 1e170, 1e171, 1e172, 1e173, 1e174, 1e175,
    1e176, 1e177, 1e178, 1e179, 1e180, 1e181, 1e182, 1e183, 1e184, 1e185, 1e186, 1e187, 1e188,
    1e189, 1e190, 1e191, 1e192, 1e193, 1e194, 1e195, 1e196, 1e197, 1e198, 1e199, 1e200, 1e201,
    1e202, 1e203, 1e204, 1e205, 1e206, 1e207, 1e208, 1e209, 1e210, 1e211, 1e212, 1e213, 1e214,
    1e215, 1e216, 1e217, 1e218, 1e219, 1e220, 1e221, 1e222, 1e223, 1e224, 1e225, 1e226, 1e227,
    1e228, 1e229, 1e230, 1e231, 1e232, 1e233, 1e234, 1e235, 1e236, 1e237, 1e238, 1e239, 1e240,
    1e241, 1e242, 1e243, 1e244, 1e245, 1e246, 1e247, 1e248, 1e249, 1e250, 1e251, 1e252, 1e253,
    1e254, 1e255, 1e256, 1e257, 1e258, 1e259, 1e260, 1e261, 1e262, 1e263, 1e264, 1e265, 1e266,
    1e267, 1e268, 1e269, 1e270, 1e271, 1e272, 1e273, 1e274, 1e275, 1e276, 1e277, 1e278, 1e279,
    1e280, 1e281, 1e282, 1e283, 1e284, 1e285, 1e286, 1e287, 1e288, 1e289, 1e290, 1e291, 1e292,
    1e293, 1e294, 1e295, 1e296, 1e297, 1e298, 1e299, 1e300, 1e301, 1e302, 1e303, 1e304, 1e305,
    1e306, 1e307, 1e308,
];

const POW_M_10: [f64; 309] = [
    1., 1e-1, 1e-2, 1e-3, 1e-4, 1e-5, 1e-6, 1e-7, 1e-8, 1e-9, 1e-10, 1e-11, 1e-12, 1e-13, 1e-14,
    1e-15, 1e-16, 1e-17, 1e-18, 1e-19, 1e-20, 1e-21, 1e-22, 1e-23, 1e-24, 1e-25, 1e-26, 1e-27,
    1e-28, 1e-29, 1e-30, 1e-31, 1e-32, 1e-33, 1e-34, 1e-35, 1e-36, 1e-37, 1e-38, 1e-39, 1e-40,
    1e-41, 1e-42, 1e-43, 1e-44, 1e-45, 1e-46, 1e-47, 1e-48, 1e-49, 1e-50, 1e-51, 1e-52, 1e-53,
    1e-54, 1e-55, 1e-56, 1e-57, 1e-58, 1e-59, 1e-60, 1e-61, 1e-62, 1e-63, 1e-64, 1e-65, 1e-66,
    1e-67, 1e-68, 1e-69, 1e-70, 1e-71, 1e-72, 1e-73, 1e-74, 1e-75, 1e-76, 1e-77, 1e-78, 1e-79,
    1e-80, 1e-81, 1e-82, 1e-83, 1e-84, 1e-85, 1e-86, 1e-87, 1e-88, 1e-89, 1e-90, 1e-91, 1e-92,
    1e-93, 1e-94, 1e-95, 1e-96, 1e-97, 1e-98, 1e-99, 1e-100, 1e-101, 1e-102, 1e-103, 1e-104,
    1e-105, 1e-106, 1e-107, 1e-108, 1e-109, 1e-110, 1e-111, 1e-112, 1e-113, 1e-114, 1e-115, 1e-116,
    1e-117, 1e-118, 1e-119, 1e-120, 1e-121, 1e-122, 1e-123, 1e-124, 1e-125, 1e-126, 1e-127, 1e-128,
    1e-129, 1e-130, 1e-131, 1e-132, 1e-133, 1e-134, 1e-135, 1e-136, 1e-137, 1e-138, 1e-139, 1e-140,
    1e-141, 1e-142, 1e-143, 1e-144, 1e-145, 1e-146, 1e-147, 1e-148, 1e-149, 1e-150, 1e-151, 1e-152,
    1e-153, 1e-154, 1e-155, 1e-156, 1e-157, 1e-158, 1e-159, 1e-160, 1e-161, 1e-162, 1e-163, 1e-164,
    1e-165, 1e-166, 1e-167, 1e-168, 1e-169, 1e-170, 1e-171, 1e-172, 1e-173, 1e-174, 1e-175, 1e-176,
    1e-177, 1e-178, 1e-179, 1e-180, 1e-181, 1e-182, 1e-183, 1e-184, 1e-185, 1e-186, 1e-187, 1e-188,
    1e-189, 1e-190, 1e-191, 1e-192, 1e-193, 1e-194, 1e-195, 1e-196, 1e-197, 1e-198, 1e-199, 1e-200,
    1e-201, 1e-202, 1e-203, 1e-204, 1e-205, 1e-206, 1e-207, 1e-208, 1e-209, 1e-210, 1e-211, 1e-212,
    1e-213, 1e-214, 1e-215, 1e-216, 1e-217, 1e-218, 1e-219, 1e-220, 1e-221, 1e-222, 1e-223, 1e-224,
    1e-225, 1e-226, 1e-227, 1e-228, 1e-229, 1e-230, 1e-231, 1e-232, 1e-233, 1e-234, 1e-235, 1e-236,
    1e-237, 1e-238, 1e-239, 1e-240, 1e-241, 1e-242, 1e-243, 1e-244, 1e-245, 1e-246, 1e-247, 1e-248,
    1e-249, 1e-250, 1e-251, 1e-252, 1e-253, 1e-254, 1e-255, 1e-256, 1e-257, 1e-258, 1e-259, 1e-260,
    1e-261, 1e-262, 1e-263, 1e-264, 1e-265, 1e-266, 1e-267, 1e-268, 1e-269, 1e-270, 1e-271, 1e-272,
    1e-273, 1e-274, 1e-275, 1e-276, 1e-277, 1e-278, 1e-279, 1e-280, 1e-281, 1e-282, 1e-283, 1e-284,
    1e-285, 1e-286, 1e-287, 1e-288, 1e-289, 1e-290, 1e-291, 1e-292, 1e-293, 1e-294, 1e-295, 1e-296,
    1e-297, 1e-298, 1e-299, 1e-300, 1e-301, 1e-302, 1e-303, 1e-304, 1e-305, 1e-306, 1e-307, 1e-308,
];

#[rustfmt::skip]
const HEX: [u64; 256] = [
    //  00  01  02  03  04  05  06  07  08  09
    16, 16, 16, 16, 16, 16, 16, 16, 16, 16, // 00
    16, 16, 16, 16, 16, 16, 16, 16, 16, 16, // 10
    16, 16, 16, 16, 16, 16, 16, 16, 16, 16, // 20
    16, 16, 16, 16, 16, 16, 16, 16, 16, 16, // 30
    16, 16, 16, 16, 16, 16, 16, 16, 0,  1,  // 40
    2,  3,  4,  5,  6,  7,  8,  9,  16, 16, // 50
    16, 16, 16, 16, 16, 10, 11, 12, 13, 14, // 60
    15, 16, 16, 16, 16, 16, 16, 16, 16, 16, // 70
    16, 16, 16, 16, 16, 16, 16, 16, 16, 16, // 80
    16, 16, 16, 16, 16, 16, 16, 10, 11, 12, // 90
    13, 14, 15, 16, 16, 16, 16, 16, 16, 16, // 100
    16, 16, 16, 16, 16, 16, 16, 16, 16, 16,
    16, 16, 16, 16, 16, 16, 16, 16, 16, 16,
    16, 16, 16, 16, 16, 16, 16, 16, 16, 16,
    16, 16, 16, 16, 16, 16, 16, 16, 16, 16,
    16, 16, 16, 16, 16, 16, 16, 16, 16, 16,
    16, 16, 16, 16, 16, 16, 16, 16, 16, 16,
    16, 16, 16, 16, 16, 16, 16, 16, 16, 16,
    16, 16, 16, 16, 16, 16, 16, 16, 16, 16,
    16, 16, 16, 16, 16, 16, 16, 16, 16, 16,
    16, 16, 16, 16, 16, 16, 16, 16, 16, 16,
    16, 16, 16, 16, 16, 16, 16, 16, 16, 16,
    16, 16, 16, 16, 16, 16, 16, 16, 16, 16,
    16, 16, 16, 16, 16, 16, 16, 16, 16, 16,
    16, 16, 16, 16, 16, 16, 16, 16, 16, 16,
    16, 16, 16, 16, 16, 16
];

bitflags! {
    struct Nums: u8 {
        const NON = 0;
        const NUM = 0b1;
        const HEX = 0b10;
        const QUO = 0b100;
        const LET = 0b1000;
    }
}

#[rustfmt::skip]
const NUMCHARS: [Nums; 256] = [
    // 0 NUL   1 SOH      2 STX      3 ETX      4 EOT      5 ENQ      6 ACK      7 BEL
    Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, //
    // 8 BS    9 HT       A NL       B VT       C NP       D CR       E SO       F SI
    Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, //
    // 10 DLE  11 DC1     12 DC2     13 DC3     14 DC4     15 NAK     16 SYN     17 ETB
    Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, //
    // 18 CAN  19 EM      1A SUB     1B ESC     1C FS      1D GS      1E RS      1F US
    Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, //
    // 20 SP   21  !      22  "      23  #      24  $      25  %      26  &      27  '
    Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::QUO, //
    // 28  (   29  )      2A  *      2B  +      2C  ,      2D  -      2E  .      2F   /
    Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, //
    // 30  0   31  1      32  2      33  3      34  4      35  5      36  6      37  7
    Nums::NUM, Nums::NUM, Nums::NUM, Nums::NUM, Nums::NUM, Nums::NUM, Nums::NUM, Nums::NUM, //
    // 38  8   39  9      3A  :      3B  ;      3C  <      3D  =      3E  >      3F  ?
    Nums::NUM, Nums::NUM, Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, //
    // 40  @   41  A      42  B      43  C      44  D      45  E      46  F      47  G
    Nums::NON, Nums::HEX, Nums::HEX, Nums::HEX, Nums::HEX, Nums::HEX, Nums::HEX, Nums::LET, //
    // 48  H   49  I      4A  J      4B  K      4C  L      4D  M      4E  N      4F  O
    Nums::LET, Nums::LET, Nums::LET, Nums::LET, Nums::LET, Nums::LET, Nums::LET, Nums::LET, //
    // 50  P   51  Q      52  R      53  S      54  T      55  U      56  V      57  W
    Nums::LET, Nums::LET, Nums::LET, Nums::LET, Nums::LET, Nums::LET, Nums::LET, Nums::LET, //
    // 58  X   59  Y      5A  Z      5B  [      5C  \      5D  ]      5E  ^      5F  _
    Nums::LET, Nums::LET, Nums::LET, Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, //
    // 60  `   61  a      62  b      63  c      64  d      65  e      66  f      67  g
    Nums::NON, Nums::HEX, Nums::HEX, Nums::HEX, Nums::HEX, Nums::HEX, Nums::HEX, Nums::LET, //
    // 68  h   69  i      6A  j      6B  k      6C  l      6D  m      6E  n      6F  o
    Nums::LET, Nums::LET, Nums::LET, Nums::LET, Nums::LET, Nums::LET, Nums::LET, Nums::LET, //
    // 70  p   71  q      72  r      73  s      74  t      75  u      76  v      77  w
    Nums::LET, Nums::LET, Nums::LET, Nums::LET, Nums::LET, Nums::LET, Nums::LET, Nums::LET, //
    // 78  x   79  y      7A  z      7B  {      7C  |      7D  }      7E  ~      7F DEL
    Nums::LET, Nums::LET, Nums::LET, Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, //
    Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, //
    Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, //
    Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, //
    Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, //
    Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, //
    Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, //
    Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, //
    Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, //
    Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, //
    Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, //
    Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, //
    Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, //
    Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, //
    Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, //
    Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, //
    Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, Nums::NON, //
];

#[derive(Clone)]
enum IntType {
    U,
    L,
    UL,
    LL,
    ULL,
    UserDefined(String),
}

lazy_static! {
    static ref INT_SUFFIXES: HashMap<&'static str, IntType> = {
        let mut map = HashMap::with_capacity(32);
        map.insert("u", IntType::U);
        map.insert("U", IntType::U);
        map.insert("l", IntType::L);
        map.insert("L", IntType::L);
        map.insert("ul", IntType::UL);
        map.insert("Ul", IntType::UL);
        map.insert("uL", IntType::UL);
        map.insert("UL", IntType::UL);
        map.insert("lu", IntType::UL);
        map.insert("lU", IntType::UL);
        map.insert("Lu", IntType::UL);
        map.insert("LU", IntType::UL);
        map.insert("ll", IntType::LL);
        map.insert("LL", IntType::LL);
        map.insert("llu", IntType::ULL);
        map.insert("llU", IntType::ULL);
        map.insert("LLu", IntType::ULL);
        map.insert("LLU", IntType::ULL);
        map.insert("ull", IntType::ULL);
        map.insert("Ull", IntType::ULL);
        map.insert("uLL", IntType::ULL);
        map.insert("ULL", IntType::ULL);
        map
    };
}

#[derive(Clone)]
enum FloatType {
    F,
    L,
    UserDefined(String),
}

lazy_static! {
    static ref FLOAT_SUFFIXES: HashMap<&'static str, FloatType> = {
        let mut map = HashMap::with_capacity(4);
        map.insert("f", FloatType::F);
        map.insert("F", FloatType::F);
        map.insert("l", FloatType::L);
        map.insert("L", FloatType::L);
        map
    };
}

#[inline(always)]
pub(crate) fn get_decimal(dec: u64, exp: i64) -> f64 {
    if exp == 0 {
        dec as f64
    } else if exp < 0 {
        let exp = (-exp) as usize;
        if exp <= 308 {
            (dec as f64) * unsafe { POW_M_10.get_unchecked(exp) }
        } else if exp <= 327 {
            ((dec as f64) * unsafe { POW_M_10.get_unchecked(exp - 19) })
                * unsafe { POW_M_10.get_unchecked(19) }
        } else {
            0.
        }
    } else if exp <= 308 {
        let exp = exp as usize;
        (dec as f64) * unsafe { POW_P_10.get_unchecked(exp) }
    } else {
        std::f64::INFINITY
    }
}

#[inline(always)]
pub(crate) fn get_hex_decimal(dec: u64, exp: i64) -> f64 {
    if exp == 0 {
        dec as f64
    } else {
        (dec as f64) * (exp as f64).exp2()
    }
}

impl<'a, PC: PreprocContext> Lexer<'a, PC> {
    #[inline(always)]
    pub(crate) fn get_exponent(&mut self) -> i64 {
        if self.buf.has_char() {
            let c = self.buf.next_char();
            let sign = c == b'-';
            let c = if sign || c == b'+' {
                self.buf.inc();
                self.buf.next_char()
            } else {
                c
            };

            self.buf.inc();
            let first = u64::from(c - b'0');
            let num = self.get_int(first) as i64;
            if sign {
                -num
            } else {
                num
            }
        } else {
            0
        }
    }

    #[inline(always)]
    pub(crate) fn get_number_after_dot(&mut self, start: u64) -> (u64, i64) {
        let spos = self.buf.pos();
        let mut num = start;
        loop {
            if self.buf.has_char() {
                let c = self.buf.next_char();
                if b'0' <= c && c <= b'9' {
                    self.buf.inc();
                    if num > (std::u64::MAX >> 7) {
                        let shift = (self.buf.pos() - spos) as i64;
                        let exp = self.skip_and_get_exponent();
                        return (num, exp - shift);
                    }
                    num = 10 * num + u64::from(c - b'0');
                } else if c == b'e' || c == b'E' {
                    self.buf.inc();
                    let shift = (self.buf.pos() - spos) as i64;
                    let exp = self.get_exponent();
                    return (num, exp - shift);
                } else {
                    let shift = (self.buf.pos() + 1 - spos) as i64;
                    return (num, -shift);
                }
            } else {
                let shift = (self.buf.pos() - spos) as i64;
                return (num, -shift);
            }
        }
    }

    #[inline(always)]
    pub(crate) fn skip_and_get_exponent(&mut self) -> i64 {
        loop {
            if self.buf.has_char() {
                let c = self.buf.next_char();
                if b'0' <= c && c <= b'9' {
                    self.buf.inc();
                    continue;
                } else if c == b'e' || c == b'E' {
                    self.buf.inc();
                    return self.get_exponent();
                } else {
                    return 0;
                }
            } else {
                return 0;
            }
        }
    }

    #[inline(always)]
    pub(crate) fn get_dot_or_number(&mut self) -> Token {
        if self.buf.has_char() {
            let c = self.buf.next_char();
            if b'0' <= c && c <= b'9' {
                self.buf.inc();
                let (dec, exp) = self.get_number_after_dot(u64::from(c - b'0'));
                return self.get_typed_float(get_decimal(dec, exp));
            } else if c == b'.' {
                self.buf.inc();
                if self.buf.has_char() {
                    let c = self.buf.next_char();
                    if c == b'.' {
                        self.buf.inc();
                        return Token::Ellipsis;
                    }
                }
            } else if c == b'*' {
                self.buf.inc();
                return Token::DotStar;
            }
        }
        Token::Dot
    }

    #[inline(always)]
    pub(crate) fn get_hex_digit(c: u8) -> u64 {
        unsafe { *HEX.get_unchecked(c as usize) }
    }

    #[inline(always)]
    pub(crate) fn get_base_hex(&mut self) -> u64 {
        let mut num = 0;
        loop {
            if self.buf.has_char() {
                let c = self.buf.next_char();
                let n = Self::get_hex_digit(c);
                if n < 16 {
                    self.buf.inc();
                    num = 16 * num + n;
                } else if c == b'\'' {
                    self.buf.inc();
                } else {
                    break;
                }
            } else {
                break;
            }
        }
        num
    }

    #[inline(always)]
    pub(crate) fn get_hex_after_dot(&mut self, start: u64) -> (u64, i64) {
        let spos = self.buf.pos();
        let mut num = start;
        loop {
            if self.buf.has_char() {
                let c = self.buf.next_char();
                self.buf.inc();
                let d = Self::get_hex_digit(c);
                if num <= (std::u64::MAX / 16) && d < 16 {
                    num = 16 * num + d;
                } else if c == b'p' || c == b'P' {
                    let shift = (self.buf.pos() - spos) as i64;
                    let exp = self.get_exponent();
                    return (num, exp - 4 * shift);
                } else {
                    let shift = (self.buf.pos() - spos) as i64;
                    return (num, -4 * shift);
                }
            } else {
                let shift = (self.buf.pos() - spos) as i64;
                return (num, -4 * shift);
            }
        }
    }

    #[inline(always)]
    pub(crate) fn get_hex(&mut self) -> Token {
        let num = self.get_base_hex();

        let c = self.buf.next_char();
        if c == b'.' {
            self.buf.inc();
            let c = self.buf.next_char();
            self.buf.inc();
            let d = Self::get_hex_digit(c);
            if d < 16 {
                if num > (std::u64::MAX / 16) {
                    let _ = self.get_hex_after_dot(0);
                    return self.get_typed_float(num as f64);
                }
                let num = 16 * num + d;
                let (dec, exp) = self.get_hex_after_dot(num);
                self.get_typed_float(get_hex_decimal(dec, exp))
            } else if c == b'p' || c == b'P' {
                let exp = self.get_exponent();
                self.get_typed_float(get_hex_decimal(num, exp))
            } else {
                self.get_typed_float_suf(c, num as f64)
            }
        } else if c == b'p' || c == b'P' {
            self.buf.inc();
            let exp = self.get_exponent();
            self.get_typed_float(get_hex_decimal(num, exp))
        } else {
            self.get_typed_int(num)
        }
    }

    #[inline(always)]
    pub(crate) fn get_oct(&mut self, start: u64) -> Token {
        let mut num = start;
        loop {
            if self.buf.has_char() {
                let c = self.buf.next_char();
                if b'0' <= c && c <= b'7' {
                    self.buf.inc();
                    num = 8 * num + u64::from(c - b'0');
                } else if c == b'\'' {
                    self.buf.inc();
                } else {
                    break;
                }
            } else {
                break;
            }
        }
        self.get_typed_int(num)
    }

    #[inline(always)]
    fn get_bin(&mut self) -> Token {
        let mut num = 0;
        loop {
            if self.buf.has_char() {
                let c = self.buf.next_char();
                if b'0' <= c && c <= b'1' {
                    self.buf.inc();
                    num = 2 * num + u64::from(c - b'0');
                } else if c == b'\'' {
                    self.buf.inc();
                } else {
                    break;
                }
            } else {
                break;
            }
        }
        self.get_typed_int(num)
    }

    #[inline(always)]
    pub(crate) fn get_int(&mut self, start: u64) -> u64 {
        let mut num = start;
        loop {
            if self.buf.has_char() {
                let c = self.buf.next_char();
                if b'0' <= c && c <= b'9' {
                    self.buf.inc();
                    // TODO: not correct here... we should handle number differently (using biguint or something similar
                    if num <= std::u64::MAX / 10 {
                        num = 10 * num + u64::from(c - b'0');
                    }
                } else if c == b'\'' {
                    self.buf.inc();
                } else {
                    break;
                }
            } else {
                break;
            }
        }
        num
    }

    #[inline(always)]
    pub(crate) fn get_typed_int(&mut self, num: u64) -> Token {
        if let Some(suf) = self.get_int_type() {
            match suf {
                IntType::U => Token::LiteralUInt(num),
                IntType::L => Token::LiteralLong(num),
                IntType::UL => Token::LiteralULong(num),
                IntType::LL => Token::LiteralLongLong(num),
                IntType::ULL => Token::LiteralULongLong(num),
                IntType::UserDefined(suf) => Token::LiteralIntUD(Box::new((num, suf))),
            }
        } else {
            Token::LiteralInt(num)
        }
    }

    #[inline(always)]
    fn get_int_type(&mut self) -> Option<IntType> {
        if self.buf.has_char() {
            let c = self.buf.next_char();
            let kind = unsafe { lexer::CHARS.get_unchecked(c as usize) };
            if *kind != lexer::Kind::NON {
                // we've a suffix
                self.buf.inc();
                let id = self.get_identifier_str();
                if let Some(suf) = INT_SUFFIXES.get(id) {
                    return Some(suf.clone());
                } else {
                    return Some(IntType::UserDefined(id.to_string()));
                }
            }
        }
        None
    }

    #[inline(always)]
    pub(crate) fn get_typed_float(&mut self, num: f64) -> Token {
        if self.buf.has_char() {
            let c = self.buf.next_char();
            self.get_typed_float_suf(c, num)
        } else {
            Token::LiteralDouble(num)
        }
    }

    #[inline(always)]
    fn get_float_type(&mut self, suf: u8) -> Option<FloatType> {
        let kind = unsafe { lexer::CHARS.get_unchecked(suf as usize) };
        if *kind != lexer::Kind::NON {
            // we've a suffix
            self.buf.inc();
            let id = self.get_identifier_str();
            if let Some(suf) = FLOAT_SUFFIXES.get(id) {
                Some(suf.clone())
            } else {
                Some(FloatType::UserDefined(id.to_string()))
            }
        } else {
            None
        }
    }

    #[inline(always)]
    pub(crate) fn get_typed_float_suf(&mut self, suf: u8, num: f64) -> Token {
        if let Some(suf) = self.get_float_type(suf) {
            self.buf.inc();
            match suf {
                FloatType::F => Token::LiteralFloat(num),
                FloatType::L => Token::LiteralLongDouble(num),
                FloatType::UserDefined(suf) => Token::LiteralFloatUD(Box::new((num, suf))),
            }
        } else {
            Token::LiteralDouble(num)
        }
    }

    #[inline(always)]
    pub(crate) fn get_number(&mut self, start: u64) -> Token {
        let num = start;
        if self.buf.has_char() {
            if num == 0 {
                let c = self.buf.next_char();
                if c == b'x' || c == b'X' {
                    // hex
                    self.buf.inc();
                    return self.get_hex();
                } else if c == b'b' || c == b'B' {
                    // binary
                    self.buf.inc();
                    return self.get_bin();
                } else if b'0' <= c && c <= b'9' {
                    // octal
                    self.buf.inc();
                    return self.get_oct(u64::from(c - b'0'));
                } else if c == b'e' || c == b'E' {
                    // We've 0e....: useless so just consume exponent and return 0.
                    self.buf.inc();
                    let _ = self.get_exponent();
                    return self.get_typed_float(0.);
                } else if c == b'.' {
                    self.buf.inc();
                    if self.buf.has_char() {
                        let c = self.buf.next_char();
                        if b'0' <= c && c <= b'9' {
                            self.buf.inc();
                            let (dec, exp) = self.get_number_after_dot(u64::from(c - b'0'));
                            return self.get_typed_float(get_decimal(dec, exp));
                        } else if c == b'e' || c == b'E' {
                            self.buf.inc();
                            let _ = self.get_exponent();
                            return self.get_typed_float(0.);
                        } else {
                            return self.get_typed_float_suf(c, 0.);
                        }
                    } else {
                        return self.get_typed_float(0.);
                    }
                }
            } else {
                let num = self.get_int(num);
                if self.buf.has_char() {
                    let c = self.buf.next_char();
                    if c == b'.' {
                        self.buf.inc();
                        let c = self.buf.next_char();
                        if b'0' <= c && c <= b'9' {
                            self.buf.inc();
                            if num > (std::u64::MAX >> 7) {
                                let exp = self.skip_and_get_exponent();
                                return self.get_typed_float(get_decimal(num, exp));
                            }
                            let num = 10 * num + u64::from(c - b'0');
                            let (dec, exp) = self.get_number_after_dot(num);

                            return self.get_typed_float(get_decimal(dec, exp));
                        } else if c == b'e' || c == b'E' {
                            self.buf.inc();
                            let exp = self.get_exponent();
                            return self.get_typed_float(get_decimal(num, exp));
                        } else {
                            return self.get_typed_float_suf(c, num as f64);
                        }
                    } else if c == b'e' || c == b'E' {
                        self.buf.inc();
                        let exp = self.get_exponent();
                        return self.get_typed_float(get_decimal(num, exp));
                    } else {
                        return self.get_typed_int(num);
                    }
                } else {
                    return Token::LiteralInt(num);
                }
            }
        }

        Token::LiteralInt(num)
    }

    #[inline(always)]
    fn skip_hex(&mut self) {
        loop {
            if self.buf.has_char() {
                let c = self.buf.next_char();
                let kind = unsafe { *NUMCHARS.get_unchecked(c as usize) };
                if !kind.intersects(Nums::HEX | Nums::NUM | Nums::QUO) {
                    break;
                }
                self.buf.inc();
            } else {
                break;
            }
        }
    }

    #[inline(always)]
    fn skip_int(&mut self) {
        loop {
            if self.buf.has_char() {
                let c = self.buf.next_char();
                let kind = unsafe { *NUMCHARS.get_unchecked(c as usize) };
                if !kind.intersects(Nums::NUM | Nums::QUO) {
                    break;
                }
                self.buf.inc();
            } else {
                break;
            }
        }
    }

    #[inline(always)]
    fn skip_exponent(&mut self) {
        if self.buf.has_char() {
            let c = self.buf.next_char();
            if c == b'+' || c == b'-' {
                self.buf.inc();
            }
            self.skip_int();
        }
    }

    #[inline(always)]
    fn skip_decimal(&mut self) {
        self.skip_int();
        if self.buf.has_char() {
            let c = self.buf.next_char();
            if c == b'e' || c == b'E' {
                self.buf.inc();
                self.skip_exponent();
            }
        }
    }

    #[inline(always)]
    fn skip_hex_decimal(&mut self) {
        self.skip_hex();
        if self.buf.has_char() {
            let c = self.buf.next_char();
            if c == b'p' || c == b'P' {
                self.buf.inc();
                self.skip_exponent();
            }
        }
    }

    #[inline(always)]
    fn skip_type(&mut self) {
        if self.buf.has_char() {
            let c = self.buf.next_char();
            let kind = unsafe { *NUMCHARS.get_unchecked(c as usize) };
            if kind.intersects(Nums::HEX | Nums::LET) {
                self.buf.inc();
                // just consume the id
                self.get_identifier_str();
            }
        }
    }

    #[inline(always)]
    pub(crate) fn skip_number(&mut self, start: u8) {
        if self.buf.has_char() {
            if start == b'0' {
                let c = self.buf.next_char();
                if c == b'x' || c == b'X' {
                    self.buf.inc();
                    self.skip_hex();
                    if self.buf.has_char() {
                        let c = self.buf.next_char();
                        if c == b'.' {
                            self.buf.inc();
                            self.skip_hex_decimal();
                        } else if c == b'p' || c == b'P' {
                            self.buf.inc();
                            self.skip_exponent();
                        }
                    }
                } else if c == b'b' || c == b'B' || (b'0' <= c && c <= b'9') {
                    self.buf.inc();
                    self.skip_int();
                } else if c == b'e' || c == b'E' {
                    self.buf.inc();
                    self.skip_exponent();
                } else if c == b'.' {
                    self.buf.inc();
                    self.skip_decimal();
                }
                self.skip_type();
            } else {
                self.skip_int();
                if self.buf.has_char() {
                    let c = self.buf.next_char();
                    if c == b'.' {
                        self.buf.inc();
                        self.skip_decimal();
                    } else if c == b'e' || c == b'E' {
                        self.buf.inc();
                        self.skip_exponent();
                    }
                    self.skip_type();
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::lexer::preprocessor::context::DefaultContext;
    use pretty_assertions::assert_eq;

    #[test]
    fn test_number_hex() {
        let mut p = Lexer::<DefaultContext>::new(b"0x12345 0xabcdef 0XA'1b2'C3D'4e5 0xaB1ul");
        assert_eq!(p.next_token().tok, Token::LiteralInt(0x12345));
        assert_eq!(p.next_token().tok, Token::LiteralInt(0xabcdef));
        assert_eq!(p.next_token().tok, Token::LiteralInt(0xa1b2c3d4e5));
        assert_eq!(p.next_token().tok, Token::LiteralULong(0xab1));
    }

    #[test]
    fn test_number_oct() {
        let mut p = Lexer::<DefaultContext>::new(b"012345 01357 012'34ul");
        assert_eq!(p.next_token().tok, Token::LiteralInt(0o12345));
        assert_eq!(p.next_token().tok, Token::LiteralInt(0o1357));
        assert_eq!(p.next_token().tok, Token::LiteralULong(0o1234));
    }

    #[test]
    fn test_number_bin() {
        let mut p = Lexer::<DefaultContext>::new(b"0b110'001'110'010'010'110'011'101 0b1001ul");
        assert_eq!(
            p.next_token().tok,
            Token::LiteralInt(0b110001110010010110011101)
        );
        assert_eq!(p.next_token().tok, Token::LiteralULong(0b1001));
    }

    #[test]
    fn test_number_dec() {
        let mut p = Lexer::<DefaultContext>::new(b"123 123e45 123e+45 123e-45");
        assert_eq!(p.next_token().tok, Token::LiteralInt(123));
        assert_eq!(p.next_token().tok, Token::LiteralDouble(123e45));
        assert_eq!(p.next_token().tok, Token::LiteralDouble(123e45));
        assert_eq!(p.next_token().tok, Token::LiteralDouble(123e-45));

        let mut p = Lexer::<DefaultContext>::new(b"123. 123.e45 123.e+45 123.e-45");
        assert_eq!(p.next_token().tok, Token::LiteralDouble(123.));
        assert_eq!(p.next_token().tok, Token::LiteralDouble(123e45));
        assert_eq!(p.next_token().tok, Token::LiteralDouble(123e45));
        assert_eq!(p.next_token().tok, Token::LiteralDouble(123e-45));

        let mut p = Lexer::<DefaultContext>::new(b"123.f 123.e45F 123.e+45L 123.e-45l");
        assert_eq!(p.next_token().tok, Token::LiteralFloat(123.));
        assert_eq!(p.next_token().tok, Token::LiteralFloat(123e45));
        assert_eq!(p.next_token().tok, Token::LiteralLongDouble(123e45));
        assert_eq!(p.next_token().tok, Token::LiteralLongDouble(123e-45));

        let mut p = Lexer::<DefaultContext>::new(b"123.456 123.456e78 123.456e+78 123.456e-78 1.79769313486231570814527423731704357e+308L 2.2250738585072014e-308F");
        assert_eq!(p.next_token().tok, Token::LiteralDouble(123.456));
        assert_eq!(p.next_token().tok, Token::LiteralDouble(123.456e78));
        assert_eq!(p.next_token().tok, Token::LiteralDouble(123.456e78));
        assert_eq!(p.next_token().tok, Token::LiteralDouble(123.456e-78));
        assert_eq!(
            p.next_token().tok,
            Token::LiteralLongDouble(1.79769313486231570814527423731704357e+308)
        );
        assert_eq!(
            p.next_token().tok,
            Token::LiteralFloat(2.2250738585072014e-308)
        );

        let mut p = Lexer::<DefaultContext>::new(b"0.123 0.123e45 0.123e+45 0.123e-45");
        assert_eq!(p.next_token().tok, Token::LiteralDouble(0.123));
        assert_eq!(p.next_token().tok, Token::LiteralDouble(0.123e45));
        assert_eq!(p.next_token().tok, Token::LiteralDouble(0.123e45));
        assert_eq!(p.next_token().tok, Token::LiteralDouble(0.123e-45));

        let mut p = Lexer::<DefaultContext>::new(b".123 .123e45 .123e+45 .123e-45");
        assert_eq!(p.next_token().tok, Token::LiteralDouble(0.123));
        assert_eq!(p.next_token().tok, Token::LiteralDouble(0.123e45));
        assert_eq!(p.next_token().tok, Token::LiteralDouble(0.123e45));
        assert_eq!(p.next_token().tok, Token::LiteralDouble(0.123e-45));

        let mut p = Lexer::<DefaultContext>::new(b"0 0. .0 0.0");
        assert_eq!(p.next_token().tok, Token::LiteralInt(0));
        assert_eq!(p.next_token().tok, Token::LiteralDouble(0.));
        assert_eq!(p.next_token().tok, Token::LiteralDouble(0.));
        assert_eq!(p.next_token().tok, Token::LiteralDouble(0.));

        let mut p = Lexer::<DefaultContext>::new(b"123 123u 123U 123llu 123LLu 123llU 123LLU 123ull 123Ull 123ULL 123lu 123ul 123uL 123L");
        assert_eq!(p.next_token().tok, Token::LiteralInt(123));
        assert_eq!(p.next_token().tok, Token::LiteralUInt(123));
        assert_eq!(p.next_token().tok, Token::LiteralUInt(123));
        assert_eq!(p.next_token().tok, Token::LiteralULongLong(123));
        assert_eq!(p.next_token().tok, Token::LiteralULongLong(123));
        assert_eq!(p.next_token().tok, Token::LiteralULongLong(123));
        assert_eq!(p.next_token().tok, Token::LiteralULongLong(123));
        assert_eq!(p.next_token().tok, Token::LiteralULongLong(123));
        assert_eq!(p.next_token().tok, Token::LiteralULongLong(123));
        assert_eq!(p.next_token().tok, Token::LiteralULongLong(123));
        assert_eq!(p.next_token().tok, Token::LiteralULong(123));
        assert_eq!(p.next_token().tok, Token::LiteralULong(123));
        assert_eq!(p.next_token().tok, Token::LiteralULong(123));
        assert_eq!(p.next_token().tok, Token::LiteralLong(123));

        let mut p = Lexer::<DefaultContext>::new(b"0x1.2p3 0x1.2p3F 0xA.Bp-1 0XAB1P-3");
        assert_eq!(p.next_token().tok, Token::LiteralDouble(9.0));
        assert_eq!(p.next_token().tok, Token::LiteralFloat(9.0));
        assert_eq!(p.next_token().tok, Token::LiteralDouble(5.34375));
        assert_eq!(p.next_token().tok, Token::LiteralDouble(342.125));
    }

    #[test]
    fn test_number_ud() {
        let mut p = Lexer::<DefaultContext>::new(b"12_km 12.34_km");
        assert_eq!(
            p.next_token().tok,
            Token::LiteralIntUD(Box::new((12, "_km".to_string())))
        );
        assert_eq!(
            p.next_token().tok,
            Token::LiteralFloatUD(Box::new((12.34, "_km".to_string())))
        );
    }
}
