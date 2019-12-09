use super::lexer::{Lexer, Token};
use super::pmacros::{Macro, PContext};
use super::preprocessor;
use super::string::StringType;

#[derive(Clone, Debug, Copy, PartialEq, PartialOrd)]
#[repr(u8)]
enum Kind {
    IDE = 0, // usual id parts
    IDL = 1, // L, R, U, u for string starter
    IDR = 2,
    IDU = 3,
    IDu = 4,
    NUM = 5,  // 0-9
    SPA = 6,  // space
    QUO = 7,  // " or '
    RET = 8,  // return
    SLA = 9,  // slash
    COM = 10, // comma
    OPP = 11, // open parenthesis
    CLP = 12, // closing parenthesis
    NON = 13, // nothin
}

#[rustfmt::skip]
const MCHARS: [Kind; 256] = [
    // 0 NUL   1 SOH      2 STX      3 ETX      4 EOT      5 ENQ      6 ACK      7 BEL
    Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, //
    // 8 BS    9 HT       A NL       B VT       C NP       D CR       E SO       F SI
    Kind::NON, Kind::SPA, Kind::RET, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, //
    // 10 DLE  11 DC1     12 DC2     13 DC3     14 DC4     15 NAK     16 SYN     17 ETB
    Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, //
    // 18 CAN  19 EM      1A SUB     1B ESC     1C FS      1D GS      1E RS      1F US
    Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, //
    // 20 SP   21  !      22  "      23  #      24  $      25  %      26  &      27  '
    Kind::SPA, Kind::NON, Kind::QUO, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::QUO, //
    // 28  (   29  )      2A  *      2B  +      2C  ,      2D  -      2E  .      2F   /
    Kind::OPP, Kind::CLP, Kind::NON, Kind::NON, Kind::COM, Kind::NON, Kind::NON, Kind::SLA, //
    // 30  0   31  1      32  2      33  3      34  4      35  5      36  6      37  7
    Kind::NUM, Kind::NUM, Kind::NUM, Kind::NUM, Kind::NUM, Kind::NUM, Kind::NUM, Kind::NUM, //
    // 38  8   39  9      3A  :      3B  ;      3C  <      3D  =      3E  >      3F  ?
    Kind::NUM, Kind::NUM, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, //
    // 40  @   41  A      42  B      43  C      44  D      45  E      46  F      47  G
    Kind::NON, Kind::IDE, Kind::IDE, Kind::IDE, Kind::IDE, Kind::IDE, Kind::IDE, Kind::IDE, //
    // 48  H   49  I      4A  J      4B  K      4C  L      4D  M      4E  N      4F  O
    Kind::IDE, Kind::IDE, Kind::IDE, Kind::IDE, Kind::IDL, Kind::IDE, Kind::IDE, Kind::IDE, //
    // 50  P   51  Q      52  R      53  S      54  T      55  U      56  V      57  W
    Kind::IDE, Kind::IDE, Kind::IDR, Kind::IDE, Kind::IDE, Kind::IDU, Kind::IDE, Kind::IDE, //
    // 58  X   59  Y      5A  Z      5B  [      5C  \      5D  ]      5E  ^      5F  _
    Kind::IDE, Kind::IDE, Kind::IDE, Kind::NON, Kind::NON, Kind::NON, Kind::IDE, Kind::IDE, //
    // 60  `   61  a      62  b      63  c      64  d      65  e      66  f      67  g
    Kind::NON, Kind::IDE, Kind::IDE, Kind::IDE, Kind::IDE, Kind::IDE, Kind::IDE, Kind::IDE, //
    // 68  h   69  i      6A  j      6B  k      6C  l      6D  m      6E  n      6F  o
    Kind::IDE, Kind::IDE, Kind::IDE, Kind::IDE, Kind::IDE, Kind::IDE, Kind::IDE, Kind::IDE, //
    // 70  p   71  q      72  r      73  s      74  t      75  u      76  v      77  w
    Kind::IDE, Kind::IDE, Kind::IDE, Kind::IDE, Kind::IDE, Kind::IDu, Kind::IDE, Kind::IDE, //
    // 78  x   79  y      7A  z      7B  {      7C  |      7D  }      7E  ~      7F DEL
    Kind::IDE, Kind::IDE, Kind::IDE, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, //
    Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, //
    Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, //
    Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, //
    Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, //
    Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, //
    Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, //
    Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, //
    Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, //
    Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, //
    Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, //
    Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, //
    Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, //
    Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, //
    Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, //
    Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, //
    Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, Kind::NON, //
];

#[derive(Clone, Debug, PartialEq)]
pub(crate) enum MacroDefArg<'a> {
    Normal(&'a str),
    VaArgs,
    NamedVaArgs(&'a str),
}

#[derive(Clone, Debug, PartialEq)]
pub(crate) enum MacroArgToken<'a> {
    None(&'a [u8]),
    String(&'a [u8]),
    Id(&'a str),
    Space,
    OpenPar,
    ClosePar,
    Comma,
    Eom,
}

#[derive(Clone, Debug, PartialEq)]
pub(crate) enum MacroNode<'a> {
    Nothing(&'a [u8]),
    String(&'a [u8]),
    Id(&'a str),
    Space,
    Args(Vec<Vec<MacroNode<'a>>>),
    VaArgs(Vec<Vec<MacroNode<'a>>>),
}

impl<'a> Lexer<'a> {
    #[inline(always)]
    pub(crate) fn get_define_argument(&mut self) -> MacroDefArg<'a> {
        let spos = self.pos;
        loop {
            if self.pos < self.len {
                let c = self.next_char(0);
                let kind = unsafe { *preprocessor::PPCHARS.get_unchecked(c as usize) };
                if kind > preprocessor::Kind::NUM {
                    if c == b'.' {
                        if self.pos == spos {
                            self.pos += 3;
                            return MacroDefArg::VaArgs;
                        } else {
                            let id = unsafe {
                                std::str::from_utf8_unchecked(
                                    &self.buf.get_unchecked(spos..self.pos),
                                )
                            };
                            self.pos += 3;
                            return MacroDefArg::NamedVaArgs(id);
                        }
                    }
                    break;
                }
                self.pos += 1;
            } else {
                break;
            }
        }

        MacroDefArg::Normal(unsafe {
            std::str::from_utf8_unchecked(&self.buf.get_unchecked(spos..self.pos))
        })
    }

    #[inline(always)]
    pub(crate) fn skip_arg_none(&mut self) {
        loop {
            if self.pos < self.len {
                let c = self.next_char(0);
                let kind = unsafe { *MCHARS.get_unchecked(c as usize) };
                if kind != Kind::NON {
                    break;
                }
                self.pos += 1;
            } else {
                break;
            }
        }
    }

    #[inline(always)]
    pub(crate) fn next_arg_token(&mut self) -> MacroArgToken<'a> {
        loop {
            if self.pos < self.len {
                let c = self.next_char(0);
                let kind = unsafe { *MCHARS.get_unchecked(c as usize) };
                match kind {
                    Kind::IDE => {
                        return MacroArgToken::Id(self.get_preproc_identifier());
                    }
                    Kind::IDL => {
                        let p = self.pos;
                        self.pos += 1;
                        if self.get_special_string_char(StringType::L).is_some() {
                            let s = unsafe { self.buf.get_unchecked(p..self.pos) };
                            return MacroArgToken::String(s);
                        } else {
                            self.pos -= 1;
                            return MacroArgToken::Id(self.get_preproc_identifier());
                        }
                    }
                    Kind::IDR => {
                        let p = self.pos;
                        self.pos += 1;
                        if self.get_special_string_char(StringType::R).is_some() {
                            let s = unsafe { self.buf.get_unchecked(p..self.pos) };
                            return MacroArgToken::String(s);
                        } else {
                            self.pos -= 1;
                            return MacroArgToken::Id(self.get_preproc_identifier());
                        }
                    }
                    Kind::IDU => {
                        let p = self.pos;
                        self.pos += 1;
                        if self.get_special_string_char(StringType::UU).is_some() {
                            let s = unsafe { self.buf.get_unchecked(p..self.pos) };
                            return MacroArgToken::String(s);
                        } else {
                            self.pos -= 1;
                            return MacroArgToken::Id(self.get_preproc_identifier());
                        }
                    }
                    Kind::IDu => {
                        let p = self.pos;
                        self.pos += 1;
                        if self.get_special_string_char(StringType::U).is_some() {
                            let s = unsafe { self.buf.get_unchecked(p..self.pos) };
                            return MacroArgToken::String(s);
                        } else {
                            self.pos -= 1;
                            return MacroArgToken::Id(self.get_preproc_identifier());
                        }
                    }
                    Kind::NUM => {
                        let p = self.pos;
                        self.pos += 1;
                        self.skip_number(c);
                        let s = unsafe { self.buf.get_unchecked(p..self.pos) };
                        return MacroArgToken::None(s);
                    }
                    Kind::SPA => {
                        self.pos += 1;
                        skip_whites!(self);
                        return MacroArgToken::Space;
                    }
                    Kind::QUO => {
                        let p = self.pos;
                        self.pos += 1;
                        self.skip_by_delim(c);
                        let s = unsafe { self.buf.get_unchecked(p..self.pos) };
                        return MacroArgToken::String(s);
                    }
                    Kind::RET => {
                        self.pos += 1;
                        self.add_new_line();
                    }
                    Kind::SLA => {
                        let p = self.pos;
                        self.pos += 1;
                        if self.skip_slash_or_not() {
                            let s = unsafe { self.buf.get_unchecked(p..p + 1) };
                            return MacroArgToken::None(s);
                        }
                    }
                    Kind::COM => {
                        self.pos += 1;
                        return MacroArgToken::Comma;
                    }
                    Kind::OPP => {
                        self.pos += 1;
                        return MacroArgToken::OpenPar;
                    }
                    Kind::CLP => {
                        self.pos += 1;
                        return MacroArgToken::ClosePar;
                    }
                    Kind::NON => {
                        let p = self.pos;
                        self.skip_arg_none();
                        let s = unsafe { self.buf.get_unchecked(p..self.pos) };
                        return MacroArgToken::None(s);
                    }
                }
            } else {
                break;
            }
        }

        MacroArgToken::Eom
    }

    #[inline(always)]
    pub(crate) fn get_macro_tokens(&mut self, n_args: usize) -> Vec<Vec<MacroNode<'a>>> {
        let mut args = Vec::with_capacity(n_args);
        let mut stack = Vec::new();
        let mut arg = Vec::new();

        loop {
            let tok = self.next_arg_token();
            match tok {
                MacroArgToken::None(s) => {
                    arg.push(MacroNode::Nothing(s));
                }
                MacroArgToken::String(s) => {
                    arg.push(MacroNode::String(s));
                }
                MacroArgToken::Id(id) => {
                    arg.push(MacroNode::Id(id));
                }
                MacroArgToken::Space => {
                    if let Some(last) = arg.last() {
                        if *last != MacroNode::Space {
                            arg.push(MacroNode::Space);
                        }
                    } else {
                        arg.push(MacroNode::Space);
                    }
                }
                MacroArgToken::OpenPar => {
                    stack.push((args, arg));
                    args = Vec::new();
                    arg = Vec::new();
                }
                MacroArgToken::ClosePar => {
                    args.push(arg);
                    let (nargs, narg) = if let Some((nargs, mut narg)) = stack.pop() {
                        narg.push(MacroNode::Args(args));
                        (nargs, narg)
                    } else {
                        break;
                    };
                    args = nargs;
                    arg = narg;
                }
                MacroArgToken::Comma => {
                    args.push(arg);
                    arg = Vec::new();
                }
                MacroArgToken::Eom => {
                    break;
                }
            }
        }
        args
    }

    #[inline(always)]
    pub(crate) fn get_arguments(
        &mut self,
        n_args: usize,
        va_args: Option<&usize>,
    ) -> Option<Vec<Vec<MacroNode<'a>>>> {
        let spos = self.pos;
        skip_whites!(self);
        if self.pos < self.len {
            let c = self.next_char(0);
            if c != b'(' {
                self.pos = spos;
                return None;
            }
            self.pos += 1;
        }

        let mut args = self.get_macro_tokens(n_args);
        if va_args.is_none() {
            if args.len() != n_args {
                self.pos = spos;
                None
            } else {
                Some(args)
            }
        } else if args.len() < n_args {
            self.pos = spos;
            None
        } else {
            let va_pos = va_args.unwrap();
            let va = args.split_off(*va_pos);
            args.push(vec![MacroNode::VaArgs(va)]);
            Some(args)
        }
    }
}

impl<'a> MacroNode<'a> {
    pub(crate) fn eval_nodes(nodes: &[MacroNode<'a>], context: &PContext, out: &mut Vec<u8>) {
        let mut pos = 0;
        let len = nodes.len();
        while pos < len {
            let node = unsafe { nodes.get_unchecked(pos) };
            match node {
                MacroNode::Nothing(s) | MacroNode::String(s) => {
                    out.extend_from_slice(s);
                }
                MacroNode::Id(id) => {
                    if let Some(mac) = context.get(id) {
                        match mac {
                            Macro::Object(mac) => {
                                mac.eval(out, context);
                            }
                            Macro::Function(mac) => {
                                // we can have a white before arguments
                                pos += 1;
                                let node = unsafe { nodes.get_unchecked(pos) };
                                let node = match *node {
                                    MacroNode::Space => {
                                        pos += 1;
                                        unsafe { nodes.get_unchecked(pos) }
                                    }
                                    _ => node,
                                };
                                if let MacroNode::Args(args) = node {
                                    mac.eval_parsed_args(&args, context, out);
                                }
                            }
                        }
                    } else {
                        out.extend_from_slice(id.as_bytes());
                    }
                }
                MacroNode::Space => {
                    if pos != 0 && pos != len - 1 {
                        out.push(b' ');
                    }
                }
                MacroNode::Args(nodes) => {
                    out.push(b'(');
                    if let Some((last, nodes)) = nodes.split_last() {
                        for arg in nodes {
                            Self::eval_nodes(arg, context, out);
                            out.push(b',');
                        }
                        Self::eval_nodes(last, context, out);
                    }
                    out.push(b')');
                }
                MacroNode::VaArgs(nodes) => {
                    if let Some((last, nodes)) = nodes.split_last() {
                        for arg in nodes {
                            Self::eval_nodes(arg, context, out);
                            out.push(b',');
                        }
                        Self::eval_nodes(last, context, out);
                    }
                }
            }
            pos += 1;
        }
    }

    pub(crate) fn make_expr(nodes: &[MacroNode<'a>], out: &mut Vec<u8>) {
        let len = nodes.len();
        for (pos, node) in nodes.iter().enumerate() {
            match node {
                MacroNode::Nothing(s) | MacroNode::String(s) => {
                    out.extend_from_slice(s);
                }
                MacroNode::Id(id) => {
                    out.extend_from_slice(id.as_bytes());
                }
                MacroNode::Space => {
                    if pos != 0 && pos != len - 1 {
                        out.push(b' ');
                    }
                }
                MacroNode::Args(nodes) => {
                    out.push(b'(');
                    if let Some((last, nodes)) = nodes.split_last() {
                        for arg in nodes {
                            Self::make_expr(arg, out);
                            out.push(b',');
                        }
                        Self::make_expr(last, out);
                    }
                    out.push(b')');
                }
                MacroNode::VaArgs(nodes) => {
                    if let Some((last, nodes)) = nodes.split_last() {
                        for arg in nodes {
                            Self::make_expr(arg, out);
                            out.push(b',');
                        }
                        Self::make_expr(last, out);
                    }
                }
            }
        }
    }

    pub(crate) fn make_string(nodes: &[MacroNode<'a>], out: &mut Vec<u8>) {
        let len = nodes.len();
        for (pos, node) in nodes.iter().enumerate() {
            match node {
                MacroNode::Nothing(s) => {
                    out.extend_from_slice(s);
                }
                MacroNode::String(s) => {
                    // Need to escape chars
                    for c in s.iter() {
                        let c = *c;
                        if c == b'\'' || c == b'\"' || c == b'\n' {
                            out.push(b'\\');
                        }
                        out.push(c);
                    }
                }
                MacroNode::Id(id) => {
                    out.extend_from_slice(id.as_bytes());
                }
                MacroNode::Space => {
                    if pos != 0 && pos != len - 1 {
                        out.push(b' ');
                    }
                }
                MacroNode::Args(nodes) => {
                    out.push(b'(');
                    if let Some((last, nodes)) = nodes.split_last() {
                        for arg in nodes {
                            Self::make_string(arg, out);
                            out.push(b',');
                        }
                        Self::make_string(last, out);
                    }
                    out.push(b')');
                }
                MacroNode::VaArgs(nodes) => {
                    if let Some((last, nodes)) = nodes.split_last() {
                        for arg in nodes {
                            Self::make_string(arg, out);
                            out.push(b',');
                        }
                        Self::make_string(last, out);
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use MacroNode::*;

    #[test]
    fn test_arg1() {
        let mut p = Lexer::new(b"(a,b,c)");
        let exp = vec![vec![Id("a")], vec![Id("b")], vec![Id("c")]];
        let res = p.get_arguments(3, None).unwrap();

        assert_eq!(res, exp);
    }

    #[test]
    fn test_arg2() {
        let mut p = Lexer::new(b"(a, foo(d, e), c, bar())");
        let exp = vec![
            vec![Id("a")],
            vec![
                Space,
                Id("foo"),
                Args(vec![vec![Id("d")], vec![Space, Id("e")]]),
            ],
            vec![Space, Id("c")],
            vec![Space, Id("bar"), Args(vec![vec![]])],
        ];
        let res = p.get_arguments(4, None).unwrap();

        assert_eq!(res, exp);
    }

    #[test]
    fn test_arg3() {
        let mut p = Lexer::new(b"(   a /* comment */  , R\"delim(\")delim\",,,)");
        let exp = vec![
            vec![Space, Id("a"), Space],
            vec![Space, String(b"R\"delim(\")delim\"")],
            vec![],
            vec![],
            vec![],
        ];
        let res = p.get_arguments(5, None).unwrap();

        assert_eq!(res, exp);
    }

    #[test]
    fn test_make_expr1() {
        let mut p = Lexer::new(b"(   a /* comment */  , b + 1)");
        let args = Args(p.get_arguments(2, None).unwrap());
        let mut out = Vec::new();
        MacroNode::make_expr(&vec![args], &mut out);
        let res = std::str::from_utf8(&out).unwrap();
        let exp = "(a,b + 1)";

        assert_eq!(res, exp);
    }

    #[test]
    fn test_make_expr2() {
        let mut p = Lexer::new(b"(a, b, foo(x+1, y * 2, bar (z,t)))");
        let args = Args(p.get_arguments(3, None).unwrap());
        let mut out = Vec::new();
        MacroNode::make_expr(&vec![args], &mut out);
        let res = std::str::from_utf8(&out).unwrap();
        let exp = "(a,b,foo(x+1,y * 2,bar (z,t)))";

        assert_eq!(res, exp);
    }
}
