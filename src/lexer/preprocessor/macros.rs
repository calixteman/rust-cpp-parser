use std::cell::Cell;
use std::fmt;

use super::context::{EmptyContext, PreprocContext};
use super::macro_args::MacroNode;
use crate::lexer::buffer::FileInfo;
use crate::lexer::{tools, Lexer};

#[derive(Clone)]
pub struct MacroObject {
    out: Vec<u8>,
    has_id: bool,
    pub(crate) in_use: Cell<bool>,
    pub(crate) file_info: FileInfo,
}

#[derive(Clone)]
pub struct MacroFunction {
    out: Vec<u8>,
    actions: Vec<Action>,
    n_args: usize,
    pub(crate) in_use: Cell<bool>,
    pub(crate) va_args: Option<usize>,
    pub(crate) file_info: FileInfo,
}

impl fmt::Debug for MacroFunction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let out: Vec<_> = self.out.iter().map(|x| *x as char).enumerate().collect();
        write!(
            f,
            "Macro Function: {:?}\n{:?}\nn_args: {}\nin_use: {:?}",
            out, self.actions, self.n_args, self.in_use
        )
    }
}

impl fmt::Debug for MacroObject {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let out: Vec<_> = self.out.iter().map(|x| *x as char).enumerate().collect();
        write!(f, "Macro Object: {:?}\nin_use: {:?}", out, self.in_use)
    }
}

#[derive(Clone, Debug)]
pub enum Macro {
    Object(MacroObject),
    Function(MacroFunction),
    Line(MacroLine),
    File(MacroFile),
    Counter(MacroCounter),
}

#[derive(Clone, Debug)]
pub enum MacroType<'a> {
    None,
    Object(&'a MacroObject),
    Function((usize, Option<usize>)),
    Line(MacroLine),
    File(MacroFile),
    Counter(&'a MacroCounter),
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Action {
    Arg(usize),
    Concat(usize),
    Stringify(usize),
    Chunk(usize),
}

impl MacroFunction {
    #[inline(always)]
    pub(crate) fn new(
        out: Vec<u8>,
        actions: Vec<Action>,
        n_args: usize,
        va_args: Option<usize>,
        file_info: FileInfo,
    ) -> Self {
        Self {
            out,
            actions,
            n_args,
            in_use: Cell::new(false),
            va_args,
            file_info,
        }
    }

    #[inline(always)]
    pub(crate) fn eval_parsed_args<'a, PC: PreprocContext>(
        &self,
        args: &[Vec<MacroNode<'a>>],
        context: &PC,
        info: &FileInfo,
        out: &mut Vec<u8>,
    ) {
        let mut out_pos = 0;
        let mut output = Vec::new();

        for action in self.actions.iter() {
            match action {
                Action::Arg(pos) => {
                    // gcc/clang are smart: they add whites only when it's required
                    // tbh, I don't care so much, the goal is just to have paste avoidance
                    if let Some(last) = output.last() {
                        if *last != b' ' {
                            output.push(b' ');
                        }
                    }
                    if let Some(arg) = args.get(*pos) {
                        MacroNode::eval_nodes(arg, context, info, &mut output, false);
                        if let Some(last) = output.last() {
                            if *last != b' ' {
                                output.push(b' ');
                            }
                        }
                        /*if *output.last().unwrap() != b' ' {
                            output.push(b' ');
                        }*/
                    }
                }
                Action::Concat(pos) => {
                    MacroNode::make_expr(&args[*pos], &mut output);
                }
                Action::Stringify(pos) => {
                    MacroNode::make_string(&args[*pos], &mut output);
                }
                Action::Chunk(pos) => {
                    output.extend_from_slice(unsafe { &self.out.get_unchecked(out_pos..*pos) });
                    out_pos = *pos;
                }
            }
        }
        output.extend_from_slice(unsafe { &self.out.get_unchecked(out_pos..) });

        let mut lexer = Lexer::<EmptyContext>::new(&output);
        self.in_use.set(true);
        lexer.macro_final_eval(out, context, info);
        self.in_use.set(false);
    }

    #[inline(always)]
    pub(crate) fn len(&self) -> usize {
        self.n_args
    }

    #[inline(always)]
    pub(crate) fn is_empty(&self) -> bool {
        self.n_args == 0
    }

    #[inline(always)]
    pub(crate) fn is_valid(&self, n: usize) -> bool {
        if self.va_args.is_none() {
            self.n_args == n
        } else {
            n >= self.n_args - 1
        }
    }
}

impl MacroObject {
    #[inline(always)]
    pub(crate) fn new(out: Vec<u8>, has_id: bool, file_info: FileInfo) -> Self {
        Self {
            out,
            has_id,
            in_use: Cell::new(false),
            file_info,
        }
    }

    #[inline(always)]
    pub(crate) fn eval<'a, PC: PreprocContext>(
        &'a self,
        out: &mut Vec<u8>,
        context: &PC,
        info: &FileInfo,
    ) {
        if let Some(last) = out.last() {
            if *last != b' ' {
                out.push(b' ');
            }
        }
        if self.has_id {
            let mut lexer = Lexer::<EmptyContext>::new(&self.out);
            self.in_use.set(true);
            lexer.macro_final_eval(out, context, info);
            self.in_use.set(false);
        } else {
            out.extend_from_slice(&self.out);
        }
        if let Some(last) = out.last() {
            if *last != b' ' {
                out.push(b' ');
            }
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct MacroLine {}

impl MacroLine {
    #[inline(always)]
    pub(crate) fn new() -> Self {
        Self {}
    }

    #[inline(always)]
    pub(crate) fn eval<'a>(&'a self, out: &mut Vec<u8>, info: &FileInfo) {
        if let Some(last) = out.last() {
            if *last != b' ' {
                out.push(b' ');
            }
        }

        tools::extend_with_u32(out, info.line);
        out.push(b' ');
    }
}

#[derive(Debug, Clone, Copy)]
pub struct MacroFile {}

impl MacroFile {
    #[inline(always)]
    pub(crate) fn new() -> Self {
        Self {}
    }

    #[inline(always)]
    pub(crate) fn eval<'a, PC: PreprocContext>(
        &'a self,
        out: &mut Vec<u8>,
        context: &PC,
        info: &FileInfo,
    ) {
        if let Some(last) = out.last() {
            if *last != b' ' {
                out.push(b' ');
            }
        }

        let path = context.get_path(info.source_id.unwrap());
        let path = path.to_str().unwrap();
        out.extend_from_slice(path.as_bytes());
        out.push(b' ');
    }
}

#[derive(Debug, Clone)]
pub struct MacroCounter {
    value: Cell<u64>,
}

impl MacroCounter {
    #[inline(always)]
    pub(crate) fn new() -> Self {
        Self {
            value: Cell::new(0),
        }
    }

    #[inline(always)]
    pub(crate) fn eval<'a>(&'a self, out: &mut Vec<u8>) {
        if let Some(last) = out.last() {
            if *last != b' ' {
                out.push(b' ');
            }
        }

        let n = self.value.get();
        tools::extend_with_u64(out, n);
        self.value.set(n + 1);

        out.push(b' ');
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::lexer::preprocessor::context::DefaultContext;
    use crate::lexer::Token;
    use pretty_assertions::{assert_eq, assert_ne};

    macro_rules! eval {
        ( $name: expr, $lexer: expr ) => {{
            let context = $lexer.context.clone();
            let mut res = Vec::new();
            let info = $lexer.buf.get_line_file();
            let mac = context.get($name).unwrap();
            match mac {
                Macro::Object(mac) => {
                    mac.eval(&mut res, &context, &info);
                }
                _ => {}
            }
            String::from_utf8(res).unwrap()
        }};
    }

    #[test]
    fn test_macro_in_context() {
        let mut p = Lexer::<DefaultContext>::new(
            b"#define foo x + 1\n#define bar y + x\n#define foobar(x, y) x ## y",
        );
        p.consume_all();
        assert!(p.context.get("foo").is_some());
        assert!(p.context.get("bar").is_some());
        assert!(p.context.get("foobar").is_some());
    }

    #[test]
    fn test_eval_object() {
        let mut p = Lexer::<DefaultContext>::new(
            concat!(
                "#define foo x + 1\n",
                "#define bar y + /* comment */ x\n",
                "#define oof (x)\n",
                "#define test1 foo\n",
                "#define test2 bar\n",
                "#define test3 oof\n",
            )
            .as_bytes(),
        );
        p.consume_all();

        assert_eq!(eval!("test1", p), "x + 1 ");
        assert_eq!(eval!("test2", p), "y + x ");
        assert_eq!(eval!("test3", p), "(x) ");
    }

    #[test]
    fn test_eval_concat1() {
        let mut p = Lexer::<DefaultContext>::new(
            concat!(
                "#define foo(x, y) x ## y\n",
                "#define bar(x) x\n",
                "#define test1 foo(12, 34)\n",
                "#define test2 foo(12, bar(34))"
            )
            .as_bytes(),
        );
        p.consume_all();

        assert_eq!(eval!("test1", p), "1234 ");
        assert_eq!(eval!("test2", p), "12bar(34) ");
    }

    #[test]
    fn test_eval_concat2() {
        let mut p = Lexer::<DefaultContext>::new(
            concat!(
                "#define Z(a,b) a ##b\n",
                "#define Y(a,b) c ## d\n",
                "#define X(a,b) c a ## d b\n",
                "#define W(a,b) a c ## b d\n",
                "#define V(a,b) A a##b B\n",
                "#define test1 Z(hello, world)\n",
                "#define test2 Y(hello, world)\n",
                "#define test3 X(hello, world)\n",
                "#define test4 W(hello, world)\n",
                "#define test5 V(hello, world)\n",
            )
            .as_bytes(),
        );
        p.consume_all();

        assert_eq!(eval!("test1", p), "helloworld ");
        assert_eq!(eval!("test2", p), "cd ");
        assert_eq!(eval!("test3", p), "c hellod world ");
        assert_eq!(eval!("test4", p), "hello cworld d ");
        assert_eq!(eval!("test5", p), "A helloworld B ");
    }

    #[test]
    fn test_eval_concat3() {
        let mut p = Lexer::<DefaultContext>::new(
            concat!(
                "#define foo(a,b) a##b\n",
                "foo(whi, le)\n",
                "#define foo(a,b) b##a\n",
                "foo(whi, le)\n",
                "#define foo bar foo\n",
                "foo\n",
            )
            .as_bytes(),
        );

        assert_eq!(p.next().tok, Token::PreprocDefine);
        assert_eq!(p.next().tok, Token::While);
        assert_eq!(p.next().tok, Token::Eol);
        assert_eq!(p.next().tok, Token::PreprocDefine);
        assert_eq!(p.next().tok, Token::Identifier("lewhi"));
        assert_eq!(p.next().tok, Token::Eol);
        assert_eq!(p.next().tok, Token::PreprocDefine);
        assert_eq!(p.next().tok, Token::Identifier("bar"));
        assert_eq!(p.next().tok, Token::Identifier("foo"));
        assert_eq!(p.next().tok, Token::Eol);
    }

    #[test]
    fn test_eval_function() {
        let mut p = Lexer::<DefaultContext>::new(
            concat!(
                "#define foo(x) x\n",
                "#define bar(x) x + 1\n",
                "#define test foo(bar(1234))",
            )
            .as_bytes(),
        );
        p.consume_all();

        assert_eq!(eval!("test", p), "1234 + 1 ");
    }

    #[test]
    fn test_eval_mix() {
        let mut p = Lexer::<DefaultContext>::new(
            concat!(
                "#define xstr(s) str(s)\n",
                "#define str(s) #s\n",
                "#define foo 4\n",
                "#define test xstr(foo)",
            )
            .as_bytes(),
        );
        p.consume_all();

        assert_eq!(eval!("test", p), "\"4\" ");
    }

    #[test]
    fn test_eval_base() {
        let mut p = Lexer::<DefaultContext>::new(
            concat!(
                "#define foo(a, b) (a) + (b)\n",
                "#define test foo(  123 ,  456  )"
            )
            .as_bytes(),
        );
        p.consume_all();

        assert_eq!(eval!("test", p), "( 123 ) + ( 456 ) ");
    }

    #[test]
    fn test_eval_hex() {
        let mut p = Lexer::<DefaultContext>::new(
            concat!(
                "#define foo(x, abc) x + 0x123abc\n",
                "#define test foo(456, 789)"
            )
            .as_bytes(),
        );
        p.consume_all();

        assert_eq!(eval!("test", p), "456 + 0x123abc ");
    }

    #[test]
    fn test_eval_comment() {
        let mut p = Lexer::<DefaultContext>::new(
            concat!(
                "#define foo(a,b,c) a b /* hello world*/     foo c\n",
                "#define bar(a,b,c) a / b // c\n",
                "#define test1 foo(A, B, C)\n",
                "#define test2 bar(A, B, C)"
            )
            .as_bytes(),
        );
        p.consume_all();

        assert_eq!(eval!("test1", p), "A B foo C ");
        assert_eq!(eval!("test2", p), "A / B ");
    }

    #[test]
    fn test_eval_stringify() {
        let mut p = Lexer::<DefaultContext>::new(
            concat!(
                "#define foo(a, b) #a + #b\n",
                "#define bar BAR\n",
                "#define test1 foo(oof, rab)\n",
                "#define test2 foo(bar, bar)"
            )
            .as_bytes(),
        );
        p.consume_all();

        assert_eq!(eval!("test1", p), "\"oof\" + \"rab\" ");
        assert_eq!(eval!("test2", p), "\"bar\" + \"bar\" ");
    }

    #[test]
    fn test_eval_stringify_string() {
        let mut p = Lexer::<DefaultContext>::new(
            concat!(
                "#define foo(a) #a\n",
                "#define test foo(R\"delimiter( a string with some \', \" and \n.)delimiter\")"
            )
            .as_bytes(),
        );
        p.consume_all();

        assert_eq!(
            eval!("test", p),
            "\"R\\\"delimiter( a string with some \\\', \\\" and \\\n.)delimiter\\\"\" "
        );
    }

    #[test]
    fn test_eval_auto_ref() {
        let mut p = Lexer::<DefaultContext>::new(
            concat!("#define foo a foo\n", "#define test foo",).as_bytes(),
        );
        p.consume_all();

        assert_eq!(eval!("test", p), "a foo ");
    }

    #[test]
    fn test_eval_auto_ref2() {
        let mut p = Lexer::<DefaultContext>::new(
            concat!(
                "#define FOO x rab bar\n",
                "#define test FOO\n",
                "#define bar FOO\n",
                "#define rab oof\n",
                "#define oof y FOO\n",
            )
            .as_bytes(),
        );
        p.consume_all();

        assert_eq!(eval!("test", p), "x y FOO FOO ");
    }

    #[test]
    fn test_eval_auto_ref3() {
        let mut p = Lexer::<DefaultContext>::new(
            concat!(
                "#define foo(x) x bar(x)\n",
                "#define bar(x) x oof(x)\n",
                "#define oof(x) x foo(x)\n",
                "#define test foo(hello)\n",
            )
            .as_bytes(),
        );
        p.consume_all();

        assert_eq!(eval!("test", p), "hello hello hello foo( hello ) ");
    }

    #[test]
    fn test_eval_va() {
        let mut p = Lexer::<DefaultContext>::new(
            concat!(
                "#define foo(x, y, ...) x y __VA_ARGS__\n",
                "#define bar(x, y, toto...) x y toto\n",
                "#define foo1(toto...) printf(toto)\n",
                "#define foo2(toto ...) printf(toto)\n",
                "#define foo3(...) printf(__VA_ARGS__)\n",
                "#define test1 foo(a, b, c,d, e , f)\n",
                "#define test2 bar(a, b, c, d, e, f)\n",
                "#define test3 foo1(a, b)\n",
                "#define test4 foo1()\n",
                "#define test5 foo2(a,  b)\n",
                "#define test6 foo3(a, b)\n",
            )
            .as_bytes(),
        );
        p.consume_all();

        assert_eq!(eval!("test1", p), "a b c,d, e , f ");
        assert_eq!(eval!("test2", p), "a b c, d, e, f ");
        assert_eq!(eval!("test3", p), "printf( a, b ) ");
        assert_eq!(eval!("test4", p), "printf( ) ");
        assert_eq!(eval!("test5", p), "printf( a, b ) ");
        assert_eq!(eval!("test6", p), "printf( a, b ) ");
    }

    #[test]
    fn test_rescan_va() {
        let mut p = Lexer::<DefaultContext>::new(
            concat!(
                "#define LPAREN (\n",
                "#define RPAREN )\n",
                "#define F(x, y) x + y\n",
                "#define ELLIP_FUNC(...) __VA_ARGS__\n",
                "#define test1 ELLIP_FUNC(F, LPAREN, 'a', 'b', RPAREN);\n",
                "#define test2 ELLIP_FUNC(F LPAREN 'a', 'b' RPAREN);\n",
            )
            .as_bytes(),
        );
        p.consume_all();

        assert_eq!(eval!("test1", p), "F, ( , 'a', 'b', ) ; ");
        assert_eq!(eval!("test2", p), "'a' + 'b' ; ");
    }

    #[test]
    fn test_eval_with_spaces() {
        let mut p = Lexer::<DefaultContext>::new(
            concat!(
                "#define A(x)\n",
                "#define test1 A(1)\n",
                "#define B(x,y)x y\n",
                "#define test2 B(1,2)\n",
                "#define C() ..\n",
                "#define test3 C()\n",
                "#define E .\n",
                "#define test4 E\n",
                "#define F X()Y\n",
                "#define test5 X()Y\n",
            )
            .as_bytes(),
        );
        p.consume_all();

        assert_eq!(eval!("test1", p), "");
        assert_eq!(eval!("test2", p), "1 2 ");
        assert_eq!(eval!("test3", p), ".. ");
        assert_eq!(eval!("test4", p), ". ");
        assert_eq!(eval!("test5", p), "X()Y ");
    }

    #[test]
    fn test_eval_space() {
        let mut p = Lexer::<DefaultContext>::new(
            concat!(
                "#define PLUS +\n",
                "#define EMPTY\n",
                "#define f(x) =x=\n",
                "#define test1 +PLUS -EMPTY- PLUS+ f(=)\n",
            )
            .as_bytes(),
        );
        p.consume_all();

        assert_eq!(eval!("test1", p), "+ + - - + + = = = ");
    }

    #[test]
    fn test_eval_paste_hard() {
        let mut p = Lexer::<DefaultContext>::new(
            concat!(
                "#define a(n) aaa ## n\n",
                "#define b 2\n",
                "#define test1 a(b b)\n",
                "#undef a\n",
                "#undef b\n",
                "#define a(n) n ## aaa\n",
                "#define b 2\n",
                "#define test2 a(b b)\n",
                "#define baaa xx\n",
                "#define test3 a(b b)\n",
            )
            .as_bytes(),
        );
        p.consume_tokens(3);
        assert_eq!(p.get_line(), 4);
        assert_eq!(eval!("test1", p), "aaab 2 ");

        p.consume_tokens(7);
        assert_eq!(p.get_line(), 9);
        assert_eq!(eval!("test2", p), "2 baaa ");

        p.consume_all();
        assert_eq!(eval!("test3", p), "2 xx ");
    }

    #[test]
    fn test_eval_empty_arg() {
        let mut p = Lexer::<DefaultContext>::new(
            concat!(
                "#define foo(n) n+\n",
                "#define test1 foo()\n",
                "#define bar(n, m) n+m\n",
                "#define test2 bar(,)\n",
            )
            .as_bytes(),
        );
        p.consume_all();
        assert_eq!(eval!("test1", p), "+ ");
        assert_eq!(eval!("test2", p), "+ ");
    }
}
