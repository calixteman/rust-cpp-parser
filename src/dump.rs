use std::io::Write;
use termcolor::{Color, ColorChoice, ColorSpec, StandardStream, StandardStreamLock, WriteColor};

use crate::parser::ast::*;
use crate::parser::operator::*;

macro_rules! start {
    ( $name: expr, $prefix: ident, $last: ident, $out: ident) => {
        color!($out, Blue);
        write!($out, "{}{}", $prefix, Self::get_pref($last)).unwrap();
        
        color!($out, Yellow, true);
        write!($out, concat!($name, ": ")).unwrap();        
    };
}

pub trait Dump {
    fn dump_me(&self) {
        let stdout = StandardStream::stdout(ColorChoice::Always);
        let mut stdout = stdout.lock();
        self.dump("", true, &mut stdout);
        color!(stdout, White);
    }

    fn get_pref(last: bool) -> &'static str {
        if last {
            "`- "
        } else {
            "|- "
        }
    }

    fn get_pref_child(last: bool) -> &'static str {
        if last {
            "   "
        } else {
            "|  "
        }
    }

    fn dump(&self, prefix: &str, last: bool, stdout: &mut StandardStreamLock);
}

impl Dump for Node {
    fn dump(&self, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        match self {
            Node::UnaryOp(x) => x.dump(prefix, last, stdout),
            Node::BinaryOp(x) => x.dump(prefix, last, stdout),
            Node::CallExpr(x) => x.dump(prefix, last, stdout),
            Node::Id(x) => x.dump(prefix, last, stdout),
            Node::UInt(x) => x.dump(prefix, last, stdout),
            Node::Arguments(x) => x.dump(prefix, last, stdout),
        }
    }
}

impl Dump for Id {
    fn dump(&self, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        start!("Identifier", prefix, last, stdout);
        
        color!(stdout, White);
        writeln!(stdout, "{}", self.name).unwrap();
    }
}

impl Dump for UInt {
    fn dump(&self, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        start!("UInt", prefix, last, stdout);

        color!(stdout, White);
        writeln!(stdout, "{}", self.value).unwrap();
    }
}

impl Dump for BinaryOp {
    fn dump(&self, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        start!("BinaryOp", prefix, last, stdout);
        
        color!(stdout, Green, true);
        writeln!(stdout, "{:?}", self.op).unwrap();

        let prefix = format!("{}{}", prefix, Self::get_pref_child(last));
        self.arg1.dump(&prefix, false, stdout);
        self.arg2.dump(&prefix, true, stdout);
    }
}

impl Dump for UnaryOp {
    fn dump(&self, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        start!("UnaryOp", prefix, last, stdout);
        
        color!(stdout, Green, true);
        writeln!(stdout, "{:?}", self.op).unwrap();

        let prefix = format!("{}{}", prefix, Self::get_pref_child(last));
        self.arg.dump(&prefix, true, stdout);
    }
}

impl Dump for CallExpr {
    fn dump(&self, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        start!("CallExpr", prefix, last, stdout);
        
        let prefix = format!("{}{}", prefix, Self::get_pref_child(last));
        self.callee.dump(&prefix, false, stdout);
        self.args.dump(&prefix, true, stdout);
    }
}

impl Dump for Arguments {
    fn dump(&self, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        start!("Arguments", prefix, last, stdout);
        
        let prefix = format!("{}{}", prefix, Self::get_pref_child(last));
        if let Some((last, args)) = self.args.split_last() {
            for arg in args.iter() {
                arg.dump(&prefix, false, stdout);
            }
            last.dump(&prefix, true, stdout);
        }
    }
}
