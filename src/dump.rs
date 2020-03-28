use std::io::Write;
use termcolor::{Color, ColorChoice, ColorSpec, StandardStream, StandardStreamLock, WriteColor};

use crate::parser::ast::*;
use crate::parser::operator::*;

pub trait Dump {
    fn dump_me(&self) {
        let stdout = StandardStream::stdout(ColorChoice::Always);
        let mut stdout = stdout.lock();
        self.dump("", true, &mut stdout);
        color!(stdout, White);
    }

    fn get_prefixes(last: bool) -> (&'static str, &'static str) {
        if last {
            ("   ", "`- ")
        } else {
            ("|  ", "|- ")
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
        let (_, pref) = Self::get_prefixes(last);

        color!(stdout, Blue);
        write!(stdout, "{}{}", prefix, pref).unwrap();

        color!(stdout, Yellow, true);
        write!(stdout, "Identifier: ").unwrap();

        color!(stdout, White);
        writeln!(stdout, "{}", self.name).unwrap();
    }
}

impl Dump for UInt {
    fn dump(&self, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        let (_, pref) = Self::get_prefixes(last);

        color!(stdout, Blue);
        write!(stdout, "{}{}", prefix, pref).unwrap();

        color!(stdout, Yellow, true);
        write!(stdout, "UInt: ").unwrap();

        color!(stdout, White);
        writeln!(stdout, "{}", self.value).unwrap();
    }
}

impl Dump for BinaryOp {
    fn dump(&self, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        let (pref_child, pref) = Self::get_prefixes(last);

        color!(stdout, Blue);
        write!(stdout, "{}{}", prefix, pref).unwrap();

        color!(stdout, Yellow, true);
        write!(stdout, "BinaryOp: ").unwrap();

        color!(stdout, Green, true);
        writeln!(stdout, "{:?}", self.op).unwrap();

        let prefix = format!("{}{}", prefix, pref_child);
        self.arg1.dump(&prefix, false, stdout);
        self.arg2.dump(&prefix, true, stdout);
    }
}

impl Dump for UnaryOp {
    fn dump(&self, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        let (pref_child, pref) = Self::get_prefixes(last);

        color!(stdout, Blue);
        write!(stdout, "{}{}", prefix, pref).unwrap();

        color!(stdout, Yellow, true);
        write!(stdout, "UnaryOp: ").unwrap();

        color!(stdout, Green, true);
        writeln!(stdout, "{:?}", self.op).unwrap();

        let prefix = format!("{}{}", prefix, pref_child);
        self.arg.dump(&prefix, true, stdout);
    }
}

impl Dump for CallExpr {
    fn dump(&self, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        let (pref_child, pref) = Self::get_prefixes(last);

        color!(stdout, Blue);
        write!(stdout, "{}{}", prefix, pref).unwrap();

        color!(stdout, Yellow, true);
        writeln!(stdout, "CallExpr: ").unwrap();

        let prefix = format!("{}{}", prefix, pref_child);
        self.callee.dump(&prefix, false, stdout);
        self.args.dump(&prefix, true, stdout);
    }
}

impl Dump for Arguments {
    fn dump(&self, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        let (pref_child, pref) = Self::get_prefixes(last);

        color!(stdout, Blue);
        write!(stdout, "{}{}", prefix, pref).unwrap();

        color!(stdout, Yellow, true);
        writeln!(stdout, "Arguments: ").unwrap();

        let prefix = format!("{}{}", prefix, pref_child);
        if let Some((last, args)) = self.args.split_last() {
            for arg in args.iter() {
                arg.dump(&prefix, false, stdout);
            }
            last.dump(&prefix, true, stdout);
        }
    }
}
