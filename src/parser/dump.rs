// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use std::cell::RefCell;
use std::rc::Rc;
use termcolor::{ColorChoice, StandardStream, StandardStreamLock};

use crate::dump_str;

pub trait Dump {
    fn dump_me(&self) {
        let stdout = StandardStream::stdout(ColorChoice::Always);
        let mut stdout = stdout.lock();
        self.dump("", "", true, &mut stdout);
        color!(stdout, White);
    }

    fn get_pref(last: bool) -> &'static str {
        // https://en.wikipedia.org/wiki/Box-drawing_character
        if last {
            // "`- "
            "\u{2570}\u{2500} "
        } else {
            // "|- "
            "\u{251C}\u{2500} "
        }
    }

    fn get_pref_child(last: bool) -> &'static str {
        if last {
            "   "
        } else {
            // "|   "
            "\u{2502}  "
        }
    }

    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock);
}

impl<T: Dump> Dump for Option<T> {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        if let Some(x) = self {
            x.dump(name, prefix, last, stdout);
        } else {
            dump_str!(name, "\u{2717}", Red, prefix, last, stdout);
        }
    }
}

impl<T: Dump> Dump for Rc<T> {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        self.as_ref().dump(name, prefix, last, stdout);
    }
}

impl<T: Dump> Dump for RefCell<T> {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        self.borrow().dump(name, prefix, last, stdout);
    }
}

impl<'a, T: Dump> Dump for &'a T {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        (*self).dump(name, prefix, last, stdout);
    }
}

impl Dump for String {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        dump_str!(name, self, prefix, last, stdout);
    }
}

impl Dump for bool {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        let v = if *self { "true" } else { "false" };
        dump_str!(name, v, Cyan, prefix, last, stdout);
    }
}
