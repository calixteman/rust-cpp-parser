// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use serde::Deserialize;
use std::fs::File;
use std::io::Read;
use std::path::PathBuf;

macro_rules! skip_whites {
    ( $lexer: expr) => {{
        loop {
            if $lexer.has_char() {
                let c = $lexer.next_char();
                if c != b' ' && c != b'\t' {
                    break;
                }
                $lexer.pos += 1;
            } else {
                break;
            }
        }
    }};
}

#[derive(Clone, Debug, PartialEq)]
pub enum Macro {
    Defined((String, String)),
    Undef(String),
}

#[derive(Debug, Default)]
pub struct PreprocOptions {
    pub def: Vec<Macro>,
    pub sys_paths: Vec<String>,
    pub includes: Vec<String>,
    pub current_dir: PathBuf,
}

struct Args<'a> {
    buf: &'a [u8],
    pos: usize,
    len: usize,
    opt: PreprocOptions,
}

impl<'a> Args<'a> {
    fn new(buf: &'a [u8]) -> Self {
        Self {
            buf,
            pos: 0,
            len: buf.len(),
            opt: PreprocOptions::default(),
        }
    }

    fn inc(&mut self) {
        self.pos += 1;
    }

    fn dec(&mut self) {
        self.pos -= 1;
    }

    fn has_char(&self) -> bool {
        self.pos < self.len
    }

    fn next_char(&self) -> u8 {
        unsafe { *self.buf.get_unchecked(self.pos) }
    }

    fn prev_char(&self) -> u8 {
        unsafe { *self.buf.get_unchecked(self.pos - 1) }
    }

    fn slice(&self, start: usize, end: usize) -> String {
        unsafe { String::from_utf8_unchecked(self.buf.get_unchecked(start..end).to_vec()) }
    }

    fn slice_to_end(&self, start: usize) -> String {
        unsafe { String::from_utf8_unchecked(self.buf.get_unchecked(start..).to_vec()) }
    }

    fn get_app_name(&mut self) -> Option<String> {
        loop {
            if self.has_char() {
                if self.next_char() == b' ' {
                    let name = self.slice(0, self.pos);
                    self.inc();
                    return Some(name);
                }
                self.inc();
            } else {
                return None;
            }
        }
    }

    fn get_hex_digit(c: u8) -> u8 {
        match c {
            b'0'..=b'9' => c - b'0',
            b'a'..=b'f' => c - b'a' + 10,
            b'A'..=b'F' => c - b'A' + 10,
            _ => 16,
        }
    }

    fn get_bash_string(&mut self, buf: &mut String) {
        loop {
            if self.has_char() {
                let c = self.next_char();
                self.inc();
                match c {
                    b'\"' => {
                        break;
                    }
                    b'\\' => {
                        let c = self.next_char();
                        self.inc();
                        match c {
                            b'a' => buf.push('\x07'),
                            b'b' => buf.push('\x08'),
                            b'e' => buf.push('\x1b'),
                            b'f' => buf.push('\x0c'),
                            b'n' => buf.push('\n'),
                            b'r' => buf.push('\r'),
                            b't' => buf.push('\t'),
                            b'v' => buf.push('\x0b'),
                            b'\\' => buf.push('\\'),
                            b'\'' => buf.push('\''),
                            b'\"' => buf.push('\"'),
                            b'0'..=b'7' => {
                                let mut n = (c - b'0') as u8;
                                for _ in 0..1 {
                                    self.inc();
                                    let c = self.next_char();
                                    if b'0' <= c && c <= b'7' {
                                        n = 8 * n + ((c - b'0') as u8);
                                    } else {
                                        break;
                                    }
                                }
                                buf.push(n as char);
                            }
                            b'x' => {
                                self.inc();
                                let c = self.next_char();
                                let n = Self::get_hex_digit(c);
                                self.inc();
                                let c = self.next_char();
                                let m = Self::get_hex_digit(c);
                                if m < 16 {
                                    buf.push((16 * n + m) as char);
                                } else {
                                    buf.push(n as char);
                                }
                            }
                            _ => {
                                unreachable!();
                            }
                        }
                    }
                    _ => {
                        buf.push(c as char);
                    }
                }
            }
        }
    }

    fn get_bash_single_string(&mut self, buf: &mut String) {
        loop {
            if self.has_char() {
                let c = self.next_char();
                self.inc();
                match c {
                    b'\'' => {
                        break;
                    }
                    _ => {
                        buf.push(c as char);
                    }
                }
            }
        }
    }

    fn get_element(&mut self, buf: &mut String) {
        // consume everything until space or eof
        loop {
            if self.has_char() {
                let c = self.next_char();
                self.inc();
                match c {
                    b' ' => {
                        break;
                    }
                    b'\"' => {
                        self.get_bash_string(buf);
                    }
                    b'\'' => {
                        self.get_bash_single_string(buf);
                    }
                    _ => {
                        buf.push(c as char);
                    }
                }
            } else {
                break;
            }
        }
    }

    fn get_parts(&mut self) -> Vec<String> {
        let mut parts = Vec::new();
        loop {
            if self.has_char() {
                let mut buf = String::new();
                let c = self.next_char();
                self.inc();
                match c {
                    b'\'' => {
                        self.get_bash_single_string(&mut buf);
                    }
                    b'\"' => {
                        self.get_bash_string(&mut buf);
                    }
                    b' ' => {
                        skip_whites!(self);
                        continue;
                    }
                    _ => {
                        buf.push(c as char);
                        self.get_element(&mut buf);
                    }
                }
                parts.push(buf);
            } else {
                break;
            }
        }
        parts
    }

    fn parse(&mut self) {
        let parts = self.get_parts();
        let mut i = 0;
        while i < parts.len() {
            let part = &parts[i];
            if !part.starts_with('-') {
                i += 1;
                continue;
            }

            let bytes = part.as_bytes();

            match bytes[1] {
                b'D' => {
                    let defined = if part.len() > 2 {
                        &part[2..]
                    } else {
                        i += 1;
                        &parts[i]
                    };
                    let toks: Vec<_> = defined.splitn(2, '=').collect();
                    if toks.len() == 1 {
                        self.opt
                            .def
                            .push(Macro::Defined((toks[0].to_string(), "1".to_string())));
                    } else {
                        self.opt
                            .def
                            .push(Macro::Defined((toks[0].to_string(), toks[1].to_string())));
                    }
                }
                b'I' => {
                    let path = if part.len() > 2 {
                        &part[2..]
                    } else {
                        i += 1;
                        &parts[i]
                    };
                    self.opt.sys_paths.push(path.to_string());
                }
                b'i' => {
                    if part.starts_with("-include") {
                        let n = "-include".len();
                        let path = if part.len() > n {
                            &part[n..]
                        } else {
                            i += 1;
                            &parts[i]
                        };
                        self.opt.includes.push(path.to_string());
                    }
                }
                b'U' => {
                    let undef = if part.len() > 2 {
                        &part[2..]
                    } else {
                        i += 1;
                        &parts[i]
                    };
                    self.opt.def.push(Macro::Undef(undef.to_string()));
                }
                _ => {}
            }

            i += 1;
        }
    }

    pub fn get_options(cl: &[u8]) -> PreprocOptions {
        let mut args = Args::new(cl);
        args.parse();

        args.opt
    }
}

#[derive(Debug, Deserialize)]
struct JsonCommand {
    directory: PathBuf,
    command: String,
    file: PathBuf,
}

#[derive(Debug)]
pub struct Command {
    pub opt: PreprocOptions,
    pub file: PathBuf,
}

impl Command {
    pub fn from_json(path: &str) -> Vec<Command> {
        let mut file = File::open(&path).unwrap();
        let mut data = Vec::new();
        file.read_to_end(&mut data).unwrap();
        let mut r: Vec<JsonCommand> = serde_json::de::from_slice(&data).unwrap();
        r.drain(..)
            .map(|c| {
                let mut opt = Args::get_options(c.command.as_bytes());
                opt.current_dir = c.directory;
                Command { opt, file: c.file }
            })
            .collect()
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn test_args_i_basic() {
        let cl = b"/usr/bin/clang-9 -std=gnu99 -o /dev/null -c -IA -IB -fPIC -IC";
        let opt = Args::get_options(cl);

        assert_eq!(opt.sys_paths, vec!["A", "B", "C"]);

        let cl = b"/usr/bin/clang-9 -std=gnu99 -o /dev/null -c -IA -I\"B C D\" -fPIC -IC";
        let opt = Args::get_options(cl);

        assert_eq!(opt.sys_paths, vec!["A", "B C D", "C"]);
    }

    #[test]
    fn test_args_i_spaces() {
        let cl = b"/usr/bin/clang-9 -std=gnu99 -o /dev/null -c -IA -I\"B C D\" -fPIC -IC";
        let opt = Args::get_options(cl);

        assert_eq!(opt.sys_paths, vec!["A", "B C D", "C"]);
    }

    #[test]
    fn test_args_i_arg_with_dash() {
        let cl = b"/usr/bin/clang-9 -std=gnu99 -o /foo/bar-oof/rab -c -IA -I\"B\" -Qunused-arguments -fPIC -IC";
        let opt = Args::get_options(cl);

        assert_eq!(opt.sys_paths, vec!["A", "B", "C"]);
    }

    #[test]
    fn test_args_ud() {
        let cl = b"/usr/bin/clang-9 -std=gnu99 -D_ABC_ -D foo=23 -UTITI -DFOO123=\"foo bar\" -D bar(a,b,c)  -U  toto -D rab(a,b)=a##b '-DR_PLATFORM_INT_TYPES=<stdint.h>'  '-D__UNUSED__=__attribute__((unused))'";
        let opt = Args::get_options(cl);

        assert_eq!(
            opt.def,
            vec![
                Macro::Defined(("_ABC_".to_string(), "1".to_string())),
                Macro::Defined(("foo".to_string(), "23".to_string())),
                Macro::Undef("TITI".to_string()),
                Macro::Defined(("FOO123".to_string(), "foo bar".to_string())),
                Macro::Defined(("bar(a,b,c)".to_string(), "1".to_string())),
                Macro::Undef("toto".to_string()),
                Macro::Defined(("rab(a,b)".to_string(), "a##b".to_string())),
                Macro::Defined(("R_PLATFORM_INT_TYPES".to_string(), "<stdint.h>".to_string())),
                Macro::Defined((
                    "__UNUSED__".to_string(),
                    "__attribute__((unused))".to_string()
                )),
            ]
        );
    }

    #[test]
    fn test_args_quote() {
        let cl = b"/usr/bin/clang-9 -std=gnu99 '-D_ABC_=\"abc\"'";
        let opt = Args::get_options(cl);

        assert_eq!(
            opt.def,
            vec![Macro::Defined(("_ABC_".to_string(), "\"abc\"".to_string())),]
        );
    }

    #[test]
    fn test_args_include() {
        let cl = b"/usr/bin/clang-9 -std=gnu99 -o /foo/bar-oof/rab -include A -include B -i blah-blah -include C";
        let opt = Args::get_options(cl);

        assert_eq!(opt.includes, vec!["A", "B", "C"]);
    }

    #[test]
    fn test_args_real() {
        let cl = b"/usr/bin/clang-9 -std=gnu99 -o /dev/null -c -I/home/calixte/dev/mozilla/mozilla-central.hg/obj-x86_64-pc-linux-gnu/dist/system_wrappers -include /home/calixte/dev/mozilla/mozilla-central.hg/config/gcc_hidden.h -U_FORTIFY_SOURCE -D_FORTIFY_SOURCE=2 -fstack-protector-strong -DNDEBUG=1 -DTRIMMED=1 -DIMPL_MFBT -DLZ4LIB_VISIBILITY= -I/home/calixte/dev/mozilla/mozilla-central.hg/mfbt -I/home/calixte/dev/mozilla/mozilla-central.hg/obj-x86_64-pc-linux-gnu/mfbt -I/home/calixte/dev/mozilla/mozilla-central.hg/mfbt/double-conversion -I/home/calixte/dev/mozilla/mozilla-central.hg/obj-x86_64-pc-linux-gnu/dist/include -I/home/calixte/dev/mozilla/mozilla-central.hg/obj-x86_64-pc-linux-gnu/dist/include/nspr -I/home/calixte/dev/mozilla/mozilla-central.hg/obj-x86_64-pc-linux-gnu/dist/include/nss -fPIC -include /home/calixte/dev/mozilla/mozilla-central.hg/obj-x86_64-pc-linux-gnu/mozilla-config.h -DMOZILLA_CLIENT -Qunused-arguments -fno-strict-aliasing -fno-math-errno -pthread -fPIC -pipe -g -O2 -fno-omit-frame-pointer -funwind-tables -Qunused-arguments -Wall -Wbitfield-enum-conversion -Wempty-body -Wignored-qualifiers -Wpointer-arith -Wshadow-field-in-constructor-modified -Wsign-compare -Wtype-limits -Wunreachable-code -Wunreachable-code-return -Wclass-varargs -Wfloat-overflow-conversion -Wfloat-zero-conversion -Wloop-analysis -Wstring-conversion -Wtautological-overlap-compare -Wtautological-unsigned-enum-zero-compare -Wtautological-unsigned-zero-compare -Wno-error=tautological-type-limit-compare -Wno-error=deprecated-declarations -Wno-error=array-bounds -Wno-error=backend-plugin -Wno-error=return-std-move -Wno-error=atomic-alignment -Wformat -Wformat-security -Wno-gnu-zero-variadic-macro-arguments /home/calixte/dev/mozilla/mozilla-central.hg/mfbt/lz4/lz4.c";
        let opt = Args::get_options(cl);

        assert_eq!(opt.includes, vec![
            "/home/calixte/dev/mozilla/mozilla-central.hg/config/gcc_hidden.h".to_string(),
            "/home/calixte/dev/mozilla/mozilla-central.hg/obj-x86_64-pc-linux-gnu/mozilla-config.h".to_string(),
        ]);

        assert_eq!(opt.sys_paths, vec![
            "/home/calixte/dev/mozilla/mozilla-central.hg/obj-x86_64-pc-linux-gnu/dist/system_wrappers".to_string(),
            "/home/calixte/dev/mozilla/mozilla-central.hg/mfbt".to_string(),
            "/home/calixte/dev/mozilla/mozilla-central.hg/obj-x86_64-pc-linux-gnu/mfbt".to_string(),
            "/home/calixte/dev/mozilla/mozilla-central.hg/mfbt/double-conversion".to_string(),
            "/home/calixte/dev/mozilla/mozilla-central.hg/obj-x86_64-pc-linux-gnu/dist/include".to_string(),
            "/home/calixte/dev/mozilla/mozilla-central.hg/obj-x86_64-pc-linux-gnu/dist/include/nspr".to_string(),
            "/home/calixte/dev/mozilla/mozilla-central.hg/obj-x86_64-pc-linux-gnu/dist/include/nss".to_string(),
        ]);

        assert_eq!(
            opt.def,
            vec![
                Macro::Undef("_FORTIFY_SOURCE".to_string()),
                Macro::Defined(("_FORTIFY_SOURCE".to_string(), "2".to_string())),
                Macro::Defined(("NDEBUG".to_string(), "1".to_string())),
                Macro::Defined(("TRIMMED".to_string(), "1".to_string())),
                Macro::Defined(("IMPL_MFBT".to_string(), "1".to_string())),
                Macro::Defined(("LZ4LIB_VISIBILITY".to_string(), "".to_string())),
                Macro::Defined(("MOZILLA_CLIENT".to_string(), "1".to_string())),
            ]
        );
    }
}
