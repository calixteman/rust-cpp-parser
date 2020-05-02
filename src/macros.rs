// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

#[macro_export]
macro_rules! node {
    ( $kind: ident $($toks:tt)*) => {
        ExprNode::$kind(Box::new($kind $( $toks )*))
    };
}

#[macro_export]
macro_rules! skip_whites {
    ( $lexer: expr) => {{
        loop {
            if $lexer.buf.has_char() {
                let c = $lexer.buf.next_char();
                if c == b'\\' {
                    if $lexer.buf.has_char_n(1) {
                        let c = $lexer.buf.next_char_n(1);
                        if c == b'\n' {
                            $lexer.buf.add_new_line();
                            $lexer.buf.inc_n(2);
                            continue;
                        }
                    }
                    break;
                }
                if c != b' ' && c != b'\t' {
                    break;
                }
                $lexer.buf.inc();
            } else {
                break;
            }
        }
    }};
}

#[macro_export]
macro_rules! skip_whites_back {
    ( $lexer: expr) => {{
        loop {
            let c = $lexer.buf.next_char();
            if c != b' ' && c != b'\t' {
                break;
            }
            $lexer.buf.dec_n(1);
        }
    }};
}

#[macro_export]
macro_rules! skip_until {
    ( $lexer: expr, $char: expr ) => {{
        loop {
            if $lexer.buf.has_char() {
                let c = $lexer.buf.next_char();
                if c == $char {
                    break;
                }
                $lexer.buf.inc();
            } else {
                break;
            }
        }
    }};
}

#[macro_export]
macro_rules! color {
    ( $stdout: ident, $color: ident) => {{
        use termcolor::WriteColor;

        $stdout
            .set_color(termcolor::ColorSpec::new().set_fg(Some(termcolor::Color::$color)))
            .unwrap();
    }};
    ( $stdout: ident, $color: ident, $intense: ident) => {{
        use termcolor::WriteColor;

        $stdout
            .set_color(
                termcolor::ColorSpec::new()
                    .set_fg(Some(termcolor::Color::$color))
                    .set_intense($intense),
            )
            .unwrap();
    }};
}

#[macro_export]
macro_rules! dump_start {
    ( $name: expr, $val: expr, $prefix: ident, $is_last: expr, $out: ident) => {{
        use std::io::Write;

        let prefix = format!("{}{}", $prefix, Self::get_pref($is_last));

        $crate::color!($out, Blue);
        write!($out, "{}", prefix).unwrap();

        if !$name.is_empty() {
            $crate::color!($out, Yellow);
            write!($out, "{}: ", $name).unwrap();
        }

        $crate::color!($out, Green);
        writeln!($out, "{}", $val).unwrap();

        format!("{}{}", $prefix, Self::get_pref_child($is_last))
    }};
}

#[macro_export]
macro_rules! dump_fields {
    ( $self: ident, $prefix: ident, $out: ident, $last: ident) => {{
        $self.$last.dump(stringify!($last), &$prefix, true, $out);
    }};

    ( $self: ident, $prefix: ident, $out: ident, $field: ident, $( $fields: ident ), *) => {{
        $self.$field.dump(stringify!($field), &$prefix, false, $out);
        dump_fields!($self, $prefix, $out, $( $fields ),*);
    }};
}

#[macro_export]
macro_rules! dump_obj {
    ( $self: ident, $name: expr, $obj_name: expr, $prefix: ident, $is_last: expr, $out: ident, $( $fields: ident ), *) => {{
        let prefix = $crate::dump_start!($name, $obj_name, $prefix, $is_last, $out);
        $crate::dump_fields!($self, prefix, $out, $( $fields ),*);
    }};
}

#[macro_export]
macro_rules! dump_vec {
    ( $name: expr, $vec: expr, $elem_name: expr, $prefix: ident, $is_last: expr, $out: ident ) => {{
        let prefix = $crate::dump_start!($name, "", $prefix, $is_last, $out);
        let mut count = 1;

        if let Some((last, elems)) = $vec.split_last() {
            for e in elems.iter() {
                e.dump(&format!("{}{}", $elem_name, count), &prefix, false, $out);
                count += 1;
            }
            last.dump(&format!("{}{}", $elem_name, count), &prefix, true, $out);
        }
    }};
}

#[macro_export]
macro_rules! dump_str {
    ( $name: expr, $val: expr, $prefix: ident, $last: ident, $out: ident) => {{
        dump_str!($name, $val, White, $prefix, $last, $out);
    }};

    ( $name: expr, $val: expr, $color: ident, $prefix: ident, $last: ident, $out: ident) => {{
        use std::io::Write;
        let prefix = format!("{}{}", $prefix, Self::get_pref($last));

        $crate::color!($out, Blue);
        write!($out, "{}", prefix).unwrap();

        $crate::color!($out, Yellow);

        if !$val.is_empty() {
            write!($out, "{}: ", $name).unwrap();
            $crate::color!($out, $color);
            writeln!($out, "{}", $val).unwrap();
        } else {
            writeln!($out, "{}", $name).unwrap();
        }
    }};
}

#[macro_export]
macro_rules! bitflags_to_str {
    ( $self: ident, $name: ident, $( $field: ident, $value: expr ), *) => {{
        let mut v = Vec::new();
        $(
            if $self.contains($name::$field) {
                v.push($value);
            }
        )*
            v.join(" | ")
    }};
}

#[macro_export]
macro_rules! error {
    ($span:expr, $($arg:tt)*) => {
        return Err($crate::errors::Error::new(
            $span,
            format!($($arg)*),
        ));
    };
}
