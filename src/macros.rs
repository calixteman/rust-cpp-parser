#[macro_export]
macro_rules! color {
    ( $stdout: ident, $color: ident) => {
        $stdout
            .set_color(ColorSpec::new().set_fg(Some(Color::$color)))
            .unwrap();
    };
    ( $stdout: ident, $color: ident, $intense: ident) => {
        $stdout
            .set_color(
                ColorSpec::new()
                    .set_fg(Some(Color::$color))
                    .set_intense($intense),
            )
            .unwrap();
    };
}

#[macro_export]
macro_rules! node {
    ( $kind: ident $($toks:tt)*) => {
        Node::$kind(Box::new($kind $( $toks )*))
    };
}

#[macro_export]
macro_rules! skip_whites {
    ( $lexer: expr) => {{
        loop {
            if $lexer.pos < $lexer.len {
                let c = unsafe { *$lexer.buf.get_unchecked($lexer.pos) };
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

#[macro_export]
macro_rules! skip_until {
    ( $lexer: expr, $char: expr ) => {{
        loop {
            if $lexer.pos < $lexer.len {
                let c = unsafe { *$lexer.buf.get_unchecked($lexer.pos) };
                if c == $char {
                    break;
                }
                $lexer.pos += 1;
            } else {
                break;
            }
        }
    }};
}
