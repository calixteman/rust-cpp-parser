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
