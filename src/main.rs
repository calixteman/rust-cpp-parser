use cpp_parser::lexer::{Lexer, Token};
use std::fs;

fn main() {
    let s = fs::read_to_string("benches/sqlite3.c").unwrap();
    //let s = std::iter::repeat(s).take(100).collect::<String>();
    let mut lexer = Lexer::new(s.as_bytes());
    loop {
        let tok = lexer.next();
        if tok == Token::Eof {
            break;
        }
    }
}
