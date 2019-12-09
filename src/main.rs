use cpp_parser::lexer::{Lexer, Token};
use std::fs;

fn main() {
    let s = fs::read("../rust-cpp-parser/benches/sqlite3.c").unwrap();
    //let s = std::iter::repeat(s).take(100).collect::<String>();
    let mut lexer = Lexer::new(&s);
    loop {
        let tok = lexer.next();
        if tok == Token::Eof {
            break;
        }
    }
}
