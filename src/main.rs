use cpp_parser::lexer::{Lexer, Token};
use std::fs;
use std::path::Path;

fn main() {
    let file = Path::new(env!("CARGO_MANIFEST_DIR")).join("benches/basic/ascii.cpp");
    let s = fs::read(&file).unwrap();
    let mut lexer = Lexer::new(&s);
    loop {
        let tok = lexer.next();
        if tok == Token::Eof {
            break;
        }
    }
}
