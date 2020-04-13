use cpp_parser::args;
use cpp_parser::defaults;
use cpp_parser::lexer::preprocessor::context::DefaultContext;
use cpp_parser::lexer::source;
use cpp_parser::lexer::{Lexer, Token};
use std::path::PathBuf;

fn main() {
    let file = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("benches/basic/ascii.cpp");
    let source = source::get_source_mutex();
    let opt = args::PreprocOptions {
        def: defaults::get_defined(),
        sys_paths: defaults::get_sys_paths(),
        includes: Vec::new(),
        current_dir: PathBuf::from("."),
    };
    let mut lexer = Lexer::<DefaultContext>::new_from_file(file.to_str().unwrap(), source, opt);
    loop {
        let tok = lexer.next();
        eprintln!("TOK: {:?}", tok);
        if tok.tok == Token::Eof {
            break;
        }
    }
}
