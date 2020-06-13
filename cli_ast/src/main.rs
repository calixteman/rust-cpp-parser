// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

#[macro_use]
extern crate clap;

use clap::{App, Arg};
use cpp_parser::args::{Language, PreprocOptions};
use cpp_parser::defaults;
use cpp_parser::lexer::preprocessor::cache::IfCache;
use cpp_parser::lexer::preprocessor::context::{DefaultContext, PreprocContext};
use cpp_parser::lexer::source::{self, FileId, SourceMutex};
use cpp_parser::lexer::{Lexer, TLexer};
use cpp_parser::parser::{Context, Dump, Unit, UnitParser};
use std::path::PathBuf;
use std::sync::{Arc, Mutex};

fn main() {
    let matches = App::new("AST dump")
        .version(crate_version!())
        .author(&*env!("CARGO_PKG_AUTHORS").replace(':', "\n"))
        .about("Report macro use")
        .arg(
            Arg::with_name("file")
                .help("File to dump")
                .takes_value(true),
        )
        .get_matches();

    let file = matches.value_of("file").unwrap().to_string();

    let source = source::get_source_mutex();
    let if_cache = Arc::new(IfCache::default());
    let opt = PreprocOptions {
        def: defaults::get_defined(),
        sys_paths: defaults::get_sys_paths(),
        includes: vec![],
        current_dir: PathBuf::from("."),
        file: PathBuf::from(""),
        lang: Language::CPP,
    };

    let lexer = Lexer::<DefaultContext>::new_from_file(&file, source, if_cache, opt);

    let context = Context::default();
    let mut parser = UnitParser { lexer, context };

    match parser.parse() {
        Ok(unit) => {
            unit.dump_me();
        }
        Err(e) => {
            eprintln!("{:?}", e);
        }
    }
}
