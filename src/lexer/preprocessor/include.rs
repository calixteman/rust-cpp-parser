use std::fs::File;
use std::io::Read;
use std::path::{Path, PathBuf};

use crate::lexer::buffer::BufferData;
use crate::lexer::lexer::Lexer;
use crate::lexer::preprocessor::PreprocContext;
use crate::lexer::source::{FileId, SourceMutex};

#[derive(Debug, Clone, Copy, Default)]
pub struct PathIndex(pub usize);

#[derive(Clone, Copy, Debug, PartialEq)]
enum IncludeType<'a> {
    Quote(&'a str),
    Angle(&'a str),
    Other,
}

pub trait IncludeLocator: Default {
    fn find(
        &mut self,
        angle: bool,
        path: &str,
        next: bool,
        current: FileId,
        path_index: PathIndex,
    ) -> Option<BufferData>;
    fn get_id(&mut self, path: &PathBuf) -> FileId;
    fn get_path(&self, id: FileId) -> PathBuf;
    fn set_source(&mut self, source: SourceMutex);
    fn set_sys_paths<P: AsRef<Path>>(&mut self, paths: &[P]);
}

#[derive(Clone, Debug, Default)]
pub struct DefaultIncludeLocator {
    sys: Vec<PathBuf>,
    source: Option<SourceMutex>,
}

impl DefaultIncludeLocator {
    pub fn new<P: AsRef<Path>>(sys: Vec<P>, source: SourceMutex) -> Self {
        let sys = sys.iter().map(|x| x.as_ref().to_path_buf()).collect();

        Self {
            sys,
            source: Some(source),
        }
    }

    fn read_file(path: &PathBuf) -> Option<Vec<u8>> {
        if let Ok(mut file) = File::open(path) {
            let mut data = Vec::new();
            file.read_to_end(&mut data).unwrap();
            Some(data)
        } else {
            None
        }
    }

    fn get_file(file: PathBuf, source: Option<&SourceMutex>, path_index: PathIndex) -> BufferData {
        // TODO: how to deal with that
        //let file = std::fs::canonicalize(file).unwrap();
        let id = source
            .as_ref()
            .map_or(FileId(0), |s| s.lock().unwrap().get_id(&file));
        BufferData::new(Self::read_file(&file).unwrap(), id, path_index)
    }

    fn find_angle(&self, path: &str, next: bool, path_index: PathIndex) -> Option<BufferData> {
        let path = PathBuf::from(path);

        if path.is_absolute() {
            return Some(Self::get_file(path, self.source.as_ref(), PathIndex(0)));
        }

        let index = if next { path_index.0 + 1 } else { 0 };

        for (n, dir) in self.sys.get(index..).unwrap().iter().enumerate() {
            let file = dir.join(&path);
            if file.is_file() {
                return Some(Self::get_file(
                    file,
                    self.source.as_ref(),
                    PathIndex(index + n + 1),
                ));
            }
        }

        None
    }

    fn find_quote(
        &self,
        path: &str,
        next: bool,
        current: FileId,
        path_index: PathIndex,
    ) -> Option<BufferData> {
        let path = PathBuf::from(path);

        if path.is_absolute() {
            return Some(Self::get_file(path, self.source.as_ref(), PathIndex(0)));
        }

        let index = if next { path_index.0 + 1 } else { 0 };

        let index = if index == 0 {
            if current.0 != 0 {
                let current = self.get_path(current);
                let current = current.parent().unwrap().to_path_buf();
                let file = current.join(&path);
                if file.is_file() {
                    return Some(Self::get_file(file, self.source.as_ref(), PathIndex(0)));
                }
            }
            1
        } else {
            index
        };

        for (n, dir) in self.sys.get(index - 1..).unwrap().iter().enumerate() {
            let file = dir.join(&path);
            if file.is_file() {
                return Some(Self::get_file(
                    file,
                    self.source.as_ref(),
                    PathIndex(index + n),
                ));
            }
        }

        None
    }
}

impl IncludeLocator for DefaultIncludeLocator {
    fn find(
        &mut self,
        angle: bool,
        path: &str,
        next: bool,
        current: FileId,
        path_index: PathIndex,
    ) -> Option<BufferData> {
        if angle {
            self.find_angle(path, next, path_index)
        } else {
            self.find_quote(path, next, current, path_index)
        }
    }

    fn get_id(&mut self, path: &PathBuf) -> FileId {
        self.source
            .as_ref()
            .map_or(FileId(0), |s| s.lock().unwrap().get_id(path))
    }

    fn get_path(&self, id: FileId) -> PathBuf {
        self.source
            .as_ref()
            .map(|s| s.lock().unwrap().get_path(id))
            .unwrap()
    }

    fn set_source(&mut self, source: SourceMutex) {
        self.source = Some(source);
    }

    fn set_sys_paths<P: AsRef<Path>>(&mut self, paths: &[P]) {
        self.sys = paths.iter().map(|s| s.as_ref().to_path_buf()).collect();
    }
}

impl<'a, PC: PreprocContext> Lexer<'a, PC> {
    pub(crate) fn get_include_content(&mut self, term: u8) -> &'a [u8] {
        let spos = self.buf.pos();
        loop {
            if self.buf.has_char() {
                let c = self.buf.next_char();
                if c == term {
                    let s = if self.buf.prev_char() == b' ' {
                        let p = self.buf.pos() + 1;
                        self.buf.dec_n(2);
                        skip_whites_back!(self);
                        let s = self.buf.slice_n(spos, 1);
                        self.buf.set_pos(p);
                        s
                    } else {
                        let s = self.buf.slice(spos);
                        self.buf.inc();
                        s
                    };
                    return &s;
                } else {
                    self.buf.inc();
                }
            } else {
                return self.buf.slice(spos);
            }
        }
    }

    fn get_path(&mut self) -> IncludeType<'a> {
        skip_whites!(self);
        if self.buf.has_char() {
            let c = self.buf.next_char();
            if c == b'\"' {
                // Quoted path
                self.buf.inc();
                skip_whites!(self);
                let path = self.get_include_content(b'\"');
                let path = std::str::from_utf8(path).unwrap();
                return IncludeType::Quote(path);
            } else if c == b'<' {
                // Angled path
                self.buf.inc();
                skip_whites!(self);
                let path = self.get_include_content(b'>');
                let path = std::str::from_utf8(path).unwrap();
                return IncludeType::Angle(path);
            }
        }
        IncludeType::Other
    }

    pub(crate) fn get_include(&mut self, next: bool) {
        match self.get_path() {
            IncludeType::Quote(path) => {
                let source_id = self.buf.get_source_id().unwrap();
                let path_index = self.buf.get_path_index().unwrap();
                let buf = self
                    .context
                    .find(false, path, next, source_id, path_index)
                    .unwrap();
                self.buf.add_buffer(buf);
            }
            IncludeType::Angle(path) => {
                let source_id = self.buf.get_source_id().unwrap();
                let path_index = self.buf.get_path_index().unwrap();
                let buf = self
                    .context
                    .find(true, path, next, source_id, path_index)
                    .unwrap();
                self.buf.add_buffer(buf);
            }
            IncludeType::Other => {
                skip_whites!(self);
                let id = self.get_preproc_identifier();
                if self.macro_eval(id) {
                    self.buf.switch_to_preproc();
                    let path = self.get_path();
                    self.buf.rm_buffer();
                    let source_id = self.buf.get_source_id().unwrap();
                    let path_index = self.buf.get_path_index().unwrap();

                    match path {
                        IncludeType::Quote(path) => {
                            let buf = self
                                .context
                                .find(false, path, next, source_id, path_index)
                                .unwrap();
                            self.buf.add_buffer(buf);
                        }
                        IncludeType::Angle(path) => {
                            let buf = self
                                .context
                                .find(true, path, next, source_id, path_index)
                                .unwrap();
                            self.buf.add_buffer(buf);
                        }
                        _ => {
                            unreachable!();
                        }
                    }
                } else {
                    skip_until!(self, b'\n');
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {

    use std::sync::{Arc, Mutex};
    use tempdir::TempDir;

    use super::*;
    use crate::lexer::lexer::Token;
    use crate::lexer::preprocessor::context::{Context, DefaultContext};
    use crate::lexer::preprocessor::macros::Macro;
    use crate::lexer::source::SourceLocator;
    use pretty_assertions::{assert_eq, assert_ne};

    macro_rules! eval {
        ( $name: expr, $lexer: expr ) => {{
            let context = $lexer.context.clone();
            let mut res = Vec::new();
            let info = $lexer.buf.get_line_file();
            let mac = context.get($name).unwrap();
            match mac {
                Macro::Object(mac) => {
                    mac.eval(&mut res, &context, &info);
                }
                _ => {}
            }
            String::from_utf8(res).unwrap()
        }};
    }

    macro_rules! lexer_for_file {
        ( $name: ident, $code: expr, $file: expr, $id: expr, $context: expr) => {
            std::fs::write($file, $code).unwrap();
            let mut file = File::open($file).unwrap();
            let mut data = Vec::new();
            file.read_to_end(&mut data).unwrap();

            let mut $name = Lexer::new_with_context(&data, $id, $context);
        };
    }

    #[derive(Clone, Default)]
    struct TestIncludeLocator {}

    impl IncludeLocator for TestIncludeLocator {
        fn find(
            &mut self,
            angle: bool,
            path: &str,
            _next: bool,
            _current: FileId,
            _path_index: PathIndex,
        ) -> Option<BufferData> {
            let buf = if angle {
                match path {
                    "path1" => b"#define foo 123\n".to_vec(),
                    "path2" => b"#include <path1>\n#define bar(x) foo x\n".to_vec(),
                    _ => unreachable!(),
                }
            } else {
                match path {
                    "path3" => b"#include \"path4\"\n".to_vec(),
                    "path4" => b"#include \"path5\"\n".to_vec(),
                    "path5" => b"#include \"path6\"\n".to_vec(),
                    "path6" => b"#include \"path7\"\n".to_vec(),
                    "path7" => b"#include \"path8\"\n".to_vec(),
                    "path8" => b"#include \"    path9   \t    \"\n".to_vec(),
                    "path9" => b"#include \"path10\"\n".to_vec(),
                    "path10" => b"#include \"path11\"\n".to_vec(),
                    "path11" => b"#include \"path12\"\n".to_vec(),
                    "path12" => b"#include \"path13\"\n".to_vec(),
                    "path13" => b"#include \"path14\"\n".to_vec(),
                    "path14" => b"#define hello world\n".to_vec(),
                    "path15" => b"#define MAC1(x) #x\n".to_vec(),
                    "path16" => b"#define pi 3.14159\n".to_vec(),
                    "path17" => concat!(
                        "#ifndef test\n",
                        "#endif\n",
                        "\n",
                        "#ifdef test\n",
                        "#undef test\n",
                        "#endif\n",
                    )
                    .as_bytes()
                    .to_vec(),
                    _ => unreachable!(),
                }
            };
            Some(BufferData::new(buf, FileId(0), PathIndex(0)))
        }

        fn get_id(&mut self, _path: &PathBuf) -> FileId {
            FileId(0)
        }

        fn get_path(&self, _id: FileId) -> PathBuf {
            PathBuf::from("")
        }

        fn set_source(&mut self, _source: SourceMutex) {}

        fn set_sys_paths<P: AsRef<Path>>(&mut self, _paths: &[P]) {}
    }

    #[test]
    fn test_include1() {
        let mut p = Lexer::<Context<TestIncludeLocator>>::new(
            concat!("#include <path1>\n", "#define test1 foo\n",).as_bytes(),
        );
        p.consume_all();
        assert_eq!(eval!("test1", p), "123 ");
    }

    #[test]
    fn test_include2() {
        let mut p = Lexer::<Context<TestIncludeLocator>>::new(
            concat!(
                "#include <path2>\n",
                "#define test1 foo\n",
                "#define test2 bar(456)\n",
            )
            .as_bytes(),
        );
        p.consume_all();
        assert_eq!(eval!("test1", p), "123 ");
        assert_eq!(eval!("test2", p), "123 456 ");
    }

    #[test]
    fn test_include_nested() {
        let mut p = Lexer::<Context<TestIncludeLocator>>::new(
            concat!("#include \"path3\"\n", "#define test1 hello\n",).as_bytes(),
        );
        p.consume_all();
        assert_eq!(eval!("test1", p), "world ");
    }

    #[test]
    fn test_include_macro() {
        let mut p = Lexer::<Context<TestIncludeLocator>>::new(
            concat!(
                "#define PATH <path1>\n",
                "#include PATH\n",
                "#define test1 foo\n",
            )
            .as_bytes(),
        );
        p.consume_all();
        assert_eq!(eval!("test1", p), "123 ");
    }

    #[test]
    fn test_include_macro_call() {
        let mut p = Lexer::<Context<TestIncludeLocator>>::new(
            concat!(
                "#define PATH \"path15\"\n",
                "#include PATH\n",
                "#include MAC1(path16)\n",
                "#define test1 pi\n",
            )
            .as_bytes(),
        );
        p.consume_all();
        assert_eq!(eval!("test1", p), "3.14159 ");
    }

    #[test]
    fn test_include_multiple() {
        let mut p = Lexer::<Context<TestIncludeLocator>>::new(
            concat!(
                "#define test\n",
                "#include \"path17\"\n",
                "#define test\n",
                "#include \"path17\"\n",
                "\n",
                "#ifdef test\n",
                "#define foo error\n",
                "#else\n",
                "#define foo ok\n",
                "#endif\n",
                "#define test foo\n",
            )
            .as_bytes(),
        );
        p.consume_all();
        assert_eq!(eval!("test", p), "ok ");
    }

    #[test]
    fn test_include_sys() {
        let tmp = TempDir::new("test").unwrap();
        let sys = tmp.path().join("sys");
        let cur = tmp.path().join("cur");
        let inc = tmp.path().join("inc");

        std::fs::create_dir_all(&sys).unwrap();
        std::fs::create_dir_all(&cur).unwrap();
        std::fs::create_dir_all(&inc).unwrap();

        std::fs::write(sys.join("foo.h"), "#define test sys_foo\n").unwrap();
        std::fs::write(cur.join("foo.h"), "#define test cur_foo\n").unwrap();
        std::fs::write(inc.join("foo.h"), "#define test inc_foo\n").unwrap();
        std::fs::write(inc.join("bar.h"), "#define test inc_bar\n").unwrap();
        std::fs::write(sys.join("oof.h"), "#include \"foo.h\"\n").unwrap();

        let source = Arc::new(Mutex::new(SourceLocator::default()));
        let include = DefaultIncludeLocator::new(
            vec![inc.to_str().unwrap(), sys.to_str().unwrap()],
            source.clone(),
        );
        let mut context = DefaultContext::new(include);

        let foo = cur.join("foo.c");
        std::fs::write(&foo, "").unwrap();
        let foo = std::fs::canonicalize(foo).unwrap();
        let id = context.get_id(&foo);

        lexer_for_file!(p, "#include <foo.h>\ntest", &foo, id, context.clone());
        assert_eq!(p.next().tok, Token::PreprocInclude);
        assert_eq!(p.next().tok, Token::PreprocDefine);
        assert_eq!(p.next().tok, Token::Eol);
        assert_eq!(p.next().tok, Token::Identifier("inc_foo".to_string()));

        lexer_for_file!(p, "#include \"foo.h\"\ntest", &foo, id, context.clone());
        assert_eq!(p.next().tok, Token::PreprocInclude);
        assert_eq!(p.next().tok, Token::PreprocDefine);
        assert_eq!(p.next().tok, Token::Eol);
        assert_eq!(p.next().tok, Token::Identifier("cur_foo".to_string()));

        lexer_for_file!(
            p,
            "#include_next \"foo.h\"\ntest",
            &foo,
            id,
            context.clone()
        );
        assert_eq!(p.next().tok, Token::PreprocIncludeNext);
        assert_eq!(p.next().tok, Token::PreprocDefine);
        assert_eq!(p.next().tok, Token::Eol);
        assert_eq!(p.next().tok, Token::Identifier("inc_foo".to_string()));

        lexer_for_file!(p, "#include_next <foo.h>\ntest", &foo, id, context.clone());
        assert_eq!(p.next().tok, Token::PreprocIncludeNext);
        assert_eq!(p.next().tok, Token::PreprocDefine);
        assert_eq!(p.next().tok, Token::Eol);
        assert_eq!(p.next().tok, Token::Identifier("sys_foo".to_string()));

        lexer_for_file!(
            p,
            "#include_next \"bar.h\"\ntest",
            &foo,
            id,
            context.clone()
        );
        assert_eq!(p.next().tok, Token::PreprocIncludeNext);
        assert_eq!(p.next().tok, Token::PreprocDefine);
        assert_eq!(p.next().tok, Token::Eol);
        assert_eq!(p.next().tok, Token::Identifier("inc_bar".to_string()));

        lexer_for_file!(p, "#include <oof.h>\ntest", &foo, id, context.clone());
        assert_eq!(p.next().tok, Token::PreprocInclude);
        assert_eq!(p.next().tok, Token::PreprocInclude);
        assert_eq!(p.next().tok, Token::PreprocDefine);
        assert_eq!(p.next().tok, Token::Eol);
        assert_eq!(p.next().tok, Token::Eol);
        assert_eq!(p.next().tok, Token::Identifier("sys_foo".to_string()));
    }
}
