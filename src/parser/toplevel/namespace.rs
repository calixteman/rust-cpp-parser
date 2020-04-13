use super::toplevel::{DeclarationList, DeclarationListParser};
use crate::lexer::preprocessor::context::PreprocContext;
use crate::lexer::{Lexer, LocToken, Token};
use crate::parser::declarations::{DeclHint, DeclarationParser};
use crate::parser::statement::Statement;
use crate::{check_semicolon, check_semicolon_or_not};

#[derive(Clone, Debug, PartialEq)]
pub struct NsName {
    pub(crate) inline: bool,
    pub(crate) name: String,
}

pub type NsNames = Vec<NsName>;

#[derive(Clone, Debug, PartialEq)]
pub struct Namespace {
    pub(crate) inline: bool,
    pub(crate) name: Option<NsNames>,
    pub(crate) alias: Option<NsNames>,
    pub(crate) body: Option<Box<DeclarationList>>,
}

struct NsNamesParser<'a, 'b, PC: PreprocContext> {
    lexer: &'b mut Lexer<'a, PC>,
}

impl<'a, 'b, PC: PreprocContext> NsNamesParser<'a, 'b, PC> {
    fn new(lexer: &'b mut Lexer<'a, PC>) -> Self {
        Self { lexer }
    }

    fn parse(self) -> (Option<LocToken<'a>>, Option<NsNames>) {
        let mut tok = self.lexer.next_useful();
        let mut names = Vec::new();
        let mut inline = false;

        loop {
            match tok.tok {
                Token::Inline => {
                    inline = true;
                }
                Token::Identifier(id) => {
                    names.push(NsName { inline, name: id });
                }
                Token::ColonColon => {
                    inline = false;
                }
                _ => {
                    return (Some(tok), Some(names));
                }
            }
            tok = self.lexer.next_useful();
        }
    }
}

pub(super) enum NPRes {
    Namespace(Namespace),
    Declaration(Statement),
}

pub struct NamespaceParser<'a, 'b, PC: PreprocContext> {
    lexer: &'b mut Lexer<'a, PC>,
}

impl<'a, 'b, PC: PreprocContext> NamespaceParser<'a, 'b, PC> {
    pub(super) fn new(lexer: &'b mut Lexer<'a, PC>) -> Self {
        Self { lexer }
    }

    pub(super) fn parse(self, tok: Option<LocToken<'a>>) -> (Option<LocToken<'a>>, Option<NPRes>) {
        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());

        let inline = if tok.tok == Token::Inline {
            let tok = self.lexer.next_useful();
            if tok.tok != Token::Namespace {
                let dp = DeclarationParser::new(self.lexer);
                let hint = DeclHint::with_inline();
                let (tok, decl) = dp.parse(Some(tok), Some(hint));
                let (tok, decl) = check_semicolon_or_not!(self, tok, decl);

                return (tok, Some(NPRes::Declaration(decl.unwrap())));
            }
            true
        } else if tok.tok != Token::Namespace {
            return (Some(tok), None);
        } else {
            false
        };

        let np = NsNamesParser::new(self.lexer);
        let (tok, name) = np.parse();
        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());

        match tok.tok {
            Token::LeftBrace => {
                let dlp = DeclarationListParser::new(self.lexer);
                let (tok, body) = dlp.parse(None);
                let tok = tok.unwrap_or_else(|| self.lexer.next_useful());

                if tok.tok != Token::RightBrace {
                    unreachable!("Invalid token in namespace definition: {:?}", tok);
                }

                let ns = Namespace {
                    inline,
                    name,
                    alias: None,
                    body: body.map(Box::new),
                };
                (None, Some(NPRes::Namespace(ns)))
            }
            Token::Equal => {
                let np = NsNamesParser::new(self.lexer);
                let (tok, alias) = np.parse();
                check_semicolon!(self, tok);
                let ns = Namespace {
                    inline,
                    name,
                    alias,
                    body: None,
                };
                (None, Some(NPRes::Namespace(ns)))
            }
            _ => {
                unreachable!("Invalid token in namespace definition: {:?}", tok);
            }
        }
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::lexer::preprocessor::context::DefaultContext;
    use crate::parser::expression::*;
    use pretty_assertions::{assert_eq, assert_ne};

    #[test]
    fn test_namespace_one() {
        let mut l = Lexer::<DefaultContext>::new(b"A");
        let p = NsNamesParser::new(&mut l);
        let (_, ns) = p.parse();

        assert_eq!(
            ns.unwrap(),
            vec![NsName {
                inline: false,
                name: "A".to_string(),
            }]
        );
    }

    #[test]
    fn test_namespace_multiple() {
        let mut l = Lexer::<DefaultContext>::new(b"A::inline B::C::inline D::E");
        let p = NsNamesParser::new(&mut l);
        let (_, ns) = p.parse();

        assert_eq!(
            ns.unwrap(),
            vec![
                NsName {
                    inline: false,
                    name: "A".to_string(),
                },
                NsName {
                    inline: true,
                    name: "B".to_string(),
                },
                NsName {
                    inline: false,
                    name: "C".to_string(),
                },
                NsName {
                    inline: true,
                    name: "D".to_string(),
                },
                NsName {
                    inline: false,
                    name: "E".to_string(),
                },
            ]
        );
    }
}
