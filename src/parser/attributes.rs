// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use crate::lexer::preprocessor::context::PreprocContext;
use crate::lexer::{Lexer, LocToken, Token};

#[derive(Clone, Debug, PartialEq)]
pub struct Attribute {
    pub namespace: Option<String>,
    pub name: String,
    pub arg: Option<AttributeArg>,
    pub has_using: bool,
}

pub type Attributes = Vec<Attribute>;

struct UsingParser<'a, 'b, PC: PreprocContext> {
    lexer: &'b mut Lexer<'a, PC>,
}

impl<'a, 'b, PC: PreprocContext> UsingParser<'a, 'b, PC> {
    fn new(lexer: &'b mut Lexer<'a, PC>) -> Self {
        Self { lexer }
    }

    fn parse(self) -> (Option<LocToken>, Option<String>) {
        let tok = self.lexer.next_useful();
        if tok.tok == Token::Using {
            let tok = self.lexer.next_useful();
            if let Token::Identifier(ns) = tok.tok {
                let ns = Some(ns);
                let tok = self.lexer.next_useful();
                match tok.tok {
                    Token::Colon => {
                        return (None, ns);
                    }
                    _ => {
                        unreachable!("Invalid token in attributes: {:?}", tok);
                    }
                }
            } else {
                unreachable!("Invalid token in attributes: {:?}", tok);
            }
        }
        (Some(tok), None)
    }
}

#[derive(Clone, Debug, Default, PartialEq)]
pub struct AttributeArg {
    pub tokens: Vec<Token>,
}

struct ArgumentParser<'a, 'b, PC: PreprocContext> {
    lexer: &'b mut Lexer<'a, PC>,
}

impl<'a, 'b, PC: PreprocContext> ArgumentParser<'a, 'b, PC> {
    fn new(lexer: &'b mut Lexer<'a, PC>) -> Self {
        Self { lexer }
    }

    fn parse(self, tok: Option<LocToken>) -> (Option<LocToken>, Option<AttributeArg>) {
        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        if tok.tok != Token::LeftParen {
            return (Some(tok), None);
        }

        let mut arg = AttributeArg::default();
        let mut paren_count = 1;
        let mut brack_count = 0;
        let mut brace_count = 0;

        loop {
            let tok = self.lexer.next_useful();
            match tok.tok {
                Token::LeftParen => {
                    paren_count += 1;
                }
                Token::RightParen => {
                    if paren_count == 1 {
                        if brack_count != 0 || brace_count != 0 {
                            unreachable!("Unbalanced attribute");
                        } else {
                            return (None, Some(arg));
                        }
                    } else {
                        paren_count -= 1;
                    }
                }
                Token::LeftBrack => {
                    brack_count += 1;
                }
                Token::RightBrack => {
                    if brack_count == 0 {
                        unreachable!("Unbalanced attribute");
                    } else {
                        brack_count -= 1;
                    }
                }
                Token::LeftBrace => {
                    brace_count += 1;
                }
                Token::RightBrace => {
                    if brace_count == 0 {
                        unreachable!("Unbalanced attribute");
                    } else {
                        brace_count -= 1;
                    }
                }
                Token::Eof => {
                    unreachable!("Wrong attribute");
                }
                t => {
                    arg.tokens.push(t);
                }
            }
        }
    }
}

struct NameParser<'a, 'b, PC: PreprocContext> {
    lexer: &'b mut Lexer<'a, PC>,
}

impl<'a, 'b, PC: PreprocContext> NameParser<'a, 'b, PC> {
    fn new(lexer: &'b mut Lexer<'a, PC>) -> Self {
        Self { lexer }
    }

    fn parse(self, tok: LocToken) -> (Option<LocToken>, (Option<String>, String)) {
        match tok.tok {
            Token::Identifier(id) => {
                let tk = self.lexer.next_useful();
                if tk.tok == Token::ColonColon {
                    let ns = Some(id);
                    let tk = self.lexer.next_useful();
                    if let Token::Identifier(id) = tk.tok {
                        (None, (ns, id))
                    } else {
                        unreachable!("Invalid token in attributes: {:?}", tk);
                    }
                } else {
                    (Some(tk), (None, id))
                }
            }
            _ => {
                unreachable!("Invalid token in attributes: {:?}", tok);
            }
        }
    }
}

struct AttributeParser<'a, 'b, PC: PreprocContext> {
    lexer: &'b mut Lexer<'a, PC>,
}

impl<'a, 'b, PC: PreprocContext> AttributeParser<'a, 'b, PC> {
    fn new(lexer: &'b mut Lexer<'a, PC>) -> Self {
        Self { lexer }
    }

    fn parse(self, attributes: &mut Attributes, tok: Option<LocToken>) -> (Option<LocToken>, bool) {
        // [[ attribute-list ]]
        // [[ using attribute-namespace : attribute-list ]]
        //
        // attributes
        //   identifier
        //   attribute-namespace :: identifier
        //   identifier ( argument-list )
        //   attribute-namespace :: identifier ( argument-list )

        let tok = tok.unwrap_or_else(|| self.lexer.next_useful());
        if tok.tok != Token::DoubleLeftBrack {
            return (Some(tok), false);
        }

        let up = UsingParser::new(self.lexer);
        let (tok, default_ns) = up.parse();
        let has_using = default_ns.is_some();

        let mut tok = tok.unwrap_or_else(|| self.lexer.next_useful());

        loop {
            let np = NameParser::new(self.lexer);
            let (tk, (namespace, id)) = np.parse(tok);

            let ap = ArgumentParser::new(self.lexer);
            let (tk, arg) = ap.parse(tk);

            attributes.push(Attribute {
                namespace: namespace.or_else(|| default_ns.clone()),
                name: id,
                arg,
                has_using,
            });

            tok = tk.unwrap_or_else(|| self.lexer.next_useful());
            match tok.tok {
                Token::Comma => {}
                Token::DoubleRightBrack => {
                    return (None, true);
                }
                _ => {
                    unreachable!("Invalid token in attributes: {:?}", tok);
                }
            }

            tok = self.lexer.next_useful();
        }
    }
}

pub struct AttributesParser<'a, 'b, PC: PreprocContext> {
    lexer: &'b mut Lexer<'a, PC>,
}

impl<'a, 'b, PC: PreprocContext> AttributesParser<'a, 'b, PC> {
    pub(super) fn new(lexer: &'b mut Lexer<'a, PC>) -> Self {
        Self { lexer }
    }

    pub(super) fn parse(self, tok: Option<LocToken>) -> (Option<LocToken>, Option<Attributes>) {
        let mut attributes = Vec::new();
        let mut tok = tok;
        let mut has_attributes = false;

        loop {
            let ap = AttributeParser::new(self.lexer);
            let (tk, has_attr) = ap.parse(&mut attributes, tok);
            tok = tk;
            has_attributes |= has_attr;

            if !has_attr {
                break;
            }
        }

        if has_attributes {
            (tok, Some(attributes))
        } else {
            (tok, None)
        }
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::lexer::preprocessor::context::DefaultContext;
    use pretty_assertions::assert_eq;

    #[test]
    fn test_attr_single() {
        let mut l = Lexer::<DefaultContext>::new(b"[[noreturn]]");
        let p = AttributesParser::new(&mut l);
        let (_, a) = p.parse(None);

        assert_eq!(
            a.unwrap(),
            vec![Attribute {
                namespace: None,
                name: "noreturn".to_string(),
                arg: None,
                has_using: false
            },]
        );
    }

    #[test]
    fn test_attr_ns() {
        let mut l = Lexer::<DefaultContext>::new(b"[[gnu::unused]]");
        let p = AttributesParser::new(&mut l);
        let (_, a) = p.parse(None);

        assert_eq!(
            a.unwrap(),
            vec![Attribute {
                namespace: Some("gnu".to_string()),
                name: "unused".to_string(),
                arg: None,
                has_using: false
            },]
        );
    }

    #[test]
    fn test_attr_arg() {
        let mut l = Lexer::<DefaultContext>::new(b"[[deprecated(\"because\")]]");
        let p = AttributesParser::new(&mut l);
        let (_, a) = p.parse(None);

        assert_eq!(
            a.unwrap(),
            vec![Attribute {
                namespace: None,
                name: "deprecated".to_string(),
                arg: Some(AttributeArg {
                    tokens: vec![Token::LiteralString("because".to_string()),],
                }),
                has_using: false
            },]
        );
    }

    #[test]
    fn test_attr_using() {
        let mut l = Lexer::<DefaultContext>::new(b"[[using CC: opt(1), debug]]");
        let p = AttributesParser::new(&mut l);
        let (_, a) = p.parse(None);

        assert_eq!(
            a.unwrap(),
            vec![
                Attribute {
                    namespace: Some("CC".to_string()),
                    name: "opt".to_string(),
                    arg: Some(AttributeArg {
                        tokens: vec![Token::LiteralInt(1),],
                    }),
                    has_using: true,
                },
                Attribute {
                    namespace: Some("CC".to_string()),
                    name: "debug".to_string(),
                    arg: None,
                    has_using: true,
                },
            ]
        );
    }

    #[test]
    fn test_attr_several() {
        let mut l = Lexer::<DefaultContext>::new(b"[[A]] [[B]] [[C]]");
        let p = AttributesParser::new(&mut l);
        let (_, a) = p.parse(None);

        assert_eq!(
            a.unwrap(),
            vec![
                Attribute {
                    namespace: None,
                    name: "A".to_string(),
                    arg: None,
                    has_using: false,
                },
                Attribute {
                    namespace: None,
                    name: "B".to_string(),
                    arg: None,
                    has_using: false,
                },
                Attribute {
                    namespace: None,
                    name: "C".to_string(),
                    arg: None,
                    has_using: false,
                },
            ]
        );
    }
}
