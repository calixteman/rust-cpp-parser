use super::namespace::{NPRes, Namespace, NamespaceParser};
use super::r#extern::{EPRes, Extern, ExternParser};
use crate::lexer::preprocessor::context::PreprocContext;
use crate::lexer::{Lexer, LocToken};
use crate::parser::statement::{Statement, StatementParser};

#[derive(Clone, Debug, PartialEq)]
pub enum TopLevel {
    Extern(Extern),
    Statement(Statement),
    Namespace(Namespace),
}

pub type DeclarationList = Vec<TopLevel>;

pub struct TopLevelParser<'a, 'b, PC: PreprocContext> {
    lexer: &'b mut Lexer<'a, PC>,
}

impl<'a, 'b, PC: PreprocContext> TopLevelParser<'a, 'b, PC> {
    fn new(lexer: &'b mut Lexer<'a, PC>) -> Self {
        Self { lexer }
    }

    pub(crate) fn parse(self, tok: Option<LocToken>) -> (Option<LocToken>, Option<TopLevel>) {
        let ep = ExternParser::new(self.lexer);
        let (tok, epr) = ep.parse(tok);

        if let Some(epr) = epr {
            match epr {
                EPRes::Extern(e) => {
                    return (tok, Some(TopLevel::Extern(e)));
                }
                EPRes::Declaration(decl) => {
                    return (tok, Some(TopLevel::Statement(decl)));
                }
            }
        }

        let np = NamespaceParser::new(self.lexer);
        let (tok, nsr) = np.parse(tok);

        if let Some(nsr) = nsr {
            match nsr {
                NPRes::Namespace(ns) => {
                    return (tok, Some(TopLevel::Namespace(ns)));
                }
                NPRes::Declaration(decl) => {
                    return (tok, Some(TopLevel::Statement(decl)));
                }
            }
        }

        let sp = StatementParser::new(self.lexer);
        let (tok, stmt) = sp.parse(tok);

        if let Some(stmt) = stmt {
            return (tok, Some(TopLevel::Statement(stmt)));
        }

        (tok, None)
    }
}

pub struct DeclarationListParser<'a, 'b, PC: PreprocContext> {
    lexer: &'b mut Lexer<'a, PC>,
}

impl<'a, 'b, PC: PreprocContext> DeclarationListParser<'a, 'b, PC> {
    pub(crate) fn new(lexer: &'b mut Lexer<'a, PC>) -> Self {
        Self { lexer }
    }

    pub(crate) fn parse(
        self,
        tok: Option<LocToken>,
    ) -> (Option<LocToken>, Option<DeclarationList>) {
        let mut tok = tok;
        let mut list = Vec::new();

        loop {
            let tp = TopLevelParser::new(self.lexer);
            let (tk, tl) = tp.parse(tok.clone());

            if let Some(tl) = tl {
                list.push(tl);
            } else {
                return (tk, Some(list));
            }

            tok = tk
        }
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::lexer::preprocessor::context::DefaultContext;
    use pretty_assertions::assert_eq;

    #[test]
    fn test_titi() {
        let mut l = Lexer::<DefaultContext>::new(
            br#"
        //inline void foo() {}

        inline namespace A { }

        //namespace B {}
        "#,
        );
        let p = DeclarationListParser::new(&mut l);
        let (_, ns) = p.parse(None);

        eprintln!("{:?}", ns.unwrap());
        //assert!(false);
    }
}

/*
int fact (int i) {
    int result = 1;
    while (i > 0) {
        result = result * i;
        i = i-1;
    }
    return(result);
}

int main () {
    int n;
    cout << 1;
    cin >> n;
    while (n > 0) {
        cout << 2;
        cin >> n;
    }
    cout << n << 3 << fact(n) << endl;
    return(0);
}
*/
