// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use termcolor::StandardStreamLock;

use hashbrown::HashMap;
use std::cell::RefCell;
use std::rc::Rc;

use crate::parser::declarations::namespace::NsNames;
use crate::parser::declarations::TypeDeclarator;
use crate::parser::dump::Dump;
use crate::parser::names::name::{Identifier, Name, Qualified};

#[derive(Debug, Default, PartialEq)]
pub struct TypeToFix(Rc<RefCell<Option<Rc<TypeDeclarator>>>>);

impl Clone for TypeToFix {
    fn clone(&self) -> Self {
        TypeToFix(Rc::clone(&self.0))
    }
}

impl Dump for TypeToFix {
    fn dump(&self, name: &str, prefix: &str, last: bool, stdout: &mut StandardStreamLock) {
        let ttf = self.0.borrow();
        if let Some(ty) = ttf.as_ref() {
            ty.get_names().typ.dump(name, prefix, last, stdout);
        } else {
            ttf.dump(name, prefix, last, stdout);
        }
    }
}

impl TypeToFix {
    pub(crate) fn fix(&self, typ: Rc<TypeDeclarator>) {
        let mut inc = self.0.borrow_mut();
        if inc.is_none() {
            *inc = Some(typ);
        }
    }

    pub(crate) fn get_type(&self) -> Option<Rc<TypeDeclarator>> {
        self.0.borrow().as_ref().map(Rc::clone)
    }
}

#[derive(Clone, Debug)]
pub enum Incomplete {
    Class(TypeToFix),
    Enum(TypeToFix),
}

#[derive(Clone, Debug)]
pub(crate) enum Kind {
    Type(Rc<TypeDeclarator>),
    Var(Rc<TypeDeclarator>),
}

#[derive(Clone, Debug)]
pub enum ScopeKind {
    Ns,
    Class,
    Enum,
    Block,
}

#[derive(Clone, Debug)]
pub struct Scope {
    kind: ScopeKind,
    decls: HashMap<Name, Kind>,
    scopes: HashMap<String, Rc<RefCell<Scope>>>,
    using: Vec<Rc<RefCell<Scope>>>,
    incomplete: Option<TypeToFix>,
}

impl Scope {
    fn new(kind: ScopeKind) -> Self {
        Self {
            kind,
            decls: HashMap::default(),
            scopes: HashMap::default(),
            using: Vec::default(),
            incomplete: None,
        }
    }
}

impl Default for Scope {
    fn default() -> Self {
        Self::new(ScopeKind::Ns)
    }
}

#[derive(Clone, Debug)]
pub struct Context {
    stack: Vec<Rc<RefCell<Scope>>>,
}

#[derive(Clone, Debug)]
pub enum SearchResult {
    Type(Rc<TypeDeclarator>),
    Var(Rc<TypeDeclarator>),
    Incomplete(TypeToFix),
}

impl SearchResult {
    pub(crate) fn is_type(&self) -> bool {
        match self {
            Self::Var(_) => false,
            _ => true,
        }
    }
}

impl Default for Context {
    fn default() -> Self {
        Self {
            stack: vec![Rc::new(RefCell::new(Scope::default()))],
        }
    }
}

trait Search {
    fn search(&self, names: &[Name]) -> Option<SearchResult>;
    fn search_scope<T: AsRef<str>>(self, names: &[T]) -> Self;
}

impl Search for Rc<RefCell<Scope>> {
    fn search(&self, names: &[Name]) -> Option<SearchResult> {
        let n_names = names.len();
        let last = &names[n_names - 1];

        let mut scope = Rc::clone(self);
        let mut index = n_names;

        for i in 0..n_names - 1 {
            let name = &names[i];
            scope = {
                let sc = scope.borrow();
                if let Some(s) = sc.scopes.get(name.as_ref()) {
                    Rc::clone(s)
                } else {
                    index = i;
                    break;
                }
            }
        }

        let sc = scope.borrow();
        if index == n_names {
            // a scope has been found so try to get the type/var
            let decl = sc.decls.get(&last);
            if let Some(decl) = decl {
                Some(match decl {
                    Kind::Type(ty) => SearchResult::Type(Rc::clone(ty)),
                    Kind::Var(ty) => SearchResult::Var(Rc::clone(ty)),
                })
            } else {
                // self refering struct/enum
                if let Some(sc) = sc.scopes.get(last.as_ref()) {
                    let mut sc = sc.borrow_mut();
                    let inc = if let Some(inc) = sc.incomplete.as_ref() {
                        inc.clone()
                    } else {
                        let inc = TypeToFix::default();
                        sc.incomplete = Some(inc.clone());
                        inc
                    };

                    /*Some(match sc.kind {
                            ScopeKind::Class => SearchResult::Inc(Incomplete::Class(inc)),
                            ScopeKind::Enum => SearchResult::Inc(Incomplete::Enum(inc)),
                            _ => unreachable!("Can refer only to a class or an enum"),
                    })*/
                    Some(SearchResult::Incomplete(inc))
                } else {
                    // search in using
                    for u in sc.using.iter() {
                        let decl = u.search(&names[n_names - 1..]);
                        if decl.is_some() {
                            return decl;
                        }
                    }
                    None
                }
            }
        } else {
            // search in using
            for u in sc.using.iter() {
                let decl = u.search(&names[index..]);
                if decl.is_some() {
                    return decl;
                }
            }
            None
        }
    }

    fn search_scope<T: AsRef<str>>(self, names: &[T]) -> Self {
        let mut scope = self;
        for name in names {
            scope = {
                let sc = scope.borrow();
                if let Some(s) = sc.scopes.get(name.as_ref()) {
                    Rc::clone(s)
                } else {
                    unreachable!("Invalid name in qualified name")
                }
            }
        }
        scope
    }
}

impl Context {
    pub fn search(&self, name: Option<&Qualified>) -> Option<SearchResult> {
        if let Some(name) = name {
            for scope in self.stack.iter().rev() {
                let ty = scope.search(&name.names);
                if ty.is_some() {
                    return ty;
                }
            }
        }
        None
    }

    pub fn set_current(&mut self, name: Option<&Qualified>, kind: ScopeKind) {
        if let Some(name) = name {
            if let Some((last, names)) = name.names.split_last() {
                let mut scope = Rc::clone(self.stack.last().unwrap());
                for name in names {
                    scope = {
                        let sc = scope.borrow();
                        if let Some(s) = sc.scopes.get(name.as_ref()) {
                            self.stack.push(Rc::clone(s));
                            Rc::clone(s)
                        } else {
                            unreachable!("Invalid name in qualified name");
                        }
                    }
                }

                // TODO: if scope already contains a type for last name
                // then it probably means that the currect type is just
                // a declaration and here we've a definition.
                // So we should make the link between them here.
                let mut sc = scope.borrow_mut();
                let ns = Rc::new(RefCell::new(Scope::new(kind)));
                sc.scopes.insert(last.as_ref().to_string(), Rc::clone(&ns));
                self.stack.push(ns);
            }
        } else {
            let ns = Rc::new(RefCell::new(Scope::default()));
            self.stack.push(ns);
        }
    }

    pub fn set_current_ns(&mut self, names: &NsNames) {
        let mut scope = Rc::clone(self.stack.last().unwrap());
        for name in names {
            let ns = {
                let mut sc = scope.borrow_mut();
                if let Some(s) = sc.scopes.get(name.as_ref()) {
                    self.stack.push(Rc::clone(s));
                    Rc::clone(s)
                } else {
                    let ns = Rc::new(RefCell::new(Scope::default()));
                    sc.scopes.insert(name.as_ref().to_string(), Rc::clone(&ns));
                    self.stack.push(Rc::clone(&ns));
                    ns
                }
            };
            if name.inline {
                scope.borrow_mut().using.push(Rc::clone(&ns));
            }
            scope = ns;
        }
    }

    pub fn pop(&mut self) -> Option<TypeToFix> {
        self.pop_n(1)
    }

    pub fn pop_n(&mut self, n: usize) -> Option<TypeToFix> {
        let last = self.stack.pop().unwrap();
        if n > 1 {
            let new_size = self.stack.len() - n + 1;
            self.stack
                .resize_with(new_size, || Rc::new(RefCell::new(Scope::default())));
        }
        {
            let last = last.borrow();
            last.incomplete.as_ref().map(|x| x.clone())
        }
    }

    pub fn add_type_decl(&mut self, typ: Rc<TypeDeclarator>) {
        let names = typ.get_names();

        macro_rules! add {
            ( $field: ident, $kind: ident) => {{
                if let Some($field) = names.$field {
                    if let Some((last, names)) = $field.names.split_last() {
                        let scope = Rc::clone(self.stack.last().unwrap());
                        let scope = scope.search_scope(&names);
                        scope
                            .borrow_mut()
                            .decls
                            .insert(last.clone(), Kind::$kind(Rc::clone(&typ)));
                    }
                }
            }};
        }

        // const int x => add x as variable
        add!(var, Var);
        // class A ... => add A as type
        add!(typ, Type);
        // typedef int x => add x as type
        add!(typd, Type);
    }

    pub fn add_alias(&mut self, name: &str, typ: Rc<TypeDeclarator>) {
        let scope = Rc::clone(self.stack.last().unwrap());
        let name = Name::Identifier(Identifier {
            val: name.to_string(),
        });
        scope.borrow_mut().decls.insert(name, Kind::Type(typ));
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::lexer::preprocessor::context::DefaultContext;
    use crate::lexer::Lexer;
    use crate::parser::declarations::DeclarationListParser;
    use crate::parser::types::{BaseType, UDType};

    #[test]
    fn test_context_typedef_basic() {
        let mut l = Lexer::<DefaultContext>::new(b"typedef int x;");
        let p = DeclarationListParser::new(&mut l);
        let mut context = Context::default();
        p.parse(None, &mut context);

        assert_eq!(context.stack.len(), 1);
        assert!(context.search(Some(&mk_id!("x"))).is_some());
    }

    #[test]
    fn test_context_typedef_qual() {
        let mut l = Lexer::<DefaultContext>::new(b"namespace A { namespace B { typedef int C; } }");
        let p = DeclarationListParser::new(&mut l);
        let mut context = Context::default();
        p.parse(None, &mut context);

        assert_eq!(context.stack.len(), 1);
        assert!(context.search(Some(&mk_id!("A", "B", "C"))).is_some());
    }

    #[test]
    fn test_context_inline_typedef_qual() {
        let mut l =
            Lexer::<DefaultContext>::new(b"namespace A { inline namespace B { typedef int C; } }");
        let p = DeclarationListParser::new(&mut l);
        let mut context = Context::default();
        p.parse(None, &mut context);

        assert_eq!(context.stack.len(), 1);
        assert!(context.search(Some(&mk_id!("A", "C"))).is_some());
    }

    #[test]
    fn test_context_inline_typedef_qual_2() {
        let mut l = Lexer::<DefaultContext>::new(b"namespace A::inline B::C { typedef int D; } }");
        let p = DeclarationListParser::new(&mut l);
        let mut context = Context::default();
        p.parse(None, &mut context);

        assert_eq!(context.stack.len(), 1);
        assert!(context.search(Some(&mk_id!("A", "C", "D"))).is_some());
        assert!(context.search(Some(&mk_id!("A", "B", "C", "D"))).is_some());
        assert!(context.search(Some(&mk_id!("A", "foo"))).is_none());
    }

    #[test]
    fn test_context_class() {
        let mut l = Lexer::<DefaultContext>::new(
            br#"
namespace A {}
class A::B;

namespace A::C {
    struct D { };
}
"#,
        );
        let p = DeclarationListParser::new(&mut l);
        let mut context = Context::default();
        p.parse(None, &mut context);

        assert_eq!(context.stack.len(), 1);
        assert!(context.search(Some(&mk_id!("A", "B"))).is_some());
        assert!(context.search(Some(&mk_id!("A", "C", "D"))).is_some());
    }

    #[test]
    fn test_context_self_ref() {
        let mut l = Lexer::<DefaultContext>::new(
            br#"
struct A {
    A * x;
    struct B {
        A * y;
        B * z;
    };
    B * t;
};
"#,
        );
        let p = DeclarationListParser::new(&mut l);
        let mut context = Context::default();
        p.parse(None, &mut context);

        assert_eq!(context.stack.len(), 1);
        assert!(context.search(Some(&mk_id!("A", "B", "x"))).is_none());
        assert!(context.search(Some(&mk_id!("A", "x"))).is_some());
        assert!(context.search(Some(&mk_id!("A", "B", "y"))).is_some());
        assert!(context.search(Some(&mk_id!("A", "B", "z"))).is_some());
        assert!(context.search(Some(&mk_id!("A", "t"))).is_some());
        assert!(context.search(Some(&mk_id!("A", "B"))).is_some());

        // check types
        let a = match context.search(Some(&mk_id!("A"))).unwrap() {
            SearchResult::Type(ty) => ty,
            _ => unreachable!(""),
        };

        let x = match context.search(Some(&mk_id!("A", "x"))).unwrap() {
            SearchResult::Var(var) => var,
            _ => unreachable!(""),
        };

        assert_eq!(x.identifier.identifier, Some(mk_id!("x")));

        let x = match &x.typ.base {
            BaseType::UD(ud) => {
                if let UDType::Indirect(ind) = &ud.typ {
                    ind.get_type()
                } else {
                    None
                }
            }
            _ => None,
        };

        assert!(x.is_some());
        let x = x.unwrap();

        assert!(Rc::ptr_eq(&x, &a));
    }
}
