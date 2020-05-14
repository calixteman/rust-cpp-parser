// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use hashbrown::HashMap;
use std::cell::RefCell;
use std::rc::Rc;

use crate::parser::declarations::TypeDeclarator;
use crate::parser::names::name::{self, Name, Qualified};

#[derive(Clone, Debug, Default)]
pub struct NamedScope {
    types: HashMap<Name, Rc<TypeDeclarator>>,
    scopes: HashMap<String, Rc<RefCell<NamedScope>>>,
}

#[derive(Clone, Debug, Default)]
pub struct Scope {
    types: HashMap<String, Rc<TypeDeclarator>>,
    scopes: Vec<Scope>,
}

#[derive(Clone, Debug)]
pub struct Context {
    root: Rc<RefCell<NamedScope>>,
    local: Scope,
    stack: Vec<Rc<RefCell<NamedScope>>>,
    using: Vec<Rc<RefCell<NamedScope>>>,
}

impl Default for Context {
    fn default() -> Self {
        let root = Rc::new(RefCell::new(NamedScope::default()));
        Self {
            root: Rc::clone(&root),
            local: Scope::default(),
            stack: vec![root],
            using: Vec::new(),
        }
    }
}

impl NamedScope {
    fn search_type(&self, names: &[Name]) -> Option<Rc<TypeDeclarator>> {
        if names.len() == 1 {
            self.types.get(&names[0]).map(Rc::clone)
        } else if let Name::Identifier(name::Identifier { val }) = &names[0] {
            if let Some(s) = self.scopes.get(val) {
                s.borrow().search_type(&names[1..])
            } else {
                None
            }
        } else {
            unreachable!("Invalid name in qualified name: {:?}", names[0])
        }
    }

    fn search_scope(&self, names: &[Name]) -> Option<Rc<RefCell<NamedScope>>> {
        if let Name::Identifier(name::Identifier { val }) = &names[0] {
            if let Some(s) = self.scopes.get(val) {
                s.borrow().search_scope(&names[1..])
            } else {
                None
            }
        } else {
            unreachable!("Invalid name in qualified name: {:?}", names[0])
        }
    }
}

impl Context {
    pub fn search_type(&self, name: &Qualified) -> Option<Rc<TypeDeclarator>> {
        if let Name::Empty = name.names[0] {
            self.root.borrow().search_type(&name.names[1..])
        } else {
            self.stack.last().unwrap().borrow().search_type(&name.names)
        }
    }

    pub fn set_current(&mut self, name: &Qualified) {
        let last = self.stack.last().unwrap();
        let scope = if let Some(scope) = last.borrow().search_scope(&name.names) {
            scope
        } else {
            Rc::new(RefCell::new(NamedScope::default()))
        };
        self.stack.push(scope);
    }

    pub fn add_type(&mut self, typ: Rc<TypeDeclarator>) {
        if let Some(name) = &typ.identifier.identifier {
            let last = self.stack.last_mut().unwrap();
            let type_name = name.names.last().unwrap();
            if name.names.len() == 1 {
                last.borrow_mut().types.insert(type_name.clone(), typ);
            } else if let Some(scope) = last
                .borrow()
                .search_scope(&name.names[0..name.names.len() - 1])
            {
                scope.borrow_mut().types.insert(type_name.clone(), typ);
            } else {
                unreachable!("Invalid type name: {}", name.to_string());
            }
        } else {
            match typ.typ.base {}
        }
    }
}
