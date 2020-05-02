// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use hashbrown::{hash_map, HashMap};

pub enum Kind {
    Namespace,
    Struct,
    Class,
    Enum,
}

#[derive(Clone, Debug, Default)]
pub struct Container {
    kind: Kind,
    sub: HashMap<String, Rc<Container>>,
    values: HashMap<String, &Node>,
}

#[derive(Clone, Debug, Default)]
pub struct Context {
    root: Containter,
    current: Rc<Container>,
}

impl Container {
    fn search(name: &Name) -> Option<&Node> {
        
    }
}
