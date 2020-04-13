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
