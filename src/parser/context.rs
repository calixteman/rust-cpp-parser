use hashbrown::{hash_map, HashMap};

#[derive(Clone, Debug)]
struct Container {
    sub: HashMap<String, Container>,
}

#[derive(Clone, Debug)]
pub struct Context {
    root: Containter,
}
