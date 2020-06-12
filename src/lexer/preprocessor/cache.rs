// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use hashbrown::HashMap;
use std::sync::Mutex;

use crate::lexer::buffer::Position;
use crate::lexer::source::FileId;

#[derive(Debug, PartialEq, Hash)]
struct Key {
    file_id: FileId,
    pos: usize,
}

impl Eq for Key {}

#[derive(Debug, Default)]
pub struct IfCache {
    cache: Mutex<HashMap<Key, Position>>,
}

impl IfCache {
    pub fn get_next(&self, file_id: FileId, pos: usize) -> Option<Position> {
        let cache = self.cache.lock().unwrap();
        cache.get(&Key { file_id, pos }).map(|v| v.clone())
    }

    pub fn save_next(&self, file_id: FileId, pos: usize, next: Position) {
        let mut cache = self.cache.lock().unwrap();
        cache.insert(Key { file_id, pos }, next);
    }
}
