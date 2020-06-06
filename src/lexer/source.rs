// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use std::path::PathBuf;
use std::sync::{Arc, Mutex};

use hashbrown::{hash_map, HashMap};

#[derive(Debug, Clone, Copy, Default, Hash, PartialEq)]
pub struct FileId(pub u32);

#[derive(Debug)]
pub struct SourceLocator {
    file2id: HashMap<PathBuf, FileId>,
    id2file: Vec<PathBuf>,
}

impl Default for SourceLocator {
    fn default() -> Self {
        Self {
            file2id: {
                let mut map = HashMap::default();
                map.insert(PathBuf::from(""), FileId(0));
                map
            },
            id2file: vec![PathBuf::from("")],
        }
    }
}

pub type SourceMutex = Arc<Mutex<SourceLocator>>;

pub fn get_source_mutex() -> SourceMutex {
    Arc::new(Mutex::new(SourceLocator::default()))
}

impl SourceLocator {
    pub fn get_id(&mut self, path: &PathBuf) -> FileId {
        match self.file2id.entry(path.clone()) {
            hash_map::Entry::Occupied(e) => *e.get(),
            hash_map::Entry::Vacant(p) => {
                let id = FileId(self.id2file.len() as u32);
                p.insert(id);
                self.id2file.push(path.clone());
                id
            }
        }
    }

    pub fn get_path(&self, id: FileId) -> PathBuf {
        unsafe { self.id2file.get_unchecked(id.0 as usize).clone() }
    }
}
