// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use hashbrown::HashMap;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use super::cache::IfCache;
use super::include::{DefaultIncludeLocator, IncludeLocator, PathIndex};
use super::macros::{
    Macro, MacroCounter, MacroFile, MacroFunction, MacroLine, MacroObject, MacroType,
};
use crate::lexer::buffer::{BufferData, Position};
use crate::lexer::source::{FileId, SourceMutex};

/// Indicate the state of the if statement
/// Eval: indicates that we're evaluating the tokens
/// Skip: indicates that we're skipping everything until the corresponding endif
/// SkipAndSwitch: indicates that we're skipping until the else (if one)
#[derive(Clone, Debug, PartialEq)]
pub enum IfState {
    Eval(usize),
    Skip(usize),
    SkipAndSwitch(usize),
}

pub trait PreprocContext: Default + IncludeLocator {
    /// Set the if state
    fn add_if(&mut self, state: IfState);

    /// Call on endif
    fn rm_if(&mut self);

    /// Get the current if state
    fn if_state(&self) -> Option<&IfState>;

    /// Change the state
    /// For example if we're in SkipAndSwitch state then switch to Eval on else
    fn if_change(&mut self, state: IfState);

    /// Add a macro function: #define foo(a, b)...
    fn add_function(&mut self, name: String, mac: MacroFunction);

    /// Add a macro object: #define foo ...
    fn add_object(&mut self, name: String, mac: MacroObject);

    /// Remove a macro
    /// Called on undef
    fn undef(&mut self, name: &str);

    /// Check if a macro is defined (used in condition with function defined())
    fn defined(&mut self, name: &str) -> bool;

    /// Get a macro (if one) with the given name
    fn get(&self, name: &str) -> Option<&Macro>;

    /// Get MacroType
    fn get_type(&self, name: &str) -> MacroType;

    /// The first time the file is preprocessed, we can save the positions of
    /// #if, #else, #elif and #endif.
    /// And when the file is read a second time then it's possible to directly
    /// jump to the matching preproc element according to the condition
    fn skip_until_next(&self, file: FileId, pos: usize) -> Option<Position>;

    /// Save the position of matching #if/#else|#endif
    fn save_switch(&self, file: FileId, pos: usize, next: Position);

    fn new_with_if_cache(if_cache: Arc<IfCache>) -> Self;
}

#[derive(Default)]
pub struct EmptyContext {}

impl PreprocContext for EmptyContext {
    fn add_if(&mut self, _state: IfState) {}
    fn rm_if(&mut self) {}

    fn if_state(&self) -> Option<&IfState> {
        None
    }

    fn if_change(&mut self, _state: IfState) {}

    fn add_function(&mut self, _name: String, _mac: MacroFunction) {}

    fn add_object(&mut self, _name: String, _mac: MacroObject) {}

    fn undef(&mut self, _name: &str) {}

    fn defined(&mut self, _name: &str) -> bool {
        false
    }

    fn get(&self, _name: &str) -> Option<&Macro> {
        None
    }

    fn get_type(&self, _name: &str) -> MacroType {
        MacroType::None
    }

    fn skip_until_next(&self, _file: FileId, _pos: usize) -> Option<Position> {
        None
    }

    fn save_switch(&self, _file: FileId, _pos: usize, _next: Position) {}

    fn new_with_if_cache(_if_cache: Arc<IfCache>) -> Self {
        Self {}
    }
}

impl IncludeLocator for EmptyContext {
    fn find(
        &mut self,
        _angle: bool,
        _path: &str,
        _next: bool,
        _current: FileId,
        _path_index: PathIndex,
    ) -> Option<BufferData> {
        None
    }

    fn get_id(&mut self, _path: &PathBuf) -> FileId {
        FileId(0)
    }

    fn get_path(&self, _id: FileId) -> PathBuf {
        PathBuf::from("")
    }

    fn set_source(&mut self, _source: SourceMutex) {}

    fn set_sys_paths<P: AsRef<Path>>(&mut self, _paths: &[P]) {}
}

#[derive(Clone, Debug, PartialEq)]
pub enum IfKind {
    If,
    Ifdef,
    Ifndef,
}

#[derive(Clone, Debug)]
pub struct Context<IL: IncludeLocator> {
    macros: HashMap<String, Macro>,
    if_stack: Vec<IfState>,
    if_cache: Arc<IfCache>,
    include: IL,
    buffer: Option<()>,
}

pub type DefaultContext = Context<DefaultIncludeLocator>;

impl<IL: IncludeLocator> Default for Context<IL> {
    fn default() -> Self {
        Self {
            macros: {
                let mut map = HashMap::default();
                map.insert("__LINE__".to_string(), Macro::Line(MacroLine::new()));
                map.insert("__FILE__".to_string(), Macro::File(MacroFile::new()));
                map.insert(
                    "__COUNTER__".to_string(),
                    Macro::Counter(MacroCounter::new()),
                );
                map
            },
            if_stack: Vec::new(),
            if_cache: Arc::new(IfCache::default()),
            include: IL::default(),
            buffer: None,
        }
    }
}

impl<IL: IncludeLocator> Context<IL> {
    pub fn new(include: IL) -> Self {
        Self {
            macros: HashMap::default(),
            if_stack: Vec::new(),
            if_cache: Arc::new(IfCache::default()),
            include,
            buffer: None,
        }
    }
}

impl<IL: IncludeLocator> PreprocContext for Context<IL> {
    fn add_if(&mut self, state: IfState) {
        self.if_stack.push(state);
    }

    fn rm_if(&mut self) {
        self.if_stack.pop();
    }

    fn if_state(&self) -> Option<&IfState> {
        self.if_stack.last()
    }

    fn if_change(&mut self, state: IfState) {
        *self.if_stack.last_mut().unwrap() = state;
    }

    fn add_function(&mut self, name: String, mac: MacroFunction) {
        self.macros.insert(name, Macro::Function(mac));
    }

    fn add_object(&mut self, name: String, mac: MacroObject) {
        self.macros.insert(name, Macro::Object(mac));
    }

    fn undef(&mut self, name: &str) {
        self.macros.remove(name);
    }

    fn defined(&mut self, name: &str) -> bool {
        self.macros.contains_key(name)
    }

    fn get(&self, name: &str) -> Option<&Macro> {
        if let Some(mac) = self.macros.get(name) {
            match mac {
                Macro::Object(m) => {
                    if m.in_use.get() {
                        None
                    } else {
                        Some(mac)
                    }
                }
                Macro::Function(m) => {
                    if m.in_use.get() {
                        None
                    } else {
                        Some(mac)
                    }
                }
                Macro::Line(_) | Macro::File(_) | Macro::Counter(_) => Some(mac),
            }
        } else {
            None
        }
    }

    fn get_type(&self, name: &str) -> MacroType {
        if let Some(mac) = self.get(name) {
            match mac {
                Macro::Object(mac) => MacroType::Object(&mac),
                Macro::Function(mac) => MacroType::Function((mac.len(), mac.va_args)),
                Macro::Line(mac) => MacroType::Line(*mac),
                Macro::File(mac) => MacroType::File(*mac),
                Macro::Counter(mac) => MacroType::Counter(mac),
            }
        } else {
            MacroType::None
        }
    }

    fn skip_until_next(&self, file: FileId, pos: usize) -> Option<Position> {
        self.if_cache.get_next(file, pos)
    }

    fn save_switch(&self, file: FileId, pos: usize, next: Position) {
        self.if_cache.save_next(file, pos, next);
    }

    fn new_with_if_cache(if_cache: Arc<IfCache>) -> Self {
        Self {
            macros: HashMap::default(),
            if_stack: Vec::new(),
            if_cache,
            include: IL::default(),
            buffer: None,
        }
    }
}

impl<IL: IncludeLocator> IncludeLocator for Context<IL> {
    fn find(
        &mut self,
        angle: bool,
        path: &str,
        next: bool,
        current: FileId,
        path_index: PathIndex,
    ) -> Option<BufferData> {
        self.include.find(angle, path, next, current, path_index)
    }

    fn get_id(&mut self, path: &PathBuf) -> FileId {
        self.include.get_id(path)
    }

    fn get_path(&self, id: FileId) -> PathBuf {
        self.include.get_path(id)
    }

    fn set_source(&mut self, source: SourceMutex) {
        self.include.set_source(source);
    }

    fn set_sys_paths<P: AsRef<Path>>(&mut self, paths: &[P]) {
        self.include.set_sys_paths(paths);
    }
}
