// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use super::preprocessor::include::PathIndex;
use super::source::FileId;

#[derive(Debug, Clone)]
struct Position {
    pos: usize,
    line: u32,
    lpos: usize,
}

impl Default for Position {
    fn default() -> Self {
        Self {
            pos: 0,
            line: 1,
            lpos: 0,
        }
    }
}

#[derive(Debug)]
pub struct BufferData {
    buf: Vec<u8>,
    position: Position,
    source_id: FileId,
    path_index: PathIndex,
    fake_source_id: Option<FileId>,
}

impl BufferData {
    pub fn new(buf: Vec<u8>, source_id: FileId, path_index: PathIndex) -> Self {
        Self {
            buf,
            position: Position::default(),
            source_id,
            path_index,
            fake_source_id: None,
        }
    }
}

#[derive(Clone, Debug, Default)]
pub struct FileInfo {
    pub line: u32,
    pub source_id: Option<FileId>,
}

#[derive(Debug)]
pub(crate) struct Buffer<'a> {
    stack: Vec<BufferData>,
    preproc: Vec<u8>,
    current: &'a [u8],
    len: usize,
    position: Position,
    saved_position: Position,
    saved_buf: &'a [u8],
}

impl<'a> Buffer<'a> {
    pub(crate) fn new(buf: Vec<u8>, source_id: FileId, path_index: PathIndex) -> Self {
        let mut ret = Self {
            stack: Vec::new(),
            preproc: Vec::new(),
            current: &[],
            len: buf.len(),
            position: Position::default(),
            saved_position: Position::default(),
            saved_buf: &[],
        };
        ret.stack.push(BufferData {
            buf,
            position: Position::default(),
            source_id,
            fake_source_id: None,
            path_index,
        });
        ret.current =
            unsafe { &*std::mem::transmute::<&[u8], *const [u8]>(&ret.stack.last().unwrap().buf) };
        ret
    }

    pub(crate) fn switch_to_preproc(&mut self) {
        if self.preproc.is_empty() {
            return;
        }

        self.saved_position = self.position.clone();
        self.saved_buf = self.current;
        self.current = unsafe { &*std::mem::transmute::<&[u8], *const [u8]>(&self.preproc) };
        self.position = Position::default();
        self.len = self.preproc.len();
    }

    #[inline(always)]
    pub(crate) fn preproc_use(&self) -> bool {
        !self.preproc.is_empty()
    }

    #[inline(always)]
    pub(crate) fn get_line_file(&self) -> FileInfo {
        FileInfo {
            line: self.get_line(),
            source_id: self.get_source_id(),
        }
    }

    pub(crate) fn add_buffer(&mut self, buf: BufferData) {
        let last = self.stack.last_mut().unwrap();
        last.position = self.position.clone();

        self.stack.push(buf);
        let last = self.stack.last().unwrap();
        self.current = unsafe { &*std::mem::transmute::<&[u8], *const [u8]>(&last.buf) };
        self.position = Position::default();
        self.len = self.current.len()
    }

    pub(crate) fn rm_buffer(&mut self) -> bool {
        if self.preproc_use() {
            self.current = self.saved_buf;
            self.len = self.current.len();
            self.position = self.saved_position.clone();
            self.preproc.clear();
            return true;
        }

        if self.stack.pop().is_none() {
            // the stack is empty
            return false;
        }

        while let Some(data) = self.stack.last() {
            if data.position.pos < data.buf.len() {
                self.current = unsafe { &*std::mem::transmute::<&[u8], *const [u8]>(&data.buf) };
                self.len = self.current.len();
                self.position = data.position.clone();
                return true;
            }
            self.stack.pop();
        }

        !self.stack.is_empty()
    }

    pub(crate) fn add_new_line(&mut self) {
        self.position.line += 1;
        self.position.lpos = self.position.pos + 1;
    }

    pub(crate) fn get_line(&self) -> u32 {
        self.position.line
    }

    pub(crate) fn set_line(&mut self, line: u32) {
        self.position.line = line;
    }

    pub(crate) fn get_source_id(&self) -> Option<FileId> {
        self.stack
            .last()
            .map(|last| last.fake_source_id.unwrap_or(last.source_id))
    }

    pub(crate) fn get_path_index(&self) -> Option<PathIndex> {
        self.stack.last().map(|last| last.path_index)
    }

    pub(crate) fn set_source_id(&mut self, id: FileId) {
        let last = self.stack.last_mut().unwrap();
        last.fake_source_id = Some(id);
    }

    pub(crate) fn get_column(&self) -> u32 {
        ((self.position.pos + 1) - self.position.lpos) as u32
    }

    pub(crate) fn reset(&mut self) {
        self.position.pos = 0;
    }

    #[inline(always)]
    pub(crate) fn pos(&self) -> usize {
        self.position.pos
    }

    #[inline(always)]
    pub(crate) fn set_pos(&mut self, pos: usize) {
        self.position.pos = pos;
    }

    #[inline(always)]
    pub(crate) fn rem(&self) -> usize {
        self.len - self.position.pos
    }

    #[inline(always)]
    pub(crate) fn get_preproc_buf(&mut self) -> &mut Vec<u8> {
        &mut self.preproc
    }

    #[inline(always)]
    pub(crate) fn slice(&self, start: usize) -> &'a [u8] {
        unsafe { self.current.get_unchecked(start..self.position.pos) }
    }

    #[inline(always)]
    pub(crate) fn slice_p(&self, start: usize, end: usize) -> &'a [u8] {
        unsafe { self.current.get_unchecked(start..end) }
    }

    #[inline(always)]
    pub(crate) fn slice_m_n(&self, start: usize, n: usize) -> &'a [u8] {
        unsafe { self.current.get_unchecked(start..self.position.pos - n) }
    }

    #[inline(always)]
    pub(crate) fn slice_n(&self, start: usize, n: usize) -> &'a [u8] {
        unsafe { self.current.get_unchecked(start..self.position.pos + n) }
    }

    #[inline(always)]
    pub(crate) fn next_char(&self) -> u8 {
        unsafe { *self.current.get_unchecked(self.position.pos) }
    }

    #[inline(always)]
    pub(crate) fn next_char_n(&self, n: usize) -> u8 {
        unsafe { *self.current.get_unchecked(self.position.pos + n) }
    }

    #[inline(always)]
    pub(crate) fn prev_char(&self) -> u8 {
        unsafe { *self.current.get_unchecked(self.position.pos - 1) }
    }

    #[inline(always)]
    pub(crate) fn prev_char_n(&self, n: usize) -> u8 {
        unsafe { *self.current.get_unchecked(self.position.pos - n) }
    }

    #[inline(always)]
    pub(crate) fn inc(&mut self) {
        self.position.pos += 1;
    }

    #[inline(always)]
    pub(crate) fn dec(&mut self) {
        self.position.pos -= 1;
    }

    #[inline(always)]
    pub(crate) fn inc_n(&mut self, n: usize) {
        self.position.pos += n;
    }

    #[inline(always)]
    pub(crate) fn dec_n(&mut self, n: usize) {
        self.position.pos -= n;
    }

    #[inline(always)]
    pub(crate) fn check_char(&mut self) -> bool {
        if self.position.pos < self.len {
            true
        } else {
            self.rm_buffer()
        }
    }

    #[inline(always)]
    pub(crate) fn has_char(&mut self) -> bool {
        self.position.pos < self.len
    }

    #[inline(always)]
    pub(crate) fn has_char_n(&mut self, n: usize) -> bool {
        self.position.pos + n < self.len
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn test_buffer() {
        let mut buf = Buffer::new(b"abc".to_vec(), FileId(0), PathIndex(0));
        assert_eq!(buf.next_char(), b'a');
        buf.inc();

        buf.preproc.extend_from_slice(b"def");
        buf.switch_to_preproc();

        assert_eq!(buf.next_char(), b'd');
        buf.rm_buffer();
        assert_eq!(buf.next_char(), b'b');
        buf.inc();

        buf.add_buffer(BufferData::new(b"ghi".to_vec(), FileId(0), PathIndex(0)));
        assert_eq!(buf.next_char(), b'g');
        buf.rm_buffer();

        assert_eq!(buf.next_char(), b'c');
    }
}
