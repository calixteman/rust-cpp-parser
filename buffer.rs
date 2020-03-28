struct BufferData<'a> {
    buf: &'a [u8],
    pos: usize,
    line: usize,
    lpos: usize,
}

pub(crate) struct Buffer<'a> {
    stack: Vec<BufferData<'a>>,
    preproc: Vec<u8>,
    current: &'a [u8],
    pos: usize,
    len: usize,
    line: usize,
    lpos: usize,
}

impl<'a> Buffer<'a> {
    pub(crate) fn new(buf: &'a [u8]) -> Self {
        Self {
            stack: Vec::new(),
            preproc: Vec::new(),
            current: buf,
            pos: 0,
            len: buf.len(),
            line: 1,
            lpos: 0,
        }
    }

    pub(crate) fn switch_to_preproc(&mut self) {
        if self.preproc.is_empty() {
            return;
        }

        self.stack.push(BufferData {
            buf: self.current,
            pos: self.pos,
            line: self.line,
            lpos: self.lpos,
        });

        self.current = unsafe { &*std::mem::transmute::<&[u8], *const [u8]>(&self.preproc) };
        self.pos = 0;
        self.len = self.preproc.len();
    }

    #[inline(always)]
    pub(crate) fn preproc_use(&self) -> bool {
        !self.preproc.is_empty()
    }

    pub(crate) fn add_buffer(&mut self, buf: &'a [u8]) {
        self.stack.push(BufferData {
            buf: self.current,
            pos: self.pos,
            line: self.line,
            lpos: self.lpos,
        });

        self.current = buf;
        self.pos = 0;
        self.len = buf.len();
        self.line = 1;
        self.lpos = 0;
    }

    pub(crate) fn rm_buffer(&mut self) -> bool {
        self.preproc.clear();
        while let Some(data) = self.stack.pop() {
            if data.pos < data.buf.len() {
                self.current = data.buf;
                self.pos = data.pos;
                self.len = self.current.len();
                self.line = data.line;
                self.lpos = data.lpos;
                return true;
            }
        }
        false
    }

    pub(crate) fn add_new_line(&mut self) {
        self.line += 1;
        self.lpos = self.pos + 1;
    }
    
    pub(crate) fn get_line(&self) -> usize {
        self.line
    }
    
    pub(crate) fn get_column(&self) -> usize {
        self.pos - self.lpos + 1
    }

    pub(crate) fn reset(&mut self) {
        self.pos = 0;
    }

    #[inline(always)]
    pub(crate) fn pos(&self) -> usize {
        self.pos
    }

    #[inline(always)]
    pub(crate) fn set_pos(&mut self, pos: usize) {
        self.pos = pos;
    }

    #[inline(always)]
    pub(crate) fn rem(&self) -> usize {
        self.len - self.pos
    }

    #[inline(always)]
    pub(crate) fn get_preproc_buf(&mut self) -> &mut Vec<u8> {
        &mut self.preproc
    }
    
    #[inline(always)]
    pub(crate) fn slice(&self, start: usize) -> &'a [u8] {
        unsafe { self.current.get_unchecked(start..self.pos) }
    }
    
    #[inline(always)]
    pub(crate) fn slice_p(&self, start: usize, end: usize) -> &'a [u8] {
        unsafe { self.current.get_unchecked(start..end) }
    }

    #[inline(always)]
    pub(crate) fn slice_m_n(&self, start: usize, n: usize) -> &'a [u8] {
        unsafe { self.current.get_unchecked(start..self.pos - n) }
    }

    #[inline(always)]
    pub(crate) fn slice_n(&self, start: usize, n: usize) -> &'a [u8] {
        unsafe { self.current.get_unchecked(start..self.pos + n) }
    }
    
    #[inline(always)]
    pub(crate) fn next_char(&self) -> u8 {
        unsafe { *self.current.get_unchecked(self.pos) }
    }

    #[inline(always)]
    pub(crate) fn next_char_n(&self, n: usize) -> u8 {
        unsafe { *self.current.get_unchecked(self.pos + n) }
    }

    #[inline(always)]
    pub(crate) fn prev_char(&self) -> u8 {
        unsafe { *self.current.get_unchecked(self.pos - 1) }
    }

    #[inline(always)]
    pub(crate) fn prev_char_n(&self, n: usize) -> u8 {
        unsafe { *self.current.get_unchecked(self.pos - n) }
    }

    #[inline(always)]
    pub(crate) fn inc(&mut self) {
        self.pos += 1;
    }

    #[inline(always)]
    pub(crate) fn dec(&mut self) {
        self.pos -= 1;
    }
    
    #[inline(always)]
    pub(crate) fn inc_n(&mut self, n: usize) {
        self.pos += n;
    }

    #[inline(always)]
    pub(crate) fn dec_n(&mut self, n: usize) {
        self.pos -= n;
    }

    #[inline(always)]
    pub(crate) fn check_char(&mut self) -> bool {
        if self.pos < self.len {
            true
        } else {
            self.rm_buffer()
        }
    }

    #[inline(always)]
    pub(crate) fn has_char(&mut self) -> bool {
        self.pos < self.len
    }

    #[inline(always)]
    pub(crate) fn has_char_n(&mut self, n: usize) -> bool {
        self.pos + n < self.len
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn test_basic() {
        let mut buf = Buffer::new(b"abc");
        assert_eq!(buf.next_char(), b'a');
        buf.inc();
        
        buf.preproc.extend_from_slice(b"def");
        buf.switch_to_preproc();

        assert_eq!(buf.next_char(), b'd');
        buf.rm_buffer();
        assert_eq!(buf.next_char(), b'b');
        buf.inc();
        
        buf.add_buffer(b"ghi");
        assert_eq!(buf.next_char(), b'g');
        buf.rm_buffer();

        assert_eq!(buf.next_char(), b'c');
    }

}
