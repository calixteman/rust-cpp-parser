#[derive(Clone, Debug, PartialEq)]
pub enum IntLiteral {
    Int(u64),
    UInt(u64),
    Long(u64),
    ULong(u64),
    LongLong(u64),
    ULongLong(u64),
}

#[derive(Clone, Debug, PartialEq)]
pub struct Integer {
    pub value: IntLiteral,
}

#[derive(Clone, Debug, PartialEq)]
pub enum FloatLiteral {
    Float(f64),
    Double(f64),
    LongDouble(f64),
}

#[derive(Clone, Debug, PartialEq)]
pub struct Float {
    pub value: FloatLiteral,
}

#[derive(Clone, Debug, PartialEq)]
pub enum CharLiteral {
    Char(u32),
    LChar(u32),
    UChar(u32),
    UUChar(u32),
    U8Char(u32),
}

#[derive(Clone, Debug, PartialEq)]
pub struct Char {
    pub value: CharLiteral,
}

#[derive(Clone, Debug, PartialEq)]
pub enum StrLiteral {
    Str(String),
    LStr(String),
    UStr(String),
    UUStr(String),
    U8Str(String),
    RStr(String),
    LRStr(String),
    URStr(String),
    UURStr(String),
    U8RStr(String),
}

#[derive(Clone, Debug, PartialEq)]
pub struct Str {
    pub value: StrLiteral,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Bool {
    pub value: bool,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Nullptr {}
