#[derive(Clone, Copy, Debug, PartialEq)]
enum TypeKind {
    Primitive,
    Struct,
    Class,
    Union,
    Pointer,
    Reference,
    RValue,
}

trait Type {
    fn get_kind(&self) -> TypeKind;
    fn is_const(&self) -> bool;
    fn get_primitive(&self) -> Option<Primitive> {
        None
    }

    fn get_members(&self) -> Option<&[(String, Box<dyn Type>)]> {
        None
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
enum Primitive {
    Void,
    Char,
    I8,
    U8,
    I16,
    U16,
    I32,
    U32,
    I64,
    U64,
    F16,
    F32,
    F64,
}

struct PrimitiveType {
    base: Primitive,
    is_const: bool,
}

impl PrimitiveType {
    fn new(base: Primitive, is_const: bool) -> Self {
        Self {
            base,
            is_const,
        }
    }
}

impl Type for PrimitiveType {
    fn get_kind(&self) -> TypeKind {
        TypeKind::Primitive
    }

    fn get_primitive(&self) -> Option<Primitive> {
        Some(self.base)
    }

    fn is_const(&self) -> bool {
        self.is_const
    }
}

struct PointerType {
    base: Box<dyn Type>,
    is_const: bool,
}

impl Type for PointerType {
    fn get_kind(&self) -> TypeKind {
        TypeKind::Pointer
    }

    fn is_const(&self) -> bool {
        self.is_const
    }
}

struct StructureType {
    members: Vec<(String, Box<dyn Type>)>,
    is_const: bool,
}

impl Type for StructureType {
    fn get_kind(&self) -> TypeKind {
        TypeKind::Struct
    }

    fn is_const(&self) -> bool {
        self.is_const
    }

    fn get_members(&self) -> Option<&[(String, Box<dyn Type>)]> {
        Some(&self.members)
    }
}
