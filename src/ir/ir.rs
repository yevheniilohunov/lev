use std::{collections::HashSet, fmt};

use crate::semantic::symbols::{FunctionId, LocalId, StructId};

use crate::semantic::types::Type;

#[derive(Debug, Clone)]
pub struct IrProgram {
    pub structs: Vec<IrStruct>,
    pub functions: Vec<IrFunction>,
}

#[derive(Debug, Clone)]
pub struct IrStruct {
    pub id: StructId,
    pub name: String,
    pub base: Option<StructId>,
    pub fields: Vec<IrField>,
}

#[derive(Debug, Clone)]
pub struct IrField {
    pub name: String,
    pub ty: IrType,
}

#[derive(Debug, Clone, Default)]
pub struct IrFunction {
    pub id: Option<FunctionId>,
    pub name: String,
    pub owner: Option<StructId>,
    pub parameters: Vec<IrLocal>,
    pub locals: Vec<IrLocal>,
    pub return_type: IrType,
    pub entry: BlockId,
    pub blocks: Vec<BasicBlock>,
}

#[derive(Debug, Clone)]
pub struct IrLocal {
    pub id: LocalId,
    pub name: String,
    pub ty: IrType,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Ord, PartialOrd, Default)]
pub struct BlockId(pub usize);

#[derive(Debug, Clone)]
pub struct BasicBlock {
    pub id: BlockId,
    pub instructions: Vec<IrInstruction>,
    pub terminator: Terminator,
}

#[derive(Debug, Clone)]
pub enum IrInstruction {
    /// Initial SSA definition for a function parameter.
    Parameter {
        destination: ValueId,
        local: LocalId,
    },

    ConstInt {
        destination: ValueId,
        value: i64,
    },

    ConstString {
        destination: ValueId,
        value: String,
    },

    ConstBool {
        destination: ValueId,
        value: bool,
    },

    LoadLocal {
        destination: ValueId,
        local: LocalId,
    },

    Copy {
        destination: ValueId,
        source: ValueId,
    },

    StructCopy {
        destination: ValueId,
        source: ValueId,
        struct_id: StructId,
    },

    StoreLocal {
        local: LocalId,
        value: ValueId,
    },

    AllocStruct {
        destination: ValueId,
        struct_id: StructId,
    },

    StoreField {
        receiver: ValueId,
        field: usize,
        value: ValueId,
    },

    LoadField {
        destination: ValueId,
        receiver: ValueId,
        field: usize,
    },

    Binary {
        destination: ValueId,
        op: IrBinaryOp,
        left: ValueId,
        right: ValueId,
    },

    Call {
        destination: Option<ValueId>,
        function: FunctionId,
        arguments: Vec<ValueId>,
    },

    /// SSA phi node.
    ///
    /// Each incoming value corresponds to a predecessor block.
    Phi {
        destination: ValueId,
        local: LocalId,
        sources: Vec<(BlockId, ValueId)>,
    },
}

#[derive(Debug, Clone, PartialEq)]
pub enum Terminator {
    Jump(BlockId),

    Branch {
        condition: ValueId,
        then_block: BlockId,
        else_block: BlockId,
    },

    Return {
        value: Option<ValueId>,
    },

    Unreachable,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct ValueId(pub usize);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum IrBinaryOp {
    Add,
    Subtract,
    Multiply,
    Divide,
    Equal,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Default)]
pub enum IrType {
    #[default]
    None,
    Int,
    String,
    Bool,
    Void,
    Struct(StructId),
}

impl From<&Type> for IrType {
    fn from(ty: &Type) -> Self {
        match ty {
            Type::Int => Self::Int,
            Type::String => Self::String,
            Type::Bool => Self::Bool,
            Type::Void => Self::Void,
            Type::Struct(id) => Self::Struct(*id),
        }
    }
}

impl IrFunction {
    pub fn block(&self, id: BlockId) -> Option<&BasicBlock> {
        self.blocks.get(id.0)
    }

    pub fn successors(&self, block: BlockId) -> Vec<BlockId> {
        let Some(block) = self.block(block) else {
            return Vec::new();
        };

        match &block.terminator {
            Terminator::Jump(target) => vec![*target],

            Terminator::Branch {
                then_block,
                else_block,
                ..
            } => {
                if then_block == else_block {
                    vec![*then_block]
                } else {
                    vec![*then_block, *else_block]
                }
            }

            Terminator::Return { .. } | Terminator::Unreachable => Vec::new(),
        }
    }

    pub fn predecessors(&self, target: BlockId) -> Vec<BlockId> {
        let mut result = Vec::new();

        for block in &self.blocks {
            if self.successors(block.id).contains(&target) {
                result.push(block.id);
            }
        }

        result
    }

    pub fn reachable_blocks(&self) -> HashSet<BlockId> {
        let mut visited = HashSet::new();
        let mut worklist = vec![self.entry];

        while let Some(block) = worklist.pop() {
            if !visited.insert(block) {
                continue;
            }

            for successor in self.successors(block) {
                worklist.push(successor);
            }
        }

        visited
    }
}

impl fmt::Display for IrProgram {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for structure in &self.structs {
            writeln!(f, "struct #{} {} {{", structure.id.0, structure.name)?;

            if let Some(base) = structure.base {
                writeln!(f, "  extends: struct #{};", base.0)?;
            }

            for field in &structure.fields {
                writeln!(f, "  {}: {:?};", field.name, field.ty)?;
            }

            writeln!(f, "}}")?;
        }

        for function in &self.functions {
            match function.owner {
                Some(owner) => {
                    writeln!(
                        f,
                        "fn #{} {}::{}: {:?} {{",
                        function.id.unwrap().0,
                        owner.0,
                        function.name,
                        function.return_type
                    )?;
                }
                None => {
                    writeln!(
                        f,
                        "fn #{} {}: {:?} {{",
                        function.id.unwrap().0,
                        function.name,
                        function.return_type
                    )?;
                }
            }

            writeln!(f, "  entry: block {}", function.entry.0)?;

            for block in &function.blocks {
                writeln!(f, "  block {}:", block.id.0)?;

                for instruction in &block.instructions {
                    writeln!(f, "    {:?}", instruction)?;
                }

                writeln!(f, "    {:?}", block.terminator)?;
            }

            writeln!(f, "}}")?;
        }

        Ok(())
    }
}
