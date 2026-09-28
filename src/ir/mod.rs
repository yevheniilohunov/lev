pub mod cleanup;
pub mod ir;
pub mod lower;
pub mod phi;
pub mod ssa;
pub mod validate;

pub use ir::{
    BasicBlock, BlockId, IrBinaryOp, IrField, IrFunction, IrInstruction, IrLocal, IrProgram,
    IrStruct, IrType, Terminator, ValueId,
};

pub use cleanup::remove_unreachable_blocks;
pub use ssa::construct_ssa;
pub use validate::{validate, validate_ssa};
