pub mod ir;
pub mod lower;
pub mod ssa;
pub mod validate;

pub use ir::{
    BasicBlock, BlockId, IrBinaryOp, IrField, IrFunction, IrInstruction, IrLocal, IrProgram,
    IrStruct, IrType, Terminator, ValueId,
};

pub use ssa::construct_ssa;
pub use validate::{validate, validate_ssa};
