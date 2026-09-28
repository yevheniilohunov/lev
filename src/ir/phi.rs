use std::collections::{HashMap, HashSet};

use crate::compiler::error::CompilerError;

use super::ir::{BasicBlock, BlockId, IrFunction, IrInstruction, IrProgram, Terminator, ValueId};

struct PhiValueAllocator {
    next: usize,
}

impl PhiValueAllocator {
    fn from_function(function: &IrFunction) -> Self {
        let mut max_value = None;

        for block in &function.blocks {
            for instruction in &block.instructions {
                if let Some(destination) = instruction_destination(instruction) {
                    if destination.0 == usize::MAX {
                        continue;
                    }

                    max_value = Some(
                        max_value
                            .map(|current: usize| current.max(destination.0))
                            .unwrap_or(destination.0),
                    );
                }
            }
        }

        Self {
            next: max_value.map(|value| value + 1).unwrap_or(0),
        }
    }

    fn fresh(&mut self) -> ValueId {
        let value = ValueId(self.next);
        self.next += 1;
        value
    }
}

fn instruction_destination(instruction: &IrInstruction) -> Option<ValueId> {
    match instruction {
        IrInstruction::Parameter { destination, .. }
        | IrInstruction::ConstInt { destination, .. }
        | IrInstruction::ConstString { destination, .. }
        | IrInstruction::ConstBool { destination, .. }
        | IrInstruction::LoadLocal { destination, .. }
        | IrInstruction::Copy { destination, .. }
        | IrInstruction::StructCopy { destination, .. }
        | IrInstruction::AllocStruct { destination, .. }
        | IrInstruction::LoadField { destination, .. }
        | IrInstruction::Binary { destination, .. }
        | IrInstruction::Phi { destination, .. } => Some(*destination),

        IrInstruction::Call { destination, .. } => *destination,

        IrInstruction::StoreLocal { .. } | IrInstruction::StoreField { .. } => None,
    }
}

/// Lower a parallel copy set into an ordered sequence of ordinary copies.
///
/// Each tuple is `(source, destination)`.
///
/// For example:
///
///     a <- b
///     b <- a
///
/// becomes:
///
///     tmp <- a
///     a   <- b
///     b   <- tmp
///
/// Cycles are broken by saving one source into a fresh temporary and then
/// replacing all pending uses of that source with the temporary.
fn lower_parallel_copies(
    copies: &[(ValueId, ValueId)],
    allocator: &mut PhiValueAllocator,
) -> Vec<IrInstruction> {
    let mut pending = copies.to_vec();
    let mut result = Vec::new();

    while !pending.is_empty() {
        // No-op copies do not need to be emitted.
        pending.retain(|(source, destination)| source != destination);

        if pending.is_empty() {
            break;
        }

        // A copy is safe to emit when its destination is not itself used
        // as a source by another pending copy.
        let sources: HashSet<ValueId> = pending.iter().map(|(source, _)| *source).collect();

        if let Some(index) = pending
            .iter()
            .position(|(_, destination)| !sources.contains(destination))
        {
            let (source, destination) = pending.remove(index);

            result.push(IrInstruction::Copy {
                destination,
                source,
            });

            continue;
        }

        // No safe copy exists, so the remaining copies contain a cycle.
        //
        // Save one source before it is overwritten, then replace every
        // pending use of that source with the temporary.
        let (source, _) = pending[0];
        let temporary = allocator.fresh();

        result.push(IrInstruction::Copy {
            destination: temporary,
            source,
        });

        for (pending_source, _) in &mut pending {
            if *pending_source == source {
                *pending_source = temporary;
            }
        }
    }

    result
}

/// Lowers SSA phi nodes into ordinary copy operations.
///
/// The pass:
///
/// 1. Finds all phi incoming edges.
/// 2. Splits critical edges that carry phi values.
/// 3. Remembers which original edge was replaced by each split block.
/// 4. Converts every phi incoming value into a copy on the corresponding
///    incoming edge.
/// 5. Lowers parallel copies and breaks cycles with fresh temporaries.
/// 6. Removes all phi instructions.
///
/// After this pass the IR is no longer in SSA form.
pub fn lower_phis(program: &mut IrProgram) -> Result<(), Vec<CompilerError>> {
    let mut errors = Vec::new();

    for function in &mut program.functions {
        if let Err(function_errors) = lower_function_phis(function) {
            errors.extend(function_errors);
        }
    }

    if errors.is_empty() {
        Ok(())
    } else {
        Err(errors)
    }
}

fn lower_function_phis(function: &mut IrFunction) -> Result<(), Vec<CompilerError>> {
    /*
     * Split critical edges first, but keep the mapping from the original
     * edge to the new edge block.
     *
     * We cannot simply split edges and then read the phi sources because
     * the phi still refers to the original predecessor.
     */
    let split_edges = split_critical_edges(function)?;

    let mut edge_copies: HashMap<(BlockId, BlockId), Vec<(ValueId, ValueId)>> = HashMap::new();

    /*
     * At this point a phi source still describes the original logical edge:
     *
     *     predecessor -> phi_block
     *
     * If that edge was split, its actual copy block is the newly-created
     * edge block. Rewrite the copy location accordingly.
     */
    for block in &function.blocks {
        for instruction in &block.instructions {
            let IrInstruction::Phi {
                destination,
                sources,
                ..
            } = instruction
            else {
                continue;
            };

            for &(predecessor, source) in sources {
                let copy_block = split_edges
                    .get(&(predecessor, block.id))
                    .copied()
                    .unwrap_or(predecessor);

                edge_copies
                    .entry((copy_block, block.id))
                    .or_default()
                    .push((source, *destination));
            }
        }
    }

    /*
     * All phi instructions can now disappear. Their values will be
     * represented by ordinary Copy instructions on incoming edges.
     */
    for block in &mut function.blocks {
        block
            .instructions
            .retain(|instruction| !matches!(instruction, IrInstruction::Phi { .. }));
    }

    insert_edge_copies(function, edge_copies)?;

    Ok(())
}

/// Split every critical edge in the function and return a mapping:
///
///     (original_predecessor, successor) -> new_edge_block
///
/// A critical edge is an edge from a block with multiple successors to a
/// block with multiple predecessors.
///
/// The mapping is essential because phi sources still refer to the original
/// predecessor after the CFG has been rewritten.
fn split_critical_edges(
    function: &mut IrFunction,
) -> Result<HashMap<(BlockId, BlockId), BlockId>, Vec<CompilerError>> {
    let mut predecessors: HashMap<BlockId, Vec<BlockId>> = HashMap::new();
    let mut successors: HashMap<BlockId, Vec<BlockId>> = HashMap::new();

    for block in &function.blocks {
        let block_successors = terminator_successors(&block.terminator);

        successors.insert(block.id, block_successors.clone());

        for successor in block_successors {
            predecessors.entry(successor).or_default().push(block.id);
        }
    }

    let mut edges_to_split = Vec::new();

    for block in &function.blocks {
        let Some(block_successors) = successors.get(&block.id) else {
            continue;
        };

        if block_successors.len() <= 1 {
            continue;
        }

        for &successor in block_successors {
            let predecessor_count = predecessors.get(&successor).map_or(0, Vec::len);

            if predecessor_count > 1 {
                edges_to_split.push((block.id, successor));
            }
        }
    }

    let mut split_edges = HashMap::new();

    for (predecessor, successor) in edges_to_split {
        let new_block = split_edge(function, predecessor, successor)?;
        split_edges.insert((predecessor, successor), new_block);
    }

    Ok(split_edges)
}

fn split_edge(
    function: &mut IrFunction,
    predecessor: BlockId,
    successor: BlockId,
) -> Result<BlockId, Vec<CompilerError>> {
    let new_block_id = next_block_id(function);

    let new_block = BasicBlock {
        id: new_block_id,
        instructions: Vec::new(),
        terminator: Terminator::Jump(successor),
    };

    let predecessor_block = function
        .blocks
        .iter_mut()
        .find(|block| block.id == predecessor)
        .ok_or_else(|| {
            vec![CompilerError::internal(format!(
                "missing predecessor block {:?}",
                predecessor
            ))]
        })?;

    redirect_successor(&mut predecessor_block.terminator, successor, new_block_id)?;

    function.blocks.push(new_block);

    Ok(new_block_id)
}

/// Insert all copies associated with incoming edges.
///
/// At this point every copy location is safe:
///
/// - a predecessor with one successor can contain the copies directly;
/// - a predecessor with multiple successors has had the relevant critical
///   edge split, so the copy block has exactly one successor.
///
/// Multiple phi copies on the same edge are lowered together as a parallel
/// copy set.
fn insert_edge_copies(
    function: &mut IrFunction,
    edge_copies: HashMap<(BlockId, BlockId), Vec<(ValueId, ValueId)>>,
) -> Result<(), Vec<CompilerError>> {
    let mut allocator = PhiValueAllocator::from_function(function);

    for ((copy_block_id, successor), copies) in edge_copies {
        let lowered = lower_parallel_copies(&copies, &mut allocator);

        let Some(block) = function
            .blocks
            .iter_mut()
            .find(|block| block.id == copy_block_id)
        else {
            return Err(vec![CompilerError::internal(format!(
                "missing phi copy block {:?}",
                copy_block_id
            ))]);
        };

        /*
         * A copy block must actually flow into the phi block. This also
         * catches accidental insertion into the wrong CFG edge.
         */
        if !terminator_successors(&block.terminator).contains(&successor) {
            return Err(vec![CompilerError::internal(format!(
                "phi copies for edge {:?} -> {:?} were inserted into block {:?}, \
                 but that block does not target {:?}",
                copy_block_id, successor, copy_block_id, successor
            ))]);
        }

        /*
         * Copies execute before the terminator, so they happen exactly when
         * this edge is taken.
         */
        block.instructions.extend(lowered);
    }

    Ok(())
}

fn terminator_successors(terminator: &Terminator) -> Vec<BlockId> {
    match terminator {
        Terminator::Jump(block) => vec![*block],

        Terminator::Branch {
            then_block,
            else_block,
            ..
        } => {
            let mut successors = Vec::with_capacity(2);

            successors.push(*then_block);

            if *else_block != *then_block {
                successors.push(*else_block);
            }

            successors
        }

        Terminator::Return { .. } | Terminator::Unreachable => Vec::new(),
    }
}

fn redirect_successor(
    terminator: &mut Terminator,
    old_target: BlockId,
    new_target: BlockId,
) -> Result<(), Vec<CompilerError>> {
    match terminator {
        Terminator::Jump(target) => {
            if *target == old_target {
                *target = new_target;
                Ok(())
            } else {
                Err(vec![CompilerError::internal(format!(
                    "edge {:?} -> {:?} does not exist",
                    old_target, new_target
                ))])
            }
        }

        Terminator::Branch {
            then_block,
            else_block,
            ..
        } => {
            let mut found = false;

            if *then_block == old_target {
                *then_block = new_target;
                found = true;
            }

            if *else_block == old_target {
                *else_block = new_target;
                found = true;
            }

            if found {
                Ok(())
            } else {
                Err(vec![CompilerError::internal(format!(
                    "edge {:?} -> {:?} does not exist",
                    old_target, new_target
                ))])
            }
        }

        Terminator::Return { .. } | Terminator::Unreachable => Err(vec![CompilerError::internal(
            "cannot redirect edge from a terminating block",
        )]),
    }
}

fn next_block_id(function: &IrFunction) -> BlockId {
    let next = function
        .blocks
        .iter()
        .map(|block| block.id.0)
        .max()
        .unwrap_or(0)
        + 1;

    BlockId(next)
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::ir::ir::{
        BasicBlock, IrFunction, IrInstruction, IrProgram, IrType, Terminator, ValueId,
    };
    use crate::semantic::symbols::{FunctionId, LocalId};

    fn diamond_function() -> IrFunction {
        IrFunction {
            id: Some(FunctionId(0)),
            name: "phi_test".to_string(),
            owner: None,
            parameters: Vec::new(),
            locals: vec![crate::ir::ir::IrLocal {
                id: LocalId(0),
                name: "value".to_string(),
                ty: IrType::Int,
            }],
            return_type: IrType::Int,
            entry: BlockId(0),
            blocks: vec![
                BasicBlock {
                    id: BlockId(0),
                    instructions: vec![IrInstruction::ConstBool {
                        destination: ValueId(0),
                        value: true,
                    }],
                    terminator: Terminator::Branch {
                        condition: ValueId(0),
                        then_block: BlockId(1),
                        else_block: BlockId(2),
                    },
                },
                BasicBlock {
                    id: BlockId(1),
                    instructions: vec![IrInstruction::ConstInt {
                        destination: ValueId(1),
                        value: 10,
                    }],
                    terminator: Terminator::Jump(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(2),
                    instructions: vec![IrInstruction::ConstInt {
                        destination: ValueId(2),
                        value: 20,
                    }],
                    terminator: Terminator::Jump(BlockId(3)),
                },
                BasicBlock {
                    id: BlockId(3),
                    instructions: vec![IrInstruction::Phi {
                        destination: ValueId(3),
                        local: LocalId(0),
                        sources: vec![(BlockId(1), ValueId(1)), (BlockId(2), ValueId(2))],
                    }],
                    terminator: Terminator::Return {
                        value: Some(ValueId(3)),
                    },
                },
            ],
        }
    }

    #[test]
    fn lowers_phi_to_edge_copy() {
        let mut program = IrProgram {
            structs: Vec::new(),
            functions: vec![diamond_function()],
        };

        lower_phis(&mut program).expect("phi lowering should succeed");

        let function = &program.functions[0];

        assert!(
            function.blocks.iter().all(|block| !block
                .instructions
                .iter()
                .any(|instruction| matches!(instruction, IrInstruction::Phi { .. }))),
            "phi instructions should be removed"
        );

        let then_block = function
            .blocks
            .iter()
            .find(|block| block.id == BlockId(1))
            .expect("then block should exist");

        let else_block = function
            .blocks
            .iter()
            .find(|block| block.id == BlockId(2))
            .expect("else block should exist");

        assert!(then_block.instructions.iter().any(|instruction| {
            matches!(
                instruction,
                IrInstruction::Copy {
                    source: ValueId(1),
                    destination: ValueId(3),
                }
            )
        }));

        assert!(else_block.instructions.iter().any(|instruction| {
            matches!(
                instruction,
                IrInstruction::Copy {
                    source: ValueId(2),
                    destination: ValueId(3),
                }
            )
        }));

        let join_block = function
            .blocks
            .iter()
            .find(|block| block.id == BlockId(3))
            .expect("join block should exist");

        assert!(matches!(
            join_block.terminator,
            Terminator::Return {
                value: Some(ValueId(3))
            }
        ));
    }

    #[test]
    fn lowers_parallel_copy_cycle() {
        let mut allocator = PhiValueAllocator { next: 2 };

        let copies = vec![(ValueId(0), ValueId(1)), (ValueId(1), ValueId(0))];

        let lowered = lower_parallel_copies(&copies, &mut allocator);

        assert_eq!(lowered.len(), 3);

        let temporary = match lowered[0] {
            IrInstruction::Copy {
                destination,
                source,
            } => {
                assert_eq!(source, ValueId(0));
                destination
            }
            _ => panic!("expected temporary copy"),
        };

        assert!(matches!(
            lowered[1],
            IrInstruction::Copy {
                source: ValueId(1),
                destination: ValueId(0),
            }
        ));

        assert!(matches!(
            lowered[2],
            IrInstruction::Copy {
                source,
                destination: ValueId(1),
            } if source == temporary
        ));
    }

    #[test]
    fn lowers_three_way_parallel_copy_cycle() {
        let mut allocator = PhiValueAllocator { next: 3 };

        let copies = vec![
            (ValueId(0), ValueId(1)),
            (ValueId(1), ValueId(2)),
            (ValueId(2), ValueId(0)),
        ];

        let lowered = lower_parallel_copies(&copies, &mut allocator);

        assert_eq!(lowered.len(), 4);

        let temporary = match lowered[0] {
            IrInstruction::Copy {
                destination,
                source,
            } => {
                assert_eq!(source, ValueId(0));
                destination
            }
            _ => panic!("expected temporary copy"),
        };

        assert!(matches!(
            lowered[1],
            IrInstruction::Copy {
                source: ValueId(2),
                destination: ValueId(0),
            }
        ));

        assert!(matches!(
            lowered[2],
            IrInstruction::Copy {
                source: ValueId(1),
                destination: ValueId(2),
            }
        ));

        assert!(matches!(
            lowered[3],
            IrInstruction::Copy {
                source,
                destination: ValueId(1),
            } if source == temporary
        ));
    }

    fn critical_edge_function() -> IrFunction {
        IrFunction {
            id: Some(FunctionId(0)),
            name: "critical_phi_test".to_string(),
            owner: None,
            parameters: Vec::new(),
            locals: vec![crate::ir::ir::IrLocal {
                id: LocalId(0),
                name: "value".to_string(),
                ty: IrType::Int,
            }],
            return_type: IrType::Int,
            entry: BlockId(0),
            blocks: vec![
                // Block 0 branches either directly to the join block or to
                // block 1.
                BasicBlock {
                    id: BlockId(0),
                    instructions: vec![IrInstruction::ConstBool {
                        destination: ValueId(0),
                        value: true,
                    }],
                    terminator: Terminator::Branch {
                        condition: ValueId(0),
                        then_block: BlockId(1),
                        else_block: BlockId(3),
                    },
                },
                // Block 1 has a single successor, the join.
                BasicBlock {
                    id: BlockId(1),
                    instructions: vec![IrInstruction::ConstInt {
                        destination: ValueId(1),
                        value: 10,
                    }],
                    terminator: Terminator::Jump(BlockId(3)),
                },
                // Block 2 also reaches the join.
                BasicBlock {
                    id: BlockId(2),
                    instructions: vec![IrInstruction::ConstInt {
                        destination: ValueId(2),
                        value: 20,
                    }],
                    terminator: Terminator::Jump(BlockId(3)),
                },
                // Join block.
                BasicBlock {
                    id: BlockId(3),
                    instructions: vec![IrInstruction::Phi {
                        destination: ValueId(3),
                        local: LocalId(0),
                        sources: vec![
                            (BlockId(0), ValueId(0)),
                            (BlockId(1), ValueId(1)),
                            (BlockId(2), ValueId(2)),
                        ],
                    }],
                    terminator: Terminator::Return {
                        value: Some(ValueId(3)),
                    },
                },
            ],
        }
    }

    #[test]
    fn splits_critical_phi_edge() {
        let mut function = critical_edge_function();

        /*
         * Block 0 has two successors and block 3 has three predecessors,
         * so 0 -> 3 is a critical edge.
         */
        let split_edges =
            split_critical_edges(&mut function).expect("edge splitting should succeed");

        let split_block = *split_edges
            .get(&(BlockId(0), BlockId(3)))
            .expect("critical edge should have been split");

        let entry = function
            .blocks
            .iter()
            .find(|block| block.id == BlockId(0))
            .expect("entry block should exist");

        assert!(terminator_successors(&entry.terminator).contains(&split_block));
        assert!(!terminator_successors(&entry.terminator).contains(&BlockId(3)));

        let edge_block = function
            .blocks
            .iter()
            .find(|block| block.id == split_block)
            .expect("split edge block should exist");

        assert_eq!(edge_block.terminator, Terminator::Jump(BlockId(3)));
    }

    #[test]
    fn critical_phi_copy_is_placed_in_split_edge_block() {
        let mut program = IrProgram {
            structs: Vec::new(),
            functions: vec![critical_edge_function()],
        };

        lower_phis(&mut program).expect("phi lowering should succeed");

        let function = &program.functions[0];

        assert!(
            function.blocks.iter().all(|block| !block
                .instructions
                .iter()
                .any(|instruction| matches!(instruction, IrInstruction::Phi { .. }))),
            "phi instructions should be removed"
        );

        let split_block = function
            .blocks
            .iter()
            .find(|block| {
                block.id != BlockId(0)
                    && block.id != BlockId(1)
                    && block.id != BlockId(2)
                    && block.id != BlockId(3)
                    && block.instructions.iter().any(|instruction| {
                        matches!(
                            instruction,
                            IrInstruction::Copy {
                                source: ValueId(0),
                                destination: ValueId(3),
                            }
                        )
                    })
            })
            .expect("critical-edge copy should be in a split edge block");

        assert_eq!(split_block.terminator, Terminator::Jump(BlockId(3)));

        let entry = function
            .blocks
            .iter()
            .find(|block| block.id == BlockId(0))
            .expect("entry block should exist");

        assert!(
            !entry.instructions.iter().any(|instruction| {
                matches!(
                    instruction,
                    IrInstruction::Copy {
                        source: ValueId(0),
                        destination: ValueId(3),
                    }
                )
            }),
            "critical-edge copy must not execute on the other branch"
        );
    }
}
