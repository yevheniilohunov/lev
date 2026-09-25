use std::collections::{BTreeMap, BTreeSet, HashMap};

use crate::compiler::error::CompilerError;

use super::ir::{BlockId, IrFunction, IrInstruction, IrProgram, Terminator, ValueId};
use super::validate::DominanceInfo;

pub fn construct_ssa(program: &mut IrProgram) -> Result<(), Vec<CompilerError>> {
    let mut errors = Vec::new();

    for function in &mut program.functions {
        if let Err(error) = construct_function_ssa(function) {
            errors.extend(error);
        }
    }

    if errors.is_empty() {
        Ok(())
    } else {
        Err(errors)
    }
}

fn construct_function_ssa(function: &mut IrFunction) -> Result<(), Vec<CompilerError>> {
    let dominance = DominanceInfo::compute(function);

    insert_phi_nodes(function, &dominance);

    let mut allocator = ValueAllocator::from_function(function);

    let mut stacks: HashMap<crate::semantic::symbols::LocalId, Vec<ValueId>> = HashMap::new();

    for local in &function.locals {
        stacks.entry(local.id).or_default();
    }

    for parameter in &function.parameters {
        stacks.entry(parameter.id).or_default();
    }

    let dominator_tree = build_dominator_tree(&dominance, function.entry);

    // Maps the ValueId produced by a LoadLocal to the actual SSA value
    // that represents that local at that point.
    let mut aliases: HashMap<ValueId, ValueId> = HashMap::new();

    rename_block(
        function,
        function.entry,
        &dominator_tree,
        &mut stacks,
        &mut aliases,
        &mut allocator,
    )?;

    sort_phi_sources(function);

    Ok(())
}

/* -------------------------------------------------------------------------- */
/* Phi insertion                                                              */
/* -------------------------------------------------------------------------- */

fn insert_phi_nodes(function: &mut IrFunction, dominance: &DominanceInfo) {
    use crate::semantic::symbols::LocalId;

    let reachable = &dominance.reachable;

    // local -> blocks where that local receives a definition.
    //
    // Definitions are:
    //   Parameter
    //   StoreLocal
    let mut definition_blocks: BTreeMap<LocalId, BTreeSet<BlockId>> = BTreeMap::new();

    for block in &function.blocks {
        if !reachable.contains(&block.id) {
            continue;
        }

        for instruction in &block.instructions {
            match instruction {
                IrInstruction::Parameter { local, .. } => {
                    definition_blocks
                        .entry(*local)
                        .or_default()
                        .insert(block.id);
                }

                IrInstruction::StoreLocal { local, .. } => {
                    definition_blocks
                        .entry(*local)
                        .or_default()
                        .insert(block.id);
                }

                _ => {}
            }
        }
    }

    for (local, definitions) in definition_blocks {
        let mut worklist: Vec<BlockId> = definitions.iter().copied().collect();

        let mut has_phi: BTreeSet<BlockId> = BTreeSet::new();

        while let Some(definition_block) = worklist.pop() {
            let frontier = match dominance.dominance_frontier(definition_block) {
                Some(frontier) => frontier,
                None => {
                    continue;
                }
            };

            let mut frontier_blocks: Vec<BlockId> = frontier.iter().copied().collect();

            frontier_blocks.sort_by_key(|id| id.0);

            for frontier_block in frontier_blocks {
                if !reachable.contains(&frontier_block) {
                    continue;
                }

                if !has_phi.insert(frontier_block) {
                    continue;
                }

                let block = match function
                    .blocks
                    .iter_mut()
                    .find(|block| block.id == frontier_block)
                {
                    Some(block) => block,
                    None => {
                        continue;
                    }
                };

                block.instructions.insert(
                    0,
                    IrInstruction::Phi {
                        destination: ValueId(usize::MAX),
                        local,
                        sources: Vec::new(),
                    },
                );

                if !definitions.contains(&frontier_block) {
                    worklist.push(frontier_block);
                }
            }
        }
    }

    // Keep all Phi instructions at the beginning of every block and make
    // their order deterministic.
    for block in &mut function.blocks {
        let mut phis = Vec::new();
        let mut rest = Vec::new();

        for instruction in block.instructions.drain(..) {
            match instruction {
                IrInstruction::Phi { .. } => phis.push(instruction),
                instruction => rest.push(instruction),
            }
        }

        phis.sort_by_key(|instruction| match instruction {
            IrInstruction::Phi { local, .. } => local.0,
            _ => usize::MAX,
        });

        phis.extend(rest);
        block.instructions = phis;
    }
}

/* -------------------------------------------------------------------------- */
/* Dominator tree                                                             */
/* -------------------------------------------------------------------------- */

fn build_dominator_tree(
    dominance: &DominanceInfo,
    entry: BlockId,
) -> BTreeMap<BlockId, Vec<BlockId>> {
    let mut tree: BTreeMap<BlockId, Vec<BlockId>> = BTreeMap::new();

    for block in &dominance.reachable {
        if *block == entry {
            continue;
        }

        if let Some(parent) = dominance.immediate_dominator(*block) {
            tree.entry(parent).or_default().push(*block);
        }
    }

    for children in tree.values_mut() {
        children.sort_by_key(|id| id.0);
    }

    tree
}

fn sort_phi_sources(function: &mut IrFunction) {
    for block in &mut function.blocks {
        for instruction in &mut block.instructions {
            if let IrInstruction::Phi { sources, .. } = instruction {
                sources.sort_by_key(|(block_id, _)| block_id.0);
            }
        }
    }
}

/* -------------------------------------------------------------------------- */
/* SSA renaming                                                               */
/* -------------------------------------------------------------------------- */

fn rename_block(
    function: &mut IrFunction,
    block_id: BlockId,
    dominator_tree: &BTreeMap<BlockId, Vec<BlockId>>,
    stacks: &mut HashMap<crate::semantic::symbols::LocalId, Vec<ValueId>>,
    aliases: &mut HashMap<ValueId, ValueId>,
    allocator: &mut ValueAllocator,
) -> Result<(), Vec<CompilerError>> {
    if !function.reachable_blocks().contains(&block_id) {
        return Ok(());
    }

    let mut pushed_locals = Vec::new();

    /*
     * Take the instructions out temporarily so we can mutate the block
     * without fighting Rust's borrowing rules.
     */
    let old_instructions = {
        let block = match function.blocks.iter_mut().find(|b| b.id == block_id) {
            Some(block) => block,
            None => {
                return Err(vec![CompilerError::internal(format!(
                    "SSA: block {:?} does not exist",
                    block_id
                ))]);
            }
        };

        std::mem::take(&mut block.instructions)
    };

    let mut phi_instructions = Vec::new();
    let mut normal_instructions = Vec::new();

    for instruction in old_instructions {
        match instruction {
            IrInstruction::Phi { .. } => {
                phi_instructions.push(instruction);
            }

            instruction => {
                normal_instructions.push(instruction);
            }
        }
    }

    let mut new_instructions = Vec::new();

    /*
    * First define all Phi values.

    * This is important because a LoadLocal later in the same block must
    * see the Phi value.
    */
    for instruction in phi_instructions {
        let IrInstruction::Phi {
            destination: _,
            local,
            sources,
        } = instruction
        else {
            unreachable!();
        };

        let destination = allocator.fresh();

        stacks.entry(local).or_default().push(destination);
        pushed_locals.push(local);

        new_instructions.push(IrInstruction::Phi {
            destination,
            local,
            sources,
        });
    }

    /*
     * Process ordinary instructions.
     */
    for instruction in normal_instructions {
        match instruction {
            /*
             * Parameter is an initial SSA definition.
             */
            IrInstruction::Parameter { destination, local } => {
                stacks.entry(local).or_default().push(destination);
                pushed_locals.push(local);

                new_instructions.push(IrInstruction::Parameter { destination, local });
            }

            /*
             * Constants are already SSA values.
             */
            IrInstruction::ConstInt { destination, value } => {
                new_instructions.push(IrInstruction::ConstInt { destination, value });
            }

            IrInstruction::ConstString { destination, value } => {
                new_instructions.push(IrInstruction::ConstString { destination, value });
            }

            IrInstruction::ConstBool { destination, value } => {
                new_instructions.push(IrInstruction::ConstBool { destination, value });
            }

            /*
            * LoadLocal disappears completely.

            * Example:
            *
            *   %4 = LoadLocal x
            *   %5 = Add %4, %2
            *
            * becomes:
            *
            *   %5 = Add %ssa_x, %2
            *
            * The old %4 is recorded as an alias.
            */
            IrInstruction::LoadLocal { destination, local } => {
                let current = current_value(stacks, local).ok_or_else(|| {
                    vec![CompilerError::internal(format!(
                        "SSA: local {:?} has no current definition",
                        local
                    ))]
                })?;

                aliases.insert(destination, current);
            }

            /*
            * StoreLocal also disappears.

            * The stored SSA value becomes the current version of the local.
            */
            IrInstruction::StoreLocal { local, value } => {
                let value = resolve_alias(aliases, value);

                stacks.entry(local).or_default().push(value);
                pushed_locals.push(local);
            }

            IrInstruction::Binary {
                destination,
                op,
                left,
                right,
            } => {
                let left = resolve_alias(aliases, left);
                let right = resolve_alias(aliases, right);

                new_instructions.push(IrInstruction::Binary {
                    destination,
                    op,
                    left,
                    right,
                });
            }

            IrInstruction::Call {
                destination,
                function: called_function,
                arguments,
            } => {
                let arguments = arguments
                    .into_iter()
                    .map(|value| resolve_alias(aliases, value))
                    .collect();

                new_instructions.push(IrInstruction::Call {
                    destination,
                    function: called_function,
                    arguments,
                });
            }

            /*
             * Phi nodes were handled above.
             */
            IrInstruction::Phi { .. } => {
                unreachable!("Phi instructions were separated above");
            }
            IrInstruction::AllocStruct {
                destination,
                struct_id,
            } => {
                new_instructions.push(IrInstruction::AllocStruct {
                    destination,
                    struct_id,
                });
            }

            IrInstruction::StoreField {
                receiver,
                field,
                value,
            } => {
                let receiver = resolve_alias(aliases, receiver);
                let value = resolve_alias(aliases, value);

                new_instructions.push(IrInstruction::StoreField {
                    receiver,
                    field,
                    value,
                });
            }

            IrInstruction::LoadField {
                destination,
                receiver,
                field,
            } => {
                let receiver = resolve_alias(aliases, receiver);

                new_instructions.push(IrInstruction::LoadField {
                    destination,
                    receiver,
                    field,
                });
            }
            IrInstruction::StructCopy {
                destination,
                source,
                struct_id,
            } => {
                let source = resolve_alias(aliases, source);

                new_instructions.push(IrInstruction::StructCopy {
                    destination,
                    source,
                    struct_id,
                });
            }
        }
    }

    /*
     * Rewrite the block terminator.
     */
    let terminator = {
        let block = function
            .blocks
            .iter()
            .find(|block| block.id == block_id)
            .expect("block disappeared during SSA construction");

        rewrite_terminator(block.terminator.clone(), aliases)
    };

    /*
     * Put the rewritten instructions and terminator back.
     */
    {
        let block = function
            .blocks
            .iter_mut()
            .find(|block| block.id == block_id)
            .expect("block disappeared during SSA construction");

        block.instructions = new_instructions;
        block.terminator = terminator;
    }

    /*
    * Every successor Phi gets an incoming value from this block.

    * Example:
    *
    *       block 1
    *          |
    *          v
    *       block 3
    *
    * If block 3 contains:
    *
    *   %10 = phi x
    *
    * we append:
    *
    *   (%1, current_x)
    */
    let successors = function.successors(block_id);

    for successor in successors {
        let successor_locals: Vec<_> = {
            let block = function
                .blocks
                .iter()
                .find(|block| block.id == successor)
                .expect("successor block disappeared");

            block
                .instructions
                .iter()
                .filter_map(|instruction| match instruction {
                    IrInstruction::Phi { local, .. } => Some(*local),
                    _ => None,
                })
                .collect()
        };

        for local in successor_locals {
            let value = current_value(stacks, local).ok_or_else(|| {
                vec![CompilerError::internal(format!(
                    "SSA: no value for local {:?} on edge {:?} -> {:?}",
                    local, block_id, successor
                ))]
            })?;

            let block = function
                .blocks
                .iter_mut()
                .find(|block| block.id == successor)
                .expect("successor block disappeared");

            for instruction in &mut block.instructions {
                if let IrInstruction::Phi {
                    local: phi_local,
                    sources,
                    ..
                } = instruction
                {
                    if *phi_local == local {
                        sources.push((block_id, value));
                    }
                }
            }
        }
    }

    /*
     * Recursively rename children in the dominator tree.
     */
    if let Some(children) = dominator_tree.get(&block_id) {
        for child in children {
            rename_block(function, *child, dominator_tree, stacks, aliases, allocator)?;
        }
    }

    /*
     * Definitions made in this block are no longer visible after leaving
     * the block.
     */
    for local in pushed_locals.into_iter().rev() {
        if let Some(stack) = stacks.get_mut(&local) {
            stack.pop();
        }
    }

    Ok(())
}

/* -------------------------------------------------------------------------- */
/* Value rewriting                                                            */
/* -------------------------------------------------------------------------- */

fn current_value(
    stacks: &HashMap<crate::semantic::symbols::LocalId, Vec<ValueId>>,
    local: crate::semantic::symbols::LocalId,
) -> Option<ValueId> {
    stacks.get(&local).and_then(|stack| stack.last()).copied()
}

fn resolve_alias(aliases: &HashMap<ValueId, ValueId>, mut value: ValueId) -> ValueId {
    let mut visited = BTreeSet::new();

    while let Some(next) = aliases.get(&value).copied() {
        if !visited.insert(value) {
            break;
        }

        value = next;
    }

    value
}

fn rewrite_terminator(terminator: Terminator, aliases: &HashMap<ValueId, ValueId>) -> Terminator {
    match terminator {
        Terminator::Jump(block) => Terminator::Jump(block),

        Terminator::Branch {
            condition,
            then_block,
            else_block,
        } => Terminator::Branch {
            condition: resolve_alias(aliases, condition),
            then_block,
            else_block,
        },

        Terminator::Return { value } => Terminator::Return {
            value: value.map(|value| resolve_alias(aliases, value)),
        },

        Terminator::Unreachable => Terminator::Unreachable,
    }
}

/* -------------------------------------------------------------------------- */
/* Value allocator                                                             */
/* -------------------------------------------------------------------------- */

struct ValueAllocator {
    next: usize,
}

impl ValueAllocator {
    fn from_function(function: &IrFunction) -> Self {
        let mut max_value = None;

        for block in &function.blocks {
            for instruction in &block.instructions {
                if let Some(destination) = instruction_destination(instruction) {
                    /*
                     * usize::MAX is our temporary Phi placeholder.
                     */
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
        | IrInstruction::Binary { destination, .. }
        | IrInstruction::LoadField { destination, .. }
        | IrInstruction::AllocStruct { destination, .. }
        | IrInstruction::StructCopy { destination, .. }
        | IrInstruction::Phi { destination, .. } => Some(*destination),

        IrInstruction::Call { destination, .. } => *destination,

        IrInstruction::StoreLocal { .. } => None,
        IrInstruction::StoreField { .. } => None,
    }
}
