use std::collections::HashMap;

use super::{ symbols::LocalId, types::Type };

#[derive(Debug, Default)]
pub struct Scope {
    scopes: Vec<HashMap<String, LocalId>>,
    locals: Vec<(LocalId, String, Type, bool)>,
}

impl Scope {
    pub fn new() -> Self {
        Self {
            scopes: vec![HashMap::new()],
            locals: Vec::new(),
        }
    }

    pub fn declare(&mut self, name: String, ty: Type, mutable: bool) -> Result<LocalId, String> {
        let current_scope = self.scopes
            .last_mut()
            .expect("scope stack must always contain a root scope");

        if current_scope.contains_key(&name) {
            return Err(format!("variable '{}' is already declared in this scope", name));
        }

        /*
         * LocalIds are function-wide rather than scope-local.
         *
         * This is important because HIR and later IR/SSA stages refer
         * directly to LocalId values. A variable declared in an inner
         * scope must not reuse the LocalId of a variable from an outer
         * scope.
         */
        let id = LocalId(self.locals.len());

        current_scope.insert(name.clone(), id);

        self.locals.push((id, name, ty, mutable));

        Ok(id)
    }

    pub fn lookup(&self, name: &str) -> Option<LocalId> {
        /*
         * Search from the innermost scope outward.
         *
         * This gives us normal lexical shadowing:
         *
         * outer:
         *     x -> LocalId(0)
         *
         * inner:
         *     x -> LocalId(1)
         *
         * While the inner scope is active, lookup("x") returns
         * LocalId(1). After pop_scope(), it returns LocalId(0).
         */
        self.scopes
            .iter()
            .rev()
            .find_map(|scope| scope.get(name).copied())
    }

    pub fn type_of(&self, id: LocalId) -> Option<&Type> {
        self.locals.get(id.0).map(|(_, _, ty, _)| ty)
    }

    pub fn locals(&self) -> &[(LocalId, String, Type, bool)] {
        &self.locals
    }

    pub fn push_scope(&mut self) {
        self.scopes.push(HashMap::new());
    }

    pub fn pop_scope(&mut self) {
        /*
         * Keep the root scope alive.
         *
         * Accidentally popping the root would make later declarations
         * and lookups panic or behave incorrectly.
         */
        if self.scopes.len() > 1 {
            self.scopes.pop();
        }
    }

    pub fn is_mutable(&self, id: LocalId) -> bool {
        self.locals.get(id.0).map_or_default(|(_, _, _, mutable)| *mutable)
    }
}
