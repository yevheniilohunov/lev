use std::collections::HashMap;

use crate::semantic::modifiers::Visibility;

use super::types::Type;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct FunctionId(pub usize);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct StructId(pub usize);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub struct LocalId(pub usize);

#[derive(Debug, Clone)]
pub struct StructSymbol {
    pub id: StructId,
    pub name: String,
    pub base: Option<StructId>,
    pub fields: Vec<FieldSymbol>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ConstructorId(pub usize);

#[derive(Debug, Clone)]
pub struct ConstructorSymbol {
    pub id: ConstructorId,
    pub owner: StructId,
    pub parameters: Vec<ParameterSymbol>,
}

#[derive(Debug, Clone)]
pub struct FieldSymbol {
    pub name: String,
    pub ty: Type,
    pub visibility: Visibility,
    pub owner: StructId,
}

#[derive(Debug, Clone)]
pub struct FunctionSymbol {
    pub id: FunctionId,
    pub name: String,

    // None means this is a top-level function.
    // Some(struct_id) means this is a method of that struct.
    pub owner: Option<StructId>,

    pub parameters: Vec<ParameterSymbol>,
    pub return_type: Type,
}

#[derive(Debug, Clone)]
pub struct ParameterSymbol {
    pub name: String,
    pub ty: Type,
}

#[derive(Debug, Default)]
pub struct SymbolTable {
    structs: Vec<StructSymbol>,
    functions: Vec<FunctionSymbol>,
    struct_names: HashMap<String, StructId>,
    function_names: HashMap<String, FunctionId>,
    constructors: Vec<ConstructorSymbol>,
    method_names: HashMap<(StructId, String), FunctionId>,
}

impl SymbolTable {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn add_struct(&mut self, name: String) -> Result<StructId, String> {
        if self.struct_names.contains_key(&name) {
            return Err(format!("struct '{}' is already declared", name));
        }
        let id = StructId(self.struct_count());
        self.struct_names.insert(name.clone(), id);
        self.structs.push(StructSymbol { id, name, base: None, fields: Vec::new() });

        Ok(id)
    }

    pub fn set_struct_base(&mut self, id: StructId, base: StructId) {
        self.structs[id.0].base = Some(base);
    }

    pub fn struct_base(&self, id: StructId) -> Option<StructId> {
        self.struct_symbol(id).base
    }

    pub fn find_field(&self, struct_id: StructId, name: &str) -> Option<(usize, &FieldSymbol)> {
        let mut current = Some(struct_id);

        while let Some(id) = current {
            let structure = &self.structs[id.0];

            if
                let Some((index, field)) = structure.fields
                    .iter()
                    .enumerate()
                    .find(|(_, field)| field.name == name)
            {
                return Some((index, field));
            }

            current = structure.base;
        }

        None
    }

    pub fn struct_count(&self) -> usize {
        self.structs.len()
    }

    pub fn set_struct_fields(&mut self, id: StructId, fields: Vec<FieldSymbol>) {
        self.structs[id.0].fields = fields;
    }

    pub fn add_function(
        &mut self,
        name: String,
        parameters: Vec<ParameterSymbol>,
        return_type: Type
    ) -> Result<FunctionId, String> {
        if self.function_names.contains_key(&name) {
            return Err(format!("function '{}' is already declared", name));
        }

        let id = FunctionId(self.functions.len());

        self.function_names.insert(name.clone(), id);
        self.functions.push(FunctionSymbol { id, name, owner: None, parameters, return_type });
        Ok(id)
    }

    pub fn add_method(
        &mut self,
        owner: StructId,
        name: String,
        parameters: Vec<ParameterSymbol>,
        return_type: Type
    ) -> Result<FunctionId, String> {
        let key = (owner, name.clone());

        if self.method_names.contains_key(&key) {
            let struct_name = self.struct_symbol(owner).name.clone();
            return Err(format!("method '{}.{}' is already declared", struct_name, name));
        }

        let id = FunctionId(self.functions.len());

        self.method_names.insert(key, id);

        self.functions.push(FunctionSymbol {
            id,
            name,
            owner: Some(owner),
            parameters,
            return_type,
        });

        Ok(id)
    }

    pub fn find_struct(&self, name: &str) -> Option<StructId> {
        self.struct_names.get(name).copied()
    }

    pub fn find_function(&self, name: &str) -> Option<FunctionId> {
        self.function_names.get(name).copied()
    }

    pub fn find_method(&self, owner: StructId, name: &str) -> Option<FunctionId> {
        let mut current = Some(owner);

        while let Some(struct_id) = current {
            if let Some(function_id) = self.method_names.get(&(struct_id, name.to_string())) {
                return Some(*function_id);
            }

            current = self.structs[struct_id.0].base;
        }

        None
    }
    
    pub fn struct_symbol(&self, id: StructId) -> &StructSymbol {
        &self.structs[id.0]
    }

    pub fn function_symbol(&self, id: FunctionId) -> &FunctionSymbol {
        &self.functions[id.0]
    }
}
