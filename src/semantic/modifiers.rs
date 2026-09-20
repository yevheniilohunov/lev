#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Visibility {
    Public,
    Protected,
    Private,
}

impl Default for Visibility {
    fn default() -> Self {
        Self::Public
    }
}
