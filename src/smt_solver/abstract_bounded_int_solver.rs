use crate::smt_solver::AbstractSolver;
use auto_impl::auto_impl;
use z3::FuncDecl;

/// A variant of [`AbstractSolver`] that tracks the usage of `Int` functions, automatically
/// ensuring that "bounded integers" maintain their expected domain.
///
/// This applies to zero-arity uninterpreted functions (`Int` constants) as well as more
/// complex uninterpreted functions whose range is `Int`. The implementation decides whether
/// unbounded integers are allowed or if all `Int` functions need to have a declared range.
/// If unbounded/undeclared integers are allowed, the solver should ensure that the domain
/// of already used symbols cannot be restricted ex-post.
#[auto_impl(Box)]
pub trait AbstractBoundedIntSolver: AbstractSolver {
    /// Declare a validity domain for a particular function declaration.
    ///
    /// The declaration can be an `Int` constant or a more complex `Int`-typed uninterpreted
    /// function. Use `domain=None` to indicate that the function is unbounded.
    fn declare_int(
        &mut self,
        f: &FuncDecl,
        domain: Option<(u32, u32)>,
    ) -> Result<(), anyhow::Error>;
}
