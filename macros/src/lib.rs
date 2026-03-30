use proc_macro::TokenStream;
use quote::quote;
use syn::{DeriveInput, parse_macro_input};

#[proc_macro_derive(InferenceConstraint, attributes(solver))]
pub fn derive_wrapper(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = &input.ident;
    let implementation = quote! {
        const _: () = {
            const fn assert_implements_trait<T: ::biodivine_algo_smt_inference::bn_inference::SimpleInferenceConstraint<z3::Solver>>() {}
            // This will fail to compile if `#name` doesn't implement `SimpleInferenceConstraint`
            assert_implements_trait::<#name>();
        };

        impl<SOLVER: ::biodivine_algo_smt_inference::smt_solver::AbstractSolver + 'static>
            ::biodivine_algo_smt_inference::bn_inference::InferenceConstraint<SOLVER> for #name {
            fn validate(&self,
                problem: &::biodivine_algo_smt_inference::bn_inference::InferenceProblem<SOLVER>
            ) -> Result<(), anyhow::Error> {
                ::biodivine_algo_smt_inference::bn_inference::SimpleInferenceConstraint::validate(self, problem)
            }

            fn assert_self(
                &self,
                encoder: &::biodivine_algo_smt_inference::bn_inference::InferenceProblemEncoder<SOLVER>,
                solver: &mut SOLVER,
            ) -> Result<(), anyhow::Error> {
                log::info!("Asserting: `{self:?}`.");
                let assertion = ::biodivine_algo_smt_inference::bn_inference::SimpleInferenceConstraint::mk_assertion(self, encoder)?;
                solver.assert(&assertion);
                Ok(())
            }
        }
    };

    TokenStream::from(implementation)
}
