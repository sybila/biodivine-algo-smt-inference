use biodivine_lib_param_bn::VariableId;
use num_rational::BigRational;
use num_traits::{One, Zero};
use std::collections::BTreeMap;

/// A simple collection that assigns [`VariableId`] objects to `bool` value "observations", where
/// each observation can have a rational "confidence" between `0` and `1`.
///
/// The confidence must be greater than `0`. If it is equal to `1`, the observation is assumed
/// to be "required". All other observations are optional and weighted
/// by the prescribed confidence.
#[derive(Clone, Default)]
pub struct StateSpecification(BTreeMap<VariableId, (bool, BigRational)>);

impl StateSpecification {
    /// Make a new [`StateSpecification`] with no assertions.
    pub fn new() -> StateSpecification {
        Self::default()
    }

    /// Assert that for the specification to be satisfied,
    /// the given `variable` *must* have the prescribed `value`.
    pub fn assert_must(&mut self, variable: VariableId, value: bool) {
        self.0.insert(variable, (value, BigRational::one()));
    }

    /// Assert that the specification "prefers" that the given `variable` has the given `value`,
    /// and this preference is subject to the given `confidence`.
    ///
    /// If `confidence` is one, then this is equivalent to [`Self::assert_must`].
    ///
    /// # Panics
    ///
    /// The method fails if `confidence` is less than equal to zero, or greater than one.
    pub fn assert_may(&mut self, variable: VariableId, value: bool, confidence: &BigRational) {
        assert!(*confidence > BigRational::zero());
        assert!(*confidence <= BigRational::one());
        self.0.insert(variable, (value, confidence.clone()));
    }

    /// Extract all "must" assertions into a single map of required values.
    pub fn make_required_assertion_map(&self) -> BTreeMap<VariableId, bool> {
        self.0
            .iter()
            .filter_map(|(k, (v, p))| if p.is_one() { Some((*k, *v)) } else { None })
            .collect()
    }

    /// Extract all "may" assertions into a single map of optional values.
    pub fn make_optional_assertion_map(&self) -> BTreeMap<VariableId, (bool, BigRational)> {
        self.0
            .iter()
            .filter_map(|(k, (v, p))| {
                if p.is_one() {
                    None
                } else {
                    Some((*k, (*v, p.clone())))
                }
            })
            .collect()
    }
}
