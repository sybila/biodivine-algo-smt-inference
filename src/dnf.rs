use std::collections::HashSet;

/// Enum to specify literals in DNF clauses (positive/negative/missing).
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum LiteralValue {
    Positive,
    Negative,
    Missing,
}

impl LiteralValue {
    pub fn is_pos(&self) -> bool {
        matches!(self, LiteralValue::Positive)
    }

    pub fn is_neg(&self) -> bool {
        matches!(self, LiteralValue::Negative)
    }
}

/// Simplified representation for a dnf clause for a fixed number of variables.
/// For now, it is just a vector of ternary values specifying if particular variable
/// is used as positive/negative literal, or is missing.
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct DNFClause {
    pub literals: Vec<LiteralValue>,
}

impl DNFClause {
    /// Build a dnf clause from truth table row (vec of bools).
    /// The provided table rows should have positive output for dnf to make sense.
    pub fn from_table_row(table_row: &[bool]) -> Self {
        let literals = table_row
            .iter()
            .map(|val| {
                if *val {
                    LiteralValue::Positive
                } else {
                    LiteralValue::Negative
                }
            })
            .collect();
        DNFClause { literals }
    }

    /// Converts the clause to a string representation using the provided variable names.
    /// Variables marked as 'Missing' are ignored.
    pub fn to_dnf_str(&self, var_names: &[String]) -> String {
        assert_eq!(var_names.len(), self.literals.len());

        let mut parts = Vec::new();
        for (i, literal) in self.literals.iter().enumerate() {
            if let Some(var_name) = var_names.get(i) {
                match literal {
                    LiteralValue::Positive => parts.push(var_name.clone()),
                    LiteralValue::Negative => parts.push(format!("!{}", var_name)),
                    LiteralValue::Missing => continue,
                }
            }
        }

        // If no literals are present, it represents a 'True' clause.
        if parts.is_empty() {
            return "true".to_string();
        }
        parts.join(" & ")
    }
}

/// Simplified representation for a dnf. There is not much clever in there,
/// just wrappers to represent DNF clauses and create expressions from them.
///
/// See [DNFClause] for more.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct DNF {
    pub clauses: HashSet<DNFClause>,
}

impl DNF {
    pub fn new(clauses: HashSet<DNFClause>) -> Self {
        Self { clauses }
    }

    /// Build DNF (list of clauses) from table rows (where row is just a vec of bools).
    /// The provided table rows should have positive output for dnf to make sense.
    pub fn from_positive_table_rows(table_rows: &HashSet<Vec<bool>>) -> Self {
        let clauses = table_rows
            .iter()
            .map(|row| DNFClause::from_table_row(row))
            .collect();
        DNF { clauses }
    }

    /// Create a DNF string expressions by interpreting the literals with
    /// given variable names.
    pub fn create_dnf_expression(&self, var_names: &[String]) -> String {
        if self.clauses.is_empty() {
            return "false".to_string(); // An empty disjunction is False
        }

        self.clauses
            .iter()
            .map(|clause| {
                let clause_str = clause.to_dnf_str(var_names);
                format!("({})", clause_str)
            })
            .collect::<Vec<String>>()
            .join(" | ")
    }

    /// Get function arity by checking the clause size (since we assume each
    /// clause contains info on all inputs).
    ///
    /// Panicks on empty DNF, which must be handled.
    pub fn get_arity(&self) -> usize {
        self.clauses.iter().next().unwrap().literals.len()
    }
}
