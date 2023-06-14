use crate::pool::{MatchSpecId, Pool, StringId};
use crate::solvable::{Solvable, SolvableId};
use crate::solver::{DecisionMap, RuleId};

#[derive(Clone)]
pub(crate) struct Rule {
    pub enabled: bool,
    pub w1: SolvableId,
    pub w2: SolvableId,
    pub n1: RuleId,
    pub n2: RuleId,
    pub kind: RuleKind,
}

impl Rule {
    pub fn new(kind: RuleKind, learnt_rules: &[Vec<Literal>], pool: &Pool) -> Self {
        let (w1, w2) = kind
            .initial_watches(learnt_rules, pool)
            .unwrap_or((SolvableId::null(), SolvableId::null()));
        Self {
            enabled: true,
            w1,
            w2,
            n1: RuleId::null(),
            n2: RuleId::null(),
            kind,
        }
    }

    pub fn debug(&self, pool: &Pool) {
        match self.kind {
            RuleKind::InstallRoot => println!("install root"),
            RuleKind::Learnt(index) => println!("learnt rule {index}"),
            RuleKind::Requires(solvable_id, match_spec_id) => {
                pool.resolve_solvable(solvable_id).debug();
                let match_spec = pool.resolve_match_spec(match_spec_id).to_string();
                println!(" requires {match_spec}")
            }
            RuleKind::Constrains(solvable_id, match_spec_id) => {
                pool.resolve_solvable(solvable_id).debug();
                let match_spec = pool.resolve_match_spec(match_spec_id).to_string();
                println!(" constrains {match_spec}")
            }
            RuleKind::SameName(s1, _) => {
                let name = pool.resolve_solvable(s1).package().record.name.as_str();
                println!("only one {name} allowed")
            }
        }
    }

    pub fn has_watches(&self) -> bool {
        // If w1 is not null, w2 won't be either
        !self.w1.is_null()
    }

    pub fn find_literal(&self, solvable_id: SolvableId, learnt_rules: &[Vec<Literal>]) -> Literal {
        match self.kind {
            RuleKind::InstallRoot => unreachable!(),
            RuleKind::Requires(s, _) => {
                let negate = solvable_id == s;
                Literal {
                    solvable_id,
                    negate
                }
            }
            RuleKind::Constrains(_, _) |
            RuleKind::SameName(_, _) =>
                Literal {
                    solvable_id,
                    negate: true
                },
            RuleKind::Learnt(index) => learnt_rules[index].iter().find(|lit| lit.solvable_id == solvable_id).unwrap().clone()
        }
    }

    pub fn watched_literals(&self, learnt_rules: &[Vec<Literal>]) -> (Literal, Literal) {
        match self.kind {
            RuleKind::InstallRoot => unreachable!(),
            RuleKind::Learnt(index) => {
                // TODO: this is probably not going to cut it for performance
                let &w1 = learnt_rules[index].iter().find(|l| l.solvable_id == self.w1).unwrap();
                let &w2 = learnt_rules[index].iter().find(|l| l.solvable_id == self.w2).unwrap();
                (w1, w2)
            }
            RuleKind::SameName(s1, s2) => (Literal::negate(s1), Literal::negate(s2)),
            RuleKind::Requires(solvable_id, _) => {
                if self.w1 == solvable_id {
                    (
                        Literal {
                            solvable_id: self.w1,
                            negate: true,
                        },
                        Literal {
                            solvable_id: self.w2,
                            negate: false,
                        },
                    )
                } else if self.w2 == solvable_id {
                    (
                        Literal {
                            solvable_id: self.w1,
                            negate: false,
                        },
                        Literal {
                            solvable_id: self.w2,
                            negate: true,
                        },
                    )
                } else {
                    (
                        Literal {
                            solvable_id: self.w1,
                            negate: false,
                        },
                        Literal {
                            solvable_id: self.w2,
                            negate: false,
                        },
                    )
                }
            }
            RuleKind::Constrains(_, _) => (
                Literal {
                    solvable_id: self.w1,
                    negate: true,
                },
                Literal {
                    solvable_id: self.w2,
                    negate: true,
                },
            ),
        }
    }

    pub fn next_unwatched_variable(
        &self,
        pool: &Pool,
        learnt_rules: &[Vec<Literal>],
        decision_map: &DecisionMap,
    ) -> Option<SolvableId> {
        // The next unwatched variable (if available), is a variable that is:
        // * Not already being watched
        // * Not yet decided, or decided in such a way that the literal yields true
        let can_watch = |solvable_lit: Literal| {
            self.w1 != solvable_lit.solvable_id
                && self.w2 != solvable_lit.solvable_id
                && solvable_lit.eval(decision_map).unwrap_or(true)
        };

        match self.kind {
            RuleKind::InstallRoot => unreachable!(),
            RuleKind::Learnt(index) => {
                learnt_rules[index].iter().cloned().find(|&l| can_watch(l)).map(|l| l.solvable_id)
            }
            RuleKind::SameName(_, _) => None,
            RuleKind::Requires(solvable_id, match_spec_id) => {
                // The solvable that added this rule
                let solvable_lit = Literal {
                    solvable_id: solvable_id.clone(),
                    negate: true,
                };
                if can_watch(solvable_lit) {
                    return Some(solvable_id);
                }

                // The available candidates
                for &candidate in pool.match_spec_to_candidates[match_spec_id.index()]
                    .as_deref()
                    .unwrap()
                {
                    let lit = Literal {
                        solvable_id: candidate,
                        negate: false,
                    };
                    if can_watch(lit) {
                        return Some(candidate);
                    }
                }

                // No solvable available to watch
                None
            }
            RuleKind::Constrains(solvable_id, match_spec_id) => {
                // The solvable that added this rule
                let solvable_lit = Literal {
                    solvable_id: solvable_id.clone(),
                    negate: true,
                };
                if can_watch(solvable_lit) {
                    return Some(solvable_id);
                }

                // The forbidden candidates
                for &forbidden in pool.match_spec_to_forbidden[match_spec_id.index()]
                    .as_deref()
                    .unwrap()
                {
                    let lit = Literal {
                        solvable_id: forbidden,
                        negate: true,
                    };
                    if can_watch(lit) {
                        return Some(forbidden);
                    }
                }

                // No solvable available to watch
                None
            }
        }
    }

    /// Returns the list of variables that imply that
    pub fn conflict_causes(
        &self,
        variable: SolvableId,
        learnt_rules: &[Vec<Literal>],
        pool: &Pool,
    ) -> Vec<Literal> {
        match self.kind {
            RuleKind::InstallRoot => unreachable!(),
            RuleKind::Learnt(index) => {
                learnt_rules[index]
                    .iter()
                    .cloned()
                    .filter(|lit| lit.solvable_id != variable)
                    .collect()
            }
            RuleKind::Requires(solvable_id, match_spec_id) => {
                // All variables contribute to the conflict
                std::iter::once(Literal {
                    solvable_id: variable,
                    negate: true,
                })
                .chain(
                    pool.match_spec_to_candidates[match_spec_id.index()]
                        .as_deref()
                        .unwrap()
                        .iter()
                        .cloned()
                        .map(|solvable_id| Literal {
                            solvable_id,
                            negate: false,
                        }),
                )
                .filter(|&l| solvable_id != l.solvable_id)
                .collect()
            }
            RuleKind::Constrains(solvable_id, match_spec_id) => {
                // All variables contribute to the conflict
                std::iter::once(Literal {
                    solvable_id: variable,
                    negate: true,
                })
                .chain(
                    pool.match_spec_to_candidates[match_spec_id.index()]
                        .as_deref()
                        .unwrap()
                        .iter()
                        .cloned()
                        .map(|solvable_id| Literal {
                            solvable_id,
                            negate: true,
                        }),
                )
                .filter(|&l| solvable_id != l.solvable_id)
                .collect()
            }
            RuleKind::SameName(s1, s2) => {
                let cause = if variable == s1 { s2 } else { s1 };

                vec![Literal {
                    solvable_id: cause,
                    negate: true,
                }]
            }
        }
    }
}

#[derive(Copy, Clone, Eq, PartialEq, Hash)]
pub struct Literal {
    pub solvable_id: SolvableId,
    pub negate: bool,
}

impl Literal {
    pub(crate) fn negate(solvable_id: SolvableId) -> Self {
        Self {
            solvable_id,
            negate: true
        }
    }

    pub(crate) fn invert(mut self) -> Self {
        self.negate = !self.negate;
        self
    }

    pub(crate) fn satisfying_value(self) -> bool {
        !self.negate
    }

    pub(crate) fn eval(self, decision_map: &DecisionMap) -> Option<bool> {
        decision_map
            .value(self.solvable_id)
            .map(|value| self.eval_inner(value))
    }

    fn eval_inner(self, solvable_value: bool) -> bool {
        if self.negate {
            !solvable_value
        } else {
            solvable_value
        }
    }
}

#[derive(Copy, Clone)]
pub enum RuleKind {
    InstallRoot,
    /// The solvable requires the candidates associated to the match spec
    ///
    /// In SAT terms: (¬A ∨ B1 ∨ B2 ∨ ... ∨ B99), where B1 to B99 represent the possible candidates
    /// for the provided match spec.
    Requires(SolvableId, MatchSpecId),
    /// The solvable forbids the candidates outside of the match spec
    ///
    /// In SAT terms: (¬A ∨ ¬B1 ∨ ¬B2 ∨ ... ∨ ¬B99), where B1 to B99 represent the candidates
    /// outside of the provided match spec.
    Constrains(SolvableId, MatchSpecId),
    /// Only one of the solvables may be installed
    ///
    /// In SAT terms: (¬A ∨ ¬B)
    SameName(SolvableId, SolvableId),
    /// Learned rule
    Learnt(usize),
}

impl RuleKind {
    fn initial_watches(&self, learnt_rules: &[Vec<Literal>], pool: &Pool) -> Option<(SolvableId, SolvableId)> {
        match self {
            RuleKind::InstallRoot => None,
            RuleKind::SameName(s1, s2) => Some((*s1, *s2)),
            RuleKind::Learnt(index) => {
                let literals = &learnt_rules[*index];
                debug_assert!(literals.len() >= 1);
                if literals.len() == 1 {
                    // No need for watches, since we learned an assertion
                    None
                } else {
                    Some((literals.first().unwrap().solvable_id, literals.last().unwrap().solvable_id))
                }
            }
            RuleKind::Requires(id, match_spec) | RuleKind::Constrains(id, match_spec) => {
                let &first_candidate = pool.match_spec_to_candidates[match_spec.index()]
                    .as_ref()
                    .unwrap()
                    .iter()
                    .next()?;
                Some((*id, first_candidate))
            }
        }
    }
}

#[test]
fn test_literal_satisfying_value() {
    let lit = Literal {
        solvable_id: SolvableId::root(),
        negate: true,
    };
    assert_eq!(lit.satisfying_value(), false);

    let lit = Literal {
        solvable_id: SolvableId::root(),
        negate: false,
    };
    assert_eq!(lit.satisfying_value(), true);
}

#[test]
fn test_literal_eval() {
    let mut decision_map = DecisionMap::new(10);

    let literal = Literal {
        solvable_id: SolvableId::root(),
        negate: false,
    };
    let negated_literal = Literal {
        solvable_id: SolvableId::root(),
        negate: true,
    };

    // Undecided
    assert_eq!(literal.eval(&decision_map), None);
    assert_eq!(negated_literal.eval(&decision_map), None);

    // Decided
    decision_map.set(SolvableId::root(), true, 1);
    assert_eq!(literal.eval(&decision_map), Some(true));
    assert_eq!(negated_literal.eval(&decision_map), Some(false));

    decision_map.set(SolvableId::root(), false, 1);
    assert_eq!(literal.eval(&decision_map), Some(false));
    assert_eq!(negated_literal.eval(&decision_map), Some(true));
}