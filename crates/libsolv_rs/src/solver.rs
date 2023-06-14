use crate::pool::{MatchSpecId, Pool, StringId};
use crate::rules::{Literal, Rule, RuleKind};
use crate::solvable::{Solvable, SolvableId};
use crate::solve_jobs::{CandidateSource, SolveJobs, SolveOperation};
use crate::solve_problem::SolveProblem;
use std::cmp::Ordering;
use std::collections::hash_map::Entry;
use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt::{Display, Formatter};

#[derive(Copy, Clone, PartialOrd, Ord, Eq, PartialEq)]
pub struct RuleId(u32);

impl RuleId {
    pub fn new(index: usize) -> Self {
        Self(index as u32)
    }

    fn index(self) -> usize {
        self.0 as usize
    }

    fn is_null(self) -> bool {
        self.0 == u32::MAX
    }

    pub fn null() -> RuleId {
        RuleId(u32::MAX)
    }
}

#[derive(Copy, Clone, Eq, PartialEq)]
struct Decision {
    solvable_id: SolvableId,
    value: bool,
}

impl Decision {
    fn new(solvable: SolvableId, value: bool) -> Self {
        Self { solvable_id: solvable, value }
    }
}

pub struct Transaction {
    pub steps: Vec<(SolvableId, TransactionKind)>,
}

#[derive(Copy, Clone, Debug)]
pub enum TransactionKind {
    Install,
}

impl Display for TransactionKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}

pub struct Config {
    pub allow_name_change: bool,
    pub allow_uninstall: bool,
    pub allow_downgrade: bool,
}

impl Default for Config {
    fn default() -> Self {
        Self {
            allow_name_change: true,
            allow_uninstall: false,
            allow_downgrade: false,
        }
    }
}

/// Map of all available solvables
pub(crate) struct DecisionMap {
    /// = 0: undecided
    /// > 0: level of decision when installed
    /// < 0: level of decision when conflict
    map: Vec<i64>,
}

impl DecisionMap {
    pub fn new(nsolvables: usize) -> Self {
        Self {
            map: vec![0; nsolvables],
        }
    }

    pub fn reset(&mut self, solvable_id: SolvableId) {
        self.map[solvable_id.index()] = 0;
    }

    pub fn set(&mut self, solvable_id: SolvableId, value: bool, level: u32) {
        self.map[solvable_id.index()] = if value { level as i64 } else { -(level as i64) };
    }

    pub fn level(&mut self, solvable_id: SolvableId) -> u32 {
        self.map[solvable_id.index()].abs() as u32
    }

    pub fn value(&self, solvable_id: SolvableId) -> Option<bool> {
        match self.map[solvable_id.index()].cmp(&0) {
            Ordering::Less => Some(false),
            Ordering::Equal => None,
            Ordering::Greater => Some(true),
        }
    }
}

pub struct Solver {
    config: Config,
    pool: Pool,

    propagate_index: usize,

    rules: Vec<Rule>,
    watches: Vec<RuleId>,

    learnt_rules: Vec<Vec<Literal>>,

    // All assertion rules
    rule_assertions: VecDeque<RuleId>,

    decision_queue: VecDeque<Decision>,
    decision_queue_why: VecDeque<RuleId>,
    decision_queue_reason: VecDeque<u32>,

    learnt_rules_start: RuleId,

    decision_map: DecisionMap,
    // name_rules: HashMap<StringId, RuleId>,

    /* list of lists of conflicting rules, < 0 for job rules */
    problems: VecDeque<()>,
}

pub mod flags {
    pub const SOLVER_SOLVABLE: u32 = 1;
    pub const SOLVER_SOLVABLE_PROVIDES: u32 = 3;
    pub const SOLVER_TRANSACTION_INSTALL: u32 = 32;
    pub const SOLVER_INSTALL: u32 = 256;
    pub const SOLVER_ERASE: u32 = 512;
    pub const SOLVER_UPDATE: u32 = 768;
    pub const SOLVER_FAVOR: u32 = 3072;
    pub const SOLVER_DISFAVOR: u32 = 3328;
    pub const SOLVER_LOCK: u32 = 1536;
}

// Solver flags used
// * SOLVER_FLAG_ALLOW_UNINSTALL
// * SOLVER_FLAG_ALLOW_DOWNGRADE
// -> All other flags are unused

impl Solver {
    /// Create a solver, using the provided pool
    pub fn new(pool: Pool) -> Self {
        Self {
            propagate_index: 0,

            rules: vec![Rule::new(RuleKind::InstallRoot, &[], &pool)],
            watches: Vec::new(),
            learnt_rules: Vec::new(),
            rule_assertions: VecDeque::from([RuleId::new(0)]),
            decision_queue: VecDeque::new(),
            decision_queue_why: VecDeque::new(),
            decision_queue_reason: VecDeque::new(),

            learnt_rules_start: RuleId(0),

            decision_map: DecisionMap::new(pool.nsolvables()),
            // name_rules: HashMap::default(),
            problems: VecDeque::new(),

            config: Config::default(),
            pool,
        }
    }

    /// Retrieve the solver's configuration in order to modify it
    pub fn config_mut(&mut self) -> &mut Config {
        &mut self.config
    }

    pub fn pool(&self) -> &Pool {
        &self.pool
    }

    fn problem_count(&self) -> usize {
        self.problems.len() / 2
    }

    /// Creates a string for each 'problem' that the solver still has which it encountered while
    /// solving the matchspecs. Use this function to print the existing problems to string.
    fn solver_problems(&self) -> Vec<String> {
        let mut output = Vec::new();

        // See solver_problem_count
        let count = self.problem_count();
        for _ in 1..=count {
            // Safe because the id valid (between [1, count])
            // let problem = unsafe { self.problem2str(i as ffi::Id) };

            output.push("TODO".to_string());
        }
        output
    }

    /// Solves all the problems in the `queue` and returns a transaction from the found solution.
    /// Returns an error if problems remain unsolved.
    pub fn solve(&mut self, jobs: SolveJobs) -> Result<Transaction, Vec<String>> {
        let mut visited_solvables = HashSet::default();

        // Initialize the root solvable with the requested packages as dependencies
        self.pool.root_solvable_mut().clear();
        for (source, op) in jobs.items {
            if let (SolveOperation::Install, CandidateSource::MatchSpec(match_spec)) = (op, source)
            {
                let match_spec_id = self.pool.intern_matchspec(match_spec.to_string());
                let root_solvable = self.pool.root_solvable_mut();
                root_solvable.push(match_spec_id);

                // Recursively add rules for the current dep
                self.add_rules_for_root_dep(&mut visited_solvables, match_spec_id);
            } else {
                panic!("Unsupported operation or candidate source")
            }
        }

        // Initialize rules ensuring only a single candidate per package name is installed
        for (name_id, candidates) in &self.pool.packages_by_name {
            // Each candidate gets a rule with each other candidate
            for (i, &candidate) in candidates.iter().enumerate() {
                for &other_candidate in &candidates[i + 1..] {
                    self.rules
                        .push(Rule::new(RuleKind::SameName(candidate, other_candidate), &self.learnt_rules, &self.pool));
                }
            }
        }

        // All new rules are learnt after this point
        self.learnt_rules_start = RuleId::new(self.rules.len());

        // Create watches chains
        self.make_watches();

        // Create assertion index. It is only used to speed up make_rule_decisions() a bit
        // for (i, rule) in self.rules.iter().enumerate().skip(1) {
        //     if rule.is_assertion(self.pool()) {
        //         self.rule_assertions.push_back(RuleId::new(i));
        //     }
        // }

        // Run SAT
        self.run_sat();

        if self.problem_count() == 0 {
            let steps = self
                .decision_queue
                .iter()
                .flat_map(|d| {
                    if d.value && d.solvable_id != SolvableId::root() {
                        Some((d.solvable_id, TransactionKind::Install))
                    } else {
                        // Ignore things that are set to false
                        None
                    }
                })
                .collect();
            Ok(Transaction { steps })
        } else {
            Err(self.solver_problems())
        }
    }

    fn add_rules_for_root_dep(&mut self, visited: &mut HashSet<SolvableId>, dep: MatchSpecId) {
        let mut candidate_stack = Vec::new();

        // Initialize candidate stack
        {
            let candidates = Pool::get_candidates(
                &self.pool.match_specs,
                &self.pool.strings_to_ids,
                &self.pool.solvables,
                &self.pool.packages_by_name,
                &mut self.pool.match_spec_to_candidates,
                dep,
            );
            for &candidate in candidates {
                if visited.insert(candidate) {
                    candidate_stack.push(candidate);
                }
            }

            // TODO: gracefully handle this (e.g. after the root decision, add a decision setting the SolvableId to false)
            if candidates.is_empty() {
                let ms = self.pool.match_specs[dep.index()].to_string();
                panic!("No candidates for matchspec: {ms}");
            }
        }

        // Process candidates, adding them recursively
        while let Some(candidate) = candidate_stack.pop() {
            let solvable = self.pool.solvables[candidate.index()].package();

            // Requires
            for &dep in &solvable.dependencies {
                // Ensure the candidates have their rules added
                let dep_candidates = Pool::get_candidates(
                    &self.pool.match_specs,
                    &self.pool.strings_to_ids,
                    &self.pool.solvables,
                    &self.pool.packages_by_name,
                    &mut self.pool.match_spec_to_candidates,
                    dep,
                );

                for &dep_candidate in dep_candidates {
                    if visited.insert(dep_candidate) {
                        candidate_stack.push(dep_candidate);
                    }
                }

                // TODO: gracefully handle this (e.g. after the root decision, add a decision setting the SolvableId to false)
                if dep_candidates.is_empty() {
                    let ms = self.pool.match_specs[dep.index()].to_string();
                    panic!("No candidates for matchspec: {ms}");
                }

                // Create requires rule
                self.rules
                    .push(Rule::new(RuleKind::Requires(candidate, dep), &self.learnt_rules, &self.pool));
            }

            // Constrains
            for &dep in &solvable.constrains {
                let dep_forbidden = Pool::get_forbidden(
                    &self.pool.match_specs,
                    &self.pool.strings_to_ids,
                    &self.pool.solvables,
                    &self.pool.packages_by_name,
                    &mut self.pool.match_spec_to_forbidden,
                    dep,
                );

                if !dep_forbidden.is_empty() {
                    // Only add the "constrains" if it actually forbids packages
                    self.rules
                        .push(Rule::new(RuleKind::Constrains(candidate, dep), &self.learnt_rules, &self.pool));
                }
            }
        }

        self.rules.push(Rule::new(
            RuleKind::Requires(SolvableId::root(), dep),
            &self.learnt_rules,
            &self.pool,
        ));
    }

    fn run_sat(&mut self) {
        // This thing is normally true
        // let disable_rules = true;

        // let mut decision_queue = VecDeque::new();
        let mut level = 0;

        // What is this again?
        let mut root_level = 1;

        loop {
            println!("=== New SAT round at level {level}");

            // First rule decision
            if level == 0 {
                level = match self.install_root_solvable() {
                    Ok(new_level) => new_level,
                    Err(_) => break,
                };

                println!("=== Root solvable installed at level {level}");

                if let Err((_, cause)) = self.propagate(level) {
                    println!("=== Propagate failed... HOW?");
                    self.analyze_unsolvable(cause, false);
                    continue;
                }

                // Why would we increase the root level? Maybe if we have assertions that are
                // unavoidable, but still want to make a distinction between them and installing
                // root?
                root_level = level + 1;
            }

            // Resolve deps
            let original_level = level;
            level = self.resolve_dependencies(level);

            // TODO: if we are always returning, do we need a loop? What is libsolv doing?
            return;
        }
    }

    fn install_root_solvable(&mut self) -> Result<u32, ()> {
        assert!(self.decision_queue.is_empty());

        self.decision_queue
            .push_back(Decision::new(SolvableId::root(), true));
        self.decision_queue_why.push_back(RuleId::new(0));

        // TODO: why do we push twice here? Why push at all?
        // self.decision_queue_reason.push_back(0);
        // self.decision_queue_reason.push_back(0);

        self.decision_map.set(SolvableId::root(), true, 1);

        Ok(1)
    }

    /// Resolves all dependencies
    ///
    /// TODO: what does this thing return?
    fn resolve_dependencies(&mut self, mut level: u32) -> u32 {
        let mut i = 0;
        loop {
            if i >= self.rules.len() {
                break;
            }

            let candidate = {
                let rule = &self.rules[i];
                i += 1;

                if !rule.enabled {
                    continue;
                }

                // We are only interested in requires rules
                let RuleKind::Requires(solvable_id, deps) = rule.kind else {
                    continue;
                };

                // Consider only rules in which we have decided to install the solvable
                if self.decision_map.value(solvable_id) != Some(true) {
                    continue;
                }

                // Consider only rules in which no candidates have been installed
                let candidates = self.pool.match_spec_to_candidates[deps.index()]
                    .as_deref()
                    .unwrap();
                if candidates
                    .iter()
                    .any(|&c| self.decision_map.value(c) == Some(true))
                {
                    continue;
                }

                // Get the first candidate that is undecided and should be installed
                //
                // This assumes that the packages have been provided in the right order when the solvables were created
                // (most recent packages first)
                candidates
                    .iter()
                    .cloned()
                    .find(|&c| self.decision_map.value(c).is_none())
                    .unwrap()
            };

            // Assumption: there are multiple candidates, otherwise this would have already been handled
            // by unit propagation
            let orig_level = level;
            self.create_branch();
            level = self.set_propagate_learn(level, candidate, true, RuleId::new(i));

            if level < orig_level {
                return level;
            }

            // We have made progress, and should look at all rules in the next iteration
            i = 0;
        }

        // We just went through all rules and there are no choices left to be made
        level
    }

    fn set_propagate_learn(
        &mut self,
        mut level: u32,
        solvable: SolvableId,
        disable_rules: bool,
        rule_id: RuleId,
    ) -> u32 {
        let s = self.pool.resolve_solvable(solvable).package();
        let name = self.pool.resolve_string(s.name);
        let version = self.pool.resolve_string(s.version);

        level += 1;
        println!("=== Set {name} = {version} at level {level}");
        self.decision_map.set(solvable, true, level);
        self.decision_queue
            .push_back(Decision::new(solvable, true));
        self.decision_queue_why.push_back(rule_id);

        loop {
            let r = self.propagate(level);
            let Err((conflicting_solvable, conflicting_rule)) = r else {
                // Propagation succeeded
                break;
            };

            if level == 1 {
                return self.analyze_unsolvable(conflicting_rule, disable_rules);
            }

            let (new_level, learned_rule_id, literal) =
                self.analyze(level, conflicting_solvable, conflicting_rule);
            level = new_level;

            // Optimization: propagate right now, since we know that the rule is a unit clause
            let decision = literal.satisfying_value();
            self.decision_map.set(literal.solvable_id, decision, level);
            self.decision_queue
                .push_back(Decision::new(
                    literal.solvable_id,
                    decision,
                ));
            self.decision_queue_why.push_back(learned_rule_id);
            print!("=== Propagate after learn: ");
            self.pool.resolve_solvable(literal.solvable_id).debug();
            println!(" = {decision}");
        }

        level
    }

    fn create_branch(&mut self) {
        // TODO: we should probably keep info here for backtracking
    }

    fn propagate(&mut self, level: u32) -> Result<(), (SolvableId, RuleId)> {
        while let Some(decision) = self.decision_queue.range(self.propagate_index..).next() {
            self.propagate_index += 1;

            let pkg = decision.solvable_id;

            // Propagate, iterating through the linked list of rules that watch this solvable
            let mut prev_rule_id: Option<RuleId> = None;
            let mut rule_id = self.watches[self.pool.solvables.len() + pkg.index()];
            while !rule_id.is_null() {
                if prev_rule_id == Some(rule_id) {
                    panic!("Linked list is circular!");
                }

                // This is a convoluted way of getting mutable access to the current and the previous rule
                let (prev_rule, rule) = if let Some(prev_rule_id) = prev_rule_id {
                    if prev_rule_id < rule_id {
                        let (prev, current) = self.rules.split_at_mut(rule_id.index());
                        (Some(&mut prev[prev_rule_id.index()]), &mut current[0])
                    } else {
                        let (current, prev) = self.rules.split_at_mut(prev_rule_id.index());
                        (Some(&mut prev[0]), &mut current[rule_id.index()])
                    }
                } else {
                    (None, &mut self.rules[rule_id.index()])
                };

                // Update the prev_rule_id for the next run
                prev_rule_id = Some(rule_id);

                // Configure the next rule to visit
                let this_rule_id = rule_id;
                if pkg == rule.w1 {
                    rule_id = rule.n1;
                } else {
                    rule_id = rule.n2;
                }

                // Skip disabled rules
                if !rule.enabled {
                    continue;
                }

                // TODO: The code below is duplicated for the w1 and w2 case, we should deduplicate it
                let (w1, w2) = rule.watched_literals(&self.learnt_rules);
                if pkg == w1.solvable_id && w1.eval(&self.decision_map) == Some(false) {
                    // The first literal is now false!
                    if let Some(variable) =
                        rule.next_unwatched_variable(&self.pool, &self.learnt_rules, &self.decision_map)
                    {
                        rule.w1 = variable;

                        // Remove this rule from its current place in the linked list
                        if let Some(prev_rule) = prev_rule {
                            // Modify the previous rule
                            if prev_rule.n1 == this_rule_id {
                                prev_rule.n1 = rule.n1;
                            } else {
                                prev_rule.n2 = rule.n1;
                            }
                        } else {
                            // This is the first rule in the chain
                            self.watches[pkg.index()] = rule.n1;
                        }

                        // Add it to its new place
                        rule.n1 = self.watches[variable.index()];
                        self.watches[variable.index()] = this_rule_id;

                        continue;
                    } else {
                        // There are no terms left to watch, so the clause is now a unit clause

                        if w2.eval(&self.decision_map) == Some(false) {
                            // Conflict, the remaining watch is already decided and evaluates to false, so we can't set it to true!
                            return Err((w2.solvable_id, this_rule_id));
                        }

                        {
                            let s = self.pool.resolve_solvable(w2.solvable_id).package();
                            println!(
                                "Propagate {} {} = {}",
                                s.record.name,
                                s.record.version,
                                w2.satisfying_value()
                            );
                        }
                        self.decision_map
                            .set(w2.solvable_id, w2.satisfying_value(), level);
                        self.decision_queue
                            .push_back(Decision::new(
                                w2.solvable_id,
                                w2.satisfying_value(),
                            ));
                        self.decision_queue_why.push_back(this_rule_id);

                        continue;
                    }
                } else if pkg == w2.solvable_id && w2.eval(&self.decision_map) == Some(false) {
                    // The second literal is now false!
                    if let Some(variable) =
                        rule.next_unwatched_variable(&self.pool, &self.learnt_rules, &self.decision_map)
                    {
                        rule.w2 = variable;

                        // Remove this rule from its current place in the linked list
                        if let Some(prev_rule) = prev_rule {
                            // Modify the previous rule
                            if prev_rule.n1 == this_rule_id {
                                prev_rule.n1 = rule.n2;
                            } else {
                                prev_rule.n2 = rule.n2;
                            }
                        } else {
                            // This is the first rule in the chain
                            self.watches[pkg.index()] = rule.n2;
                        }

                        // Add it to its new place
                        rule.n2 = self.watches[variable.index()];
                        self.watches[variable.index()] = this_rule_id;

                        continue;
                    } else {
                        // There are no terms left to watch, so the clause is now a unit clause

                        if w1.eval(&self.decision_map) == Some(false) {
                            // Conflict, the remaining watch is already decided and evaluates to false, so we can't set it to true!
                            return Err((w1.solvable_id, this_rule_id));
                        }

                        {
                            let s = self.pool.resolve_solvable(w1.solvable_id).package();
                            println!(
                                "Propagate {} {} = {}",
                                s.record.name,
                                s.record.version,
                                w1.satisfying_value()
                            );
                        }
                        self.decision_map
                            .set(w1.solvable_id, w1.satisfying_value(), level);
                        self.decision_queue
                            .push_back(Decision::new(
                                w1.solvable_id,
                                w1.satisfying_value(),
                            ));
                        self.decision_queue_why.push_back(this_rule_id);

                        continue;
                    }
                } else {
                    // Both watched literals are still true in this rule
                    continue;
                }
            }
        }

        Ok(())
    }

    fn analyze_unsolvable(&mut self, _rule: RuleId, _disable_rules: bool) -> u32 {
        todo!()
    }

    fn analyze(
        &mut self,
        mut current_level: u32,
        mut s: SolvableId,
        mut rule_id: RuleId,
    ) -> (u32, RuleId, Literal) {
        let solvable = self.pool.resolve_solvable(s).package();

        println!(
            "=== Conflict: could not set the value for: {} {}",
            solvable.record.name, solvable.record.version
        );
        print!("Triggered by rule: ");
        self.rules[rule_id.index()].debug(&self.pool);

        let mut seen = HashSet::new();
        let mut causes_at_current_level = 0u32;
        let mut learnt = Vec::new();
        let mut btlevel = 0;
        loop {
            let causes =
                self.rules[rule_id.index()].conflict_causes(s, &self.learnt_rules, &self.pool);

            // Collect literals that imply that `p` should be assigned a given value (triggering a conflict)
            for cause in causes {
                if seen.insert(cause.solvable_id) {
                    let decision_level = self.decision_map.level(cause.solvable_id);
                    if decision_level == current_level {
                        causes_at_current_level += 1;
                    } else if current_level > 1 {
                        learnt.push(cause.invert());
                        btlevel = btlevel.max(decision_level);
                    } else {
                        // A conflict with a decision at level 1 means the problem is unsatisfiable
                        // (otherwise we would "learn" that the decision at level 1 was wrong, but
                        // those decisions are either directly provided by [or derived from] the
                        // user's input)
                        panic!("unsolvable");
                    }
                }
            }

            // Select next literal to look at
            loop {
                s = self.decision_queue.back().unwrap().solvable_id;
                rule_id = *self.decision_queue_why.back().unwrap();

                current_level = self.undo_one();

                // We are interested in the first literal we come across that caused the conflicting
                // assignment
                if seen.contains(&s) {
                    break;
                }
            }

            causes_at_current_level = causes_at_current_level.saturating_sub(1);
            if causes_at_current_level == 0 {
                break;
            }
        }

        let last_literal = self.rules[rule_id.index()].find_literal(s, &self.learnt_rules).invert();
        learnt.push(last_literal);

        // Add the rule
        let rule_id = RuleId::new(self.rules.len());
        let learnt_index = self.learnt_rules.len();
        self.learnt_rules.push(learnt.clone());

        let mut rule = Rule::new(RuleKind::Learnt(
            learnt_index
        ), &self.learnt_rules, &self.pool);

        // Hook the rule up to the watches
        if rule.has_watches() {
            rule.n1 = self.watches[rule.w1.index()];
            self.watches[rule.w1.index()] = rule_id;

            rule.n2 = self.watches[rule.w2.index()];
            self.watches[rule.w2.index()] = rule_id;
        }

        // Store it
        self.rules.push(rule);

        println!("Learnt disjunction:");
        for lit in learnt {
            let s = self.pool.resolve_solvable(lit.solvable_id).package();
            let yes_no = if lit.negate { "NOT" } else { "" };
            println!("- {yes_no} {} {}", s.record.name, s.record.version);
        }

        // println!("Backtracked from {level} to {btlevel}");

        // print!("Last decision before backtracking: ");
        // let decision = self.decision_queue.back().unwrap();
        // self.pool.resolve_solvable(decision.solvable_id).debug();
        // println!(" = {}", decision.value);

        // Should revert at most to the root level
        let target_level = btlevel.max(1);
        self.revert(target_level);

        print!("Last decision after backtracking: ");
        let decision = self.decision_queue.back().unwrap();
        self.pool.resolve_solvable(decision.solvable_id).debug();
        println!(" = {}", decision.value);

        (target_level, rule_id, last_literal)
    }

    // Unbinds the last decision
    fn undo_one(&mut self) -> u32 {
        let decision = self.decision_queue.pop_back().unwrap();
        self.decision_map.reset(decision.solvable_id);
        self.decision_queue_why.pop_back();

        self.propagate_index = self.decision_queue.len();

        let top_decision = self.decision_queue.back().unwrap();
        self.decision_map.level(top_decision.solvable_id)
    }

    fn revert(&mut self, level: u32) {
        while let Some(decision) = self.decision_queue.back() {
            if self.decision_map.level(decision.solvable_id) <= level {
                break;
            }

            self.undo_one();
        }
    }

    fn make_watches(&mut self) {
        // Lower half for removals, upper half for installs
        self.watches = vec![RuleId::null(); self.pool.solvables.len() * 2];

        // Watches are already initialized in the rules themselves, here we initialize the linked list
        for (i, rule) in self.rules.iter_mut().enumerate().skip(1).rev() {
            if !rule.has_watches() {
                // Skip rules without watches
                continue;
            }

            let w1_solvable_index = self.pool.solvables.len() + rule.w1.index();
            rule.n1 = self.watches[w1_solvable_index];
            self.watches[w1_solvable_index] = RuleId::new(i);

            let w2_solvable_index = self.pool.solvables.len() + rule.w2.index();
            rule.n2 = self.watches[w2_solvable_index];
            self.watches[w2_solvable_index] = RuleId::new(i);
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::solvable::Solvable;
    use rattler_conda_types::{PackageRecord, Version};

    fn pool(packages: &[(&str, &str, Vec<&str>)]) -> Pool {
        let mut pool = Pool::new();
        let repo_id = pool.new_repo("");

        for (pkg_name, version, deps) in packages {
            let pkg_name = *pkg_name;
            let version = *version;
            let record = Box::new(PackageRecord {
                arch: None,
                build: "".to_string(),
                build_number: 0,
                constrains: vec![],
                depends: deps.iter().map(|s| s.to_string()).collect(),
                features: None,
                legacy_bz2_md5: None,
                legacy_bz2_size: None,
                license: None,
                license_family: None,
                md5: None,
                name: pkg_name.to_string(),
                noarch: Default::default(),
                platform: None,
                sha256: None,
                size: None,
                subdir: "".to_string(),
                timestamp: None,
                track_features: vec![],
                version: version.parse().unwrap(),
            });

            let solvable_id = pool.add_package(repo_id, Box::leak(record));

            for &dep in deps {
                pool.add_dependency(solvable_id, dep.to_string());
            }
        }

        pool
    }

    fn install(packages: &[&str]) -> SolveJobs {
        let mut jobs = SolveJobs::default();
        for &p in packages {
            jobs.install(p.parse().unwrap());
        }
        jobs
    }

    #[test]
    fn test_unit_propagation_1() {
        let pool = pool(&[("asdf", "1.2.3", vec![])]);
        let mut solver = Solver::new(pool);
        let solved = solver.solve(install(&["asdf"])).unwrap();

        assert_eq!(solved.steps.len(), 1);

        let solvable = solver.pool.resolve_solvable(solved.steps[0].0).package();
        assert_eq!(solvable.record.name, "asdf");
        assert_eq!(solvable.record.version.to_string(), "1.2.3");
    }

    #[test]
    fn test_unit_propagation_nested() {
        let pool = pool(&[
            ("asdf", "1.2.3", vec!["efgh"]),
            ("efgh", "4.5.6", vec![]),
            ("dummy", "42.42.42", vec![]),
        ]);
        let mut solver = Solver::new(pool);
        let solved = solver.solve(install(&["asdf"])).unwrap();

        assert_eq!(solved.steps.len(), 2);

        let solvable = solver.pool.resolve_solvable(solved.steps[0].0).package();
        assert_eq!(solvable.record.name, "asdf");
        assert_eq!(solvable.record.version.to_string(), "1.2.3");

        let solvable = solver.pool.resolve_solvable(solved.steps[1].0).package();
        assert_eq!(solvable.record.name, "efgh");
        assert_eq!(solvable.record.version.to_string(), "4.5.6");
    }

    #[test]
    fn test_resolve_dependencies() {
        let pool = pool(&[
            ("asdf", "1.2.4", vec![]),
            ("asdf", "1.2.3", vec![]),
            ("efgh", "4.5.7", vec![]),
            ("efgh", "4.5.6", vec![]),
        ]);
        let mut solver = Solver::new(pool);
        let solved = solver.solve(install(&["asdf", "efgh"])).unwrap();

        assert_eq!(solved.steps.len(), 2);

        let solvable = solver.pool.resolve_solvable(solved.steps[0].0).package();
        assert_eq!(solvable.record.name, "asdf");
        assert_eq!(solvable.record.version.to_string(), "1.2.4");

        let solvable = solver.pool.resolve_solvable(solved.steps[1].0).package();
        assert_eq!(solvable.record.name, "efgh");
        assert_eq!(solvable.record.version.to_string(), "4.5.7");
    }

    #[test]
    fn test_resolve_with_conflict() {
        let pool = pool(&[
            ("asdf", "1.2.4", vec!["conflicting=1.0.1"]),
            ("asdf", "1.2.3", vec!["conflicting=1.0.0"]),
            ("efgh", "4.5.7", vec!["conflicting=1.0.0"]),
            ("efgh", "4.5.6", vec!["conflicting=1.0.0"]),
            ("conflicting", "1.0.1", vec![]),
            ("conflicting", "1.0.0", vec![]),
        ]);
        let mut solver = Solver::new(pool);
        let solved = solver.solve(install(&["asdf", "efgh"])).unwrap();

        for &(solvable_id, _) in &solved.steps {
            let solvable = solver.pool().resolve_solvable(solvable_id).package();
            let name = solver.pool().resolve_string(solvable.name);
            let version = solver.pool().resolve_string(solvable.version);
            println!("Install {name} {version}");
        }

        assert_eq!(solved.steps.len(), 3);

        let solvable = solver.pool.resolve_solvable(solved.steps[0].0).package();
        assert_eq!(solvable.record.name, "asdf");
        assert_eq!(solvable.record.version.to_string(), "1.2.3");

        let solvable = solver.pool.resolve_solvable(solved.steps[1].0).package();
        assert_eq!(solvable.record.name, "efgh");
        assert_eq!(solvable.record.version.to_string(), "4.5.7");

        let solvable = solver.pool.resolve_solvable(solved.steps[1].0).package();
        assert_eq!(solvable.record.name, "conflicting");
        assert_eq!(solvable.record.version.to_string(), "1.0.0");
    }
}