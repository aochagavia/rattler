use crate::pool::{MatchSpecId, Pool, StringId};
use crate::rules::{Literal, Rule, RuleKind};
use crate::solvable::SolvableId;
use crate::solve_jobs::SolveJobs;

use crate::watch_map::WatchMap;

use crate::decision_tracker::DecisionTracker;
use rattler_conda_types::MatchSpec;
use std::collections::{HashMap, HashSet};
use std::fmt::{Display, Formatter};

#[derive(Copy, Clone, PartialOrd, Ord, Eq, PartialEq, Debug)]
pub(crate) struct RuleId(u32);

impl RuleId {
    pub(crate) fn new(index: usize) -> Self {
        Self(index as u32)
    }

    fn install_root() -> Self {
        Self(0)
    }

    fn index(self) -> usize {
        self.0 as usize
    }

    fn is_null(self) -> bool {
        self.0 == u32::MAX
    }

    pub(crate) fn null() -> RuleId {
        RuleId(u32::MAX)
    }
}

#[derive(Copy, Clone, Eq, PartialEq)]
pub(crate) struct Decision {
    pub(crate) solvable_id: SolvableId,
    pub(crate) value: bool,
    pub(crate) derived_from: RuleId,
}

impl Decision {
    pub(crate) fn new(solvable: SolvableId, value: bool, derived_from: RuleId) -> Self {
        Self {
            solvable_id: solvable,
            value,
            derived_from,
        }
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

pub struct Solver {
    pool: Pool,

    rules: Vec<Rule>,
    watches: WatchMap,

    learnt_rules: Vec<Vec<Literal>>,
    learnt_rules_start: RuleId,

    decision_tracker: DecisionTracker,
}

impl Solver {
    /// Create a solver, using the provided pool
    pub fn new(pool: Pool) -> Self {
        Self {
            rules: Vec::new(),
            watches: WatchMap::new(),
            learnt_rules: Vec::new(),
            learnt_rules_start: RuleId(0),
            decision_tracker: DecisionTracker::new(pool.nsolvables()),
            pool,
        }
    }

    pub fn pool(&self) -> &Pool {
        &self.pool
    }

    /// Creates a string for each 'problem' that the solver still has which it encountered while
    /// solving the matchspecs. Use this function to print the existing problems to string.
    fn solver_problems(&self) -> Vec<String> {
        Vec::new()
    }

    /// Solves the provided `jobs` and returns a transaction from the found solution.
    ///
    /// Returns an error if problems remain unsolved.
    pub fn solve(&mut self, jobs: SolveJobs) -> Result<Transaction, Vec<String>> {
        // TODO: sanity check that solvables inside jobs.lock and jobs.favor are unique

        // Clear state
        self.pool.root_solvable_mut().clear();
        self.decision_tracker.clear();
        self.rules = vec![Rule::new(RuleKind::InstallRoot, &[], &self.pool)];
        self.learnt_rules.clear();

        // Favored map
        let mut favored_map = HashMap::new();
        for &favored_id in &jobs.favor {
            let name_id = self.pool.resolve_solvable_inner(favored_id).package().name;
            favored_map.insert(name_id, favored_id);
        }

        // Initialize the root solvable with the requested packages as dependencies
        let mut visited_solvables = HashSet::default();
        for match_spec in &jobs.install {
            let match_spec_id = self.pool.intern_matchspec(match_spec.to_string());
            let root_solvable = self.pool.root_solvable_mut();
            root_solvable.push(match_spec_id);

            // Recursively add rules for the current dep
            self.add_rules_for_root_dep(&mut visited_solvables, &favored_map, match_spec_id);
        }

        // Initialize rules ensuring only a single candidate per package name is installed
        for candidates in self.pool.packages_by_name.values() {
            // Each candidate gets a rule with each other candidate
            for (i, &candidate) in candidates.iter().enumerate() {
                for &other_candidate in &candidates[i + 1..] {
                    self.rules.push(Rule::new(
                        RuleKind::Forbids(candidate, other_candidate),
                        &self.learnt_rules,
                        &self.pool,
                    ));
                }
            }
        }

        // All new rules are learnt after this point
        self.learnt_rules_start = RuleId::new(self.rules.len());

        // Create watches chains
        self.make_watches();

        // Run SAT
        self.run_sat(&jobs.install, &jobs.lock);

        let remaining_problems = self.solver_problems();
        if remaining_problems.is_empty() {
            let steps = self
                .decision_tracker
                .stack()
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
            Err(remaining_problems)
        }
    }

    fn add_rules_for_root_dep(
        &mut self,
        visited: &mut HashSet<SolvableId>,
        favored_map: &HashMap<StringId, SolvableId>,
        dep: MatchSpecId,
    ) {
        let mut candidate_stack = Vec::new();

        // Gather direct candidates for the dependency
        {
            let candidates = Pool::get_candidates(
                &self.pool.match_specs,
                &self.pool.strings_to_ids,
                &self.pool.solvables,
                &self.pool.packages_by_name,
                &mut self.pool.match_spec_to_candidates,
                favored_map,
                dep,
            );
            for &candidate in candidates {
                if visited.insert(candidate) {
                    candidate_stack.push(candidate);
                }
            }
        }

        // Process candidates, adding their dependencies recursively
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
                    favored_map,
                    dep,
                );

                for &dep_candidate in dep_candidates {
                    if visited.insert(dep_candidate) {
                        candidate_stack.push(dep_candidate);
                    }
                }

                // Create requires rule
                self.rules.push(Rule::new(
                    RuleKind::Requires(candidate, dep),
                    &self.learnt_rules,
                    &self.pool,
                ));
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
                )
                .to_vec();

                for dep in dep_forbidden {
                    self.rules.push(Rule::new(
                        RuleKind::Constrains(candidate, dep),
                        &self.learnt_rules,
                        &self.pool,
                    ));
                }
            }
        }

        // Root has a requirement on this match spec
        self.rules.push(Rule::new(
            RuleKind::Requires(SolvableId::root(), dep),
            &self.learnt_rules,
            &self.pool,
        ));
    }

    fn run_sat(&mut self, top_level_requirements: &[MatchSpec], locked_solvables: &[SolvableId]) {
        let level = match self.install_root_solvable() {
            Ok(new_level) => new_level,
            Err(_) => panic!("install root solvable failed"),
        };

        if self.decide_top_level_assertions(level, locked_solvables).is_err() {
            panic!("propagate assertions failed");
        };

        if self.decide_top_level_exclusions(top_level_requirements).is_err() {
            panic!("decide top level exclusions failed");
        }

        if let Err((_, _, cause)) = self.propagate(level) {
            self.analyze_unsolvable(cause, false);
            panic!("Propagate after installing root failed");
        }

        if self.resolve_dependencies(level).is_err() {
            panic!("Resolve dependencies failed");
        }
    }

    fn install_root_solvable(&mut self) -> Result<u32, ()> {
        assert!(self.decision_tracker.is_empty());
        self.decision_tracker
            .try_add_decision(Decision::new(SolvableId::root(), true, RuleId::install_root()), 1)
            .expect("bug: solvable was already decided!");
        Ok(1)
    }

    fn decide_top_level_assertions(
        &mut self,
        level: u32,
        locked_solvables: &[SolvableId],
    ) -> Result<(), ()> {
        println!("=== Deciding assertions");

        // Assertions derived from locked dependencies
        for &locked_solvable_id in locked_solvables {
            // For each locked solvable, decide that other solvables with the same name are
            // forbidden
            let name = self
                .pool
                .resolve_solvable_inner(locked_solvable_id)
                .package()
                .name;
            if let Some(other_candidates) = self.pool.packages_by_name.get(&name) {
                for &other_candidate in other_candidates {
                    if other_candidate != locked_solvable_id {
                        self.decision_tracker.try_add_decision(
                            Decision::new(other_candidate, false, RuleId::install_root()),
                            level,
                        )?;
                    }
                }
            }
        }

        // Assertions derived from requirements that cannot be fulfilled
        for (i, rule) in self.rules.iter().enumerate() {
            if let RuleKind::Requires(solvable_id, _) = rule.kind {
                if !rule.has_watches() {
                    // A requires rule without watches means it has a single literal (i.e.
                    // there are no candidates)
                    let decided = self.decision_tracker.try_add_decision(
                        Decision::new(solvable_id, false, RuleId::new(i)),
                        level,
                    )?;

                    if decided {
                        println!(
                            "Set {} = false",
                            self.pool.resolve_solvable_inner(solvable_id).display()
                        );
                    }
                }
            }
        }

        Ok(())
    }

    fn decide_top_level_exclusions(
        &mut self,
        top_level_requirements: &[MatchSpec],
    ) -> Result<(), ()> {
        println!("=== Deciding exclusions");
        for req in top_level_requirements {
            let name = req.name.as_deref().unwrap();

            let Some(candidates) = self.pool.strings_to_ids.get(name).and_then(|name_id| self.pool.packages_by_name.get(name_id)) else {
                return Ok(());
            };
            let non_matching = candidates.iter().filter(|solvable_id| {
                let solvable = &self.pool.solvables[solvable_id.index()];
                !req.matches(solvable.package().record)
            });

            for &solvable_id in non_matching {
                let decided = self
                    .decision_tracker
                    .try_add_decision(Decision::new(solvable_id, false, RuleId::new(0)), 1)?;
                if decided {
                    println!(
                        "{} = false",
                        self.pool.resolve_solvable_inner(solvable_id).display()
                    );
                }
            }
        }

        Ok(())
    }

    /// Resolves all dependencies
    fn resolve_dependencies(&mut self, mut level: u32) -> Result<u32, ()> {
        let mut i = 0;
        loop {
            if i >= self.rules.len() {
                break;
            }

            let (required_by, candidate) = {
                let rule = &self.rules[i];
                i += 1;

                // We are only interested in requires rules
                let RuleKind::Requires(solvable_id, deps) = rule.kind else {
                    continue;
                };

                // Consider only rules in which we have decided to install the solvable
                if self.decision_tracker.assigned_value(solvable_id) != Some(true) {
                    continue;
                }

                // Consider only rules in which no candidates have been installed
                let candidates = self.pool.match_spec_to_candidates[deps.index()]
                    .as_deref()
                    .unwrap();
                if candidates
                    .iter()
                    .any(|&c| self.decision_tracker.assigned_value(c) == Some(true))
                {
                    continue;
                }

                // Get the first candidate that is undecided and should be installed
                //
                // This assumes that the packages have been provided in the right order when the solvables were created
                // (most recent packages first)
                (
                    solvable_id,
                    candidates
                        .iter()
                        .cloned()
                        .find(|&c| self.decision_tracker.assigned_value(c).is_none())
                        .unwrap(),
                )
            };

            // Assumption: there are multiple candidates, otherwise this would have already been handled
            // by unit propagation
            self.create_branch();
            level =
                self.set_propagate_learn(level, candidate, required_by, true, RuleId::new(i))?;

            // if level < orig_level {
            //     return Err(level);
            // }

            // We have made progress, and should look at all rules in the next iteration
            i = 0;
        }

        // We just went through all rules and there are no choices left to be made
        Ok(level)
    }

    fn set_propagate_learn(
        &mut self,
        mut level: u32,
        solvable: SolvableId,
        required_by: SolvableId,
        disable_rules: bool,
        rule_id: RuleId,
    ) -> Result<u32, ()> {
        level += 1;

        println!(
            "=== Install {} at level {level} (required by {})",
            self.pool.resolve_solvable_inner(solvable).display(),
            self.pool.resolve_solvable_inner(required_by).display(),
        );

        self.decision_tracker
            .try_add_decision(Decision::new(solvable, true, rule_id), level)
            .expect("bug: solvable was already decided!");

        loop {
            let r = self.propagate(level);
            let Err((conflicting_solvable, attempted_value, conflicting_rule)) = r else {
                // Propagation succeeded
                println!("=== Propagation succeeded");
                break;
            };

            {
                let solvable = self
                    .pool
                    .resolve_solvable_inner(conflicting_solvable)
                    .display();
                println!(
                    "=== Propagation conflicted: could not set {solvable} to {attempted_value}"
                );
                print!("During unit propagation for rule: ");
                self.rules[conflicting_rule.index()].debug(&self.pool);
                let decision = self
                    .decision_tracker
                    .stack()
                    .iter()
                    .find(|d| d.solvable_id == conflicting_solvable)
                    .unwrap();
                print!(
                    "Previously decided value: {}. Derived from: ",
                    !attempted_value
                );
                self.rules[decision.derived_from.index()].debug(&self.pool);
            }

            if level == 1 {
                // Is it really unsolvable if we are back to level 1?
                println!("=== UNSOLVABLE");
                for decision in self.decision_tracker.stack() {
                    let rule = &self.rules[decision.derived_from.index()];
                    let level = self.decision_tracker.level(decision.solvable_id);
                    let action = if decision.value { "install" } else { "forbid" };

                    if let RuleKind::Forbids(_, _) = rule.kind {
                        // Skip forbids rules, to reduce noise
                        continue;
                    }

                    print!(
                        "* ({level}) {action} {}",
                        self.pool
                            .resolve_solvable_inner(decision.solvable_id)
                            .display()
                    );
                    print!(". Reason: ");
                    rule.debug(&self.pool);
                }
                self.analyze_unsolvable(conflicting_rule, disable_rules);
                return Err(());
            }

            let (new_level, learned_rule_id, literal) =
                self.analyze(level, conflicting_solvable, conflicting_rule);
            level = new_level;

            println!("=== Backtracked to level {level}");

            // Optimization: propagate right now, since we know that the rule is a unit clause
            let decision = literal.satisfying_value();
            self.decision_tracker
                .try_add_decision(
                    Decision::new(literal.solvable_id, decision, learned_rule_id),
                    level,
                )
                .expect("bug: solvable was already decided!");
            println!(
                "=== Propagate after learn: {} = {decision}",
                self.pool
                    .resolve_solvable_inner(literal.solvable_id)
                    .display()
            );
        }

        Ok(level)
    }

    fn create_branch(&mut self) {
        // TODO: we should probably keep info here for backtracking
    }

    fn propagate(&mut self, level: u32) -> Result<(), (SolvableId, bool, RuleId)> {
        // Learnt assertions
        let learnt_rules_start = self.learnt_rules_start.index();
        for (i, rule) in self.rules[learnt_rules_start..].iter().enumerate() {
            let RuleKind::Learnt(learnt_index) = rule.kind else {
                unreachable!();
            };

            let literals = &self.learnt_rules[learnt_index];
            if literals.len() > 1 {
                continue;
            }

            debug_assert!(!literals.is_empty());

            let literal = literals[0];
            let decision = literal.satisfying_value();
            let rule_id = RuleId::new(learnt_rules_start + i);

            let decided = self
                .decision_tracker
                .try_add_decision(Decision::new(literal.solvable_id, decision, rule_id), level)
                .map_err(|_| (literal.solvable_id, decision, rule_id))?;

            if decided {
                let s = self.pool.resolve_solvable_inner(literal.solvable_id);
                println!("Propagate assertion {} = {}", s.display(), decision);
            }
        }

        // Watched literals
        while let Some(decision) = self.decision_tracker.next_unpropagated() {
            let pkg = decision.solvable_id;

            // Propagate, iterating through the linked list of rules that watch this solvable
            let mut old_predecessor_rule_id: Option<RuleId>;
            let mut predecessor_rule_id: Option<RuleId> = None;
            let mut rule_id = self.watches.first_rule_watching_solvable(pkg);
            while !rule_id.is_null() {
                if predecessor_rule_id == Some(rule_id) {
                    panic!("Linked list is circular!");
                }

                // This is a convoluted way of getting mutable access to the current and the previous rule,
                // which is necessary when we have to remove the current rule from the list
                let (predecessor_rule, rule) = if let Some(prev_rule_id) = predecessor_rule_id {
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
                old_predecessor_rule_id = predecessor_rule_id;
                predecessor_rule_id = Some(rule_id);

                // Configure the next rule to visit
                let this_rule_id = rule_id;
                rule_id = rule.next_watched_rule(pkg);

                if let Some((watched_literals, watch_index)) =
                    rule.watch_turned_false(pkg, self.decision_tracker.map(), &self.learnt_rules)
                {
                    // One of the watched literals is now false
                    if let Some(variable) = rule.next_unwatched_variable(
                        &self.pool,
                        &self.learnt_rules,
                        self.decision_tracker.map(),
                    ) {
                        debug_assert!(!rule.watched_literals.contains(&variable));

                        self.watches.update_watched(
                            predecessor_rule,
                            rule,
                            this_rule_id,
                            watch_index,
                            pkg,
                            variable,
                        );

                        // Make sure the right predecessor is kept for the next iteration (i.e. the
                        // current rule is no longer a predecessor of the next one; the current
                        // rule's predecessor is)
                        predecessor_rule_id = old_predecessor_rule_id;
                    } else {
                        // We could not find another literal to watch, which means the remaining
                        // watched literal can be set to true
                        let remaining_watch_index = match watch_index {
                            0 => 1,
                            1 => 0,
                            _ => unreachable!(),
                        };

                        let remaining_watch = watched_literals[remaining_watch_index];
                        let decided = self
                            .decision_tracker
                            .try_add_decision(
                                Decision::new(
                                    remaining_watch.solvable_id,
                                    remaining_watch.satisfying_value(),
                                    this_rule_id,
                                ),
                                level,
                            )
                            .map_err(|_| (remaining_watch.solvable_id, true, this_rule_id))?;

                        if decided {
                            match rule.kind {
                                RuleKind::InstallRoot
                                | RuleKind::Requires(_, _)
                                | RuleKind::Constrains(_, _)
                                | RuleKind::Learnt(_) => {
                                    print!(
                                        "Propagate {} = {}. ",
                                        self.pool
                                            .resolve_solvable_inner(remaining_watch.solvable_id)
                                            .display(),
                                        remaining_watch.satisfying_value()
                                    );
                                    rule.debug(&self.pool);
                                }
                                // Skip logging for forbids, which is so noisy
                                RuleKind::Forbids(_, _) => {}
                            }
                        }
                    }
                }
            }
        }

        Ok(())
    }

    fn analyze_unsolvable(&mut self, _rule: RuleId, _disable_rules: bool) {
        // todo!()
    }

    fn analyze(
        &mut self,
        mut current_level: u32,
        mut s: SolvableId,
        mut rule_id: RuleId,
    ) -> (u32, RuleId, Literal) {
        let mut seen = HashSet::new();
        let mut causes_at_current_level = 0u32;
        let mut learnt = Vec::new();
        let mut btlevel = 0;

        // println!("=== ANALYZE");

        let mut first_iteration = true;
        let mut s_value;
        loop {
            // TODO: we should be able to get rid of the branching, always retrieving the whole list
            // of literals, since the hash set will ensure we aren't considering the conflicting
            // solvable after the first iteration
            let causes = if first_iteration {
                first_iteration = false;
                self.rules[rule_id.index()].literals(&self.learnt_rules, &self.pool)
            } else {
                self.rules[rule_id.index()].conflict_causes(s, &self.learnt_rules, &self.pool)
            };

            debug_assert!(!causes.is_empty());

            // print!("level = {current_level}; rule: ");
            // self.rules[rule_id.index()].debug(&self.pool);

            // Collect literals that imply that `s` should be assigned a given value (triggering a conflict)
            for cause in causes {
                if seen.insert(cause.solvable_id) {
                    let decision_level = self.decision_tracker.level(cause.solvable_id);
                    // let decision = self
                    //     .decision_tracker
                    //     .assigned_value(cause.solvable_id)
                    //     .unwrap();
                    // println!(
                    //     "- {} = {} (level {decision_level})",
                    //     self.pool.solvables[cause.solvable_id.index()].display(),
                    //     decision
                    // );
                    if decision_level == current_level {
                        causes_at_current_level += 1;
                    } else if current_level > 1 {
                        let learnt_literal = Literal {
                            solvable_id: cause.solvable_id,
                            negate: self
                                .decision_tracker
                                .assigned_value(cause.solvable_id)
                                .unwrap(),
                        };
                        learnt.push(learnt_literal);
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
                let (last_decision, last_decision_level) = self.decision_tracker.undo_last();

                s = last_decision.solvable_id;
                s_value = last_decision.value;
                rule_id = last_decision.derived_from;

                current_level = last_decision_level;

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

        let last_literal = Literal {
            solvable_id: s,
            negate: s_value,
        };
        learnt.push(last_literal);

        // Add the rule
        let rule_id = RuleId::new(self.rules.len());
        let learnt_index = self.learnt_rules.len();
        self.learnt_rules.push(learnt.clone());

        let mut rule = Rule::new(
            RuleKind::Learnt(learnt_index),
            &self.learnt_rules,
            &self.pool,
        );

        if rule.has_watches() {
            self.watches.start_watching(&mut rule, rule_id);
        }

        // Store it
        self.rules.push(rule);

        println!("Learnt disjunction:");
        for lit in learnt {
            let yes_no = if lit.negate { "NOT " } else { "" };
            println!(
                "- {yes_no}{}",
                self.pool.resolve_solvable_inner(lit.solvable_id).display()
            );
        }

        // println!("Backtracked from {level} to {btlevel}");

        // print!("Last decision before backtracking: ");
        // let decision = self.decision_queue.back().unwrap();
        // self.pool.resolve_solvable(decision.solvable_id).debug();
        // println!(" = {}", decision.value);

        // Should revert at most to the root level
        let target_level = btlevel.max(1);
        self.decision_tracker.undo_until(target_level);

        (target_level, rule_id, last_literal)
    }

    fn make_watches(&mut self) {
        self.watches.initialize(self.pool.solvables.len());

        // Watches are already initialized in the rules themselves, here we build a linked list for
        // each package (a rule will be linked to other rules that are watching the same package)
        for (i, rule) in self.rules.iter_mut().enumerate() {
            if !rule.has_watches() {
                // Skip rules without watches
                continue;
            }

            self.watches.start_watching(rule, RuleId::new(i));
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use rattler_conda_types::{PackageRecord, Version};
    use std::str::FromStr;

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

    fn transaction_to_string(pool: &Pool, transaction: &Transaction) -> String {
        use std::fmt::Write;
        let mut buf = String::new();
        for &(solvable_id, _) in &transaction.steps {
            writeln!(
                buf,
                "{}",
                pool.resolve_solvable_inner(solvable_id).display()
            )
            .unwrap();
        }

        buf
    }

    #[test]
    fn test_unit_propagation_1() {
        let pool = pool(&[("asdf", "1.2.3", vec![])]);
        let mut solver = Solver::new(pool);
        let solved = solver.solve(install(&["asdf"])).unwrap();

        assert_eq!(solved.steps.len(), 1);

        let solvable = solver
            .pool
            .resolve_solvable_inner(solved.steps[0].0)
            .package();
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

        let solvable = solver
            .pool
            .resolve_solvable_inner(solved.steps[0].0)
            .package();
        assert_eq!(solvable.record.name, "asdf");
        assert_eq!(solvable.record.version.to_string(), "1.2.3");

        let solvable = solver
            .pool
            .resolve_solvable_inner(solved.steps[1].0)
            .package();
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

        let solvable = solver
            .pool
            .resolve_solvable_inner(solved.steps[0].0)
            .package();
        assert_eq!(solvable.record.name, "asdf");
        assert_eq!(solvable.record.version.to_string(), "1.2.4");

        let solvable = solver
            .pool
            .resolve_solvable_inner(solved.steps[1].0)
            .package();
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
            let solvable = solver.pool().resolve_solvable_inner(solvable_id).display();
            println!("Install {solvable}");
        }

        assert_eq!(solved.steps.len(), 3);

        let solvable = solver
            .pool
            .resolve_solvable_inner(solved.steps[0].0)
            .package();
        assert_eq!(solvable.record.name, "conflicting");
        assert_eq!(solvable.record.version.to_string(), "1.0.0");

        let solvable = solver
            .pool
            .resolve_solvable_inner(solved.steps[1].0)
            .package();
        assert_eq!(solvable.record.name, "asdf");
        assert_eq!(solvable.record.version.to_string(), "1.2.3");

        let solvable = solver
            .pool
            .resolve_solvable_inner(solved.steps[2].0)
            .package();
        assert_eq!(solvable.record.name, "efgh");
        assert_eq!(solvable.record.version.to_string(), "4.5.7");
    }

    #[test]
    fn test_resolve_with_nonexisting() {
        let pool = pool(&[
            ("asdf", "1.2.4", vec!["b"]),
            ("asdf", "1.2.3", vec![]),
            ("b", "1.2.3", vec!["idontexist"]),
        ]);
        let mut solver = Solver::new(pool);
        let solved = solver.solve(install(&["asdf"])).unwrap();

        assert_eq!(solved.steps.len(), 1);

        let solvable = solver
            .pool
            .resolve_solvable_inner(solved.steps[0].0)
            .package();
        assert_eq!(solvable.record.name, "asdf");
        assert_eq!(solvable.record.version.to_string(), "1.2.3");
    }

    #[test]
    fn test_resolve_locked_top_level() {
        let pool = pool(&[("asdf", "1.2.4", vec![]), ("asdf", "1.2.3", vec![])]);

        let locked = pool
            .solvables
            .iter()
            .position(|s| {
                if let Some(package) = s.get_package() {
                    package.record.version == Version::from_str("1.2.3").unwrap()
                } else {
                    false
                }
            })
            .unwrap();

        let locked = SolvableId::new(locked);

        let mut solver = Solver::new(pool);
        let mut jobs = install(&["asdf"]);
        jobs.lock(locked);

        let solved = solver.solve(jobs).unwrap();

        assert_eq!(solved.steps.len(), 1);
        let solvable_id = solved.steps[0].0;
        assert_eq!(solvable_id, locked);
    }

    #[test]
    fn test_resolve_ignored_locked_top_level() {
        let pool = pool(&[
            ("asdf", "1.2.4", vec![]),
            ("asdf", "1.2.3", vec!["fgh"]),
            ("fgh", "1.0.0", vec![]),
        ]);

        let locked = pool
            .solvables
            .iter()
            .position(|s| {
                if let Some(package) = s.get_package() {
                    package.record.version == Version::from_str("1.0.0").unwrap()
                } else {
                    false
                }
            })
            .unwrap();

        let locked = SolvableId::new(locked);

        let mut solver = Solver::new(pool);
        let mut jobs = install(&["asdf"]);
        jobs.lock(locked);

        let solved = solver.solve(jobs).unwrap();

        assert_eq!(solved.steps.len(), 1);
        let solvable = solver
            .pool
            .resolve_solvable_inner(solved.steps[0].0)
            .package();
        assert_eq!(solvable.record.name, "asdf");
        assert_eq!(solvable.record.version, Version::from_str("1.2.4").unwrap());
    }

    #[test]
    fn test_resolve_favor_without_conflict() {
        let pool = pool(&[
            ("A", "1", vec![]),
            ("A", "2", vec![]),
            ("B", "1", vec![]),
            ("B", "2", vec![]),
        ]);

        let mut jobs = install(&["A", "B>=2"]);

        // Already installed: A=1; B=1
        let already_installed = pool
            .solvables
            .iter()
            .enumerate()
            .skip(1) // Skip the root solvable
            .filter(|(_, s)| s.package().record.version == Version::from_str("1").unwrap())
            .map(|(i, _)| SolvableId::new(i));

        for solvable_id in already_installed {
            jobs.favor(solvable_id);
        }

        let mut solver = Solver::new(pool);
        let solved = solver.solve(jobs).unwrap();

        let result = transaction_to_string(&solver.pool, &solved);
        insta::assert_snapshot!(result, @r###"
        B 2
        A 1
        "###);
    }

    #[test]
    fn test_resolve_favor_with_conflict() {
        let pool = pool(&[
            ("A", "1", vec!["C=1"]),
            ("A", "2", vec![]),
            ("B", "1", vec!["C=1"]),
            ("B", "2", vec!["C=2"]),
            ("C", "1", vec![]),
            ("C", "2", vec![]),
        ]);

        let mut jobs = install(&["A", "B>=2"]);

        // Already installed: A=1; B=1; C=1
        let already_installed = pool
            .solvables
            .iter()
            .enumerate()
            .skip(1) // Skip the root solvable
            .filter(|(_, s)| s.package().record.version == Version::from_str("1").unwrap())
            .map(|(i, _)| SolvableId::new(i));

        for solvable_id in already_installed {
            jobs.favor(solvable_id);
        }

        let mut solver = Solver::new(pool);
        let solved = solver.solve(jobs).unwrap();

        let result = transaction_to_string(&solver.pool, &solved);
        insta::assert_snapshot!(result, @r###"
        B 2
        C 2
        A 2
        "###);
    }
}
