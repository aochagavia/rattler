use rattler_conda_types::{parse_matchspec_package_name, MatchSpec, RepoDataRecord, Version};
use resolvelib_rs::{Criterion, Provider, RequirementInformation};
use std::cmp::Ordering;
use std::collections::{HashMap, HashSet};
use std::str::FromStr;

pub struct SubdirData<'a> {
    pub records: &'a [RepoDataRecord],
}

impl<'a> SubdirData<'a> {
    pub fn new(records: &'a [RepoDataRecord]) -> Self {
        Self { records }
    }

    fn query<'this>(
        &'this self,
        match_spec: &'this MatchSpec,
    ) -> impl Iterator<Item = &'a RepoDataRecord> + '_ {
        self.records
            .into_iter()
            .filter(|r| match_spec.matches(&r.package_record))
    }
}

pub struct CondaProvider<'a> {
    subdir_data: Vec<SubdirData<'a>>,
    virtual_packages: HashMap<&'a str, &'a RepoDataRecord>,
}

impl<'a> CondaProvider<'a> {
    pub fn new(
        subdir_data: Vec<SubdirData<'a>>,
        virtual_packages: HashMap<&'a str, &'a RepoDataRecord>,
    ) -> Self {
        Self {
            subdir_data,
            virtual_packages,
        }
    }

    fn query<'this>(
        &'this self,
        match_spec: &'this MatchSpec,
    ) -> impl Iterator<Item = &'a RepoDataRecord> + '_ {
        self.subdir_data
            .iter()
            .flat_map(|data| data.query(match_spec))
    }

    fn find_highest_version(&self, match_spec: &MatchSpec) -> Option<(Version, bool)> {
        // // First try to read from cache
        // let borrow = self.match_spec_cache.borrow();
        // if let Some(result) = borrow.get(match_spec) {
        //     return Some(result.clone());
        // }
        // drop(borrow);

        // Determine the highest version as well as the whether all matching records have tracked
        // features.
        let result: Option<(Version, bool)> = self.query(match_spec).fold(None, |init, record| {
            Some(init.map_or_else(
                || {
                    (
                        record.package_record.version.clone(),
                        !record.package_record.track_features.is_empty(),
                    )
                },
                |(version, has_tracked_features)| {
                    (
                        version.max(record.package_record.version.clone()),
                        has_tracked_features && record.package_record.track_features.is_empty(),
                    )
                },
            ))
        });

        // // Store in cache for later
        // if let Some(result) = &result {
        //     self.match_spec_cache
        //         .borrow_mut()
        //         .insert(match_spec.clone(), result.clone());
        // }

        result
    }

    /// Returns the order of two candidates based on rules used by conda.
    fn compare_candidates(&self, r1: &RepoDataRecord, r2: &RepoDataRecord) -> Ordering {
        let a = &r1.package_record;
        let b = &r2.package_record;

        // First compare by "tracked_features". If one of the packages has a tracked feature it is
        // sorted below the one that doesnt have the tracked feature.
        let a_has_tracked_features = a.track_features.is_empty();
        let b_has_tracked_features = b.track_features.is_empty();
        match b_has_tracked_features.cmp(&a_has_tracked_features) {
            Ordering::Less => return Ordering::Less,
            Ordering::Greater => return Ordering::Greater,
            Ordering::Equal => {}
        };

        // Otherwise, select the variant with the highest version
        match a.version.cmp(&b.version) {
            Ordering::Less => return Ordering::Greater,
            Ordering::Greater => return Ordering::Less,
            Ordering::Equal => {}
        };

        // Otherwise, select the variant with the highest build number
        match a.build_number.cmp(&b.build_number) {
            Ordering::Less => return Ordering::Greater,
            Ordering::Greater => return Ordering::Less,
            Ordering::Equal => {}
        };

        // Otherwise, compare the dependencies of the variants. If there are similar
        // dependencies select the variant that selects the highest version of the dependency.
        let a_match_specs: Vec<_> = r1
            .package_record
            .depends
            .iter()
            .map(|d| MatchSpec::from_str(d).unwrap())
            .collect();
        let b_match_specs: Vec<_> = r1
            .package_record
            .depends
            .iter()
            .map(|d| MatchSpec::from_str(d).unwrap())
            .collect();

        let b_specs_by_name: HashMap<_, _> = b_match_specs
            .iter()
            .filter_map(|spec| spec.name.as_ref().map(|name| (name, spec)))
            .collect();

        let a_specs_by_name = a_match_specs
            .iter()
            .filter_map(|spec| spec.name.as_ref().map(|name| (name, spec)));

        let mut total_score = 0;
        for (a_dep_name, a_spec) in a_specs_by_name {
            if let Some(b_spec) = b_specs_by_name.get(&a_dep_name) {
                if &a_spec == b_spec {
                    continue;
                }

                // Find which of the two specs selects the highest version
                let highest_a = self.find_highest_version(a_spec);
                let highest_b = self.find_highest_version(b_spec);

                // Skip version if no package is selected by either spec
                let (a_version, a_tracked_features, b_version, b_tracked_features) = if let (
                    Some((a_version, a_tracked_features)),
                    Some((b_version, b_tracked_features)),
                ) =
                    (highest_a, highest_b)
                {
                    (a_version, a_tracked_features, b_version, b_tracked_features)
                } else {
                    continue;
                };

                // If one of the dependencies only selects versions with tracked features, down-
                // weight that variant.
                if let Some(score) = match a_tracked_features.cmp(&b_tracked_features) {
                    Ordering::Less => Some(-100),
                    Ordering::Greater => Some(100),
                    Ordering::Equal => None,
                } {
                    total_score += score;
                    continue;
                }

                // Otherwise, down-weigh the version with the lowest selected version.
                total_score += match a_version.cmp(&b_version) {
                    Ordering::Less => 1,
                    Ordering::Equal => 0,
                    Ordering::Greater => -1,
                };
            }
        }

        // If ranking the dependencies provides a score, use that for the sorting.
        match total_score.cmp(&0) {
            Ordering::Equal => {}
            ord => return ord,
        };

        // Otherwise, order by timestamp
        b.timestamp.cmp(&a.timestamp)
    }
}

impl<'a> Provider for CondaProvider<'a> {
    type Candidate = &'a RepoDataRecord;
    type Requirement = &'a str;
    type Identifier = &'a str;

    fn identify_candidate(&self, candidate: Self::Candidate) -> Self::Identifier {
        &candidate.package_record.name
    }

    fn identify_requirement(&self, requirement: Self::Requirement) -> Self::Identifier {
        // TODO: we probably want to parse the match specs beforehand, especially now we have
        // sparse loading. Then we won't need hacks like the one below anymore!
        parse_matchspec_package_name(requirement).unwrap()
    }

    fn get_preference(
        &self,
        identifier: Self::Identifier,
        _resolutions: &HashMap<Self::Identifier, Self::Candidate>,
        candidates: &HashMap<Self::Identifier, Criterion<Self::Requirement, Self::Candidate>>,
        backtrack_causes: &[RequirementInformation<Self::Requirement, Self::Candidate>],
    ) -> u64 {
        // prefer the candidate that is a backtrack cause
        for cause in backtrack_causes {
            if self.identify_requirement(cause.requirement) == identifier {
                return 0;
            }
            if cause.parent.is_some()
                && identifier == self.identify_candidate(cause.parent.unwrap())
            {
                return 0;
            }
        }

        candidates[identifier].candidates.len() as u64
    }

    fn find_matches(
        &self,
        identifier: Self::Identifier,
        requirements: &HashMap<Self::Identifier, Vec<Self::Requirement>>,
        incompatibilities: &HashMap<Self::Identifier, Vec<Self::Candidate>>,
    ) -> Vec<Self::Candidate> {
        let requirements = &requirements[identifier];
        let bad_versions: HashSet<_> = incompatibilities[identifier]
            .iter()
            .map(|record| (&record.package_record.version, &record.package_record.build))
            .collect();

        let mut all_candidates = Vec::new();
        let mut first_requirement = true;
        for requirement in requirements {
            let requirement = MatchSpec::from_str(requirement).unwrap();

            if let Some(&candidate) = self
                .virtual_packages
                .get(requirement.name.as_deref().unwrap())
            {
                all_candidates.push(candidate);
                break;
            }

            let mut requirement_candidates = Vec::new();
            for s in &self.subdir_data {
                requirement_candidates.extend(s.query(&requirement));
            }

            if first_requirement {
                all_candidates = requirement_candidates;
            } else {
                // Different requirements will return different candidates, and it only makes sense
                // to keep candidates that were compatible with all requirements
                all_candidates.retain(|c| requirement_candidates.contains(c));
            }

            first_requirement = false;
        }

        // Remove incompatible candidates
        all_candidates.retain(|candidate| {
            !bad_versions.contains(&(
                &candidate.package_record.version,
                &candidate.package_record.build,
            ))
        });

        // Sort according to version (highest first)
        let mut all_candidates: Vec<_> = all_candidates.into_iter().collect();
        all_candidates.sort_unstable_by(|c1, c2| self.compare_candidates(c1, c2));

        // println!("all_candidates for requirements: {requirements:?}");
        // for candidate in &all_candidates {
        //     println!(
        //         "{} {}",
        //         candidate.package_record.name, candidate.package_record.build
        //     );
        // }

        all_candidates
    }

    fn is_satisfied_by(&self, requirement: Self::Requirement, candidate: Self::Candidate) -> bool {
        let requirement = MatchSpec::from_str(requirement).unwrap();
        assert_eq!(
            requirement.name.as_ref(),
            Some(&candidate.package_record.name)
        );
        requirement.matches(&candidate.package_record)
    }

    fn get_dependencies(&self, candidate: Self::Candidate) -> Vec<Self::Requirement> {
        candidate
            .package_record
            .depends
            .iter()
            .map(|s| s.as_str())
            .collect()
    }

    fn get_constraints(&self, candidate: Self::Candidate) -> Vec<Self::Requirement> {
        candidate
            .package_record
            .constrains
            .iter()
            .map(|s| s.as_str())
            .collect()
    }
}
