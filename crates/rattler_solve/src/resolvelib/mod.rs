use std::collections::HashMap;

use conda_provider::{CondaProvider, SubdirData};
use rattler_conda_types::{PackageRecord, RepoDataRecord};
use resolvelib_rs::{NoOpReporter, ResolutionError, Resolver};
use url::Url;

use crate::{SolveError, SolverTask};

mod conda_provider;

/// A [`SolverBackend`] implemented using the `resolvelib` library
pub struct ResolvelibBackend;

impl ResolvelibBackend {
    /// Foo
    pub fn solve<'a>(
        &self,
        task: SolverTask<impl Iterator<Item = &'a [RepoDataRecord]>>,
    ) -> Result<Vec<RepoDataRecord>, SolveError> {
        let subdir_data: Vec<_> = task
            .available_packages
            .map(|records| SubdirData::new(records))
            .collect();

        let packages_by_name: HashMap<_, _> = subdir_data
            .iter()
            .flat_map(|data| data.records)
            .map(|record| (record.file_name.as_str(), record))
            .collect();

        let virtual_packages: Vec<_> = task
            .virtual_packages
            .iter()
            .map(|p| RepoDataRecord {
                file_name: String::default(),
                channel: String::default(),
                url: Url::parse("http://example.com").unwrap(),
                package_record: PackageRecord {
                    arch: None,
                    name: p.name.clone(),
                    noarch: Default::default(),
                    platform: None,
                    sha256: None,
                    size: None,
                    subdir: "".to_string(),
                    timestamp: None,
                    build_number: 0,
                    version: p.version.clone(),
                    build: p.build_string.clone(),
                    depends: Vec::new(),
                    features: None,
                    legacy_bz2_md5: None,
                    legacy_bz2_size: None,
                    license: None,
                    license_family: None,
                    constrains: vec![],
                    md5: None,
                    track_features: vec![],
                },
            })
            .collect();

        let virtual_packages: HashMap<_, _> = virtual_packages
            .iter()
            .map(|r| (r.package_record.name.as_str(), r))
            .collect();

        let provider = CondaProvider::new(subdir_data, virtual_packages.clone());
        let reporter = NoOpReporter::new();
        let resolver = Resolver::new(&provider, &reporter);

        let requirements1: Vec<_> = task.specs.iter().map(|ms| ms.to_string()).collect();
        let requirements2 = requirements1.iter().map(|s| s.as_str()).collect();
        let mut result = resolver
            .resolve_bounded(requirements2, 100_000)
            .map_err(|err| {
                let msgs = match err {
                    ResolutionError::ResolutionImpossible(err) => err
                        .unsatisfied_requirements()
                        .iter()
                        .map(|r| format!("nothing provides requested {}", r.requirement))
                        .collect(),
                    ResolutionError::ResolutionTooDeep(_) => {
                        vec!["resolution too deep".to_string()]
                    }
                };
                SolveError::Unsolvable(msgs)
            })?;

        for value in result.mapping.values_mut() {
            if !value.file_name.ends_with(".conda") {
                let replaced = value
                    .file_name
                    .replace(".tar.bz2", ".conda")
                    .replace(".zip", ".conda");
                if let Some(conda_package) = packages_by_name.get(replaced.as_str()) {
                    *value = *conda_package;
                }
            }
        }

        // Remove virtual packages from results
        result
            .mapping
            .retain(|_, v| !virtual_packages.contains_key(v.package_record.name.as_str()));

        Ok(result.mapping.values().map(|&v| v.clone()).collect())

        // TODO: locked
        // // Create a special pool for records that are already installed or locked.
        // let repo = Repo::new(&pool, "locked");
        // let installed_solvables = add_repodata_records(&pool, &repo, &task.locked_packages);
        //
        // // Also add the installed records to the repodata
        // repo_mapping.insert(repo.id(), repo_mapping.len());
        // all_repodata_records.push(&task.locked_packages);
        //
        // // Favor the currently installed packages
        // for favor_solvable in installed_solvables {
        //     goal.favor(favor_solvable);
        // }

        // TODO: pinned
        // // Create a special pool for records that are pinned and cannot be changed.
        // let repo = Repo::new(&pool, "pinned");
        // let pinned_solvables = add_repodata_records(&pool, &repo, &task.pinned_packages);
        //
        // // Also add the installed records to the repodata
        // repo_mapping.insert(repo.id(), repo_mapping.len());
        // all_repodata_records.push(&task.pinned_packages);
        //
        // // Lock the currently pinned packages
        // for locked_solvable in pinned_solvables {
        //     goal.lock(locked_solvable);
        // }
    }
}
