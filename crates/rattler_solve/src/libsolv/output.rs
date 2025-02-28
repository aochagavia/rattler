//! Contains business logic to retrieve the results from libsolv after attempting to resolve a conda
//! environment

use crate::libsolv::wrapper::pool::{Pool, StringId};
use crate::libsolv::wrapper::repo::RepoId;
use crate::libsolv::wrapper::solvable::SolvableId;
use crate::libsolv::wrapper::transaction::Transaction;
use crate::libsolv::wrapper::{ffi, solvable};
use rattler_conda_types::RepoDataRecord;
use std::collections::HashMap;

/// Returns which packages should be installed in the environment
///
/// If the transaction contains libsolv operations that are not "install" an error is returned
/// containing their ids.
pub fn get_required_packages(
    pool: &Pool,
    repo_mapping: &HashMap<RepoId, usize>,
    transaction: &Transaction,
    repodata_records: &[&[RepoDataRecord]],
) -> Result<Vec<RepoDataRecord>, Vec<ffi::Id>> {
    let mut required_packages = Vec::new();
    let mut unsupported_operations = Vec::new();

    let solvable_index_id = pool
        .find_interned_str("solvable:repodata_record_index")
        .unwrap();

    // Safe because `transaction.steps` is an active queue
    let transaction_queue = transaction.get_steps();

    for id in transaction_queue.iter() {
        let transaction_type = transaction.transaction_type(id);

        // Retrieve the repodata record corresponding to this solvable
        let (repo_index, solvable_index) =
            get_solvable_indexes(pool, repo_mapping, solvable_index_id, id);
        let repodata_record = &repodata_records[repo_index][solvable_index];

        match transaction_type as u32 {
            ffi::SOLVER_TRANSACTION_INSTALL => {
                required_packages.push(repodata_record.clone());
            }
            _ => {
                unsupported_operations.push(transaction_type);
            }
        }
    }

    if !unsupported_operations.is_empty() {
        return Err(unsupported_operations);
    }

    Ok(required_packages)
}

fn get_solvable_indexes(
    pool: &Pool,
    repo_mapping: &HashMap<RepoId, usize>,
    solvable_index_id: StringId,
    id: SolvableId,
) -> (usize, usize) {
    let solvable = id.resolve_raw(pool);
    let solvable_index =
        solvable::lookup_num(solvable.as_ptr(), solvable_index_id).unwrap() as usize;

    // Safe because there are no active mutable borrows of any solvable at this stage
    let repo_id = RepoId::from_ffi_solvable(unsafe { solvable.as_ref() });

    let repo_index = repo_mapping[&repo_id];

    (repo_index, solvable_index)
}
