use crate::id::MatchSpecId;
use crate::id::{RepoId, StringId};
use rattler_conda_types::{PackageRecord, Version};
use std::fmt::{Display, Formatter};

pub(crate) struct SolvableDisplay<'a> {
    name: &'a str,
    version: Option<&'a Version>,
    build: Option<&'a str>,
}

impl Display for SolvableDisplay<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)?;
        if let Some(version) = self.version {
            write!(f, " {}", version)?;
        }

        if let Some(build) = self.build {
            if !build.is_empty() {
                write!(f, " {}", build)?;
            }
        }

        Ok(())
    }
}

pub struct PackageSolvable<'a> {
    pub(crate) repo_id: RepoId,
    pub(crate) dependencies: Vec<MatchSpecId>,
    pub(crate) constrains: Vec<MatchSpecId>,
    pub(crate) record: &'a PackageRecord,
    pub(crate) name: StringId,
    pub metadata: SolvableMetadata,
}

impl PackageSolvable<'_> {
    pub fn repo_id(&self) -> RepoId {
        self.repo_id
    }
}

#[derive(Default)]
pub struct SolvableMetadata {
    pub original_index: Option<usize>,
}

pub(crate) struct Solvable<'a> {
    pub(crate) inner: SolvableInner<'a>,
}

pub(crate) enum SolvableInner<'a> {
    Root(Vec<MatchSpecId>),
    Package(PackageSolvable<'a>),
}

impl<'a> Solvable<'a> {
    pub(crate) fn new_root() -> Solvable<'static> {
        Solvable {
            inner: SolvableInner::Root(Vec::new()),
        }
    }

    pub(crate) fn new_package(repo_id: RepoId, name: StringId, record: &'a PackageRecord) -> Self {
        Self {
            inner: SolvableInner::Package(PackageSolvable {
                repo_id,
                record,
                name,
                dependencies: Vec::new(),
                constrains: Vec::new(),
                metadata: SolvableMetadata::default(),
            }),
        }
    }

    pub(crate) fn display(&self) -> SolvableDisplay {
        match &self.inner {
            SolvableInner::Root(_) => SolvableDisplay {
                name: "root",
                version: None,
                build: None,
            },
            SolvableInner::Package(p) => SolvableDisplay {
                name: &p.record.name,
                version: Some(&p.record.version),
                build: Some(&p.record.build),
            },
        }
    }

    pub(crate) fn root_mut(&mut self) -> &mut Vec<MatchSpecId> {
        match &mut self.inner {
            SolvableInner::Root(match_specs) => match_specs,
            _ => panic!("unexpected package solvable!"),
        }
    }

    pub(crate) fn get_package(&self) -> Option<&PackageSolvable> {
        match &self.inner {
            SolvableInner::Root(_) => None,
            SolvableInner::Package(p) => Some(p),
        }
    }

    pub(crate) fn get_package_mut<'b>(&'b mut self) -> Option<&'b mut PackageSolvable<'a>> {
        match &mut self.inner {
            SolvableInner::Root(_) => None,
            SolvableInner::Package(p) => Some(p),
        }
    }

    pub fn package(&self) -> &PackageSolvable {
        self.get_package().expect("unexpected root solvable")
    }

    pub fn package_mut<'b>(&'b mut self) -> &'b mut PackageSolvable<'a> {
        self.get_package_mut().expect("unexpected root solvable")
    }
}
