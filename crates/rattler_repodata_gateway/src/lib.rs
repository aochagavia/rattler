#![deny(missing_docs)]

//! `rattler_repodata_gateway` is a crate that provides functionality to interact with Conda
//! repodata. It currently provides functionality to download and cache `repodata.json` files
//! through the [`fetch::fetch_repo_data`] function.
//!
//! In the future this crate will also provide more high-level functionality to query information
//! about specific packages from different sources.
//!
//! # Install
//! Add the following to your *Cargo.toml*:
//!
//! ```toml
//! [dependencies]
//! rattler_repodata_gateway = "0.2.0"
//! ```
//!
//! or run
//!
//! ```bash
//! cargo add rattler_repodata_gateway
//! ```
//!
//! # Examples
//! Below is a basic example that shows how to retrieve and cache the repodata for a conda channel
//! using the [`fetch::fetch_repo_data`] function:
//!
//! ```rust
//! use std::{path::Path, default::Default};
//! use reqwest::Client;
//! use url::Url;
//! use rattler_repodata_gateway::fetch;
//!
//! #[tokio::main]
//! async fn main() {
//!     let repodata_url = Url::parse("https://conda.anaconda.org/conda-forge/osx-64/").unwrap();
//!     let client = Client::new();
//!     let cache = Path::new("./cache");
//!
//!     let result = fetch::fetch_repo_data(
//!         repodata_url,
//!         client,
//!         cache,
//!         fetch::FetchRepoDataOptions { ..Default::default() }
//!     ).await;
//!
//!     let result = match result {
//!         Err(err) => {
//!             panic!("{:?}", err);
//!         },
//!         Ok(result) => result
//!     };
//!
//!     println!("{:?}", result.cache_state);
//!     println!("{:?}", result.cache_result);
//!     println!("{:?}", result.lock_file);
//!     println!("{:?}", result.repo_data_json_path);
//! }
//! ```

pub mod fetch;
#[cfg(feature = "sparse")]
pub mod sparse;

mod utils;
