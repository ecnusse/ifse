use std::{fs, path::Path};

use itertools::Itertools;
use tempdir::TempDir;
use uuid::Uuid;
use walkdir::WalkDir;

use super::{FuzzResult, Fuzzer};

/// LibFuzzer stub.
#[derive(Debug)]
pub struct LibFuzzer {
    pub verbosity: isize,
    pub max_time_in_milliseconds: Option<usize>,
    pub rss_limit_mb: Option<usize>
}

impl Default for LibFuzzer {
    fn default() -> Self {
        Self::new()
    }
}

impl LibFuzzer {
    const TIMEOUT_EXIT_CODE: i32 = 0;
    const TARGET_FOUND_EXIT_CODE: i32 = 77;
    const CTRL_C_CODE: i32 = 72;

    pub fn new() -> Self {
        Self {
            verbosity: 0,
            max_time_in_milliseconds: None,
            rss_limit_mb: Some(0),
        }
    }

    fn prepare_files(&self, program_text: &str) -> TempDir {
        let work_dir = TempDir::new(Uuid::new_v4().to_string().as_str()).unwrap();
        fs::write(work_dir.path().join("fuzz.cpp"), program_text).unwrap();
        work_dir
    }

    fn compile(&self, fuzz_src: &Path) {
        let mut cmd = std::process::Command::new("clang++");
        cmd.arg("-std=c++11")
            .arg("-g")
            .arg("-fsanitize=fuzzer")
            .arg("-DCUSTOM_MUTATOR")
            .arg("-o")
            .arg(fuzz_src.with_extension(""))
            .arg(fuzz_src);
        let output = cmd.output().unwrap();
        if !output.status.success() {
            panic!(
                "Failed to compile fuzz program: {}",
                String::from_utf8_lossy(&output.stderr)
            );
        }
    }
}

impl Fuzzer for LibFuzzer {
    fn set_option(&mut self, option: &str, value: &str) {
        match option {
            "verbosity" => self.verbosity = value.parse().unwrap(),
            "max_time_in_milliseconds" => {
                self.max_time_in_milliseconds = Some(value.parse().unwrap())
            }
            "rss_limit_mb" => {
                self.rss_limit_mb = Some(value.parse().unwrap())
            }
            _ => panic!("Unknown option: {}", option),
        }
    }

    fn get_option(&self, option: &str) -> Option<String> {
        match option {
            "verbosity" => Some(self.verbosity.to_string()),
            "max_time_in_milliseconds" => self
                .max_time_in_milliseconds
                .map(|x| x.to_string())
                .or(Some("".to_string())),
            _ => panic!("Unknown option: {}", option),
        }
    }

    fn fuzz(&self, program_text: &str) -> Result<FuzzResult, i32> {
        let work_dir = self.prepare_files(program_text);
        self.compile(&work_dir.path().join("fuzz.cpp"));
        let mut cmd = std::process::Command::new(work_dir.path().join("fuzz"));
        cmd.current_dir(work_dir.path());
        if let Some(max) = self.max_time_in_milliseconds {
            cmd.arg(format!("-max_total_time={}", (max / 1000).max(1)).as_str());
        }
        cmd.arg(format!("-error_exitcode={}", Self::TARGET_FOUND_EXIT_CODE).as_str());
        let artifact_dir = work_dir.path().join("output");
        std::fs::create_dir(artifact_dir.as_path()).unwrap();
        cmd.arg(format!("-artifact_prefix={}/", artifact_dir.as_path().display()).as_str());
        if let Some(rss_limit) = self.rss_limit_mb {
            cmd.arg(format!("-rss_limit_mb={}", rss_limit));
        }
        cmd.arg("-malloc_limit_mb=0");
        let mut child = cmd.spawn().unwrap();
        let status = child.wait().unwrap();
        let return_code = status.code().unwrap();
        match return_code {
            Self::TARGET_FOUND_EXIT_CODE => {
                let artifact_files = WalkDir::new(artifact_dir.as_path())
                    .min_depth(1)
                    .into_iter()
                    .filter_entry(|entry| {
                        entry.depth() == 1
                            && entry.file_name().to_str().unwrap() != self.output_file()
                    })
                    .filter_map(|item| item.ok())
                    .collect_vec();
                assert_eq!(1, artifact_files.len());

                let bytes = fs::read(artifact_dir.join(self.output_file())).unwrap_or_default();

                Ok(FuzzResult::Success(bytes))
            }
            Self::TIMEOUT_EXIT_CODE | Self::CTRL_C_CODE => Ok(FuzzResult::Timeout),
            _ => Err(return_code),
        }
    }

    fn id(&self) -> &str {
        "cpp:libfuzzer"
    }
}
