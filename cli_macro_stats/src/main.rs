// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

#[macro_use]
extern crate clap;
#[macro_use]
extern crate serde;
#[cfg_attr(test, macro_use)]
extern crate serde_json;

use clap::{App, Arg};
use cpp_parser::args::{Command, CompilationDB};
use cpp_parser::defaults;
use cpp_parser::lexer::buffer::{BufferData, FileInfo, Position};
use cpp_parser::lexer::preprocessor::cache::IfCache;
use cpp_parser::lexer::preprocessor::context::{DefaultContext, IfState, PreprocContext};
use cpp_parser::lexer::preprocessor::include::{IncludeLocator, PathIndex};
use cpp_parser::lexer::preprocessor::macros::{Macro, MacroFunction, MacroObject, MacroType};
use cpp_parser::lexer::source::{self, FileId, SourceMutex};
use cpp_parser::lexer::{Lexer, TLexer, Token};
use crossbeam::channel::{Receiver, Sender};
use crossbeam::crossbeam_channel::unbounded;
use globset::{Glob, GlobSet, GlobSetBuilder};
use hashbrown::{hash_map, HashMap, HashSet};
use num_cpus;
use std::cell::Cell;
use std::collections::BTreeSet;
use std::fs::File;
use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};
use std::{process, thread};

#[derive(Debug, PartialOrd, Ord, PartialEq, Serialize)]
struct Res {
    counter: usize,
    name: String,
    line: u32,
    path: String,
}

impl Eq for Res {}

#[derive(Clone, Debug)]
struct Stats {
    info: FileInfo,
    counter: Cell<usize>,
}

#[derive(Default)]
struct StatsContext {
    default: DefaultContext,
    stats: HashMap<String, Stats>,
}

impl StatsContext {
    fn get_stats(&self) -> &HashMap<String, Stats> {
        &self.stats
    }
}

impl PreprocContext for StatsContext {
    fn add_if(&mut self, state: IfState) {
        self.default.add_if(state);
    }

    fn rm_if(&mut self) {
        self.default.rm_if();
    }

    fn if_state(&self) -> Option<&IfState> {
        self.default.if_state()
    }

    fn if_change(&mut self, state: IfState) {
        self.default.if_change(state);
    }

    fn add_function(&mut self, name: String, mac: MacroFunction) {
        let info = mac.get_file_info().clone();
        self.default.add_function(name.clone(), mac);
        match self.stats.entry(name) {
            hash_map::Entry::Occupied(p) => {
                let p = p.into_mut();
                p.info = info;
            }
            hash_map::Entry::Vacant(p) => {
                p.insert(Stats {
                    info,
                    counter: Cell::new(0),
                });
            }
        }
    }

    fn add_object(&mut self, name: String, mac: MacroObject) {
        let info = mac.get_file_info().clone();
        self.default.add_object(name.clone(), mac);
        match self.stats.entry(name) {
            hash_map::Entry::Occupied(p) => {
                let p = p.into_mut();
                p.info = info;
            }
            hash_map::Entry::Vacant(p) => {
                p.insert(Stats {
                    info,
                    counter: Cell::new(0),
                });
            }
        }
    }

    fn undef(&mut self, name: &str) {
        self.default.undef(name);
    }

    fn defined(&mut self, name: &str) -> bool {
        if self.default.defined(name) {
            if let Some(stat) = self.stats.get(name) {
                stat.counter.set(stat.counter.get() + 1);
            }
            true
        } else {
            self.stats.insert(
                name.to_string(),
                Stats {
                    info: FileInfo::default(),
                    counter: Cell::new(1),
                },
            );
            false
        }
    }

    fn get(&self, name: &str) -> Option<&Macro> {
        let mac = self.default.get(name);
        if mac.is_some() {
            if let Some(stat) = self.stats.get(name) {
                stat.counter.set(stat.counter.get() + 1);
            }
        }
        mac
    }

    fn get_type(&self, name: &str) -> MacroType {
        let typ = self.default.get_type(name);
        if let MacroType::Object(_) = typ {
            if let Some(stat) = self.stats.get(name) {
                stat.counter.set(stat.counter.get() + 1);
            }
        }
        typ
    }

    fn skip_until_next(&self, file: FileId, pos: usize) -> Option<Position> {
        self.default.skip_until_next(file, pos)
    }

    fn save_switch(&self, file: FileId, pos: usize, next: Position) {
        self.default.save_switch(file, pos, next);
    }

    fn new_with_if_cache(if_cache: Arc<IfCache>) -> Self {
        Self {
            default: DefaultContext::new_with_if_cache(if_cache),
            stats: HashMap::default(),
        }
    }
}

impl IncludeLocator for StatsContext {
    fn find(
        &mut self,
        angle: bool,
        path: &str,
        next: bool,
        current: FileId,
        path_index: PathIndex,
    ) -> Option<BufferData> {
        self.default.find(angle, path, next, current, path_index)
    }

    fn get_id(&mut self, path: &PathBuf) -> FileId {
        self.default.get_id(path)
    }

    fn get_path(&self, id: FileId) -> PathBuf {
        self.default.get_path(id)
    }

    fn set_source(&mut self, source: SourceMutex) {
        self.default.set_source(source)
    }

    fn set_sys_paths<P: AsRef<Path>>(&mut self, paths: &[P]) {
        self.default.set_sys_paths(paths);
    }
}

#[derive(Clone, Debug, Hash, PartialEq)]
struct Key {
    info: FileInfo,
    name: String,
}

impl Eq for Key {}

struct JobItem {
    cmd: Command,
    if_cache: Arc<IfCache>,
    source: SourceMutex,
    stats: Arc<Mutex<HashMap<Key, usize>>>,
}

type JobReceiver = Receiver<Option<JobItem>>;
type JobSender = Sender<Option<JobItem>>;

fn consumer(receiver: JobReceiver) {
    while let Ok(job) = receiver.recv() {
        if job.is_none() {
            break;
        }
        let JobItem {
            cmd,
            if_cache,
            source,
            stats,
        } = job.unwrap();
        let file = cmd.file.to_str().unwrap();
        //eprintln!("File {}", file);

        if !file.contains("ecp_25519.c") {
            //continue;
        }

        let mut lexer = Lexer::<StatsContext>::new_from_file(
            cmd.file.to_str().unwrap(),
            source,
            if_cache,
            cmd.opt,
        );

        loop {
            let tok = lexer.next_useful();
            //eprintln!("{:?} -- {:?}", tok, lexer.span());
            if tok == Token::Eof {
                break;
            }
        }

        let context = lexer.get_context();
        let lexer_stats = context.get_stats();

        let mut stats = stats.lock().unwrap();

        for (name, data) in lexer_stats.iter() {
            let k = Key {
                info: data.info.clone(),
                name: name.clone(),
            };
            match stats.entry(k) {
                hash_map::Entry::Occupied(p) => {
                    let c = p.into_mut();
                    *c += data.counter.get();
                }
                hash_map::Entry::Vacant(p) => {
                    p.insert(data.counter.get());
                }
            }
        }
    }
}

fn mk_globset(elems: clap::Values, files: clap::Values) -> GlobSet {
    let mut globset = GlobSetBuilder::new();
    for e in elems {
        if !e.is_empty() {
            if let Ok(glob) = Glob::new(e) {
                globset.add(glob);
            }
        }
    }

    for file in files {
        let mut file = File::open(file).unwrap();
        let mut content = String::new();
        file.read_to_string(&mut content).unwrap();
        for line in content.split('\n').filter(|s| !s.is_empty()) {
            let mut glob = String::new();
            if !line.starts_with('/') {
                glob.push_str("**/");
            }
            glob.push_str(line);
            if line.ends_with('/') {
                glob.push_str("**");
            }
            if let Ok(glob) = Glob::new(&glob) {
                globset.add(glob);
            }
        }
    }

    if let Ok(globset) = globset.build() {
        globset
    } else {
        GlobSet::empty()
    }
}

fn main() {
    let matches = App::new("Macro stats")
        .version(crate_version!())
        .author(&*env!("CARGO_PKG_AUTHORS").replace(':', "\n"))
        .about("Report macro use")
        .arg(
            Arg::with_name("database")
                .help("Compilation database path")
                .short("c")
                .takes_value(true),
        )
        .arg(
            Arg::with_name("exclude")
                .help("Paths to file which contains path pattern")
                .short("x")
                .multiple(true)
                .takes_value(true),
        )
        .arg(
            Arg::with_name("exclude_pattern")
                .help("Path glob to exclude")
                .short("X")
                .multiple(true)
                .takes_value(true),
        )
        .arg(
            Arg::with_name("num_jobs")
                .help("Number of jobs")
                .short("j")
                .value_name("NUMBER")
                .default_value("")
                .takes_value(true),
        )
        .arg(
            Arg::with_name("output")
                .help("Output file/directory")
                .short("o")
                .long("output")
                .default_value("")
                .takes_value(true),
        )
        .get_matches();

    let database = matches.value_of("database").unwrap().to_string();
    let num_jobs = if let Ok(num_jobs) = matches.value_of("num_jobs").unwrap().parse::<usize>() {
        num_jobs
    } else {
        num_cpus::get()
    };

    let exclude = matches.values_of("exclude").unwrap();
    let exclude_pat = matches.values_of("exclude_pattern").unwrap();
    let exclude = mk_globset(exclude_pat, exclude);

    let output = matches.value_of("output").unwrap().to_string();

    let all_stats = Arc::new(Mutex::new(HashMap::default()));
    let source = source::get_source_mutex();
    let if_cache = Arc::new(IfCache::default());

    let (sender, receiver) = unbounded();

    let mut receivers = Vec::with_capacity(num_jobs);
    for i in 0..num_jobs {
        let receiver = receiver.clone();

        let t = thread::Builder::new()
            .name(format!("Consumer {}", i))
            .spawn(|| {
                consumer(receiver);
            })
            .unwrap();

        receivers.push(t);
    }

    let mut sent: HashSet<PathBuf> = HashSet::default();
    let sys_paths = defaults::get_sys_paths();
    for mut cmd in CompilationDB::from_json(&database) {
        let file = if cmd.opt.file.is_absolute() {
            cmd.opt.file.clone()
        } else {
            cmd.opt.current_dir.join(&cmd.opt.file)
        };
        if file.exists() && !sent.contains(&file) {
            cmd.file = file.clone();
            sent.insert(file.clone());

            cmd.opt.sys_paths.extend_from_slice(&sys_paths);
            let mut def = defaults::get_defined();
            def.extend_from_slice(&cmd.opt.def);
            cmd.opt.def = def;

            sender
                .send(Some(JobItem {
                    cmd,
                    if_cache: Arc::clone(&if_cache),
                    source: Arc::clone(&source),
                    stats: Arc::clone(&all_stats),
                }))
                .unwrap();
        }
    }

    // Poison the receiver, now that the producer is finished.
    for _ in 0..num_jobs {
        sender.send(None).unwrap();
    }

    for receiver in receivers {
        if let Err(e) = receiver.join() {
            eprintln!("Error: {:?}", e);
            process::exit(1);
        }
    }

    let all_stats = Arc::try_unwrap(all_stats).unwrap().into_inner().unwrap();
    let mut set = BTreeSet::default();
    let mut total = 0;

    for (Key { info, name }, counter) in all_stats.iter() {
        if let Some(sid) = info.source_id {
            if sid.0 != 0 {
                let path = source.lock().unwrap().get_path(sid);
                let path = path.to_str().unwrap();
                if !exclude.is_match(path) {
                    set.insert(Res {
                        counter: *counter,
                        name: name.clone(),
                        line: info.line,
                        path: path.to_string(),
                    });
                    total += counter;
                }
            }
        }
    }

    let data = serde_json::to_string(&set).unwrap();
    if output.is_empty() {
        println!("{}", data);
    } else {
        let mut file = File::create(output).unwrap();
        file.write_all(data.as_bytes()).unwrap();
    }
}
