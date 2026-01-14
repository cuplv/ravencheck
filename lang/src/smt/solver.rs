// use std::ffi::{OsStr, OsString};

#[derive(Debug)]
pub struct SolverConfig {
    program: String,
    args: Vec<String>,
}

impl SolverConfig {

    /// Current default is [`Self::cvc5`].
    pub fn default() -> Self { Self::cvc5() }

    /** 
    This config invokes the [CVC5 solver](https://cvc5.github.io/)
    with the following arguments:
    ```ignore
    [
        "--lang", "smt2",
        "--force-logic", "ALL",
        "--full-saturate-quant",
        "--finite-model-find",
    ]
    ```
    Without `--full-saturate-quant` and `--finite-model-find`,
    CVC5 tends to return Unknown instead of Sat or Unsat.
    See <https://github.com/cvc5/cvc5/issues/6274> for details.
    */
    pub fn cvc5() -> Self {
        let mut conf = Self::program("cvc5");
        conf.add_args_array([
            "--lang", "smt2",
            "--force-logic", "ALL",
            "--full-saturate-quant",
            "--finite-model-find",
        ]);
        conf
    }
    /** 
    Create a new `SolverConfig` for the given program,
    with no arguments.
    ```
    use ravenlang::SolverConfig;

    let conf = SolverConfig::program("z3");
    ```
    */
    pub fn program<T: ToString>(name: T) -> Self {
        Self {
            program: name.to_string(),
            args: Vec::new(),
        }
    }
    /**
    Add an argument to a `SolverConfig`.
    ```
    use ravenlang::SolverConfig;

    let mut conf = SolverConfig::cvc5();
    conf.add_arg("--mbqi");
    ```
    */
    pub fn add_arg<T: ToString>(&mut self, arg: T) {
        self.args.push(arg.to_string())
    }
    /**
    Add an array of arguments to a `SolverConfig`.
    ```
    use ravenlang::SolverConfig;

    let mut conf = SolverConfig::default();
    conf.add_args_array([
        "--mbqi",
        "--mbqi-check-timeout", "0",
    ]);
    ```
    */
    pub fn add_args_array<T: ToString, const N: usize>(&mut self, args: [T;N]) {
        for a in args {
            self.add_arg(a)
        }
    }
    /// Add a `Vec<String>` of arguments to a `SolverConfig`.
    pub fn add_args_vec(&mut self, mut args: Vec<String>) {
        self.args.append(&mut args)
    }

    pub fn context_builder(&self) -> easy_smt::ContextBuilder {
        println!("{:?}", self);
        let mut builder = easy_smt::ContextBuilder::new();
        builder.solver(&self.program, &self.args);
        builder
    }
}
