# Supplemental material for the paper "'do' Unchained: Embracing Local Imperativity in a Purely Functional Language"

This supplement consists of a Lean 4 package containing translation rules and example proofs of equivalence as described in the paper.
Each extension is declared in a separate `.lean` file in the `Do` directory.
`Do/Formal.lean` contains the formalization of the equivalence proof written in a literate style explaining more details not mentioned in the paper.
Each Lean file comes with a corresponding `.html` file rendered using Alectryon that allows for exploring the file including type and goal information in any browser without installing Lean.
The directory `gh-survey` contains simple scripts for aggregating the use of extended `do` notation from Lean projects on GitHub.

## Exploring the supplement with Lean

While the [generic instructions](https://leanprover.github.io/lean4/doc/setup.html) for setting up Lean 4 can be used for interacting with this package, we will give a simplified workflow using the specific version of Lean 4 and a single editor, VS Code, in the following:

* Download and unpack your platform's release of [Lean 4.0.0-nightly-2022-05-19](https://github.com/leanprover/lean4-nightly/releases/tag/nightly-2022-05-19)
* Add the `bin` directory of that archive to your shell's search path, e.g.
```bash
$ export PATH=$PATH:~/Downloads/lean-4.0.0-linux/bin
```
* Install VS Code and open the package in it: `code .`.
  It is very important that `lean` is in the search path of VS Code and that the supplement folder is opened as a workspace, which this command should ensure.
* Open the Extensions tab (`Ctrl+Shift+X`) and install the `lean4` extension (author: `leanprover`).
* You should now have working error diagnostics, go-to-definition, as well as a goal display for tactic proofs in the supplement files!