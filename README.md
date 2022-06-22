# Supplemental material for the paper "'do' Unchained: Embracing Local Imperativity in a Purely Functional Language (Functional Pearl)"

This supplement consists of a Lean 4 package containing translation rules and example proofs of equivalence as described in the paper.
Each extension is declared in a separate `.lean` file in the `Do` directory:

```
Do/
  Basic.lean     # Section 2, Figure 1
  Mut.lean       # Section 2, Figures 3 & 5
  Return.lean    # Section 3
  For.lean       # Section 4

  LazyList.lean  # nondeterministic monad implementation used in `Mut.lean` examples
```

`Do/Formal.lean` contains the formalization of the equivalence proof written in a literate style explaining more details not mentioned in the paper.
Each Lean file comes with a corresponding `.html` file rendered using Alectryon that allows for exploring the file including type and goal information in any browser without installing Lean.
The directory `gh-survey` contains simple scripts for aggregating the use of extended `do` notation from Lean projects on GitHub.

## Exploring the supplement with Lean

While the [generic instructions](https://leanprover.github.io/lean4/doc/setup.html) for setting up Lean 4 can be used for interacting with this package, we will give a simplified workflow using the specific version of Lean 4 and a single editor, VS Code, that minimizes changes to the host machines in the following:

* Download and unpack your platform's release of [Lean 4.0.0-nightly-2022-06-01](https://github.com/leanprover/lean4-nightly/releases/tag/nightly-2022-06-01)
* Add the `bin` directory of that archive to your shell's search path, e.g.
```bash
$ export PATH=$PATH:~/Downloads/lean-4.0.0-linux/bin
```
* Install VS Code and open the package in it: `code .`.
  It is very important that `lean` is in the search path of VS Code and that the supplement folder is opened as a workspace, which this command should ensure.
* Open the Extensions tab (`Ctrl+Shift+X`) and install the `lean4` extension (author: `leanprover`).
* You should now have working error diagnostics, go-to-definition, as well as a goal display for tactic proofs in the supplement files!

## Regenerating the HTML output

The versions of [Alectryon](https://github.com/cpitclaudel/alectryon) and its Lean 4 backend [LeanInk](https://github.com/leanprover/LeanInk) used to generate the accompanying HTML files are archived in the folders `alectryon` and `LeanInk`, respectively.
To regenerate the output, first install the local Alectryon version as described in its readme:
``` bash
python3 -m pip install ./alectryon
```
After ensuring that `alectryon` is now in your `PATH`, running `make html` (optionally preceded by `make clean`) should regenerate the files.
