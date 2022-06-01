/- Basic `do` notation -/

open Lean

declare_syntax_cat stmt
syntax "do'" stmt : term

-- Prevent `if ...` from being parsed as a term
syntax (priority := low) term : stmt
syntax "let" ident "←" stmt:1 ";" stmt : stmt
macro "{" s:stmt "}" : stmt => `($s)

/-
  Remark: we annotate `macro`s and `macro_rules` with their corresponding
  translation/abbreviation id from the paper.
-/

syntax "d!" stmt : term  -- corresponds to `D(s)`

macro_rules
  | `(do' $s) => `(d! $s)  -- (1)

macro_rules
  | `(d! $e:term) => `($e)                                       -- (D1)
  | `(d! let $x ← $s; $s') => `((d! $s) >>= fun $x => (d! $s'))  -- (D2)
  | `(d! $s) => do
    -- fallback rule: try to expand abbreviation
    let s' ← expandMacros s
    if s == s' then
      Macro.throwUnsupported
    else
      `(d! $s')

macro "let" x:ident ":=" e:term ";" s:stmt : stmt => `(let $x ← pure $e; $s)  -- (A1)
-- priority `0` prevents `;` from being used in trailing contexts without braces (see e.g. `:1` above)
macro:0 s₁:stmt ";" s₂:stmt : stmt => `(let x ← $s₁; $s₂)                     -- (A2)
