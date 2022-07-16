import Do.Basic
import Do.LazyList

/-! # Local Mutation -/

open Lean

/-! Disable the automatic monadic lifting feature described in the paper.
   We want to make it clear that we do not depend on it. -/
set_option autoLift false

syntax "let" "mut" ident ":=" term ";" stmt : stmt
syntax ident ":=" term : stmt
syntax "if" term "then" stmt "else" stmt:1 : stmt

declare_syntax_cat expander
-- generic syntax for traversal-like functions S_y/R/B/L
syntax "expand!" expander "in" stmt:1 : stmt
syntax "mut" ident : expander  -- corresponds to `S_y`

-- generic traversal rules
macro_rules
  | `(stmt| expand! $exp in let $x ← $s; $s') => `(stmt| let $x ← expand! $exp in $s; expand! $exp in $s')                -- subsumes (R3, B4, L4)
  | `(stmt| expand! $exp in let mut $x := $e; $s') => `(stmt| let mut $x := $e; expand! $exp in $s')                      -- subsumes (R4, B5, L5)
  | `(stmt| expand! $_ in $x:ident := $e) => `(stmt| $x:ident := $e)                                                      -- subsumes (R5, B6, L6)
  | `(stmt| expand! $exp in if $e then $s₁ else $s₂) => `(stmt| if $e then expand! $exp in $s₁ else expand! $exp in $s₂)  -- subsumes (S6, R6, B7, L7)
  | `(stmt| expand! $exp in $s) => do
    let s' ← expandStmt s
    `(stmt| expand! $exp in $s')


macro_rules
  | `(d! let mut $x := $e; $s) => `(let $x := $e; StateT.run' (d! expand! mut $x in $s) $x) -- (D3)
  | `(d! $x:ident := $_:term) =>
      -- `s!"..."` is an interpolated string. For more information, see https://leanprover.github.io/lean4/doc/stringinterp.html.
      throw <| Macro.Exception.error x s!"variable '{x.getId}' is not reassignable in this scope"
  | `(d! if $e then $s₁ else $s₂) => `(if $e then d! $s₁ else d! $s₂)                       -- (D4)

macro_rules
  | `(stmt| expand! mut $_ in $e:term) => `(stmt| StateT.lift $e)  -- (S1)
  | `(stmt| expand! mut $y in let $x ← $s; $s') =>                -- (S2)
    if x == y then
      throw <| Macro.Exception.error x s!"cannot shadow 'mut' variable '{x.getId}'"
    else
      `(stmt| let $x ← expand! mut $y in $s; let $y ← get; expand! mut $y in $s')
  | `(stmt| expand! mut $y in let mut $x := $e; $s') =>           -- (S3)
    if x == y then
      throw <| Macro.Exception.error x s!"cannot shadow 'mut' variable '{x.getId}'"
    else
      `(stmt| let mut $x := $e; expand! mut $y in $s')
  | `(stmt| expand! mut $y in $x:ident := $e) =>
    if x == y then
      `(stmt| set $e)                                             -- (S5)
    else
      `(stmt| $x:ident := $e)                                     -- (S4)

macro:0 "let" "mut" x:ident "←" s:stmt:1 ";" s':stmt : stmt => `(let y ← $s; let mut $x := y; $s') -- (A3)
macro:0 x:ident "←" s:stmt:1 : stmt => `(let y ← $s; $x:ident := y)                                -- (A4)
-- a variant of (A4) since we technically cannot make the above macro a `stmt`
macro:0 x:ident "←" s:stmt:1 ";" s':stmt : stmt => `(let y ← $s; $x:ident := y; $s')
macro "if" e:term "then" s₁:stmt:1 : stmt => `(if $e then $s₁ else pure ())                        -- (A5)
macro "unless" e:term "do'" s₂:stmt:1 : stmt => `(if $e then pure () else $s₂)                     -- (A6)

/-
The `variable` command instructs Lean to insert the declared variables as bound variables
in definitions that refer to them.
-/

variable [Monad m]
variable (ma ma' : m α)

/-
  Mark `map_eq_pure_bind` as a simplification lemma.
  It is a theorem for
  `f <$> x = x >>= pure (f a)`
-/
attribute [local simp] map_eq_pure_bind

/-
  Remark: an `example` in Lean is like a "nameless" definition, and it does not update the environment.
  It is useful for writing tests.
-/

/-
  The instance `[LawfulMonad m]` contains the monadic laws.
  For more information, see https://github.com/leanprover/lean4/blob/v4.0.0-m4/src/Init/Control/Lawful.lean
-/

example [LawfulMonad m] :
    (do' let mut x ← ma;
         pure x : m α)
    =
    ma
:= by simp

example [LawfulMonad m] :
    (do' let mut x ← ma;
         x ← ma';
         pure x)
    =
    (ma >>= fun _ => ma')
:= by simp

/- The command `#check_failure <term>` succeeds only if `<term>` fails to be elaborated. -/

#check_failure do'
  let mut x ← ma;
  let x ← ma';  -- cannot shadow 'mut' variable 'x'
  pure x

#check_failure do'
  x ← ma;  -- variable 'x' is not reassignable in this scope
  pure ()

variable (b : Bool)

-- The following equivalence is true even if `m` does not satisfy the monadic laws.
example :
    (do' if b then {
           discard ma
         })
    =
    (if b then discard ma else pure ())
:= rfl

theorem simple [LawfulMonad m] :
    (do' let mut x ← ma;
         if b then {
           x ← ma'
         };
         pure x)
    =
    (ma >>= fun x => if b then ma' else pure x)
:= by cases b <;> simp

example [LawfulMonad m] (f : α → α → α) :
    (do' let mut x ← ma;
         let y ←
           if b then {
             x ← ma;
             ma'
           } else {
             ma'
           };
         pure (f x y))
    =
    (ma >>= fun x => if b then ma >>= fun x => ma' >>= fun y => pure (f x y) else ma' >>= fun y => pure (f x y))
:= by cases b <;> simp

/-
Nondeterminism example from Section 2.
-/
def choose := @List.toLazy

def ex : LazyList Nat := do'
  let mut x := 0;
  let y ← choose [0, 1, 2, 3];
  x := x + 1;
  guard (x < 3);
  pure (x + y)

-- Generate all solutions
#eval ex.toList
