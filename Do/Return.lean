import Do.Mut

/-! # Early Return -/

open Lean

/- Disable the automatic monadic lifting feature described in the paper.
   We want to make it clear that we do not depend on it. -/
set_option autoLift false

def runCatch [Monad m] (x : ExceptT α m α) : m α :=
  ExceptT.run x >>= fun
    | Except.ok x => pure x
    | Except.error e => pure e

/-- Count syntax nodes satisfying `p`. -/
partial def Lean.Syntax.count (stx : Syntax) (p : Syntax → Bool) : Nat :=
  stx.getArgs.foldl (fun n arg => n + arg.count p) (if p stx then 1 else 0)

syntax "return" term : stmt

syntax "return" : expander

macro_rules
  | `(do' $s) => do  -- (1')
    -- optimization: fall back to original rule (1) if now `return` statement was expanded
    let s' ← expandStmt (← `(stmt| expand! return in $s))
    if s'.raw.count (· matches `(stmt| return $_)) == s.raw.count (· matches `(stmt| return $_)) then
      `(d! $s)
    else
      `(ExceptCpsT.runCatch (d! $s'))

macro_rules
  | `(stmt| expand! return in return $e) => `(stmt| throw $e)          -- (R1)
  | `(stmt| expand! return in $e:term) => `(stmt| ExceptCpsT.lift $e)  -- (R2)

variable [Monad m]
variable (ma ma' : m α)
variable (b : Bool)

example [LawfulMonad m] :
    (do' let x ← ma;
         return x)
    = ma
:= by simp

example : Id.run
    (do' let x := 1; return x)
    = 1
:= rfl

example [LawfulMonad m] :
     (do' if b then {
            let x ← ma;
            return x
          };
          ma')
     =
     (if b then ma else ma')
:= by cases b <;> simp

example [LawfulMonad m] :
    (do' let y ←
           if b then {
             let x ← ma;
             return x
           } else {
             ma'
           };
         pure y)
    =
    (if b then ma else ma')
:= by cases b <;> simp
