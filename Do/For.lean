import Do.Return

open Lean

/- Disable the automatic monadic lifting feature described in the paper.
   We want to make it clear that we do not depend on it. -/
set_option autoLift false

/- Iteration -/

syntax "for" ident "in" term "do'" stmt:1 : stmt
syntax "break " : stmt
syntax "continue " : stmt

syntax "break" : expander
syntax "continue" : expander
syntax "lift" : expander

macro_rules
  | `(stmt| expand! $_   in break) => `(stmt| break)                                              -- subsumes (S7, R7, B2, L1)
  | `(stmt| expand! $_   in continue) => `(stmt| continue)                                        -- subsumes (S8, R8, L2)
  | `(stmt| expand! $exp in for $x in $e do' $s) => `(stmt| for $x in $e do' expand! $exp in $s)  -- subsumes (L8, R9)

macro_rules
  | `(d! for $x in $e do' $s) => do  -- (D5), optimized like (1')
    let mut s := s
    let sb ← expandStmt (← `(stmt| expand! break in $s))
    let hasBreak := sb.raw.count (· matches `(stmt| break)) < s.raw.count (· matches `(stmt| break))
    if hasBreak then
      s := sb
    let sc ← expandStmt (← `(stmt| expand! continue in $s))
    let hasContinue := sc.raw.count (· matches `(stmt| continue)) < s.raw.count (· matches `(stmt| continue))
    if hasContinue then
      s := sc
    let mut body ← `(d! $s)
    if hasContinue then
      body ← `(ExceptCpsT.runCatch $body)
    let mut loop ← `(forM $e (fun $x => $body))
    if hasBreak then
      loop ← `(ExceptCpsT.runCatch $loop)
    pure loop
  | `(d! break%$b) =>
    throw <| Macro.Exception.error b "unexpected 'break' outside loop"
  | `(d! continue%$c) =>
    throw <| Macro.Exception.error c "unexpected 'continue' outside loop"

macro_rules
  | `(stmt| expand! break in break) => `(stmt| throw ())                                           -- (B1)
  | `(stmt| expand! break in $e:term) => `(stmt| ExceptCpsT.lift $e)                               -- (B3)
  | `(stmt| expand! break in for $x in $e do' $s) => `(stmt| for $x in $e do' expand! lift in $s)  -- (B8)
  | `(stmt| expand! continue in continue) => `(stmt| throw ())
  | `(stmt| expand! continue in $e:term) => `(stmt| ExceptCpsT.lift $e)
  | `(stmt| expand! continue in for $x in $e do' $s) => `(stmt| for $x in $e do' expand! lift in $s)

macro_rules
  | `(stmt| expand! lift in $e:term) => `(stmt| ExceptCpsT.lift $e)  -- (L3)

macro_rules
  | `(stmt| expand! mut $y in for $x in $e do' $s) => `(stmt| for $x in $e do' { let $y ← get; expand! mut $y in $s })  -- (S9)

variable [Monad m]
variable (ma ma' : m α)
variable (b : Bool)
variable (xs : List α) (act : α → m Unit)

attribute [local simp] map_eq_pure_bind

example [LawfulMonad m] :
    (do' for x in xs do' {
           act x
         })
    =
    xs.forM act
:= by induction xs <;> simp_all!

def ex2 (f : β → α → m β) (init : β) (xs : List α) : m β := do'
  let mut y := init;
  for x in xs do' {
    y ← f y x
  };
  return y

example [LawfulMonad m] (f : β → α → m β) :
    ex2 f init xs = xs.foldlM f init := by
  unfold ex2; induction xs generalizing init <;> simp_all!

@[simp] theorem List.find?_cons {xs : List α} : (x::xs).find? p = if p x then some x else xs.find? p := by
  cases h : p x <;> simp_all!

example (p : α → Bool) : Id.run
    (do' for x in xs do' {
           if p x then {
             return some x
           }
         };
         pure none)
    =
    xs.find? p
:= by induction xs with
      | nil => simp [Id.run, List.find?]
      | cons x => cases h : p x <;> simp_all [Id.run]

variable (p : α → m Bool)

theorem byCases_Bool_bind (x : m Bool) (f g : Bool → m β) (isTrue : f true = g true) (isFalse : f false = g false) : (x >>= f) = (x >>= g) := by
  have : f = g := by
    funext b
    cases b with
    | true  => exact isTrue
    | false => exact isFalse
  rw [this]

theorem eq_findM [LawfulMonad m] :
    (do' for x in xs do' {
           let b ← p x;
           if b then {
             return some x
           }
         };
         pure none)
    =
    xs.findM? p
:= by induction xs with
      | nil => simp!
      | cons x xs ih =>
        rw [List.findM?, ← ih]; simp
        apply byCases_Bool_bind <;> simp

def ex3 [Monad m] (p : α → m Bool) (xss : List (List α)) : m (Option α) := do'
  for xs in xss do' {
    for x in xs do' {
      let b ← p x;
      if b then {
        return some x
      }
    }
  };
  pure none

theorem eq_findSomeM_findM [LawfulMonad m] (xss : List (List α)) :
    ex3 p xss = xss.findSomeM? (fun xs => xs.findM? p) := by
  unfold ex3
  induction xss with
  | nil => simp!
  | cons xs xss ih =>
    simp [List.findSomeM?]
    rw [← ih, ← eq_findM]
    induction xs with
    | nil => simp
    | cons x xs ih => simp; apply byCases_Bool_bind <;> simp [ih]

def List.untilM (p : α → m Bool) : List α → m Unit
  | []    => pure ()
  | a::as => p a >>= fun | true => pure () | false => as.untilM p

theorem eq_untilM [LawfulMonad m] :
  (do' for x in xs do' {
         let b ← p x;
         if b then {
           break
         }
       })
  =
  xs.untilM p
:= by induction xs with
      | nil => simp!
      | cons x xs ih =>
        simp [List.untilM]; rw [← ih]; clear ih
        apply byCases_Bool_bind <;> simp

/-
The notation `[0:10]` is a range from 0 to 10 (exclusively).
-/

#eval do'
  for x in [0:10] do' {
    if x > 5 then {
      break
    };
    for y in [0:x] do' {
      IO.println y;
      break
    };
    IO.println x
  }

#eval do'
  for x in [0:10] do' {
    if x > 5 then {
      break
    };
    IO.println x
  }

#eval do'
  for x in [0:10] do' {
    if x % 2 == 0 then {
      continue
    };
    if x > 5 then {
      break
    };
    IO.println x
  }

#eval do'
  for x in [0:10] do' {
    if x % 2 == 0 then {
      continue
    };
    if x > 5 then {
      return ()
    };
    IO.println x
  }


-- set_option trace.compiler.ir.init true
def ex1 (xs : List Nat) (z : Nat) : Id Nat := do'
  let mut s1 := 0;
  let mut s2 := 0;
  for x in xs do' {
    if x % 2 == 0 then {
      continue
    };
    if x == z then {
      return s1
    };
    s1 := s1 + x;
    s2 := s2 + s1
  };
  return (s1 + s2)

/-
Adding `repeat` and `while` statements
-/

-- The "partial" keyword allows users to define non-terminating functions in Lean.
-- However, we currently cannot reason about them.
@[specialize] partial def loopForever [Monad m] (f : Unit → m Unit) : m Unit :=
  f () *> loopForever f

-- `Loop'` is a "helper" type. It is similar to `Unit`.
-- Its `ForM` instance produces an "infinite" sequence of units.
inductive Loop' where
  | mk : Loop'

instance : ForM m Loop' Unit where
  forM _ f := loopForever f

macro:0 "repeat" s:stmt:1 : stmt => `(stmt| for u in Loop'.mk do' $s)

#eval do'
  let mut i := 0;
  repeat {
    if i > 10 then {
      break
    };
    IO.println i;
    i := i + 1
  };
  return i

macro:0 "while" c:term "do'" s:stmt:1 : stmt => `(stmt| repeat { unless $c do' break; { $s } })

#eval do'
  let mut i := 0;
  while (i < 10) do' {
    IO.println i;
    i := i + 1
  };
  return i
