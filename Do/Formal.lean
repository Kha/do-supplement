import Do.For  -- import `runCatch`
import Lean

/-!
==========================================
Formalization of Extended `do` Translation
==========================================

This is the supplement file to the paper "‘do’ Unchained: Embracing Local Imperativity in a Purely
Functional Language".
It contains an intrinsically typed representation of the paper's syntax of `do` statements as well
of their translation functions and an equivalence proof thereof to a simple denotational semantics. -/

/-!
Contexts
--------

We represent contexts as lists of types and assignments of them as heterogeneous lists over these types.
As is common with lists, contexts grow to the left in our presentation.
The following encoding of heterogeneous lists avoids the universe bump of the usual inductive definition
(https://lists.chalmers.se/pipermail/agda/2010/001826.html). -/
def HList : List (Type u) → Type u
  | []      => PUnit
  | α :: αs => α × HList αs

@[matchPattern] abbrev HList.nil : HList [] := ⟨⟩
@[matchPattern] abbrev HList.cons (a : α) (as : HList αs) : HList (α :: αs) := (a, as)

/-! We overload the common list notations `::` and `[e, ...]` for `HList`. -/

infixr:67 " :: " => HList.cons

syntax (name := hlistCons) "[" term,* "]" : term
macro_rules (kind := hlistCons)
  | `([])          => `(HList.nil)
  | `([$x])        => `(HList.cons $x [])
  | `([$x, $xs,*]) => `(HList.cons $x [$xs,*])

/-!
Lean's very general, heterogeneous definition of `++` causes some issues with our overloading above in terms
such as `a ++ [b]`, so we restrict it to the `List` interpretation in the following, which is sufficient for our purposes.
-/

local macro_rules
  | `($a ++ $b) => `(List.append $a $b)

abbrev Assg Γ := HList Γ

/-! Updating a heterogeneous list at a given, guaranteed in-bounds index. -/

def HList.set : {αs : List (Type u)} → HList αs → (i : Fin αs.length) → αs.get i → HList αs
  | _ :: _, _ :: as, ⟨0,          _⟩, b => b :: as
  | _ :: _, a :: as, ⟨Nat.succ n, h⟩, b => a :: set as ⟨n, Nat.le_of_succ_le_succ h⟩ b
  | [],     [],      _,               _ => []

/-!
We write `∅` for empty contexts and assignments and `Γ ⊢ α` for the type of values of type `α` under the context `Γ`
- that is, the function type from an assignment to `α`.
-/
instance : EmptyCollection (Assg ∅) where
  emptyCollection := []

instance : CoeSort (List (Type u)) (Type u) := ⟨Assg⟩

notation:30 Γ " ⊢ " α => Assg Γ → α

def Assg.drop : Assg (α :: Γ) → Assg Γ
  | _ :: as => as

/-! In one special case, we will need to manipulate contexts from the right, i.e. the outermost scope. -/

def Assg.extendBot (x : α) : {Γ : _} → Assg Γ → Assg (Γ ++ [α])
  | [],     []      => [x]
  | _ :: _, a :: as => a :: extendBot x as

def Assg.dropBot : {Γ : _} → Assg (Γ ++ [α]) → Assg Γ
  | [],     _       => []
  | _ :: _, a :: as => a :: dropBot as

/-!
Intrinsically Typed Representation of `do` Statements
-----------------------------------------------------

where

* m: base monad
* ω: `return` type, `m ω` is the type of the entire `do` block
* Γ: `do`-local immutable context
* Δ: `do`-local mutable context
* b: `break` allowed
* c: `continue` allowed
* α: local result type, `m α` is the type of the statement

The constructor signatures are best understood by comparing them with the corresponding typing rules in the paper.
Note that the choice of de Bruijn indices changes/simplifies some parts, such as obviating freshness checks (`x ∉ Δ`).
-/

inductive Stmt (m : Type → Type u) (ω : Type) : (Γ Δ : List Type) → (b c : Bool) → (α : Type) → Type _ where
  | expr (e : Γ ⊢ Δ ⊢ m α) : Stmt m ω Γ Δ b c α
  | bind (s : Stmt m ω Γ Δ b c α) (s' : Stmt m ω (α :: Γ) Δ b c β) : Stmt m ω Γ Δ b c β  -- let _ ← s; s'
  | letmut (e : Γ ⊢ Δ ⊢ α) (s : Stmt m ω Γ (α :: Δ) b c β) : Stmt m ω Γ Δ b c β  -- let mut _ := e; s
  | assg (x : Fin Δ.length) (e : Γ ⊢ Δ ⊢ Δ.get x) : Stmt m ω Γ Δ b c Unit  -- x := e
  | ite (e : Γ ⊢ Δ ⊢ Bool) (s₁ s₂ : Stmt m ω Γ Δ b c α) : Stmt m ω Γ Δ b c α  -- if e then s₁ else s₂
  | ret (e : Γ ⊢ Δ ⊢ ω) : Stmt m ω Γ Δ b c α   -- return e
  | sfor (e : Γ ⊢ Δ ⊢ List α) (s : Stmt m ω (α :: Γ) Δ true true Unit) : Stmt m ω Γ Δ b c Unit  -- for _ in e do s
  | sbreak : Stmt m ω Γ Δ true c α  -- break
  | scont : Stmt m ω Γ Δ b true α  -- continue

/-! Neutral statements are a restriction of the above type. -/

inductive Neut (ω α : Type) : (b c : Bool) → Type _ where
  | val (a : α) : Neut ω α b c
  | ret (o : ω) : Neut ω α b c
  | rbreak : Neut ω α true c
  | rcont : Neut ω α b true

/-! We elide `Neut.val` where unambiguous. -/

instance : Coe α (Neut ω α b c) := ⟨Neut.val⟩
instance : Coe (Id α) (Neut ω α b c) := ⟨Neut.val⟩

/-!
We write `e[ρ][σ]` for the substitution of both contexts in `e`, a simple application in this encoding.
`σ[x ↦ v]` updates `σ` at `v` (a de Bruijn index). -/

macro:max (priority := high) e:term:max noWs "[" ρ:term "]" "[" σ:term "]" : term => `($e $ρ $σ)
macro:max (priority := high) σ:term:max noWs "[" x:term " ↦ " v:term "]" : term => `(HList.set $σ $x $v)

/-!
Dynamic Evaluation Function
---------------------------

A direct encoding of the paper's operational semantics as a denotational function,
generalized over an arbitrary monad.
Note that the immutable context `ρ` is accumulated (`v :: ρ`) and passed explicitly instead of immutable
bindings being substituted immediately as that is a better match for the above definition of `Stmt`.
Iteration over the values of the given list in the `for` case introduces a nested, mutually recursive helper
function, with termination of the mutual bundle following from a size argument over the statement primarily
and the length of the list in the `for` case secondarily.
-/

@[simp] def Stmt.eval [Monad m] (ρ : Assg Γ) : Stmt m ω Γ Δ b c α → Assg Δ → m (Neut ω α b c × Assg Δ)
  | expr e, σ => e[ρ][σ] >>= fun v => pure ⟨v, σ⟩
  | bind s s', σ =>
    -- defining this part as a separate definition helps Lean with the termination proof
    let rec cont val
      | ⟨Neut.val v, σ'⟩ => val v σ'
      -- the `Neut` type family forces us to repeat these cases as the LHS/RHS indices are not identical
      | ⟨Neut.ret o, σ'⟩ => pure ⟨Neut.ret o, σ'⟩
      | ⟨Neut.rbreak, σ'⟩ => pure ⟨Neut.rbreak, σ'⟩
      | ⟨Neut.rcont, σ'⟩ => pure ⟨Neut.rcont, σ'⟩
    s.eval ρ σ >>= cont (fun v σ' => s'.eval (v :: ρ) σ')
  | letmut e s, σ =>
    s.eval ρ (e[ρ][σ], σ) >>= fun ⟨r, σ'⟩ => pure ⟨r, σ'.drop⟩
  -- `x` is a valid de Bruijn index into `σ` by definition of `assg`
  | assg x e, σ => pure ⟨(), σ[x ↦ e[ρ][σ]]⟩
  | ite e s₁ s₂, σ => if e[ρ][σ] then s₁.eval ρ σ else s₂.eval ρ σ
  | ret e, σ => pure ⟨Neut.ret e[ρ][σ], σ⟩
  | sfor e s, σ =>
    let rec go σ
      | [] => pure ⟨(), σ⟩
      | a::as =>
        s.eval (a :: ρ) σ >>= fun
        | ⟨(), σ'⟩ => go σ' as
        | ⟨Neut.rcont, σ'⟩ => go σ' as
        | ⟨Neut.rbreak, σ'⟩ => pure ⟨(), σ'⟩
        | ⟨Neut.ret o, σ'⟩ => pure ⟨Neut.ret o, σ'⟩
    go σ e[ρ][σ]
  | sbreak, σ => pure ⟨Neut.rbreak, σ⟩
  | scont, σ => pure ⟨Neut.rcont, σ⟩
termination_by
  eval s _ => (sizeOf s, 0)
  eval.go as => (sizeOf s, as.length)

/-! At the top-level statement, the contexts are empty, no loop control flow statements are allowed, and the return and result type are identical. -/

abbrev Do m α := Stmt m α ∅ ∅ false false α

def Do.eval [Monad m] (s : Do m α) : m α :=  -- corresponds to the reduction rule `do s ⇒ v` in the paper
  Stmt.eval ∅ s ∅ >>= fun
    | ⟨Neut.val a, _⟩ => pure a
    | ⟨Neut.ret o, _⟩ => pure o

notation "⟦" s "⟧" => Do.eval s

/-!
Translation Functions
---------------------

We adjust the immutable context where necessary.
The mutable context does not have to be adjusted. -/

@[simp] def Stmt.mapAssg (f : Assg Γ' → Assg Γ) : Stmt m ω Γ Δ b c β → Stmt m ω Γ' Δ b c β
  | expr e => expr (e ∘ f)
  | bind s₁ s₂ => bind (s₁.mapAssg f) (s₂.mapAssg (fun (a :: as) => (a :: f as)))
  | letmut e s => letmut (e ∘ f) (s.mapAssg f)
  | assg x e => assg x (e ∘ f)
  | ite e s₁ s₂ => ite (e ∘ f) (s₁.mapAssg f) (s₂.mapAssg f)
  | ret e => ret (e ∘ f)
  | sfor e s => sfor (e ∘ f) (s.mapAssg (fun (a :: as) => (a :: f as)))
  | sbreak => sbreak
  | scont => scont

/-! Let us write `f ∘ₑ e` for the composition of `f : α → β` with `e : Γ ⊢ Δ ⊢ α`, which we will use to rewrite embedded terms. -/

infixr:90 " ∘ₑ "  => fun f e => fun ρ σ => f e[ρ][σ]

/-!
The formalization of `S` creates some technical hurdles. Because it operates on the outer-most mutable binding,
we have to operate on that context from the right, from which we lose some helpful definitional equalities and
have to rewrite types using nested proofs instead.

The helper function `shadowSnd` is particularly interesting because it shows how the shadowing in
translation rules (S2) and (S9) is expressed in our de Bruijn encoding: The context `α :: β :: α :: Γ`
corresponds, in this order, to the `y` that has just been bound to the value of `get`, then `x` from the
respective rule, followed by the `y` of the outer scope. We encode the shadowing of `y` by dropping the
third element from the context as well as the assignment. We are in fact forced to do so because the corresponding
branches of `S` would not otherwise typecheck. The only mistake we could still make is to drop the wrong `α` value
from the assignment, which (speaking from experience) would eventually be caught by the correctness proof.
-/
@[simp] def S [Monad m] : Stmt m ω Γ (Δ ++ [α]) b c β → Stmt (StateT α m) ω (α :: Γ) Δ b c β
/-(S1)-/ | Stmt.expr e => Stmt.expr (StateT.lift ∘ₑ unmut e)
/-(S2)-/ | Stmt.bind s₁ s₂ => Stmt.bind (S s₁) (Stmt.bind (Stmt.expr (fun _ _ => get)) (Stmt.mapAssg shadowSnd (S s₂)))
/-(S3)-/ | Stmt.letmut e s => Stmt.letmut (unmut e) (S s)
         | Stmt.assg x e =>
           if h : x < Δ.length then
/-(S4)-/     Stmt.assg ⟨x, h⟩ (fun (y :: ρ) σ => List.get_append_left .. ▸ e ρ (Assg.extendBot y σ))
           else
/-(S5)-/     Stmt.expr (set (σ := α) ∘ₑ cast (List.get_last h) ∘ₑ unmut e)
/-(S6)-/ | Stmt.ite e s₁ s₂ => Stmt.ite (unmut e) (S s₁) (S s₂)
         -- unreachable case; could be eliminated by a more precise specification of `ω`, but the benefit would be minimal
         | Stmt.ret e => Stmt.ret (unmut e)
/-(S7)-/ | Stmt.sbreak => Stmt.sbreak
/-(S8)-/ | Stmt.scont => Stmt.scont
/-(S9)-/ | Stmt.sfor e s => Stmt.sfor (unmut e) (Stmt.bind (Stmt.expr (fun _ _ => get)) (Stmt.mapAssg shadowSnd (S s)))
where
  @[simp] unmut {β} (e : Γ ⊢ Δ ++ [α] ⊢ β) : α :: Γ ⊢ Δ ⊢ β
    | y :: ρ, σ => e ρ (Assg.extendBot y σ)
  @[simp] shadowSnd {β} : Assg (α :: β :: α :: Γ) → Assg (α :: β :: Γ)
    | a' :: b :: _ :: ρ => a' :: b :: ρ

@[simp] def R [Monad m] : Stmt m ω Γ Δ b c α → Stmt (ExceptT ω m) Empty Γ Δ b c α
/-(R1)-/ | Stmt.ret e => Stmt.expr (throw ∘ₑ e)
/-(R2)-/ | Stmt.expr e => Stmt.expr (ExceptT.lift ∘ₑ e)
/-(R3)-/ | Stmt.bind s s' => Stmt.bind (R s) (R s')
/-(R4)-/ | Stmt.letmut e s => Stmt.letmut e (R s)
/-(R5)-/ | Stmt.assg x e => Stmt.assg x e
/-(R6)-/ | Stmt.ite e s₁ s₂ => Stmt.ite e (R s₁) (R s₂)
/-(R7)-/ | Stmt.sbreak => Stmt.sbreak
/-(R8)-/ | Stmt.scont => Stmt.scont
/-(R9)-/ | Stmt.sfor e s => Stmt.sfor e (R s)

@[simp] def L [Monad m] : Stmt m ω Γ Δ b c α → Stmt (ExceptT Unit m) ω Γ Δ b c α
/-(L1)-/ | Stmt.sbreak => Stmt.sbreak
/-(L2)-/ | Stmt.scont => Stmt.scont
/-(L3)-/ | Stmt.expr e => Stmt.expr (ExceptT.lift ∘ₑ e)
/-(L4)-/ | Stmt.bind s s' => Stmt.bind (L s) (L s')
/-(L5)-/ | Stmt.letmut e s => Stmt.letmut e (L s)
/-(L6)-/ | Stmt.assg x e => Stmt.assg x e
/-(L7)-/ | Stmt.ite e s₁ s₂ => Stmt.ite e (L s₁) (L s₂)
         | Stmt.ret e => Stmt.ret e
/-(L8)-/ | Stmt.sfor e s => Stmt.sfor e (L s)

@[simp] def B [Monad m] : Stmt m ω Γ Δ b c α → Stmt (ExceptT Unit m) ω Γ Δ false c α
/-(B1)-/ | Stmt.sbreak => Stmt.expr (fun _ _ => throw ())
/-(B2)-/ | Stmt.scont => Stmt.scont
/-(B3)-/ | Stmt.expr e => Stmt.expr (ExceptT.lift ∘ₑ e)
/-(B4)-/ | Stmt.bind s s' => Stmt.bind (B s) (B s')
/-(B5)-/ | Stmt.letmut e s => Stmt.letmut e (B s)
/-(B6)-/ | Stmt.assg x e => Stmt.assg x e
/-(B7)-/ | Stmt.ite e s₁ s₂ => Stmt.ite e (B s₁) (B s₂)
         | Stmt.ret e => Stmt.ret e
/-(B8)-/ | Stmt.sfor e s => Stmt.sfor e (L s)

-- (elided in the paper)
@[simp] def C [Monad m] : Stmt m ω Γ Δ false c α → Stmt (ExceptT Unit m) ω Γ Δ false false α
  | Stmt.scont => Stmt.expr (fun _ _ => throw ())
  | Stmt.expr e => Stmt.expr (ExceptT.lift ∘ₑ e)
  | Stmt.bind s s' => Stmt.bind (C s) (C s')
  | Stmt.letmut e s => Stmt.letmut e (C s)
  | Stmt.assg x e => Stmt.assg x e
  | Stmt.ite e s₁ s₂ => Stmt.ite e (C s₁) (C s₂)
  | Stmt.ret e => Stmt.ret e
  | Stmt.sfor e s => Stmt.sfor e (L s)

/-!
The remaining function to be translated is `D`, which is straightforward as well except for its termination proof,
as it recurses on the results of `S` (D3) and `C ∘ B` (D5). Because of rules (S2, S9) that introduce new bindings,
`S` may in fact increase the size of the input, and the same is true for `C` and `B` for the `sizeOf` function
automatically generated by Lean. Thus we introduce a new measure `numExts` that counts the number of special statements
on top of basic `do` notation and prove that all three functions do not increase the size according to that measure.
Because the rules (D3) and (D5) each eliminate such a special statement, it follows that `D` terminates because either
the number of special statements decreases in each case, or it remains the same and the total number of statements decreases.
-/

@[simp] def Stmt.numExts : Stmt m ω Γ Δ b c α → Nat
  | expr _ => 0
  | bind s₁ s₂ => s₁.numExts + s₂.numExts
  | letmut _ s => s.numExts + 1
  | assg _ _ => 1
  | ite _ s₁ s₂ => s₁.numExts + s₂.numExts
  | ret _ => 1
  | sfor _ s => s.numExts + 1
  | sbreak => 1
  | scont => 1

@[simp] theorem Stmt.numExts_mapAssg (f : Assg Γ' → Assg Γ) (s : Stmt m ω Γ Δ b c β) : numExts (mapAssg f s) = numExts s := by
  induction s generalizing Γ' <;> simp [*]

theorem Stmt.numExts_S [Monad m] (s : Stmt m ω Γ (Δ ++ [α]) b c β) : numExts (S s) ≤ numExts s := by
  -- `induction` does not work with non-variable indices, so we first generalize `Δ ++ [α]` into an explicit equation
  revert s
  suffices {Δ': _ } → (s : Stmt m ω Γ Δ' b c β) → (h : Δ' = (Δ ++ [α])) → numExts (S (h ▸ s : Stmt m ω Γ (Δ ++ [α]) b c β)) ≤ numExts s
    from fun s => this s rfl
  intro Δ' s h
  induction s generalizing Δ with
    subst h
  | bind _ _ ih₁ ih₂ => simp [Nat.add_le_add, ih₁ rfl, ih₂ rfl]
  | letmut _ _ ih => simp [Nat.add_le_add, ih (List.cons_append ..).symm]
  | assg => simp; split <;> simp
  | ite _ _ _ ih₁ ih₂ => simp [Nat.add_le_add, ih₁ rfl, ih₂ rfl]
  | sfor _ _ ih => simp [Nat.add_le_add, ih rfl]
  | _ => simp

theorem Stmt.numExts_L_L [Monad m] (s : Stmt m ω Γ Δ b c β) : numExts (L (L s)) ≤ numExts s := by
  induction s <;> simp [Nat.add_le_add, *]

theorem Stmt.numExts_C_B [Monad m] (s : Stmt m ω Γ Δ b c β) : numExts (C (B s)) ≤ numExts s := by
  induction s <;> simp [Nat.add_le_add, numExts_L_L, *]

-- Auxiliary tactic for showing that `D` terminates
macro "D_tac" : tactic =>
  `({simp_wf
     solve
      | apply Prod.Lex.left; assumption
      | apply Prod.Lex.right' <;> simp_arith })

@[simp] def D [Monad m] : Stmt m Empty Γ ∅ false false α → (Γ ⊢ m α)
  | Stmt.expr e => (e[·][∅])
  | Stmt.bind s s' => (fun ρ => D s ρ >>= fun x => D s' (x :: ρ))
  | Stmt.letmut e s =>
    have := Nat.lt_succ_of_le <| Stmt.numExts_S (Δ := []) s  -- for termination
    fun ρ =>
      let x := e[ρ][∅]
      StateT.run' (D (S s) (x :: ρ)) x
  | Stmt.ite e s₁ s₂ => (fun ρ => if e[ρ][∅] then D s₁ ρ else D s₂ ρ)
  | Stmt.sfor e s =>
    have := Nat.lt_succ_of_le <| Stmt.numExts_C_B (Δ := []) s  -- for termination
    fun ρ =>
      runCatch (forM e[ρ][∅] (fun x => runCatch (D (C (B s)) (x :: ρ))))
  | Stmt.ret e => (nomatch e[·][∅])
termination_by _ s => (s.numExts, sizeOf s)
decreasing_by D_tac

/-! Finally we compose `D` and `R` into the translation rule for a top-level statement (1'). -/

def Do.trans [Monad m] (s : Do m α) : m α := runCatch (D (R s) ∅)

/-!
Equivalence Proof
-----------------

Using the monadic dynamic semantics, we can modularly prove for each individual translation function that
evaluating its output is equivalent to directly evaluating the input, modulo some lifting and adjustment
of resulting values. After induction on the statement, the proofs are mostly concerned with case splitting,
application of congruence theorems, and simplification.
-/
attribute [local simp] map_eq_pure_bind

theorem eval_R [Monad m] [LawfulMonad m] (s : Stmt m ω Γ Δ b c α) : (R s).eval ρ σ = (ExceptT.lift (s.eval ρ σ) >>= fun x => match (generalizing := false) x with
    | (Neut.ret o, _) => throw o
    | (Neut.val a, σ) => pure (Neut.val a, σ)
    | (Neut.rcont, σ) => pure (Neut.rcont, σ)
    | (Neut.rbreak, σ) => pure (Neut.rbreak, σ) : ExceptT ω m (Neut Empty α b c × Assg Δ)) := by
  apply ExceptT.ext
  induction s with
    simp
  | bind _ _ ih₁ ih₂ =>
    simp [ExceptT.run_bind, ih₁, Stmt.eval.cont]
    apply bind_congr; intro
    split <;> simp [ih₂]
  | letmut _ _ ih =>
    simp [ExceptT.run_bind, ih]
    apply bind_congr; intro ⟨r, (_ :: σ')⟩
    cases r <;> simp
  | ite e _ _ ih₁ ih₂ =>
    by_cases h : e ρ σ <;> simp [ExceptT.run_bind, h, ih₁, ih₂]
  | sfor e s ih =>
    induction e ρ σ generalizing σ with
    | nil => simp [Stmt.eval.go]
    | cons _ _ ih' =>
      simp [ExceptT.run_bind, ih, Stmt.eval.go]
      apply bind_congr; intro
      split <;> simp [ih']

@[simp] theorem eval_mapAssg [Monad m] [LawfulMonad m] (f : Assg Γ' → Assg Γ) : ∀ (s : Stmt m ω Γ Δ b c β), Stmt.eval ρ (Stmt.mapAssg f s) σ = Stmt.eval (f ρ) s σ := by
  intro s
  induction s generalizing Γ' with
  | bind _ _ ih₁ ih₂ =>
    simp [ih₁, Stmt.eval.cont]
    apply bind_congr; intro ⟨r, σ'⟩
    cases r <;> simp [ih₂]
  | sfor e s ih =>
    simp
    induction e (f ρ) σ generalizing σ with
    | nil => simp [Stmt.eval.go]
    | cons _ _ ih' =>
      simp [ExceptT.run_bind, ih, Stmt.eval.go]
      apply bind_congr; intro
      split <;> simp [ih']
  | _ => simp [*]

/-!
We need one last helper function on context bottoms to be able to state the invariant of `S`, and then
prove various lemmas about their interactions. -/

def Assg.bot : {Γ : _} → Assg (Γ ++ [α]) → α
  | [],     [a]     => a
  | _ :: _, _ :: as => bot as

@[simp] theorem Assg.dropBot_extendBot (a : α) (σ : Assg Γ) : Assg.dropBot (Assg.extendBot a σ) = σ := by
  induction Γ <;> cases σ <;> simp [dropBot, extendBot, *]
@[simp] theorem Assg.bot_extendBot (a : α) (σ : Assg Γ) : Assg.bot (Assg.extendBot a σ) = a := by
  induction Γ <;> cases σ <;> simp [bot, extendBot, *]
@[simp] theorem Assg.extendBot_bot_dropBot (σ : Assg (Γ ++ [α])) : Assg.extendBot (Assg.bot σ) (Assg.dropBot σ) = σ := by
  induction Γ <;> cases σ <;> simp [dropBot, bot, extendBot, *] <;> rfl

@[simp] theorem Assg.dropBot_set_extendBot_init (a : α) (σ : Assg Γ) (h : i.1 < Γ.length) {b} : Assg.dropBot ((Assg.extendBot a σ).set i b) = σ.set ⟨i.1, h⟩ (List.get_append_left .. ▸ b) := by
  induction Γ with
  | nil => contradiction
  | cons  _ _ ih =>
    cases σ
    have ⟨i, h'⟩ := i
    cases i <;> simp [HList.set, dropBot]
    rw [ih]

@[simp] theorem Assg.bot_set_extendBot_init (a : α) (σ : Assg Γ) (h : i.1 < Γ.length) {b} : Assg.bot ((Assg.extendBot a σ).set i b) = a := by
  induction Γ with
  | nil => contradiction
  | cons  _ _ ih =>
    cases σ
    have ⟨i, h'⟩ := i
    cases i <;> simp [HList.set, dropBot, bot]
    rw [ih]; apply Nat.lt_of_succ_lt_succ h

@[simp] theorem Assg.dropBot_set_extendBot_bottom (a : α) (σ : Assg Γ) (h : ¬ i.1 < Γ.length) {b} : Assg.dropBot ((Assg.extendBot a σ).set i b) = σ := by
  induction Γ with
  | nil => rfl
  | cons  _ _ ih =>
    cases σ
    have ⟨i, h'⟩ := i
    cases i
    · apply False.elim (h (Nat.zero_lt_succ _))
    · simp [HList.set, dropBot]
      rw [ih]
      intro h''
      apply False.elim (h (Nat.succ_lt_succ h''))

@[simp] theorem Assg.bot_set_extendBot_bottom (a : α) (σ : Assg Γ) (h : ¬ i.1 < Γ.length) {b} : Assg.bot ((Assg.extendBot a σ).set i b) = cast (List.get_last h) b := by
  induction Γ with
  | nil =>
    have ⟨i, h'⟩ := i
    cases i
    · simp [HList.set, extendBot, bot]; rfl
    · apply False.elim (Nat.not_lt_zero _ (Nat.lt_of_succ_lt_succ h'))
  | cons  _ _ ih =>
    cases σ
    have ⟨i, h'⟩ := i
    cases i
    · apply False.elim (h (Nat.zero_lt_succ _))
    · simp [bot]
      rw [ih]
      intro h''
      apply False.elim (h (Nat.succ_lt_succ h''))

theorem eval_S [Monad m] [LawfulMonad m] : ∀ (s : Stmt m ω Γ (Δ ++ [α]) b c β), StateT.run ((S s).eval (a :: ρ) σ) a = s.eval ρ (Assg.extendBot a σ) >>= fun
    | r :: σ => pure ((r :: Assg.dropBot σ), Assg.bot σ)
  | Stmt.expr e => by simp
  | Stmt.bind s₁ s₂ => by
    simp [eval_S s₁, Stmt.eval.cont]
    apply bind_congr; intro ⟨r, σ⟩
    cases r <;> simp [eval_S s₂]
  | Stmt.letmut e s => by simp; rw [eval_S (Δ := _ :: Δ) s]; simp; rfl
  | Stmt.assg x e => by
    simp
    split <;> simp [*]
  | Stmt.ite e s₁ s₂ => by simp; split <;> simp [eval_S s₁, eval_S s₂]
  | Stmt.ret e => by simp
  | Stmt.sfor e s => by
    simp only [S, Stmt.eval, S.unmut]
    generalize h : a = a'
    conv =>
      pattern HList.cons a' _
      rw [← h]
    clear h
    induction e ρ _ generalizing σ a' with
    | nil => simp [Stmt.eval.go]
    | cons _ _ ih' =>
      simp [ExceptT.run_bind, Stmt.eval.go, Stmt.eval.cont, eval_S s]
      apply bind_congr; intro ⟨r, σ'⟩
      cases r with
      | val => simp at ih'; simp [ih']
      | rcont => simp at ih'; simp [ih']
      | _ => simp
  | Stmt.sbreak => by simp
  | Stmt.scont => by simp

theorem HList.eq_nil (as : HList ∅) : as = ∅ := rfl

theorem eval_L [Monad m] [LawfulMonad m] (s : Stmt m ω Γ Δ b c α) : (L s).eval ρ σ = ExceptT.lift (s.eval ρ σ) := by
  induction s with
    apply ExceptT.ext <;> simp
  | bind _ _ ih₁ ih₂ =>
    simp [ih₁, Stmt.eval.cont]
    apply bind_congr; intro ⟨r, σ'⟩
    cases r <;> simp [ih₂]
  | letmut _ _ ih => simp [ih]
  | ite e _ _ ih₁ ih₂ =>
    by_cases h : e ρ σ <;> simp [h, ih₁, ih₂]
  | sfor e s ih =>
    induction e ρ σ generalizing σ with
    | nil => simp [Stmt.eval.go]
    | cons _ _ ih' =>
      simp [ExceptT.run_bind, ih, Stmt.eval.go]
      apply bind_congr; intro
      split <;> simp [ih']

theorem eval_B [Monad m] [LawfulMonad m] (s : Stmt m ω Γ Δ b c α) : (B s).eval ρ σ = (ExceptT.lift (s.eval ρ σ) >>= fun x => match (generalizing := false) x with
    | (Neut.ret o, σ) => pure (Neut.ret o, σ)
    | (Neut.val a, σ) => pure (Neut.val a, σ)
    | (Neut.rcont, σ) => pure (Neut.rcont, σ)
    | (Neut.rbreak, σ) => throw () : ExceptT Unit m (Neut ω α false c × Assg Δ)) := by
  induction s with
    apply ExceptT.ext <;> simp
  | bind _ _ ih₁ ih₂ =>
    simp [ih₁, Stmt.eval.cont]
    apply bind_congr; intro
    split <;> simp [ih₂]
  | letmut _ _ ih =>
    simp [ih]
    apply bind_congr; intro
    split <;> simp
  | ite e _ _ ih₁ ih₂ =>
    by_cases h : e ρ σ <;> simp [h, ih₁, ih₂]
  | sfor e s ih =>
    induction e ρ σ generalizing σ with
    | nil => simp [Stmt.eval.go]
    | cons _ _ ih' =>
      simp [ExceptT.run_bind, ih, Stmt.eval.go, eval_L]
      apply bind_congr; intro
      split <;> simp [ih']

@[simp] def throwOnContinue [Monad m] : (Neut ω α false c × Assg Δ) → ExceptT Unit m (Neut ω α false false × Assg Δ)
  | (Neut.ret o, σ) => pure (Neut.ret o, σ)
  | (Neut.val a, σ) => pure (Neut.val a, σ)
  | (Neut.rcont, σ) => throw ()

theorem eval_C [Monad m] [LawfulMonad m] (s : Stmt m ω Γ Δ false c α) : (C s).eval ρ σ = ExceptT.lift (s.eval ρ σ) >>= throwOnContinue := by
  revert s
  suffices {b: _ } → (s' : Stmt m ω Γ Δ b c α) → (h : b = false) → let s : Stmt m ω Γ Δ false c α := h ▸ s'; (C s).eval ρ σ = ExceptT.lift (s.eval ρ σ) >>= throwOnContinue
    from fun s => this s rfl
  intro b' s h
  induction s with
    (first | subst h | trivial) <;> apply ExceptT.ext <;> simp
  | bind _ _ ih₁ ih₂ =>
    simp [ih₁, Stmt.eval.cont]
    apply bind_congr; intro
    split <;> simp [ih₂]
  | letmut _ _ ih =>
    simp [ih]
    apply bind_congr; intro
    split <;> simp
  | ite e _ _ ih₁ ih₂ =>
    by_cases h : e ρ σ <;> simp [h, ih₁, ih₂]
  | sfor e s ih =>
    induction e ρ σ generalizing σ with
    | nil => simp [Stmt.eval.go]
    | cons _ _ ih' =>
      simp [ExceptT.run_bind, ih, Stmt.eval.go, eval_L]
      apply bind_congr; intro
      split <;> simp [ih']

theorem D_eq [Monad m] [LawfulMonad m] : (s : Stmt m Empty Γ ∅ false false α) →
    D s ρ = s.eval ρ ∅ >>= fun (Neut.val a, _) => pure a
  | Stmt.expr e => by simp
  | Stmt.bind s₁ s₂ => by
    simp [D_eq s₁, D_eq s₂, Stmt.eval.cont]
    apply bind_congr; intro x
    split <;> simp [HList.eq_nil]
  | Stmt.letmut e s => by
    have := Nat.lt_succ_of_le <| Stmt.numExts_S (Δ := []) s  -- for termination
    simp [D_eq (S s), eval_S]
    apply bind_congr; intro x
    cases x.fst with
    | val   => simp
    | ret o => contradiction
  | Stmt.ite e s₁ s₂ => by simp; split <;> simp [D_eq s₁, D_eq s₂]
  | Stmt.ret e => nomatch e ρ ∅
  | Stmt.sfor e s => by
    have := Nat.lt_succ_of_le <| Stmt.numExts_C_B (Δ := []) s  -- for termination
    simp
    induction e ρ ∅ with
    | nil => simp [Stmt.eval.go, runCatch]
    | cons _ _ ih' =>
      simp [D_eq (C (B s)), runCatch, ExceptT.run_bind, eval_C, eval_B, Stmt.eval.go] at *
      apply bind_congr; intro ⟨r, σ'⟩
      cases r with
      | ret => contradiction
      | rbreak => simp
      | _ => simp [ih']; simp [HList.eq_nil]
termination_by _ s => (s.numExts, sizeOf s)
decreasing_by D_tac

/-! The equivalence proof cited in the paper follows from the invariants of `D` and `S`. -/

theorem Do.trans_eq_eval [Monad m] [LawfulMonad m] : ∀ s : Do m α, Do.trans s = ⟦s⟧ := by
  intro s
  simp [D_eq, eval_R, runCatch, Do.trans, Do.eval]
  apply bind_congr; intro
  split <;> simp

/-!
Partial Evaluation
------------------

We define a new term notation `simp [...] in e` that rewrites the term e using the given
simplification theorems.
-/

open Lean in
open Lean.Parser.Tactic in
open Lean.Meta in
open Lean.Elab in
elab "simp" "[" simps:simpLemma,* "]" "in" e:term : term => do
  -- construct goal `⊢ e = ?x` with fresh metavariable `?x`, simplify, solve by reflexivity,
  -- and return assigned value of `?x`
  let e ← Term.elabTermAndSynthesize e none
  let x ← mkFreshExprMVar (← inferType e)
  let goal ← mkFreshExprMVar (← mkEq e x)
  -- disable ζ-reduction to preserve `let`s
  Term.runTactic goal.mvarId! (← `(tactic| (simp (config := { zeta := false }) [$simps:simpLemma,*]; rfl)))
  instantiateMVars x

-- further clean up generated programs
attribute [local simp] Assg.extendBot cast
attribute [-simp] StateT.run'_eq

/-!
We can now use this new notation to completely erase the translation functions
from an invocation on the example `ex2` from `For.lean` (manually translated to `Stmt`).
-/
/-
let mut y := init;
for x in xs do' {
  y ← f y x
};
return y
-/

def ex2' [Monad m] (f : β → α → m β) (init : β) (xs : List α) : m β :=
  simp [Do.trans] in Do.trans (
      Stmt.letmut (fun _ _ => init) <|
      Stmt.bind (
        Stmt.sfor (fun _ _ => xs) <|
        -- `y ← f y x` unfolded to `let z ← f y x; y := z` (A4)
        Stmt.bind
          (Stmt.expr (fun ([x]) ([y]) => f y x))
          (Stmt.assg ⟨0, by simp⟩ (fun ([z, x]) _ => z))) <|
      Stmt.ret (fun _ ([y]) => y))

/-!
Compare the output of the two versions - the structure is identical except for unused
monadic layers in the formal translation, which would be harder to avoid in this typed
approach. -/
#print ex2
#print ex2'

/-! We can evaluate the generated program like any other Lean program, and prove that both versions are equivalent. -/
#eval ex2' (m := Id) (fun a b => pure (a + b)) 0 [1, 2]

example [Monad m] [LawfulMonad m] (f : β → α → m β) :
    ex2' f init xs = ex2 f init xs := by
  rw [ex2, ex2']; unfold runCatch; induction xs generalizing init <;> simp_all! [StateT.run'_eq]

/-!
For one more example, consider `ex3` from `For.lean`.
-/
/-
for xs in xss do' {
  for x in xs do' {
    let b ← p x;
    if b then {
      return some x
    }
  }
};
pure none
-/

def ex3' [Monad m] (p : α → m Bool) (xss : List (List α)) : m (Option α) :=
  simp [Do.trans] in Do.trans (
      Stmt.bind
        (Stmt.sfor (fun _ _ => xss) <|
          Stmt.sfor (fun ([xs]) _ => xs) <|
            Stmt.bind
              (Stmt.expr (fun ([x, xs]) _ => p x))
              (Stmt.ite (fun ([b, x, xs]) _ => b)
                (Stmt.ret (fun ([b, x, xs]) _ => some x))
                (Stmt.expr (fun _ _ => pure ()))))
        (Stmt.expr (fun _ _ => pure none)))

#print ex3
#print ex3'
#eval ex3' (m := Id) (fun n => n % 2 == 0) [[1, 3], [2, 4]]

example [Monad m] [LawfulMonad m] (p : α → m Bool) (xss : List (List α)) :
    ex3' p xss = ex3 p xss := by
  rw [ex3, ex3']
  unfold runCatch
  induction xss with
  | nil => simp!
  | cons xs xss ih =>
    simp
    induction xs with
    | nil => simp [←ih]
    | cons x xs ih => simp; apply byCases_Bool_bind <;> simp [ih]

/-!
While it would be possible to override our `do'` notation such that its named syntax
is first translated to nameless `Stmt` constructors and then applied to `simp [Do.trans] in`,
for demonstration purposes we decided to encode these examples manually. In practice, the
macro implementation remains more desirable as mentioned in the paper.
-/
