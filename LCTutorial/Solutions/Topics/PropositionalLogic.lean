import LCTutorial.Library.Basic
open Set

namespace PropositionalLogic

/- Let's try to implement a language of classical propositional logic. -/

def Variable : Type := ℕ

/- We define propositional formula, and some notation for them. We will use a minimal propositional
logic with only implication and falsum (`⊥`), so that proofs involve fewer steps. -/

inductive Formula : Type where
  | var : Variable → Formula
  | bot : Formula
  | conj : Formula → Formula → Formula
  | disj : Formula → Formula → Formula
  | impl : Formula → Formula → Formula

open Formula
local notation:max (priority := high) "#" x:50 => var x
local infix:30 (priority := high) " || " => disj
local infix:35 (priority := high) " && " => conj
local infix:28 (priority := high) " ⇒ " => impl
local notation (priority := high) "⊥" => bot

def neg (A : Formula) : Formula := A ⇒ ⊥
local notation:(max+2) (priority := high) "~" x:max => neg x
def top : Formula := ~⊥
local notation (priority := high) "⊤" => top
def equiv (A B : Formula) : Formula := (A ⇒ B) && (B ⇒ A)
local infix:29 (priority := high) " ⇔ " => equiv

/- Let's define truth w.r.t. a valuation, i.e. classical validity -/

@[simp]
def IsTrue (v : Variable → Prop) : Formula → Prop
  | ⊥      => False
  | # P    => v P
  | A || B => IsTrue v A ∨ IsTrue v B
  | A && B => IsTrue v A ∧ IsTrue v B
  | A ⇒ B => IsTrue v A → IsTrue v B

def Satisfies (v : Variable → Prop) (Γ : Set Formula) : Prop := ∀ {A}, A ∈ Γ → IsTrue v A
def Models (Γ : Set Formula) (A : Formula) : Prop := ∀ {v}, Satisfies v Γ → IsTrue v A
local infix:27 (priority := high) " ⊨ " => Models
def Valid (A : Formula) : Prop := ∅ ⊨ A

/- Here are some basic properties.
  The tactic `simp` will automatically simplify definitions tagged with `@[simp]` and rewrite
  using theorems tagged with `@[simp]`. -/

variable {v : Variable → Prop} {A B : Formula}
@[simp] lemma isTrue_neg : IsTrue v ~A ↔ ¬ IsTrue v A := by simp

@[simp] lemma isTrue_top : IsTrue v ⊤ := by {
  -- sorry
  simp
  -- sorry
}

@[simp] lemma isTrue_equiv : IsTrue v (A ⇔ B) ↔ (IsTrue v A ↔ IsTrue v B) := by {
  -- sorry
  simp
  tauto
  -- sorry
}

/- As an exercise, let's prove (using classical logic) the double negation elimination principle.
  `by_contra h` might be useful to prove something by contradiction. -/

example : Valid (~~A ⇔ A) := by {
  -- sorry
  intros v _
  simp
  tauto
  -- sorry
}

@[simp] lemma satisfies_insert_iff : Satisfies v (insert A Γ) ↔ IsTrue v A ∧ Satisfies v Γ := by {
  simp [Satisfies]
}

/- Let's define provability w.r.t. classical logic. -/
section
set_option hygiene false  -- hacky: allow forward reference in notation
local infix:27 " ⊢ " => ProvableFrom

inductive ProvableFrom : Set Formula → Formula → Prop
  | ax    : ∀ {Γ A},   A ∈ Γ   → Γ ⊢ A
  | impI  : ∀ {Γ A B},  insert A Γ ⊢ B                → Γ ⊢ A ⇒ B
  | impE  : ∀ {Γ A B},           Γ ⊢ (A ⇒ B) → Γ ⊢ A  → Γ ⊢ B
  | botC  : ∀ {Γ A},   insert ~A Γ ⊢ ⊥                → Γ ⊢ A
  | andI  : ∀ {Γ A B},           Γ ⊢ A       → Γ ⊢ B  → Γ ⊢ A && B
  | andE1 : ∀ {Γ A B},           Γ ⊢ A && B           → Γ ⊢ A
  | andE2 : ∀ {Γ A B},           Γ ⊢ A && B           → Γ ⊢ B
  | orI1  : ∀ {Γ A B},           Γ ⊢ A                → Γ ⊢ A || B
  | orI2  : ∀ {Γ A B},           Γ ⊢ B                → Γ ⊢ A || B
  | orE   : ∀ {Γ A B C}, Γ ⊢ A || B → insert A Γ ⊢ C → insert B Γ ⊢ C → Γ ⊢ C

end

local infix:80 (priority := high) " ⊢ " => ProvableFrom
def Provable (A : Formula) := ∅ ⊢ A

export ProvableFrom (ax impI impE botC andI andE1 andE2 orI1 orI2 orE)
variable {Γ Δ : Set Formula}
/- To practice with the proof system, let's prove the following.
  The following lemmas about insert are useful
```
  mem_insert x s : x ∈ insert x s
  mem_insert_of_mem y : x ∈ s → x ∈ insert y s
  insert_subset_insert : s ⊆ t → insert x s ⊆ insert x t
```
-/
example : Provable (~~A ⇔ A) := by {
  -- sorry
  apply andI
  · apply impI
    apply botC
    apply impE (ax $ mem_insert_of_mem _ $ mem_insert _ _)
    apply ax (mem_insert _ _)
  · apply impI
    apply impI
    apply impE (ax $ mem_insert _ _)
    apply ax (mem_insert_of_mem _ $ mem_insert _ _)
  -- sorry
}

/- You can prove the following using `induction` on `h`. You will want to tell Lean that you want
  to prove it for all `Δ` simultaneously using `induction h generalizing Δ`.
  Lean will mark created assumptions as inaccessible (marked with †)
  if you don't explicitly name them.
  You can name the last inaccessible variables using for example `rename_i ih` or
  `rename_i A B h ih`. Or you can prove a particular case using `case impI ih => <proof>`. -/
lemma weakening (h : Γ ⊢ A) (h2 : Γ ⊆ Δ) : Δ ⊢ A := by {
  -- sorry
  induction h generalizing Δ
  case ax => apply ax; solve_by_elim
  case impI ih => apply impI; solve_by_elim [insert_subset_insert]
  case impE ih₁ ih₂ => apply impE <;> solve_by_elim
  case andI ih₁ ih₂ => apply andI <;> solve_by_elim
  case andE1 ih => apply andE1 <;> solve_by_elim
  case andE2 ih => apply andE2 <;> solve_by_elim
  case orI1 ih => apply orI1; solve_by_elim
  case orI2 ih => apply orI2; solve_by_elim
  case orE ih₁ ih₂ ih₃ => apply orE <;> solve_by_elim [insert_subset_insert]
  case botC ih => apply botC <;> solve_by_elim [insert_subset_insert]
  -- sorry
}

/- Use the `suggest` tactic to find the lemma that states `Γ ⊆ insert x Γ`.
  You can click the blue suggestion in the right panel to automatically apply the suggestion. -/

lemma ProvableFrom.insert (h : Γ ⊢ A) : insert B Γ ⊢ A := by {
  -- sorry
  apply weakening h
  -- use `suggest` here
  exact subset_insert B Γ
  -- sorry
}

/- Proving the deduction theorem is now easy. -/
lemma deduction_theorem (h : Γ ⊢ A) : insert (A ⇒ B) Γ ⊢ B := by {
  -- sorry
  intros
  apply impE (ax $ mem_insert _ _)
  exact h.insert
  -- sorry
}


lemma Provable.mp (h1 : Provable (A ⇒ B)) (h2 : Γ ⊢ A) : Γ ⊢ B := by {
  -- sorry
  apply impE _ h2
  apply weakening h1
  -- suggest
  exact empty_subset Γ
  -- sorry
}

/-- It might be useful -/
theorem soundness_theorem (h : Γ ⊢ A) : Γ ⊨ A := by {
  -- sorry
  induction h <;> intros v hv
  solve_by_elim
  case impI ih => intro hA; apply ih; simp [*]
  case impE ih₁ ih₂ => exact ih₁ hv (ih₂ hv)
  case botC ih => by_contra hA; apply ih (satisfies_insert_iff.mpr ⟨by exact hA, hv⟩)
  case andI ih₁ ih₂ => exact ⟨ih₁ hv, ih₂ hv⟩
  case andE1 ih => exact (ih hv).1
  case andE2 ih => exact (ih hv).2
  case orI1 ih => exact .inl (ih hv)
  case orI2 ih => exact .inr (ih hv)
  case orE ih₁ ih₂ ih₃ => refine (ih₁ hv).elim (fun hA => ih₂ ?_) (fun hB => ih₃ ?_) <;> simp [*]
  -- sorry
}

theorem valid_of_provable (h : Provable A) : Valid A := by {
  -- sorry
  exact soundness_theorem h
  -- sorry
}

/-
  As a much longer project, you can now try some other projects.

  1. Prove completeness: if a formula is valid, then it is provable
  Here is one possible strategy for this proof:
  * If a formula is valid, then so is its negation normal form (NNF);
  * If a formula in NNF is valid, then so is its conjunctive normal form (CNF);
  * If a formula in CNF is valid then it is syntactically valid:
      all its clauses contain both `A` and `¬ A` in it for some `A` (or contain `⊤`);
  * If a formula in CNF is syntactically valid, then its provable;
  * If the CNF of a formula in NNF is provable, then so is the formula itself.
  * If the NNF of a formula is provable, then so is the formula itself.

  2. Define Kripke semantics and provability for constructive propositional logic,
    and prove soundness (or even completeness) for constructive propositional logic.
-/

end PropositionalLogic