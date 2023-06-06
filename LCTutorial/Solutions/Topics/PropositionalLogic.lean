import LCTutorial.Library.Basic
open Set

namespace PropositionalLogic

/- Let's try to implement a language of propositional logic. -/

def Variable : Type := ℕ
instance : DecidableEq Variable := by { rw [Variable]; infer_instance }

/- We define propositional formula, and some notation for them. -/

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
local infix:40 (priority := high) " ⇒ " => impl
local notation (priority := high) "⊥" => bot

def neg (A : Formula) : Formula := A ⇒ ⊥
local notation:(max+2) (priority := high) "~" x:max => neg x
def top : Formula := ~⊥
local notation (priority := high) "⊤" => top
def equiv (A B : Formula) : Formula := (A ⇒ B) && (B ⇒ A)
local infix:45 (priority := high) " ⇔ " => equiv

/- Let's define truth w.r.t. a valuation, i.e. classical validity -/

@[simp]
def IsTrue (v : Variable → Prop) : Formula → Prop
  | ⊥      => False
  | # P    => v P
  | A || B => IsTrue v A ∨ IsTrue v B
  | A && B => IsTrue v A ∧ IsTrue v B
  | A ⇒ B => IsTrue v A → IsTrue v B

def Satisfies (v : Variable → Prop) (Γ : Set Formula) : Prop := ∀ A ∈ Γ, IsTrue v A
def Models (Γ : Set Formula) (A : Formula) : Prop := ∀ v, Satisfies v Γ → IsTrue v A
local infix:80 (priority := high) " ⊨ " => Models
def Valid (A : Formula) : Prop := ∅ ⊨ A

/- Here are some basic properties.
  The tactic `simp` will automatically simplify definitions tagged with `@[simp]` and rewrite
  using theorems tagged with `@[simp]`. -/

variable {v : Variable → Prop} {A B : Formula}
@[simp] lemma isTrue_neg : IsTrue v ~A ↔ ¬ IsTrue v A := by simp

@[simp] lemma isTrue_top : IsTrue v ⊤ := by
  -- sorry
  simp [IsTrue]
  -- sorry

@[simp] lemma isTrue_equiv : IsTrue v (A ⇔ B) ↔ (IsTrue v A ↔ IsTrue v B) := by
  -- sorry
  simp
  tauto
  -- sorry

/- As an exercise, let's prove (using classical logic) the double negation elimination principle. -/

example : Valid (~~A ⇔ A) := by
  -- sorry
  intros v _
  simp
  tauto
  -- sorry

/- Let's define provability w.r.t. classical logic -/
section
set_option hygiene false in  -- hacky: allow forward reference in notation
local notation:50 Γ " ⇐  " A => Provable Γ A

-- Reserved Notation "Γ ⊢ A" (at level 80).
inductive Provable : Set Formula → Formula → Prop
| ax    : ∀ {Γ A},   A ∈ Γ → Provable Γ A
| impI  : ∀ {Γ A B}, Provable (insert A Γ) B           → Provable Γ (A ⇒ B)
| impE  : ∀ {Γ A B}, Provable Γ (A ⇒ B) → Provable Γ A → Provable Γ B
| botC  : ∀ {Γ A},   Provable (insert ~A Γ) ⊥        → Provable Γ A
| andI  : ∀ {Γ A B}, Provable Γ A     → Provable Γ B              → Provable Γ (A && B)
| andE1 : ∀ {Γ A B}, Provable Γ (A && B)                        → Provable Γ A
| andE2 : ∀ {Γ A B}, Provable Γ (A && B)                        → Provable Γ B
| orI1  : ∀ {Γ A B}, Provable Γ A                           → Provable Γ (A || B)
| orI2  : ∀ {Γ A B}, Provable Γ B                           → Provable Γ (A || B)
| orE   : ∀ {Γ A B C}, Provable Γ (A || B) → Provable (insert A Γ) C → Provable (insert B Γ) C → Provable Γ C
-- | ax    : ∀ {Γ A},   A ∈ Γ   → Γ ⊢ A
-- | ImpI  : ∀ {Γ A B},  insert A Γ ⊢ B               → Γ ⊢ A → B
-- | ImpE  : ∀ {Γ A B},           Γ ⊢ A ⇒ B  → Γ ⊢ A  → Γ ⊢ B
-- | BotC  : ∀ {Γ A},   insert ~A Γ ⊢ ⊥               → Γ ⊢ A
-- | andI  : ∀ {Γ A B},           Γ ⊢ A      → Γ ⊢ B  → Γ ⊢ A && B
-- | andE1 : ∀ {Γ A B},           Γ ⊢ A && B          → Γ ⊢ A
-- | andE2 : ∀ {Γ A B},           Γ ⊢ A && B          → Γ ⊢ B
-- | orI1  : ∀ {Γ A B},           Γ ⊢ A               → Γ ⊢ A || B
-- | orI2  : ∀ {Γ A B},           Γ ⊢ B               → Γ ⊢ A || B
-- | orE   : ∀ {Γ A B C}, Γ ⊢ A || B → A::Γ ⊢ C → B::Γ ⊢ C → Γ ⊢ C
end
local infix:80 (priority := high) " ⊢ " => Provable
def IsTheorem (A : Formula) := ∅ ⊢ A

export Provable (ax impI impE botC andI andE1 andE2 orI1 orI2 orE)
variable {Γ Δ : Set Formula}
/- To practice with the proof system, let's prove the following.
  The following lemmas about insert are useful
```
  mem_insert x s : x ∈ insert x s
  mem_insert_of_mem y : x ∈ s → x ∈ insert y s
  insert_subset_insert : s ⊆ t → insert x s ⊆ insert x t
```
-/
example : IsTheorem (~~A ⇔ A) := by
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

/- You can prove the following using `induction` on `h`. You will want to tell Lean that you want
  to prove it for all `Δ` simultaneously using `induction h generalizing Δ`.
  Lean will mark created assumptions as inaccessible (marked with †)
  if you don't explicitly name them.
  You can name the last inaccessible variables using for example `rename_i ih` or
  `rename_i A B h ih`. Or you can prove a particular case using `case impI ih => <proof>`. -/
lemma weakening (h : Γ ⊢ A) (h2 : Γ ⊆ Δ) : Δ ⊢ A := by
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

/- Use the `suggest` tactic to find the lemma that states `Γ ⊆ insert x Γ`.
  You can click the blue suggestion in the right panel to automatically apply the suggestion. -/

lemma Provable.insert (h : Γ ⊢ A) : insert B Γ ⊢ A := by
  -- sorry
  apply weakening h
  -- use `suggest` here
  exact subset_insert B Γ
  -- sorry

/- Proving the deduction theorem is now easy. -/
lemma deduction_theorem (h : Γ ⊢ A) : insert (A ⇒ B) Γ ⊢ B := by
  -- sorry
  intros
  apply impE (ax (mem_insert _ _))
  exact h.insert
  -- sorry


lemma IsTheorem.mp (h1 : IsTheorem (A ⇒ B)) (h2 : Γ ⊢ A) : Γ ⊢ B := by
  -- sorry
  apply impE _ h2
  apply weakening h1
  -- suggest
  exact empty_subset Γ
  -- sorry

theorem soundness_theorem (h : Γ ⊢ A) : Γ ⊨ A := by
  -- sorry
  induction h <;> intros v hv
  solve_by_elim
  simp
  -- sorry

Theorem Soundness_general : forall A Γ, Γ ⊢ A → Γ ⊨ A.
intros A Γ H0 v;induction H0;simpl;intros;auto;
 try simpl in IHNc;try simpl in IHNc1;try simpl in IHNc2;
  case_bool v A;try (case_bool v B;fail);
   try (apply IHNc||apply IHNc2;prove_satisfaction);
    case_bool v B;apply IHNc3;prove_satisfaction.
Qed.

Theorem Soundness : Prop_Soundness.
intros ? ? ? ?;eapply Soundness_general;eassumption.
Qed.

End sound_mod.


end PropositionalLogic