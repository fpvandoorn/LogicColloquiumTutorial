import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Group.Pi

namespace Forall
/- # Universal quantifiers

In this file, we'll learn about the `∀` quantifier.

Let `P` be a predicate on a type `X`. This means for every mathematical
object `x` with type `X`, we get a mathematical statement `P x`.
In Lean, `P x` has type `Prop`.

Lean sees a proof `h` of `∀ x, P x` as a function sending any `x : X` to
a proof `h x` of `P x`.
This already explains the main way to use an assumption or lemma which
starts with a `∀`.

In order to prove `∀ x, P x`, we use `intro x` to fix an arbitrary object
with type `X`, and call it `x` (`intro` stands for "introduce").

Note also we don't need to give the type of `x` in the expression `∀ x, P x`
as long as the type of `P` is clear to Lean, which can then infer the type of `x`.

Let's define a predicate to play with `∀`.
-/

def even_fun (f : ℝ → ℝ) := ∀ x, f (-x) = f x

/-
In the next proof, we also take the opportunity to introduce the
`unfold` tactic, which simply unfolds definitions. Here this is purely
for didactic reason, Lean doesn't need those `unfold` invocations.
We will also use `rfl` which is a term proving equalities that are true
by definition (in a very strong sense), it stands for "reflexivity".
-/

example (f g : ℝ → ℝ) (hf : even_fun f) (hg : even_fun g) : even_fun (f + g) := by
  -- Our assumption on that f is even means ∀ x, f (-x) = f x
  unfold even_fun at hf
  -- and the same for g
  unfold even_fun at hg
  -- We need to prove ∀ x, (f+g)(-x) = (f+g)(x)
  unfold even_fun
  -- Let x be any real number
  intro x
  -- and let's compute
  calc (f + g) (-x) = f (-x) + g (-x)  := rfl
  _                 = f x + g (-x)     := by rw [hf x]
  _                 = f x + g x        := by rw [hg x]
  _                 = (f + g) x        := rfl


/-
In the preceding proof, all `unfold` lines are purely for
psychological comfort.

Sometimes unfolding is necessary because we want to apply a tactic
that operates purely on the syntactical level.
The main such tactic is `rw`.

The same property of `rw` explain why the first computation line
is necessary, although its proof is simply `rfl`.
Before that line, `rw hf x` won't find anything like `f (-x)` hence
will give up.
The last line is not necessary however, since it only proves
something that is true by definition, and is not followed by
a `rw`.

Also, Lean doesn't need to be told that `hf` should be specialized to
`x` before rewriting, exactly as in the first file.

Recall also that `rw` can take a list of expressions to use for
rewriting. For instance `rw [h₁, h₂, h₃]` is equivalent to three
lines `rw [h₁]`, `rw [h₂]` and `rw [h₃]`. Note that you can inspect the tactic
state between those rewrites when reading a proof using this syntax. You
simply need to move the cursor inside the list.

Hence we can compress the above proof to:
-/

example (f g : ℝ → ℝ) : even_fun f → even_fun g →  even_fun (f + g) := by
  intro hf hg x
  calc (f + g) (-x) = f (-x) + g (-x)  := rfl
  _                 = f x + g x        := by rw [hf, hg]

/-
Now let's practice. Recall that if you need to learn how to type a unicode
symbol you can put your mouse cursor above the symbol and wait for one second.
-/

example (f g : ℝ → ℝ) (hf : even_fun f) : even_fun (g ∘ f) := by
  sorry

/-
Let's have more quantifiers, and play with forward and backward reasoning.

In the next definitions, note how `∀ x₁, ∀ x₂` is abreviated to `∀ x₁ x₂`.
-/

def non_decreasing (f : ℝ → ℝ) := ∀ x₁ x₂, x₁ ≤ x₂ → f x₁ ≤ f x₂

def non_increasing (f : ℝ → ℝ) := ∀ x₁ x₂, x₁ ≤ x₂ → f x₁ ≥ f x₂

/- Let's be very explicit and use forward reasoning first. -/
example (f g : ℝ → ℝ) (hf : non_decreasing f) (hg : non_decreasing g) : non_decreasing (g ∘ f) := by
  -- Let x₁ and x₂ be real numbers such that x₁ ≤ x₂
  intro x₁ x₂ h
  -- Since f is non-decreasing, f x₁ ≤ f x₂.
  have step₁ : f x₁ ≤ f x₂
  · exact hf x₁ x₂ h
  -- Since g is non-decreasing, we then get g (f x₁) ≤ g (f x₂).
  exact hg (f x₁) (f x₂) step₁

/-
In the above proof, note how inconvenient it is to specify `x₁` and `x₂` in `hf x₁ x₂ h` since
they could be inferred from the type of `hf`.
We could have written `hf _ _ h` and Lean would have filled the holes denoted by `_`.
The same remark applies to the last line.

One possible variation on the above proof is to
use the `specialize` tactic to replace hf by its specialization to the relevant value.
 -/

example (f g : ℝ → ℝ) (hf : non_decreasing f) (hg : non_decreasing g) : non_decreasing (g ∘ f) := by
  intro x₁ x₂ h
  specialize hf x₁ x₂ h
  exact hg (f x₁) (f x₂) hf

/-
This `specialize` tactic is mostly useful for exploration, or in preparation for rewriting
in the assumption. One can very often replace its use by using more complicated expressions
directly involving the original assumption, as in the next variation:
-/
example (f g : ℝ → ℝ) (hf : non_decreasing f) (hg : non_decreasing g) : non_decreasing (g ∘ f) := by
  intro x₁ x₂ h
  exact hg (f x₁) (f x₂) (hf x₁ x₂ h)


/-
Let's see how backward reasoning would look like here.
As usual with this style, we use `apply` and enjoy Lean specializing assumptions for us
using so-called unification.
-/

example (f g : ℝ → ℝ) (hf : non_decreasing f) (hg : non_decreasing g) : non_decreasing (g ∘ f) := by
  -- Let x₁ and x₂ be real numbers such that x₁ ≤ x₂
  intro x₁ x₂ h
  -- We need to prove (g ∘ f) x₁ ≤ (g ∘ f) x₂.
  -- Since g is non-decreasing, it suffices to prove f x₁ ≤ f x₂
  apply hg
  -- which follows from our assumption on f
  apply hf
  -- and on x₁ and x₂
  exact h

example (f g : ℝ → ℝ) (hf : non_decreasing f) (hg : non_increasing g) : non_increasing (g ∘ f) := by
  sorry

/-
This is the end of this file where you learned how to handle universal quantifiers.
You learned about tactics:
* `intro`
* `unfold`
* `specialize`

-/