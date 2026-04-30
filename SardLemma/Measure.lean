-- Measure.lean
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Data.Finset.Defs

open BigOperators
open Finset

namespace Measure

def is_negligeable (A : Set ℝ) : Prop :=
  ∀ ε > 0,
  ∃ (a b: ℕ → ℝ), (∀ n, a n ≤ b n) ∧
  (A ⊆ ⋃ n, Set.Icc (a n) (b n)) ∧
  (∀ n : ℕ, (∑ k ∈ range (n+1), (b k - a k)) ≤ ε)

lemma negligeable_subset {A B : Set ℝ} (hA : A ⊆ B) (hB : is_negligeable B) : is_negligeable A := by
  intro ε hε
  obtain ⟨a, b, hleq, hsub, hsum⟩ := hB ε hε
  have hsub : A ⊆ ⋃ n, Set.Icc (a n) (b n) := by
    exact LE.le.subset fun ⦃a⦄ a_1 ↦ hsub (hA a_1)
  exact ⟨a, b, hleq, hsub, hsum⟩

end Measure
