-- Measure.lean
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Data.Finset.Defs

open BigOperators
open Finset

namespace Measure

def measure_maj (A : Set ℝ) (ε : ℝ) : Prop :=
  ∃ (a b: ℕ → ℝ), (∀ n, a n ≤ b n) ∧
  (A ⊆ ⋃ n, Set.Icc (a n) (b n)) ∧
  (∀ n : ℕ, (∑ k ∈ range (n+1), (b k - a k)) ≤ ε)

def is_negligeable (A : Set ℝ) : Prop :=
  ∀ ε > 0, measure_maj A ε

lemma subset_measure_maj {A B : Set ℝ} (hA : A ⊆ B)
  {ε : ℝ} (hB : measure_maj B ε) : measure_maj A ε := by
  obtain ⟨a, b, hleq, hsub, hsum⟩ := hB
  have hsub : A ⊆ ⋃ n, Set.Icc (a n) (b n) := by
    exact LE.le.subset fun ⦃a⦄ a_1 ↦ hsub (hA a_1)
  exact ⟨a, b, hleq, hsub, hsum⟩

lemma negligeable_subset {A B : Set ℝ} (hA : A ⊆ B) (hB : is_negligeable B) : is_negligeable A := by
  intro ε hε
  exact subset_measure_maj hA (hB ε hε)

end Measure
