-- SardLemma/Monotonicity.lean
import Mathlib.Topology.MetricSpace.Basic


namespace Monotonous

lemma weaker_uniform (f : ℝ → ℝ) (I : Set ℝ) (δ δ' ε : ℝ) (hδ : ∀ x ∈ I, ∀ y ∈ I, dist x y < δ → dist (f x) (f y) < ε) (hδ' : δ' ≤ δ) : ∀ x ∈ I, ∀ y ∈ I, dist x y < δ' → dist (f x) (f y) < ε := by
  intro x hx y hy h
  replace h: dist x y < δ := lt_of_lt_of_le h hδ'
  apply hδ at h
  apply h
  apply hx
  exact hy

end Monotonous
