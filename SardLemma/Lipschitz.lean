-- Lipschitz.lean
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Basic


namespace Lipschitz

def lip (f : ℝ → ℝ) (I : Set ℝ) (C : ℝ) : Prop :=
  ∀ x ∈ I, ∀ y ∈ I, |f x - f y| ≤ C * |x - y|

end Lipschitz
