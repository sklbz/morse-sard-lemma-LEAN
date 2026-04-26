import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace Derivative

lemma contdiff_imp_diff_restriction {f : ℝ → ℝ} {A : Set ℝ}
  (hf : ContDiff ℝ 1 f) : ∀ x ∈ A, DifferentiableAt ℝ f x := by
    intro x hx
    refine Differentiable.differentiableAt ?_
    have h : (1 : WithTop ℕ∞) ≠ 0 := by
      simp
    exact hf.differentiable h

end Derivative
