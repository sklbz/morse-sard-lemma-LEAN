-- Lipschitz.lean
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Basic
import SardLemma.Derivative

open Derivative
open Convex

namespace Lipschitz

def lip (f : ℝ → ℝ) (I : Set ℝ) (C : ℝ) : Prop :=
  ∀ x ∈ I, ∀ y ∈ I, |f x - f y| ≤ C * |x - y|

lemma deriv_bound_imp_lip {f : ℝ → ℝ} {I : Set ℝ} {k : ℝ} {x y : ℝ}
  (hf : ContDiff ℝ 1 f) (hderiv : ∀ x ∈ I, |deriv f x| ≤ k)
  (hI : Convex ℝ I) (hx : x ∈ I) (hy : y ∈ I) : |f y - f x| ≤ k * |y - x| := by
    have hf : ∀ x ∈ I, DifferentiableAt ℝ f x := 
      contdiff_imp_diff_restriction hf
    have f_lip : |f y - f x| ≤ k * |y - x| := 
      norm_image_sub_le_of_norm_deriv_le 
        hf
        (fun h => by    
          have := hderiv h
          rwa [Real.norm_eq_abs])
        hI
        hx hy
    exact f_lip

end Lipschitz
