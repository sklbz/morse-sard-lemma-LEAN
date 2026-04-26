-- Basic.lean
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Analysis.Convex.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Real.Basic
import SardLemma.Subdivision
import SardLemma.Derivative
import SardLemma.Interval
import SardLemma.Uniform
import SardLemma.Measure
import SardLemma.Boolean

open BigOperators
open Set

open Subdivision
open Derivative
open Interval
open Uniform
open Measure
open Boolean

lemma sard_lemma_compact (a b : ℝ) (f : ℝ → ℝ) (hμ : b - a > 0) (hf : ContDiff ℝ 1 f) : 
  is_negligeable (f '' {x ∈ Icc a b | deriv f x = 0}) := 
by
  let I : Set ℝ := Icc a b
  let μ := b - a
  let f' : ℝ → ℝ := deriv f

  change μ > 0 at hμ

  have hI : IsCompact I := isCompact_Icc

  have hf'_uniform : is_uniform_metric f' I := uniform_derivative hI hf

  intro ε hε

  let ε' := ε / μ
  let hε' := div_pos hε hμ

  obtain ⟨δ, δ_pos, hδ⟩ := hf'_uniform ε' hε'

  let k : ℤ := ⌈μ / δ⌉
  have hk : (k: ℝ) > 0 := Int.cast_pos.2 (Int.ceil_pos.2 (div_pos hμ δ_pos))

  let δ' := μ / k
  have δ'_pos: δ' > 0 := div_pos hμ hk
  have δ'_leq_δ: δ' ≤ δ := div_ceil_le hμ δ_pos

  have hδ': is_uniform_with f' I ε' δ' := 
    uniform_transitivity hδ δ'_leq_δ

  let n : ℕ := k.toNat
  let subdiv (i : ℕ) : ℝ := a + i * δ'
  let J (i : ℕ) : Set ℝ := Icc (subdiv i) (subdiv (i+1))

  have subdiv_above_a : ∀ i ≤ n, a ≤ subdiv i := by
    intro i hi
    have term_pos : 0 ≤ i * δ' := by positivity
    linarith

  have subdiv_below_b : ∀ i ≤ n, subdiv i ≤ b := by
    intro i hi
    have term_maj : i * δ' ≤ n * δ' := by
      gcongr
    have eq : n * (μ / k) = μ := toNat_mul_div_eq hk
    linarith

  have subdiv_in_I : ∀ i ≤ n, subdiv i ∈ I := by
    intro i hi
    unfold I
    refine Set.mem_Icc.mpr ?_
    constructor
    · exact subdiv_above_a i hi
    · exact subdiv_below_b i hi

  have J_in_I : ∀ i < n,  J i ⊆ I := by
    intro i hi
    refine Set.Icc_subset I ?_ (subdiv_in_I (i + 1) hi)
    exact subdiv_in_I i (le_of_lt hi)
  
  lemma cover {x : ℝ} (hx : x ∈ I) : ∃ i < n, x ∈ (J i) := by
    apply?

  have f'_uniform_on_J : ∀ i < n, is_uniform_with f' (J i) ε' δ' := by
    intro i hi
    exact uniform_restriction hδ' (J_in_I i hi)

  have dist_J {i : ℕ} 
    {x y : ℝ} 
    (hx : x ∈ J i)
    (hy : y ∈ J i) : 
    dist x y ≤ δ' := by
    have h : |x - y| ≤ (subdiv (i+1) - subdiv i) := abs_sub_le_of_Icc hx hy
    have hδ : subdiv (i+1) - subdiv i = δ' := by
      simp [subdiv]
      linarith
    simpa [dist, hδ] using h

  let φ (i : ℕ) : Bool := {x ∈ (J i) | f' x = 0} != ∅

  have hφ_f' : ∀ i < n, φ i → ∀ x ∈ J i, |f' x| ≤ ε' := by
    intro i hi hJ y hy
    obtain ⟨x, h₁x, h₂x⟩ := exists_in_nonempty hJ
    have h : |f' y - f' x| ≤ ε' := 
      (f'_uniform_on_J i) hi y hy x h₁x (dist_J hy h₁x)
    simpa [h₂x] using h

  have hφ_f : ∀ i < n,
    φ i → ∀ x ∈ J i, ∀ y ∈ J i,
    |f x - f y| ≤ δ' * ε' := by
      intro i hi hφ x hx y hy
      have hxy : |x - y| ≤ δ' := dist_J hx hy
      have hf_J : ∀ x ∈ J i, DifferentiableAt ℝ f x := 
        contdiff_imp_diff_restriction hf
      have f_lip : |f x - f y| ≤ ε' * |x - y| := 
        Convex.norm_image_sub_le_of_norm_deriv_le 
          hf_J
          (fun x hx => by    
            have := hφ_f' i hi hφ x hx
            rwa [Real.norm_eq_abs])
          (convex_Icc (subdiv i) (subdiv (i+1)))
          hy hx
      nlinarith

  let A := {x ∈ I | f' x = 0}
  have K := {i < n | φ i}

  have A_sub_I : A ⊆ I := by
    intro x ⟨ h, _ ⟩
    exact h

  have hA : A ⊆ ⋃ i ∈ K, J i := by
    intro x ⟨ h, hx ⟩

  sorry

theorem sard_lemma (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) :
  is_negligeable (f '' {x | deriv f x = 0}) := 
by 
  sorry
