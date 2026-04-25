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
import SardLemma.CeilDiv
import SardLemma.Uniform
import SardLemma.Measure

open Set
open Finset
open BigOperators

open Inequalities
open Uniform
open Measure

lemma sard_lemma_compact (a b : ℝ) (f : ℝ → ℝ) (hμ : b - a > 0) (hf : ContDiff ℝ 1 f) : 
  is_negligeable (f '' {x ∈ Icc a b | deriv f x = 0}) := 
by
  let I : Set ℝ := Icc a b
  let μ := b - a
  let f' : ℝ → ℝ := deriv f

  change μ > 0 at hμ

  have hI : IsCompact I := isCompact_Icc

  have hf'_uniform : is_uniform_metric f' I := uniform_derivative f I hI hf

  intro ε hε

  let ε' := ε / μ
  let hε' := div_pos hε hμ

  obtain ⟨δ, δ_pos, hδ⟩ := hf'_uniform ε' hε'

  let k : ℤ := ⌈μ / δ⌉
  have hk : (k: ℝ) > 0 := Int.cast_pos.2 (Int.ceil_pos.2 (div_pos hμ δ_pos))

  let δ' := μ / k
  have δ'_pos: δ' > 0 := div_pos hμ hk
  have δ'_leq_δ: δ' ≤ δ := div_ceil_le μ δ hμ δ_pos

  have hδ': is_uniform_with f' I ε' δ' := 
    uniform_transitivity f' I ε' δ δ' hδ δ'_leq_δ

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
    have eq : n * (μ / k) = μ := by
      have hk_ne_zero : (k : ℝ) ≠ 0 := by positivity
      have hk_eq_n : (k : ℝ) = (n : ℝ) := by
        unfold n
        have hk' : 0 < k := by 
          simpa using hk
        have h : 0 ≤ k := le_of_lt hk'
        have h' : (k.toNat : ℤ) = k := by
          simpa [hk, not_le.mpr hk']
        exact_mod_cast h'.symm
      rw [← hk_eq_n]
      field_simp [hk_ne_zero]
    rw [eq] at term_maj
    have ineq : a + i * δ' ≤ a + μ := by
      gcongr
    unfold μ at ineq
    replace ineq : a + i * δ' ≤ b := by
      linarith
    exact ineq

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

  have f'_uniform_on_J : ∀ i < n, is_uniform_with f' (J i) ε' δ' := by
    intro i hi
    exact uniform_restriction f' I (J i) ε' δ' hδ' (J_in_I i hi)

  have dist_J (i : ℕ) 
    (x y : ℝ) 
    (hx : x ∈ J i)
    (hy : y ∈ J i) : 
    dist x y ≤ δ' := by
    have hx := Set.mem_Icc.mp hx
    have hy := Set.mem_Icc.mp hy
    obtain ⟨h₁x, h₂x⟩ := hx
    obtain ⟨h₁y, h₂y⟩ := hy

    have h : |x - y| ≤ (subdiv (i+1) - subdiv i) := by
      refine abs_sub_le_of_le_of_le ?_ ?_ ?_ ?_
      · apply h₁x
      · apply h₂x
      · apply h₁y
      · apply h₂y

    have hδ : subdiv (i+1) - subdiv i = δ' := by
      simp [subdiv]
      linarith
    simpa [dist, hδ] using h

  let φ (i : ℕ) : Bool := {x ∈ (J i) | f' x = 0} != ∅

  have hφ_f' : ∀ i < n, φ i → ∀ x ∈ J i, |f' x| ≤ ε' := by
    intro i hi hJ
    unfold φ at hJ
    simp only [
      bne_iff_ne,
      ne_eq,
      sep_eq_empty_iff_mem_false, 
      not_forall,
      exists_prop,
      Classical.not_not
    ] at hJ
    obtain ⟨x, hx⟩ := hJ
    obtain ⟨h₁x, h₂x⟩ := hx
    intro y hy

    have h : |f' y - f' x| ≤ ε' := by
      exact (f'_uniform_on_J i) hi y hy x h₁x (dist_J i y x hy h₁x)
    rw [h₂x] at h
    simpa using h

  have hφ_f : ∀ i < n,
    φ i → ∀ x ∈ J i, ∀ y ∈ J i,
    |f x - f y| ≤ δ' * ε' := by
      intro i hi hφ x hx y hy
      have hxy : |x - y| ≤ δ' := dist_J i x y hx hy
      have hf : ∀ x ∈ J i, DifferentiableAt ℝ f x := by
        intro x hx
        refine Differentiable.differentiableAt ?_
        have h : (1 : WithTop ℕ∞) ≠ 0 := by
          simp
        exact hf.differentiable h
      have f_lip : |f x - f y| ≤ ε' * |x - y| := Convex.norm_image_sub_le_of_norm_deriv_le 
        hf
        (fun x hx => by    
          have := hφ_f' i hi hφ x hx
          rwa [Real.norm_eq_abs])
        (convex_Icc (subdiv i) (subdiv (i+1)))
        hy hx
      sorry
  sorry

theorem sard_lemma (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) : 
  is_negligeable (f '' {x | deriv f x = 0}) := 
by 
  sorry
