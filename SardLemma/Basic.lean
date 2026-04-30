-- Basic.lean
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Analysis.Convex.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Real.Basic
import SardLemma.Subdivision
import SardLemma.Lipschitz
import SardLemma.Interval
import SardLemma.Uniform
import SardLemma.Measure
import SardLemma.Boolean

open BigOperators
open Set

open Subdivision
open Lipschitz
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

  have hJ_convex {i : ℕ} : Convex ℝ (J i) := by
    let a : ℝ := subdiv i; let b : ℝ := subdiv (i + 1)
    have h : Convex ℝ (Icc a b) := convex_Icc (subdiv i) (subdiv (i + 1))
    exact h

  have J_in_I {i : ℕ} (hi : i < n) : J i ⊆ I :=
    subdivision_intervals_subset hk hμ hi

  have f'_uniform_on_J {i : ℕ} (hi : i < n) : is_uniform_with f' (J i) ε' δ' :=
    uniform_restriction hδ' (J_in_I hi)

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

  have hφ_f' {i : ℕ} (hi : i < n) (hJ : φ i)
    {x : ℝ} (hx : x ∈ J i) : |f' x| ≤ ε' := by
    obtain ⟨critical_point, h₁, h₂⟩ := exists_in_nonempty hJ
    have h : |f' x - f' critical_point| ≤ ε' :=
      f'_uniform_on_J  hi x hx critical_point h₁ (dist_J hx h₁)
    simpa [h₂] using h

  have hφ_f' {i : ℕ} (hi : i < n) (hJ : φ i) :∀ x ∈ J i, |f' x| ≤ ε' := by
    intro y hy
    obtain ⟨x, h₁x, h₂x⟩ := exists_in_nonempty hJ
    have h : |f' y - f' x| ≤ ε' :=
      f'_uniform_on_J  hi y hy x h₁x (dist_J hy h₁x)
    simpa [h₂x] using h

  have hφ_f : ∀ i < n,
    φ i → ∀ x ∈ J i, ∀ y ∈ J i,
    |f x - f y| ≤ δ' * ε' := by
      intro i hi hφ x hx y hy
      have hxy : |x - y| ≤ δ' := dist_J hx hy
      have lip_ineq : |f x - f y| ≤ ε' * |x - y| :=
        deriv_bound_imp_lip hf (hφ_f' hi hφ) hJ_convex hy hx
      nlinarith

  let A := {x ∈ I | f' x = 0}
  have K := {i < n | φ i}

  have A_sub_I : A ⊆ I := by
    intro x ⟨ h, _ ⟩
    exact h

  have hA : A ⊆ ⋃ i ∈ K, J i := by
    intro x ⟨ h, hx ⟩
    sorry

  sorry

theorem sard_lemma (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) :
  is_negligeable (f '' {x | deriv f x = 0}) :=
by
  sorry
