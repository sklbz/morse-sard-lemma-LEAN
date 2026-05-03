-- Construction.lean
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Analysis.Convex.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Real.Basic
import SardLemma.CompactImage
import SardLemma.Subdivision
import SardLemma.Lipschitz
import SardLemma.Interval
import SardLemma.Uniform
import SardLemma.Measure

open BigOperators
open Set

open Subdivision
open Lipschitz
open Interval
open Uniform
open Measure

lemma no_classical_part {a b ε δ : ℝ} {f : ℝ → ℝ}
  (hμ : b - a > 0) (hf : ContDiff ℝ 1 f)
  (hε : 0 < ε) (δ_pos : δ > 0)
  (hδ : is_uniform_with (deriv f) (Icc a b) ε δ) :
  let μ := b - a
  let f' : ℝ → ℝ := deriv f
  let k : ℤ := ⌈μ / δ⌉
  let n : ℕ := k.toNat
  let δ' := μ / k
  let subdiv (i : ℕ) : ℝ := a + i * δ'
  let J (i : ℕ) : Set ℝ := Icc (subdiv i) (subdiv (i+1))
  let φ (i : ℕ) : Prop := {x ∈ (J i) | f' x = 0}.Nonempty
  let P (i : ℕ) (pair : ℝ×ℝ) : Prop :=
    pair.1 ≤ pair.2 ∧ |pair.1 - pair.2| ≤ δ' * ε ∧
    f '' J i ⊆ Icc pair.1 pair.2
  let K := {i < n | φ i}
  ∀ i ∈ K, ∃ pair : ℝ×ℝ, P i pair :=
by
  intro μ f' k n δ' subdiv J φ P K i hi
  change μ > 0 at hμ
  let I := Icc a b
  have hI : IsCompact I := isCompact_Icc
  have hk : (k : ℝ) > 0 :=
    Int.cast_pos.2 (Int.ceil_pos.2 (div_pos hμ δ_pos))
  have hδ' : is_uniform_with f' I ε δ' :=
    uniform_transitivity hδ (div_ceil_le hμ δ_pos)
  have J_convex {i : ℕ} : Convex ℝ (J i) :=
    convex_Icc (subdiv i) (subdiv (i + 1))
  have J_in_I {i : ℕ} (hi : i < n) : J i ⊆ I :=
    subdivision_intervals_subset hk hμ hi
  have f'_uniform_on_J {i : ℕ} (hi : i < n) :
    is_uniform_with f' (J i) ε δ' :=
    uniform_restriction hδ' (J_in_I hi)
  have dist_J {i : ℕ}
    {x y : ℝ}
    (hx : x ∈ J i)
    (hy : y ∈ J i) :
    dist x y ≤ δ' := by
    have h : |x - y| ≤ (subdiv (i+1) - subdiv i) := abs_sub_le_of_Icc hx hy
    have hδ : subdiv (i+1) - subdiv i = δ' := by
      simp only [
        Nat.cast_add,
        Nat.cast_one,
        add_sub_add_left_eq_sub,
        subdiv]
      linarith
    simpa [dist, hδ] using h
  have hφ_f' {i : ℕ} (hi : i < n) (hJ : φ i) : ∀ x ∈ J i, |f' x| ≤ ε := by
    intro y hy
    obtain ⟨x, hx_in_J, hx_critical⟩ := hJ
    have h : |f' y - f' x| ≤ ε :=
      f'_uniform_on_J hi y hy x hx_in_J (dist_J hy hx_in_J)
    simpa [hx_critical] using h
  have hφ_f {i : ℕ} (hi : i < n) (hφ : φ i)
    {x y : ℝ} (hx : x ∈ J i) (hy : y ∈ J i) :
    |f x - f y| ≤ δ' * ε := by
      have hxy : |x - y| ≤ δ' := dist_J hx hy
      have lip_ineq : |f x - f y| ≤ ε * |x - y| :=
        deriv_bound_imp_lip hf (hφ_f' hi hφ) J_convex hy hx
      nlinarith
  have hφ {i : ℕ} (hi : i < n) (hφ : φ i)
    {y₁ y₂ : ℝ} (h₁ : y₁ ∈ f '' J i) (h₂ : y₂ ∈ f '' J i) :
    |y₁ - y₂| ≤ δ' * ε := by
    obtain ⟨x₁, hx₁, hy₁⟩ := (mem_image f (J i) y₁).mp h₁
    obtain ⟨x₂, hx₂, hy₂⟩ := (mem_image f (J i) y₂).mp h₂
    rw [← hy₁, ← hy₂]
    exact hφ_f hi hφ hx₁ hx₂
  have J_compact (i : ℕ) : IsCompact (J i) := isCompact_Icc
  have J_ne {i : ℕ} (hi : φ i) : (J i).Nonempty := by
    simp only [φ] at hi
    obtain ⟨x, hx, _⟩ := hi
    exact ⟨x, hx⟩
  have f_cont (i : ℕ) : ContinuousOn f (J i) :=
    Continuous.continuousOn (ContDiff.continuous hf)
  have fJ_bounds {i : ℕ} (hi : i ∈ K) :
    ∃ m M : ℝ, m ∈ f '' (J i) ∧ M ∈ f '' (J i) ∧
    ∀ x ∈ f '' (J i), m ≤ x ∧ x ≤ M := by
    simp only [K, mem_setOf_eq] at hi
    obtain ⟨hi₁, hi₂⟩ := hi
    exact compact_has_compact_image (J_compact i) (J_ne hi₂) (f_cont i)
  have hJ {i : ℕ} (hi : i ∈ K) :
    ∃ m M : ℝ, m ≤ M ∧ |m - M| ≤ δ' * ε ∧ f '' J i ⊆ Icc m M := by
    obtain ⟨m, M, hm₁, hM₁, h₂⟩ := fJ_bounds hi
    let hm₂ {x : ℝ} (hx : x ∈ f '' (J i)) := (h₂ x hx).1
    let hM₂ {x : ℝ} (hx : x ∈ f '' (J i)) := (h₂ x hx).2
    simp only [K, mem_setOf_eq] at hi
    obtain ⟨hi₁, hi₂⟩ := hi
    use m, M
    refine ⟨hm₂ hM₁, hφ hi₁ hi₂ hm₁ hM₁, h₂⟩
  simpa only [P, Prod.exists] using hJ hi
