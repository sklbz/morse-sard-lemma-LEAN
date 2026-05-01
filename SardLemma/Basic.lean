-- Basic.lean
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
import SardLemma.Tactics
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

  have f'_uniform : is_uniform_metric f' I := uniform_derivative hI hf

  intro ε hε

  let ε' := ε / μ
  let hε' : 0 < ε / μ := div_pos hε hμ

  obtain ⟨δ, δ_pos, hδ⟩ := f'_uniform ε' hε'

  let k : ℤ := ⌈μ / δ⌉
  have hk : (k : ℝ) > 0 := Int.cast_pos.2 (Int.ceil_pos.2 (div_pos hμ δ_pos))

  let δ' := μ / k
  have δ'_pos : δ' > 0 := div_pos hμ hk
  have δ'_leq_δ : δ' ≤ δ := div_ceil_le hμ δ_pos

  have hδ' : is_uniform_with f' I ε' δ' :=
    uniform_transitivity hδ δ'_leq_δ

  clear δ'_leq_δ δ_pos hδ f'_uniform hI

  let n : ℕ := k.toNat
  let subdiv (i : ℕ) : ℝ := a + i * δ'
  let J (i : ℕ) : Set ℝ := Icc (subdiv i) (subdiv (i+1))

  have J_convex {i : ℕ} : Convex ℝ (J i) := by
    let a : ℝ := subdiv i; let b : ℝ := subdiv (i + 1)
    have h : Convex ℝ (Icc a b) := convex_Icc (subdiv i) (subdiv (i + 1))
    exact h

  have J_in_I {i : ℕ} (hi : i < n) : J i ⊆ I :=
    subdivision_intervals_subset hk hμ hi

  have f'_uniform_on_J {i : ℕ} (hi : i < n) : is_uniform_with f' (J i) ε' δ' :=
    uniform_restriction hδ' (J_in_I hi)

  clear hδ'

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

  have hφ_f' {i : ℕ} (hi : i < n) (hJ : φ i) : ∀ x ∈ J i, |f' x| ≤ ε' := by
    intro y hy
    obtain ⟨x, h₁x, h₂x⟩ := exists_in_nonempty hJ
    have h : |f' y - f' x| ≤ ε' :=
      f'_uniform_on_J hi y hy x h₁x (dist_J hy h₁x)
    simpa [h₂x] using h

  have hφ_f {i : ℕ} (hi : i < n) (hφ : φ i)
    {x y : ℝ} (hx : x ∈ J i) (hy : y ∈ J i) :
    |f x - f y| ≤ δ' * ε' := by
      have hxy : |x - y| ≤ δ' := dist_J hx hy
      have lip_ineq : |f x - f y| ≤ ε' * |x - y| :=
        deriv_bound_imp_lip hf (hφ_f' hi hφ) J_convex hy hx
      nlinarith

  have hφ {i : ℕ} (hi : i < n) (hφ : φ i)
    {y₁ y₂ : ℝ} (h₁ : y₁ ∈ f '' J i) (h₂ : y₂ ∈ f '' J i) :
    |y₁ - y₂| ≤ δ' * ε' := by
    obtain ⟨x₁, hx₁, hy₁⟩ := (mem_image f (J i) y₁).mp h₁
    obtain ⟨x₂, hx₂, hy₂⟩ := (mem_image f (J i) y₂).mp h₂
    rw [← hy₁, ← hy₂]
    exact hφ_f hi hφ hx₁ hx₂

  clear J_in_I J_convex dist_J hφ_f' hφ_f f'_uniform_on_J

  have J_covers_I {x : ℝ} (hx : x ∈ I) : ∃ i < n, x ∈ J i := by
    suffices h : I = ⋃ i < n, J i by
      simp only [h, mem_iUnion, exists_prop] at hx
      exact hx
    exact subdivision_covers hk hμ

  let A := {x ∈ I | f' x = 0}
  let K := {i < n | φ i}

  have A_eq_A : {x ∈ I | deriv f x = 0} = A := by
    unfold A
    unfold f'
    rfl

  rw [A_eq_A]
  clear A_eq_A

  have hA : A ⊆ ⋃ i ∈ K, J i := by
    intro x ⟨ h, hx ⟩
    obtain ⟨i, h, hi ⟩ := J_covers_I h
    have hφ : φ i := by
      unfold φ
      simp only [nonempty]
      exact ⟨x, hi, hx⟩
    unfold K
    simp only [mem_setOf_eq, mem_iUnion, exists_prop, and_assoc]
    exact ⟨i, h, hφ, hi⟩

  have h_imU : f '' ⋃ i ∈ K, J i = ⋃ i ∈ K, f '' J i := by
    exact image_iUnion₂ f fun i j ↦ J i

  have h_imA : f '' A ⊆ ⋃ i ∈ K, f '' J i := by
    suffices h : f '' A ⊆ f '' ⋃ i ∈ K, J i by
      exact subset_of_subset_of_eq h h_imU
    exact image_mono hA

  clear h_imU hA

  suffices h :
    ∃ a b : ℕ → ℝ, (∀ (n : ℕ), a n ≤ b n) ∧
    ⋃ i ∈ K, f '' J i ⊆ ⋃ n, Icc (a n) (b n) ∧
    ∀ (n : ℕ), ∑ k ∈ Finset.range (n + 1), (b k - a k) ≤ ε by
    exact subset_measure_maj h_imA h

  clear A h_imA J_covers_I

  have J_compact (i : ℕ) : IsCompact (J i) := isCompact_Icc
  have J_ne {i : ℕ} (hi : φ i) : (J i).Nonempty := by
    unfold φ at hi
    simp only [nonempty] at hi
    obtain ⟨x, hx, _⟩ := hi
    exact ⟨x, hx⟩

  have f_cont (i : ℕ) : ContinuousOn f (J i) :=
    Continuous.continuousOn (ContDiff.continuous hf)

  have fJ_bounds {i : ℕ} (hi : i ∈ K) :
    ∃ m M : ℝ, m ∈ f '' (J i) ∧ M ∈ f '' (J i) ∧
    ∀ x ∈ f '' (J i), m ≤ x ∧ x ≤ M := by
    unfold K at hi
    simp only [mem_setOf_eq] at hi
    obtain ⟨hi₁, hi₂⟩ := hi
    exact compact_has_compact_image (J_compact i) (J_ne hi₂) (f_cont i)

  clear J_compact J_ne

  have hJ {i : ℕ} (hi : i ∈ K) :
    ∃ m M : ℝ, m ≤ M ∧ |m - M| ≤ δ' * ε' ∧ f '' J i ⊆ Icc m M := by
    obtain ⟨m, M, hm₁, hM₁, h₂⟩ := fJ_bounds hi
    let hm₂ {x : ℝ} (hx : x ∈ f '' (J i)) := (h₂ x hx).1
    let hM₂ {x : ℝ} (hx : x ∈ f '' (J i)) := (h₂ x hx).2
    unfold K at hi
    simp only [mem_setOf_eq] at hi
    obtain ⟨hi₁, hi₂⟩ := hi
    use m, M
    refine ⟨hm₂ hM₁, hφ hi₁ hi₂ hm₁ hM₁, h₂⟩

  let P (i : ℕ) (pair : ℝ×ℝ) : Prop :=
    pair.1 ≤ pair.2 ∧ |pair.1 - pair.2| ≤ δ' * ε' ∧
    f '' J i ⊆ Icc pair.1 pair.2

  have exist_bound : ∀ i ∈ K, ∃ pair : ℝ×ℝ, P i pair := by
    intro i hi
    unfold P
    simp only [Prod.exists]
    exact hJ hi

  open Classical in
  have exist_choice_fun : ∃ f : ℕ → ℝ × ℝ, ∀ i ∈ K, P i (f i) := by
    refine ⟨fun i => ?_, fun i hi => ?_⟩
    · exact if hi : i ∈ K then choose (exist_bound i hi) else (0, 0)
    · simp only [hi, ↓reduceDIte]
      exact choose_spec (exist_bound i hi)
  open Classical in
  let bound_choice := choose exist_choice_fun
  open Classical in
  have spec : ∀ i ∈ K, P i (bound_choice i) := by
    unfold bound_choice
    exact choose_spec exist_choice_fun

  let lower (i : ℕ) : ℝ := if hi : i ∈ K then (bound_choice i).1 else 0
  let upper (i : ℕ) : ℝ := if hi : i ∈ K then (bound_choice i).2 else 0
  have spec_prod : ∀ i ∈ K, P i (lower i, upper i) := by
    intro i hi
    unfold upper lower
    simp only [hi, ↓reduceDIte, Prod.mk.eta]
    exact spec i hi

  sorry

theorem sard_lemma (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) :
  is_negligeable (f '' {x | deriv f x = 0}) :=
by
  sorry
