-- Basic.lean
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Data.Finset.Defs
import SardLemma.CompactImage
import SardLemma.Decidable
import SardLemma.Subdivision
import SardLemma.Uniform
import SardLemma.Measure

open BigOperators
open Finset
open Set

open Subdivision
open Uniform
open Measure

lemma sard_lemma_compact (a b : ℝ) (f : ℝ → ℝ) (hμ : b - a > 0) (hf : ContDiff ℝ 1 f) :
  is_negligeable (f '' {x ∈ Icc a b | deriv f x = 0}) :=
by
  let I : Set ℝ := Icc a b
  let μ := b - a
  let f' : ℝ → ℝ := deriv f

  change μ > 0 at hμ

  intro ε hε

  let ε' := ε / μ
  have hε' : 0 < ε / μ := div_pos hε hμ

  have hI : IsCompact I := isCompact_Icc
  have f'_uniform : is_uniform_metric f' I := uniform_derivative hI hf

  obtain ⟨δ, δ_pos, hδ⟩ := f'_uniform ε' hε'

  let k : ℤ := ⌈μ / δ⌉
  have hk : (k : ℝ) > 0 := Int.cast_pos.2 (Int.ceil_pos.2 (div_pos hμ δ_pos))

  let δ' := μ / k

  let n : ℕ := k.toNat
  let subdiv (i : ℕ) : ℝ := a + i * δ'
  let J (i : ℕ) : Set ℝ := Icc (subdiv i) (subdiv (i+1))

  let φ (i : ℕ) : Prop := {x ∈ (J i) | f' x = 0}.Nonempty

  have J_covers_I {x : ℝ} (hx : x ∈ I) : ∃ i < n, x ∈ J i := by
    suffices h : I = ⋃ i < n, J i by
      simp only [h, mem_iUnion, exists_prop] at hx
      exact hx
    exact subdivision_covers hk hμ

  let A := {x ∈ I | f' x = 0}
  let K := {i < n | φ i}

  have A_eq_A : {x ∈ I | deriv f x = 0} = A := by
    unfold A f'
    rfl

  rw [A_eq_A]
  clear A_eq_A

  have hA : A ⊆ ⋃ i ∈ K, J i := by
    intro x ⟨ h, hx ⟩
    obtain ⟨i, h, hi ⟩ := J_covers_I h
    have hφ : φ i := by
      unfold φ
      exact ⟨x, hi, hx⟩
    simp only [K, mem_setOf_eq, mem_iUnion, exists_prop, and_assoc]
    exact ⟨i, h, hφ, hi⟩

  have h_imU : f '' ⋃ i ∈ K, J i = ⋃ i ∈ K, f '' J i := by
    exact image_iUnion₂ f fun i j ↦ J i

  have h_imA : f '' A ⊆ ⋃ i ∈ K, f '' J i := by
    suffices h : f '' A ⊆ f '' ⋃ i ∈ K, J i by
      exact subset_of_subset_of_eq h h_imU
    exact image_mono hA

  suffices h :
    ∃ a b : ℕ → ℝ, (∀ (n : ℕ), a n ≤ b n) ∧
    ⋃ i ∈ K, f '' J i ⊆ ⋃ n, Icc (a n) (b n) ∧
    ∀ (n : ℕ), ∑ k ∈ Finset.range (n + 1), (b k - a k) ≤ ε by
    exact subset_measure_maj h_imA h

  clear A h_imU hA h_imA J_covers_I

  let P (i : ℕ) (pair : ℝ×ℝ) : Prop :=
    pair.1 ≤ pair.2 ∧ |pair.1 - pair.2| ≤ δ' * ε' ∧
    f '' J i ⊆ Icc pair.1 pair.2

  have exist_bound : ∀ i ∈ K, ∃ pair : ℝ×ℝ, P i pair :=
    no_classical_part hμ hf hε' δ_pos hδ

  open Classical in
  have exist_choice_fun : ∃ f : ℕ → ℝ × ℝ, ∀ i ∈ K, P i (f i) := by
    choose τ h using exist_bound
    refine ⟨fun (i : ℕ) => if hi : i ∈ K then τ i hi else (0, 0), ?_⟩
    intro i hi
    simp only [hi, ↓reduceDIte, h]
  let bound_choice := choose exist_choice_fun
  have spec : ∀ i ∈ K, P i (bound_choice i) :=
    choose_spec exist_choice_fun

  let lower (i : ℕ) : ℝ := if hi : i ∈ K then (bound_choice i).1 else 0
  let upper (i : ℕ) : ℝ := if hi : i ∈ K then (bound_choice i).2 else 0
  let dist (i : ℕ) : ℝ := (upper i) - (lower i)
  have spec : ∀ i ∈ K, P i (lower i, upper i) := by
    intro i hi
    simp only [upper, lower, hi, ↓reduceDIte, Prod.mk.eta, spec]

  unfold P at spec
  simp only at spec

  have hK : ∀ i ∈ K, dist i ≤ ε / n := by
    intro i hi
    unfold dist
    unfold δ' ε' at spec
    have hn : (n : ℝ) = (k : ℝ) := by
      unfold n
      exact Eq.symm (nat_eq_toNat hk)
    rw [hn]
    field_simp at spec
    field_simp
    have h : (upper i) - (lower i) ≤ |(upper i) - (lower i)| :=
      le_abs_self (upper i - lower i)
    have h : ((upper i) - (lower i)) * k ≤ |(upper i) - (lower i)| * k :=
      (mul_le_mul_iff_of_pos_right hk).mpr h
    have h_abs : |(lower i) - (upper i)| * k ≤ ε := (spec i hi).2.1
    have eq_invert : |(lower i) - (upper i)| = |(upper i) - (lower i)| := by
      exact abs_sub_comm (lower i) (upper i)
    rw [eq_invert] at h_abs
    exact Std.IsPreorder.le_trans
      ((upper i - lower i) * ↑k)
      (|upper i - lower i| * ↑k)
      ε h h_abs

  have hn {i : ℕ} (hi : i < n) : dist i ≤ ε / n := by
    if h : i ∈ K then
      exact hK i h
    else
      expose_names
      unfold dist lower upper
      simp only [h, ↓reduceDIte, sub_self]
      have n_pos : 0 ≤ (n : ℝ) := by
        unfold n
        rw [← nat_eq_toNat hk]
        exact le_of_lt (RCLike.ofReal_pos.mp hk)
      refine div_nonneg (le_of_lt hε) n_pos

  have hbeyondK {i : ℕ} (hi : i ≥ n) : i ∉ K := by
    unfold K
    refine notMem_setOf_iff.mpr ?_
    refine Decidable.not_and_iff_or_not.mpr ?_
    constructor
    · exact Nat.not_lt.mpr hi

  have hinfty {i : ℕ} (hi : i ≥ n) : dist i = 0 := by
    unfold dist upper lower
    simp only [hbeyondK hi, ↓reduceDIte, sub_self]

  have hpos (i : ℕ) : dist i ≥ 0 := by
    unfold dist
    simp only [ge_iff_le, sub_nonneg]
    if hi : i ∈ K then
      exact (spec i hi).1
    else
      unfold upper lower
      simp only [hi, ↓reduceDIte, Std.le_refl]

  let L := ⋃ i ∈ K, f '' (J i)
  let U := ⋃ n, Icc (lower n) (upper n)


  use lower, upper

  change (∀ (n : ℕ), lower n ≤ upper n) ∧ L ⊆ U ∧
    ∀ (n : ℕ), ∑ k ∈ Finset.range (n + 1), (upper k - lower k) ≤ ε

  refine ⟨?_, ?_, ?_⟩
  · intro i
    if hi : i ∈ K then
      apply (spec i hi).1
    else
      expose_names
      simp only [lower, upper, hi, ↓reduceDIte]
      rfl
  · unfold L U
    refine iUnion₂_subset_iff.mpr ?_
    intro i hi
    have h : f '' J i ⊆ Icc (lower i) (upper i) := (spec i hi).2.2
    exact subset_iUnion_of_subset i h
  · intro m
    change ∑ i ∈ Finset.range (m + 1), dist i ≤ ε
    if h : m > n then
      sorry
    else
      simp only [gt_iff_lt, not_lt] at h
      have hpos : ∀ i : ℕ, dist i ≥ 0 := by
        intro i
        exact RCLike.ofReal_nonneg.mp (hpos i)
      have h :
        ∑ i ∈ Finset.range (m + 1), dist i ≤
        ∑ i ∈ Finset.range (n + 1), dist i := by
          sorry
      sorry

theorem sard_lemma (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) :
  is_negligeable (f '' {x | deriv f x = 0}) :=
by
  sorry
