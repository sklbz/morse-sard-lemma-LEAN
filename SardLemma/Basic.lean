-- Basic.lean
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Data.Finset.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Order
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

lemma sard_lemma_compact {a b : ℝ} {f : ℝ → ℝ} (hμ : b - a > 0) (hf : ContDiff ℝ 1 f) :
  is_negligeable (f '' {x ∈ Icc a b | deriv f x = 0}) :=
by
  let I : Set ℝ := Icc a b
  let μ := b - a
  change μ > 0 at hμ
  intro ε hε
  let ε' := ε / μ
  have hε' : 0 < ε / μ := div_pos hε hμ
  have hI : IsCompact I := isCompact_Icc
  have f'_uniform : is_uniform_metric (deriv f) I :=
    uniform_derivative hI hf
  obtain ⟨δ, δ_pos, hδ⟩ := f'_uniform ε' hε'
  let k : ℤ := ⌈μ / δ⌉
  have hk : (k : ℝ) > 0 :=
    Int.cast_pos.2 (Int.ceil_pos.2 (div_pos hμ δ_pos))
  let δ' := μ / k
  let n : ℕ := k.toNat
  have n_eq_k : (n : ℝ) = (k : ℝ) := Eq.symm (nat_eq_toNat hk)
  let subdiv (i : ℕ) : ℝ := a + i * δ'
  let J (i : ℕ) : Set ℝ := Icc (subdiv i) (subdiv (i+1))
  let φ (i : ℕ) : Prop := {x ∈ (J i) | deriv f x = 0}.Nonempty
  have J_covers_I {x : ℝ} (hx : x ∈ I) : ∃ i < n, x ∈ J i := by
    suffices h : I = ⋃ i < n, J i by
      simp only [h, mem_iUnion, exists_prop] at hx
      exact hx
    exact subdivision_covers hk hμ
  let A := {x ∈ I | deriv f x = 0}
  let K := {i < n | φ i}
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
    ∑' (n : ℕ), (b n - a n) ≤ ε by
    exact subset_measure_maj h_imA h
  clear A h_imU hA h_imA J_covers_I
  let P (i : ℕ) (pair : ℝ×ℝ) : Prop :=
    pair.1 ≤ pair.2 ∧ |pair.1 - pair.2| ≤ δ' * ε' ∧
    f '' J i ⊆ Icc pair.1 pair.2
  have exist_bound : ∀ i ∈ K, ∃ pair : ℝ×ℝ, P i pair :=
    no_classical_part hμ hf hε' δ_pos hδ
  classical
  choose τ hτ using exist_bound
  let lower (i : ℕ) : ℝ := if hi : i ∈ K then (τ i hi).1 else 0
  let upper (i : ℕ) : ℝ := if hi : i ∈ K then (τ i hi).2 else 0
  let dist (i : ℕ) : ℝ := (upper i) - (lower i)
  have spec : ∀ i ∈ K, P i (lower i, upper i) := by
    intro i hi
    simp only [upper, lower, hi, ↓reduceDIte, Prod.mk.eta, hτ]
  unfold P at spec
  simp only at spec
  have hK : ∀ i ∈ K, dist i ≤ ε / n := by
    intro i hi
    have hs := spec i hi
    unfold dist δ' ε' at *
    rw [show (n : ℝ) = k by simpa [n] using (nat_eq_toNat hk).symm]
    field_simp at hs ⊢
    calc
      k * (upper i - lower i) ≤ |upper i - lower i| * k := by
        field_simp
        exact le_abs_self _
      _ = |lower i - upper i| * k := by rw [abs_sub_comm]
      _ ≤ ε := hs.2.1
  have hn {i : ℕ} (hi : i < n) : dist i ≤ ε / n := by
    by_cases h : i ∈ K
    · exact hK i h
    · unfold dist lower upper
      unfold n
      rw [← nat_eq_toNat hk]
      simp only [h, ↓reduceDIte, sub_self]
      refine div_nonneg (le_of_lt hε) (le_of_lt (RCLike.ofReal_pos.mp hk))
  let A : Finset ℕ := range n
  have hA : ∀ i ∉ A, dist i = 0 := by
    unfold A
    simp only [Finset.mem_range, not_lt]
    intro i hi
    apply Nat.not_lt.mpr at hi
    unfold dist upper lower K
    have hmem : i ∉ {i | i < n ∧ φ i} := by
      intro h
      exact hi h.1
    simp only [hmem, ↓reduceDIte, sub_self]
  let L := ⋃ i ∈ K, f '' (J i)
  let U := ⋃ n, Icc (lower n) (upper n)
  have hdist : ∑ i ∈ A, dist i ≤ ε := by
    calc
      ∑ i ∈ A, dist i
        ≤ ∑ i ∈ A, (ε / (n : ℝ)) := by
          refine sum_le_sum ?_
          unfold A
          simp only [Finset.mem_range]
          intro i hi
          exact hn hi
      _ = n * (ε / (n : ℝ)) := by
        unfold A
        simp only [sum_const, card_range, nsmul_eq_mul]
      _ = ε := by
        refine mul_div_cancel_of_imp' ?_
        intro h
        rw [← n_eq_k] at hk
        have hn : (n : ℝ) ≠ 0 := by
          exact Ne.symm (Std.ne_of_lt hk)
        exact not_neZero.mp fun a ↦ hn h
  use lower, upper
  change (∀ (n : ℕ), lower n ≤ upper n) ∧ L ⊆ U ∧
    ∑' (n : ℕ), (upper n - lower n) ≤ ε
  refine ⟨?_, ?_, ?_⟩
  · intro i
    by_cases hi : i ∈ K
    · apply (spec i hi).1
    · simp only [lower, upper, hi, ↓reduceDIte]
      rfl
  · unfold L U
    refine iUnion₂_subset_iff.mpr ?_
    intro i hi
    have h : f '' J i ⊆ Icc (lower i) (upper i) := (spec i hi).2.2
    exact subset_iUnion_of_subset i h
  · rw [tsum_eq_sum hA]
    exact hdist

theorem sard_lemma (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) :
  is_negligeable (f '' {x | deriv f x = 0}) :=
by
  have hcompact : ∀ n : ℕ,
    is_negligeable (f '' { x ∈ Icc (-n : ℝ) (n : ℝ) |
    deriv f x = 0}) := by
      intro n
      by_cases h : n > 0
      · have hsub : (n : ℝ) - (-n : ℝ) > 0 := by
          field_simp
          simp only [
            sub_neg_eq_add,
            pos_add_self_iff,
            zero_lt_one,
            mul_pos_iff_of_pos_right,
            Nat.cast_pos
          ]
          exact h
        exact sard_lemma_compact hsub hf
      · simp only [gt_iff_lt, not_lt, nonpos_iff_eq_zero] at h
        simp only [Set.mem_Icc, h, CharP.cast_eq_zero, neg_zero]
        refine negligeable_singleton ?_
        refine Subsingleton.image ?_ f
        intro x hx y hy
        simp only [mem_setOf_eq] at hx hy
        linarith
  suffices h :
    f '' {x | deriv f x = 0} =
    ⋃ (n : ℕ), f '' { x ∈ Icc (-n : ℝ) (n : ℝ) | deriv f x = 0} by
      rw [h]
      exact negligeable_union hcompact
  simp only [Set.mem_Icc]
  rw [← image_iUnion]
  ext x
  simp only [Set.mem_image, mem_setOf_eq, mem_iUnion, exists_and_right]
  refine ⟨?_, ?_⟩
  · intro ⟨y, h₁, h₂⟩
    use y
    rw [h₁, h₂]
    simp only [and_true]
    obtain ⟨n, hn⟩ := exists_nat_gt (|y|)
    refine ⟨n, ?_, ?_⟩
    · have hy : -|y| ≤ y := neg_abs_le y
      linarith
    · have hy : y ≤ |y| := le_abs_self y
      linarith
  · intro ⟨y, ⟨_, h₁⟩, h₂⟩
    refine ⟨y, h₁, h₂⟩
