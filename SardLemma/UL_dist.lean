-- UL_dist.lean
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Data.Finset.Defs
import SardLemma.CompactImage
import SardLemma.Decidable
import SardLemma.Subdivision
import SardLemma.Uniform
import SardLemma.Measure

lemma name {μ ε : ℝ} {φ : ℕ → Prop} {k : ℤ} (hk : (k : ℝ) > 0)
  {upper lower : ℕ → ℝ}
  (spec : ∀ i ∈ K, lower i ≤ upper i ∧
  |lower i - upper i| ≤ μ / ↑k * (ε / μ)) :
  let dist (i : ℕ) : ℝ := (upper i) - (lower i)
  ∀ i ∈ K, dist i ≤ ε / n ∧ ∀ i < n, dist i ≤ ε / n ∧ ∀ i ≥ n, dist i = 0
 := by
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
