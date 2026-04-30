-- SardLemma/Subdivision.lean
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Real.Basic

open Set

namespace Subdivision

lemma div_ceil_le {μ δ : ℝ} (hμ : μ > 0) (hδ : δ > 0) : μ / ⌈μ / δ⌉ ≤ δ := by
  have hk : (0 : ℝ) < (⌈μ / δ⌉ : ℤ) := Int.cast_pos.mpr (Int.ceil_pos.mpr (div_pos hμ hδ))
  have hle : μ / δ ≤ (⌈μ / δ⌉ : ℝ) := Int.le_ceil (μ / δ)
  rw [div_le_iff₀ hk]
  nlinarith [div_mul_cancel₀ μ (ne_of_gt hδ)]

lemma nat_eq_toNat {k : ℤ} (hk : (k : ℝ) > 0) : (k : ℝ) = (k.toNat : ℝ) := by
  have hk' : 0 < k := Int.cast_pos.mp hk
  have h : 0 ≤ k := le_of_lt hk'
  have h' : (k.toNat : ℤ) = k := by simpa [not_le.mpr hk']
  exact_mod_cast h'.symm

lemma toNat_mul_div_eq
  {k : ℤ}
  {μ : ℝ}
  (hk : (k : ℝ) > 0) :
  k.toNat * (μ / k) = μ :=
by
  have hk_ne_zero : (k : ℝ) ≠ 0 := by positivity
  have hk_eq_n : (k : ℝ) = (k.toNat : ℝ) := nat_eq_toNat hk
  rw [← hk_eq_n]
  field_simp [hk_ne_zero]

lemma subdivision_bounds
    {a b : ℝ} {k : ℤ} {i : ℕ}
    (hk : (k : ℝ) > 0) (hμ : b - a > 0) (hi : i ≤ k.toNat) :
    let δ := (b - a) / k
    let subdiv := a + i * δ
    let I := Set.Icc a b
    subdiv ∈ I := by
  intro δ subdiv I
  let n := k.toNat
  let μ : ℝ := b - a
  have subdiv_above_a : a ≤ subdiv := by
    have term_pos : 0 ≤ i * δ := by positivity
    linarith
  have subdiv_below_b : subdiv ≤ b := by
    have term_maj : i * δ ≤ n * δ := by
      gcongr
    have eq : n * (μ / k) = μ := toNat_mul_div_eq hk
    linarith
  unfold I
  refine Set.mem_Icc.mpr ?_
  constructor
  · exact subdiv_above_a
  · exact subdiv_below_b

lemma subdivision_intervals_subset
    {a b : ℝ} {k : ℤ} {i : ℕ}
    (hk : (k : ℝ) > 0) (hμ : b - a > 0) (hi : i < k.toNat) :
    let δ := (b - a) / k
    let subdiv := fun i : ℕ => a + i * δ
    let J := fun i : ℕ => Set.Icc (subdiv i) (subdiv (i + 1))
    let I := Set.Icc a b
    J i ⊆ I := by
  intro δ subdiv J I
  have hi_plus: i + 1 ≤ k.toNat := by
    nlinarith
  refine Set.Icc_subset I ?_ (subdivision_bounds hk hμ hi_plus)
  exact subdivision_bounds hk hμ (le_of_lt hi)

def growing (a : ℕ → ℝ) : Prop :=
  ∀ i, (a i) ≤ (a (i + 1))

lemma growing_transitive {a : ℕ → ℝ} (ha : growing a) (n : ℕ) : a 0 ≤ a n := by
  induction n
  · rfl
  · (expose_names; exact Std.IsPreorder.le_trans (a 0) (a n) (a (n + 1)) h (ha n))

lemma subdivision_union {a : ℕ → ℝ} (n : ℕ) (ha : growing a) :
    let I := fun (i : ℕ) => Icc (a i) (a (i + 1))
    Icc (a 0) (a (n + 1)) = ⋃ i ≤ n, I i := by
  intro I
  induction n
  · simp only [zero_add, nonpos_iff_eq_zero, iUnion_iUnion_eq_left]
    unfold I
    rfl
  · rw [biUnion_le_succ]
    (expose_names; rw [← h])
    unfold I
    have h0 : a 0 ≤ a (n + 1) := growing_transitive ha (n + 1)
    have hn : a (n + 1) ≤ a (n + 1 + 1) := ha (n + 1)
    exact Eq.symm (Icc_union_Icc_eq_Icc h0 hn)


lemma subdivision_covers
    {a b : ℝ} {k : ℤ}
    (hk : (k : ℝ) > 0) (hμ : b - a > 0) :
    let δ := (b - a) / k
    let subdiv := fun i : ℕ => a + i * δ
    let I := Set.Icc a b
    let J := fun i : ℕ => Set.Icc (subdiv i) (subdiv (i + 1))
    I = ⋃ i < k.toNat, J i := by
  intro δ sub I
  unfold I
  have hsub : growing sub := by
    intro i
    unfold sub
    simp
    gcongr
    · simp
  have h := subdivision_union n hsub
  have h0 : a = sub 0 := by
    unfold sub
    simp
  have hn : b = sub (k.toNat) := by
    unfold sub
    unfold δ
    field_simp
    have h1 : k.toNat * (b - a) = k.toNat * b - k.toNat * a := by
      exact mul_sub_left_distrib (↑k.toNat) b a
    have h2 : k.toNat * b - k.toNat * a = - k.toNat * a + k.toNat * b := by
      field_simp
      simp
      constructor
      · exact sub_eq_neg_add b a
    rw [h1, h2]
    rw [← nat_eq_toNat hk]
    rw [← @AddSemigroup.add_assoc]
    rw [@neg_mul]
    field_simp
    simp
  rw [h0, hn]
  repeat rw [Int.toNat_of_nonneg hk]
  simp [Nat.cast_natCast]
  rw [Nat.lt_succ_iff]

end Subdivision
