-- SardLemma/Subdivision.lean
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Real.Basic

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
    let δ' := (b - a) / k
    let subdiv := fun i : ℕ => a + i * δ'
    let J := fun i : ℕ => Set.Icc (subdiv i) (subdiv (i + 1))
    let I := Set.Icc a b
    J i ⊆ I := by
  intro δ' subdiv J I
  have hi_plus: i + 1 ≤ k.toNat := by
    nlinarith
  refine Set.Icc_subset I ?_ (subdivision_bounds hk hμ hi_plus)
  exact subdivision_bounds hk hμ (le_of_lt hi)

end Subdivision
