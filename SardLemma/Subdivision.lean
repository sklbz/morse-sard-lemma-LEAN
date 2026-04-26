-- SardLemma/Subdivision.lean
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Tactic.Positivity
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

lemma subdivision_intervals_subset 
    {a b : ℝ} {k : ℤ}
    (n : ℕ) (hk : (k : ℝ) > 0) (hμ : b - a > 0) :
    let δ' := (b - a) / k
    let subdiv := fun i : ℕ => a + i * δ'
    let J := fun i : ℕ => Set.Icc (subdiv i) (subdiv (i + 1))
    ∀ i < n, J i ⊆ Set.Icc a b := by
  intro δ' subdiv J i hi
  intro x hx
  have hx := Set.mem_Icc.mp hx
  constructor
  · have : 0 ≤ i * δ' := by positivity
    linarith [hx.1]
  · have term_maj : i * δ' ≤ n * δ' := by gcongr
    have eq : n * ((b - a) / k) = b - a := toNat_mul_div_eq hk
    linarith [hx.2]

end Subdivision
