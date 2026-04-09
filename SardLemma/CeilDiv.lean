-- SardLemma/CeilDiv.lean
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Real.Basic

namespace SardLemma

lemma div_ceil_le (μ δ : ℝ) (hμ : μ > 0) (hδ : δ > 0) : μ / ⌈μ / δ⌉ ≤ δ := by
  have hk : (0 : ℝ) < (⌈μ / δ⌉ : ℤ) := Int.cast_pos.mpr (Int.ceil_pos.mpr (div_pos hμ hδ))
  have hle : μ / δ ≤ (⌈μ / δ⌉ : ℝ) := Int.le_ceil (μ / δ)
  rw [div_le_iff₀ hk]
  nlinarith [div_mul_cancel₀ μ (ne_of_gt hδ)]

end SardLemma
