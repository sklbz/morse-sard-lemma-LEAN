-- Interval.lean
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Data.Real.Basic

open Set

namespace Interval

lemma abs_sub_le_of_Icc {a b x y : ℝ}
  (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) : |x - y| ≤ b - a :=
by
    have hx := Set.mem_Icc.mp hx
    have hy := Set.mem_Icc.mp hy
    obtain ⟨h₁x, h₂x⟩ := hx
    obtain ⟨h₁y, h₂y⟩ := hy
    refine abs_sub_le_of_le_of_le ?_ ?_ ?_ ?_
    · apply h₁x
    · apply h₂x
    · apply h₁y
    · apply h₂y
  

end Interval
