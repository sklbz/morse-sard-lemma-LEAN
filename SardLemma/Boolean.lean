import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic

open Set

namespace Boolean

lemma exists_in_nonempty {A : Set ℝ} {P : ℝ → Prop}
  (h : {x ∈ A | P x} != ∅) : ∃ x ∈ A, P x := by
  simp only [
    bne_iff_ne,
    ne_eq,
    sep_eq_empty_iff_mem_false, 
    not_forall,
    exists_prop,
    Classical.not_not
  ] at h
  exact h
end Boolean
