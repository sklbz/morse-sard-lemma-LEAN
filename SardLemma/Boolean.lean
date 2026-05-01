import SardLemma.Tactics

namespace Boolean

lemma exists_in_nonempty {A : Set ℝ} {P : ℝ → Prop}
  (h : {x ∈ A | P x} != ∅) : ∃ x ∈ A, P x := by
  simp only [nonempty] at h
  exact h
end Boolean
