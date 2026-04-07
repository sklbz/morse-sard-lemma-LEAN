import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Data.Finset.Defs

open BigOperators

example (I : Set ℝ) (f : ℝ → ℝ) (f_cont : ContinuousOn f I) (hI : IsCompact I) : 
    UniformContinuousOn f I := by
  exact IsCompact.uniformContinuousOn_of_continuous hI f_cont

-- Définition d'un ensemble de mesure nulle
def is_negligeable (A : Set ℝ) : Prop :=
  ∀ ε > 0,
  ∃ (a b: ℕ → ℝ), (∀ n, a n ≤ b n) ∧ 
  (A ⊆ ⋃ n, Set.Icc (a n) (b n)) ∧
  (∀ n : ℕ, (∑ k ∈ Finset.range (n+1), (b k - a k)) ≤ ε)

lemma sard_lemma_compact (a b : ℝ) (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) : 
  is_negligeable (f '' {x ∈ Set.Icc a b | deriv f x = 0}) := 
by
  let I : Set ℝ := Set.Icc a b
  let f' : ℝ → ℝ := deriv f

  have hf'_cont : Continuous f' := ContDiff.continuous_deriv_one hf
  have hf'_cont_on_I : ContinuousOn f' I := hf'_cont.continuousOn

  have hI_compact : IsCompact I := isCompact_Icc

  have hf'_uniform : UniformContinuousOn f' I := 
    IsCompact.uniformContinuousOn_of_continuous hI_compact hf'_cont_on_I
  -- hε : ε > 0
  intro ε hε

  obtain ⟨δ, δ_pos, hδ⟩ := hf'_uniform ε hε
  sorry

theorem sard_lemma (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) : 
  is_negligeable (f '' {x | deriv f x = 0}) := 
by 
  sorry
