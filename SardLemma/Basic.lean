import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Data.Finset.Defs

open BigOperators

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
  -- hε : ε > 0
  intro ε hε
  sorry

theorem sard_lemma (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) : 
  is_negligeable (f '' {x | deriv f x = 0}) := 
by 
  sorry
