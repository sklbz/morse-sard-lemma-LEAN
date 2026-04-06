import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Analysis.Series.Basic
open BigOperators

def majore (ε : ℝ) (u : ℕ → ℝ) : Prop :=
  Summable u ∧ ∑' n, u n ≤ ε

-- Définition d'un ensemble de mesure nulle
def is_negligeable (A : Set ℝ) : Prop :=
  ∀ ε >0 ,
  (∃ (a: ℕ → ℝ), ∃ (b: ℕ → ℝ), (∀ n, (a n)≤ (b n)) ∧ 
  (A ⊆ ⋃ n, Set.Icc (a n) (b n)) ∧
  (majore ε (a - b)))


theorem sard_lemma (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) : 
  is_negligeable (f '' {x | deriv f x = 0}) := 
by 
  sorry
