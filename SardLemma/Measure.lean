import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Data.Finset.Defs

open BigOperators
open Finset

namespace Measure

def is_negligeable (A : Set ℝ) : Prop :=
  ∀ ε > 0,
  ∃ (a b: ℕ → ℝ), (∀ n, a n ≤ b n) ∧ 
  (A ⊆ ⋃ n, Set.Icc (a n) (b n)) ∧
  (∀ n : ℕ, (∑ k ∈ range (n+1), (b k - a k)) ≤ ε)

end Measure
