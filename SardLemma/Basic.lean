import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Data.Finset.Defs
import SardLemma.CeilDiv
import SardLemma.Uniform
import SardLemma.Measure

open Set
open Finset
open BigOperators

open Inequalities
open Uniform
open Measure

lemma sard_lemma_compact (a b : ℝ) (f : ℝ → ℝ) (hμ : b - a > 0) (hf : ContDiff ℝ 1 f) : 
  is_negligeable (f '' {x ∈ Icc a b | deriv f x = 0}) := 
by
  let I : Set ℝ := Icc a b
  let μ := b - a
  let f' : ℝ → ℝ := deriv f

  change μ > 0 at hμ

  have hI : IsCompact I := isCompact_Icc

  have hf'_uniform : is_uniform_metric f' I := uniform_derivative f I hI hf

  intro ε hε

  let ε' := ε / μ
  let hε' := div_pos hε hμ

  obtain ⟨δ, δ_pos, hδ⟩ := hf'_uniform ε' hε'

  let k : ℤ := ⌈μ / δ⌉
  have hk : (k: ℝ) > 0 := Int.cast_pos.2 (Int.ceil_pos.2 (div_pos hμ δ_pos))

  let δ' := μ / k
  have δ'_pos: δ' > 0 := div_pos hμ hk
  have δ'_leq_δ: δ' ≤ δ := div_ceil_le μ δ hμ δ_pos

  have hδ': is_uniform_with f' I ε' δ' := 
    uniform_transitivity f' I ε' δ δ' hδ δ'_leq_δ

  let n : ℕ := k.toNat
  let subdiv (i : ℕ) : ℝ := a + i * δ'
  let J (i : ℕ) : Set ℝ := Icc (subdiv i) (subdiv (i+1))
  have J_in_I : ∀ i, i ≤ n → J i ⊆ I := by
    intro i
    intro hi
    intro x
    intro hx
    apply?






  sorry

example (a b : ℝ) (sub : ℕ → ℝ) (n : ℕ) (ha: sub 0 = a) (hb : sub n = b) : Icc a b ⊆ ⋃ k ∈ range n, Icc (sub k) (sub (k+1))  := by
  apply?


theorem sard_lemma (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) : 
  is_negligeable (f '' {x | deriv f x = 0}) := 
by 
  sorry
