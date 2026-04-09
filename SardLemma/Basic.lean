import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Data.Finset.Defs
import SardLemma.CeilDiv
import SardLemma.Monotonicity

open BigOperators
open SardLemma
open Monotonous

-- Définition d'un ensemble de mesure nulle
def is_negligeable (A : Set ℝ) : Prop :=
  ∀ ε > 0,
  ∃ (a b: ℕ → ℝ), (∀ n, a n ≤ b n) ∧ 
  (A ⊆ ⋃ n, Set.Icc (a n) (b n)) ∧
  (∀ n : ℕ, (∑ k ∈ Finset.range (n+1), (b k - a k)) ≤ ε)

lemma sard_lemma_compact (a b : ℝ) (f : ℝ → ℝ) (hμ : b - a > 0) (hf : ContDiff ℝ 1 f) : 
  is_negligeable (f '' {x ∈ Set.Icc a b | deriv f x = 0}) := 
by
  let I : Set ℝ := Set.Icc a b
  let μ := b-a
  let f' : ℝ → ℝ := deriv f

  change μ > 0 at hμ

  have hf'_cont : Continuous f' := ContDiff.continuous_deriv_one hf
  have hf'_cont_on_I : ContinuousOn f' I := hf'_cont.continuousOn

  have hI_compact : IsCompact I := isCompact_Icc

  have hf'_uniform : UniformContinuousOn f' I := 
    IsCompact.uniformContinuousOn_of_continuous hI_compact hf'_cont_on_I

  rw [Metric.uniformContinuousOn_iff] at hf'_uniform

  intro ε hε

  let ε' := ε / μ

  let hε' := div_pos hε hμ


  obtain ⟨δ, δ_pos, hδ⟩ := hf'_uniform ε' hε'

  let k := ⌈μ / δ⌉
  have hk : (k: ℝ) > 0 := Int.cast_pos.2 (Int.ceil_pos.2 (div_pos hμ δ_pos))

  let δ' := μ / k
  have δ'_pos: δ' > 0 := div_pos hμ hk
  have δ'_leq_δ: δ' ≤ δ := div_ceil_le μ δ hμ δ_pos

  have hδ': ∀ x ∈ I, ∀ y ∈ I, dist x y < δ' → dist (f' x) (f' y) < ε' := 
    weaker_uniform f' I δ δ' ε' hδ δ'_leq_δ

  sorry

theorem sard_lemma (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) : 
  is_negligeable (f '' {x | deriv f x = 0}) := 
by 
  sorry
