-- SardLemma/Monotonicity.lean
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Topology.UniformSpace.HeineCantor

namespace Uniform


def is_uniform_with (f : ℝ → ℝ) (I : Set ℝ) (ε δ : ℝ) : Prop :=
  ∀ x ∈ I, ∀ y ∈ I, dist x y < δ → dist (f x) (f y) < ε 

def is_uniform_metric (f : ℝ → ℝ) (I : Set ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, is_uniform_with f I ε δ

lemma uniform_derivative (f : ℝ → ℝ) (I : Set ℝ) (compact : IsCompact I) (hf : ContDiff ℝ 1 f) : is_uniform_metric (deriv f) I := by
  let f' := deriv f
  have hf'_cont : Continuous f' := ContDiff.continuous_deriv_one hf
  have hf'_cont_on_I : ContinuousOn f' I := hf'_cont.continuousOn
  have hf'_uniform : UniformContinuousOn f' I := 
    IsCompact.uniformContinuousOn_of_continuous compact hf'_cont_on_I
  rw [Metric.uniformContinuousOn_iff] at hf'_uniform
  exact hf'_uniform



lemma uniform_transitivity (f : ℝ → ℝ) (I : Set ℝ) (ε δ δ' : ℝ) (hδ : is_uniform_with f I ε δ) (hδ' : δ' ≤ δ) : is_uniform_with f I ε δ' := by
  intro x hx y hy h
  replace h: dist x y < δ := lt_of_lt_of_le h hδ'
  apply hδ at h
  apply h
  apply hx 
  exact hy


end Uniform
