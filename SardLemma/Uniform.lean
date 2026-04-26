-- SardLemma/Uniform.lean
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Topology.UniformSpace.HeineCantor

namespace Uniform

def is_uniform_with (f : ℝ → ℝ) (I : Set ℝ) (ε δ : ℝ) : Prop :=
  ∀ x ∈ I, ∀ y ∈ I, dist x y <= δ → dist (f x) (f y) <= ε 

def is_uniform_metric (f : ℝ → ℝ) (I : Set ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, is_uniform_with f I ε δ

lemma uniform_derivative
  {f : ℝ → ℝ}
  {I : Set ℝ}
  (compact : IsCompact I)
  (hf : ContDiff ℝ 1 f) :
  is_uniform_metric (deriv f) I := by
  let f' := deriv f
  have hf'_cont : Continuous f' := ContDiff.continuous_deriv_one hf
  have hf'_cont_on_I : ContinuousOn f' I := hf'_cont.continuousOn
  have hf'_uniform : UniformContinuousOn f' I := 
    IsCompact.uniformContinuousOn_of_continuous compact hf'_cont_on_I
  rw [Metric.uniformContinuousOn_iff] at hf'_uniform
  intro ε hε
  obtain ⟨δ, hδpos, hδ⟩ := hf'_uniform (ε / 2) (by linarith)
  use δ/2
  constructor
  · linarith
  · intro x hx y hy hxy
    have hxy : dist x y < δ := by
      exact lt_of_le_of_lt hxy (by linarith)
    have h : dist (f' x) (f' y) < ε / 2 := hδ x hx y hy hxy
    have : dist (f' x) (f' y) ≤ ε :=
      le_of_lt (lt_of_lt_of_le h (by linarith))
    exact this

lemma uniform_transitivity
  {f : ℝ → ℝ}
  {I : Set ℝ}
  {ε δ δ' : ℝ}
  (hδ : is_uniform_with f I ε δ)
  (hδ' : δ' ≤ δ) :
  is_uniform_with f I ε δ' := by
  intro x hx y hy h
  replace h: dist x y <= δ := by 
    exact Std.IsPreorder.le_trans (dist x y) δ' δ h hδ'
  apply hδ at h
  · apply h
  · apply hx 
  exact hy

lemma uniform_restriction
  {f : ℝ → ℝ}
  {I J : Set ℝ}
  {ε δ : ℝ}
  (hI : is_uniform_with f I ε δ)
  (hJ : J ⊆ I) : 
  is_uniform_with f J ε δ := by
  intro x hx y hy hdist
  have hx: x ∈ I := Set.mem_of_subset_of_mem hJ hx
  have hy: y ∈ I := Set.mem_of_subset_of_mem hJ hy
  (expose_names; exact Metric.mem_closedBall.mp (hI x (hJ hx_1) y hy hdist))

end Uniform
