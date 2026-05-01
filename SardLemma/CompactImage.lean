-- CompactImage.lean
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Analysis.Convex.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Real.Basic

open Set

lemma compact_has_compact_image {A : Set ℝ} {f : ℝ → ℝ} (h₁ : IsCompact A)
  (h₂ : A.Nonempty) (hf : ContinuousOn f A) :
  ∃ m M : ℝ, m ∈ f '' A ∧ M ∈ f '' A ∧
  ∀ x ∈ f '' A, m ≤ x ∧ x ≤ M := by
  obtain ⟨s, hs₁, hs₂⟩ :=
    IsCompact.exists_isMinOn h₁ h₂ hf
  obtain ⟨S, hS₁, hS₂⟩ :=
    IsCompact.exists_isMaxOn h₁ h₂ hf
  simp only [isMinOn_iff, isMaxOn_iff] at hs₂ hS₂
  let m := f s
  let M := f S
  obtain ⟨hm₁, hm₂⟩ : m ∈ f '' A ∧ ∀ x ∈ A, m ≤ f x := by
    unfold m
    constructor
    · exact mem_image_of_mem f hs₁
    · intro x hx
      exact hs₂ x hx
  obtain ⟨hM₁, hM₂⟩ : M ∈ f '' A ∧ ∀ x ∈ A, f x ≤ M := by
    unfold M
    constructor
    · exact mem_image_of_mem f hS₁
    · intro x hx
      exact hS₂ x hx
  use m, M
  use hm₁, hM₁
  intro y hy
  obtain ⟨x, hx, hy⟩ := (mem_image f A y).mp hy
  rw [← hy]
  constructor
  · exact hm₂ x hx
  · exact hM₂ x hx
