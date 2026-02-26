/- Copyright (c) 2021 Antoine Chambert-Loir, María-Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María-Inés de Frutos-Fernández
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-! # Homogeneous algebra morphisms between graded algebras

-/

@[expose] public section
open MvPolynomial

variable {R S : Type*} [CommSemiring R] {S : Type*} [CommSemiring S] [Algebra R S]

/-- An `R`-algebra map `f` between graded algebras `A` and `B` is homogeneous
with respect to a map `φ : ι → κ` if, for every degree `i`, `f(𝒜 i) ⊆ ℬ (φ i)`. -/
def AlgHom.isHomogeneous {ι κ : Type*} {A : Type*} [CommSemiring A] [Algebra R A]
    (𝒜 : ι → Submodule R A) {B : Type*} [CommSemiring B] [Algebra R B] [Algebra S B]
    (ℬ : κ → Submodule S B) (φ : ι → κ) (f : A →ₐ[R] B) : Prop :=
  ∀ i a, a ∈ 𝒜 i → f a ∈ ℬ (φ i)

/-- The evaluation of a weighted homogeneous polynomial at
  elements of adequate grades is homogeneous -/
theorem AlgHom.isHomogeneous_aeval {σ : Type*} {ι κ : Type*} [AddCommMonoid ι] [AddCommMonoid κ]
    [DecidableEq κ] (A : Type*) [CommSemiring A] [Algebra R A] (𝒜 : κ → Submodule R A)
    [GradedAlgebra 𝒜] {w : σ → ι} (φ : ι →+ κ) (f : σ → A) (h : ∀ s : σ, f s ∈ 𝒜 (φ (w s))) :
    AlgHom.isHomogeneous (weightedHomogeneousSubmodule R w) 𝒜 φ (MvPolynomial.aeval f) := by
  intro i p hp
  rw [p.as_sum, map_sum]
  apply Submodule.sum_mem
  intro c hc
  rw [aeval_monomial, ← smul_eq_mul, algebraMap_smul]
  apply Submodule.smul_mem
  rw [Finsupp.prod]
  convert SetLike.finset_prod_npow_mem_graded c.support (fun j ↦ φ (w j)) f ⇑c (fun s _ ↦ h s)
  rw [MvPolynomial.mem_support_iff] at hc
  simp_rw [← map_nsmul, ← map_sum]
  rw [← hp hc, Finsupp.weight_apply, Finsupp.sum]
