/-
Copyright (c) 2025 Antoine Chambert-Loir, María-Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María-Inés de Frutos-Fernández
-/
module

public import Mathlib.Data.Finset.Sym
public import Mathlib.Data.Finsupp.SMul

variable {ι α : Type*} [DecidableEq ι] [DecidableEq α] [AddCommMonoid α]

theorem Sym.val_sum_eq_sum_count_smul {n : ℕ} {k : Sym (ι →₀ α) n}
    {s : Finset (ι →₀ α)} (hk : k ∈ s.sym n) :
    k.val.sum = ∑ d ∈ s, Multiset.count d k • d := by
  rw [Finset.sum_multiset_count_of_subset _ s]
  · apply Finset.sum_congr rfl (by simp)
  intro x hx
  simp only [Sym.val_eq_coe, Multiset.mem_toFinset, Sym.mem_coe] at hx
  simp only [Finset.mem_sym_iff] at hk
  exact hk x hx
