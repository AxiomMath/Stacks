module

public import Mathlib.RingTheory.Artinian.Module

/-!
# Simple modules over Artinian rings

This file contains some results about the existence and the dimension of simple modules
over Artinian rings.

## Main results

* `exists_simple_submod` : Over an Artinian ring, every nonzero module contains a simple submodule.
* `Module.finite_of_simple_tower` : A simple module over a finite `k`-algebra `A` is
  finite-dimensional over `k` where `k` is any commutative semiring.

## Tags
Artinian ring, simple module, finite-dimensional

-/

@[expose] public section

universe u

@[stacks 0746 "(2)"]
lemma exists_simple_submod (A M : Type*) [Ring A] [Nontrivial M] [AddCommGroup M]
    [Module A M] [IsArtinianRing A] : ∃ (p : Submodule A M), IsSimpleModule A p := by
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  have : Nontrivial (Submodule.span A {m}) :=
    ⟨⟨⟨m, Submodule.mem_span_singleton_self m⟩, ⟨0, by simp [hm]⟩⟩⟩
  obtain ⟨a, ha⟩ := IsAtomic.exists_atom (Submodule A (Submodule.span A {m}))
  have : IsSimpleModule A a := isSimpleModule_iff_isAtom.mpr ha
  exact ⟨a.map (Submodule.span A {m}).subtype,
    IsSimpleModule.congr (a.equivMapOfInjective _ (Submodule.injective_subtype _)).symm⟩

-- here we have to restrict universe because `A` and `Submodule A A` lives in the same universe
@[stacks 0746 "(1)"]
lemma exists_simple_submod_algebra (A : Type u) [Ring A] [Nontrivial A] [IsArtinianRing A] :
    ∃ (M : Type u) (_ : AddCommGroup M) (_ : Module A M), IsSimpleModule A M := by
  obtain ⟨p, hp⟩ := exists_simple_submod A A
  exact ⟨p, inferInstance, inferInstance, hp⟩

@[stacks 0746 "(3)"]
lemma Module.finite_of_simple_tower (k A M : Type*) [CommSemiring k] [Ring A] [Algebra k A]
    [Module.Finite k A] [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
    [IsSimpleModule A M] : Module.Finite k M := by
  have : Nontrivial M := IsSimpleModule.nontrivial A M
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  exact ⟨Submodule.FG.restrictScalars (IsSimpleModule.span_singleton_eq_top A hm ▸
    Submodule.fg_span_singleton m)⟩
