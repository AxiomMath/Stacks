module

public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import Mathlib.RingTheory.RingHom.Etale
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.FiniteType.Pi
public import StacksFrontier.RingTheory.Rig.Reduction
public import StacksFrontier.RingTheory.Smooth.Reduced
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletionOver
public import StacksFrontier.Topology.Algebra.AdicTopology.FiniteTypeIsLocalRefined
public import StacksFrontier.Topology.Algebra.AdicTopology.FiniteTypeOnReductionsIsLocal
public import StacksFrontier.Topology.Algebra.AdicTopology.LocalPropertiesRefined

/-!
# Finite type on reductions is a local property: the refined forms

A continuous homomorphism of linearly topologized rings is of finite type on reductions when the
induced map of reductions is of finite type. This property is local on morphisms of countably
indexed weakly admissible topological rings.

These are the strengthened and newly added declarations of the 2026-10 chapter-87 round that
belong with `StacksFrontier.Topology.Algebra.AdicTopology.FiniteTypeOnReductionsIsLocal`. A
declaration of that module whose statement the round strengthened keeps its original statement
there; its strengthened form lives here under a primed name.

## Main results

* `TopologicalRing.surjective_redMap_of_surjective`: a surjective continuous homomorphism induces
  a surjection on reductions.
* `TopologicalRing.isFiniteTypeOnReductions_isomorphismInvariant`: being of finite type on
  reductions is invariant under bicontinuous isomorphisms of the source and the target.
* `TopologicalRing.isFiniteTypeOnReductions_propertyIsLocal'`: being of finite type on reductions
  is a local property of morphisms of countably indexed weakly admissible topological rings.
-/

@[expose] public section

namespace TopologicalRing

open Filter
open scoped Topology

section Nilradical

variable {R : Type*} [CommRing R] [TopologicalSpace R] [IsLinearTopology R R]

end Nilradical

section Reduction

universe u

variable {A A' : Type u} [CommRing A] [TopologicalSpace A] [IsLinearTopology A A] [CommRing A']

variable [IsTopologicalRing A]

end Reduction

section Functorial

variable {X Y Z : Type*} [CommRing X] [TopologicalSpace X] [IsLinearTopology X X]
  [CommRing Y] [TopologicalSpace Y] [IsLinearTopology Y Y]
  [CommRing Z] [TopologicalSpace Z] [IsLinearTopology Z Z]

/-- A surjective continuous homomorphism induces a surjection on reductions. -/
public theorem surjective_redMap_of_surjective (φ : X →+* Y) (hφ : Continuous φ)
    (hsurj : Function.Surjective φ) : Function.Surjective (redMap φ hφ) := by
  intro z
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨x, rfl⟩ := hsurj y
  exact ⟨Ideal.Quotient.mk _ x, Ideal.quotientMap_mk⟩

end Functorial

section CanonicalMap

universe u

variable {A A' : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsLinearTopology A A] [CommRing A']

end CanonicalMap

section Pi

variable {ι : Type*} {A : ι → Type*} [∀ i, CommRing (A i)]

variable [∀ i, TopologicalSpace (A i)]

end Pi

section Local

universe u

/-- Finite type on reductions is carried along a bicontinuous isomorphism of the source and of
the target: the reduction of the transported map is the composite of the reductions, and the
reductions of the two isomorphisms are surjective, hence of finite type. -/
private theorem finiteType_redMap_transport {B A B' A' : Type u}
    [CommRing B] [TopologicalSpace B] [IsLinearTopology B B]
    [CommRing A] [TopologicalSpace A] [IsLinearTopology A A]
    [CommRing B'] [TopologicalSpace B'] [IsLinearTopology B' B']
    [CommRing A'] [TopologicalSpace A'] [IsLinearTopology A' A']
    (eB : B ≃+* B') (eA : A ≃+* A')
    (heBs : Continuous eB.symm) (heA : Continuous eA)
    (f : B →+* A) (hf : Continuous f) (h : (redMap f hf).FiniteType) :
    (redMap ((eA.toRingHom.comp f).comp eB.symm.toRingHom)
      ((heA.comp hf).comp heBs)).FiniteType := by
  rw [redMap_comp eB.symm.toRingHom (eA.toRingHom.comp f) heBs (heA.comp hf),
    redMap_comp f eA.toRingHom hf heA]
  exact ((RingHom.FiniteType.of_surjective _
      (surjective_redMap_of_surjective eA.toRingHom heA eA.surjective)).comp h).comp
    (RingHom.FiniteType.of_surjective _
      (surjective_redMap_of_surjective eB.symm.toRingHom heBs eB.symm.surjective))

/-- **Stacks 0GC2**, presentation independence: being of finite type on reductions does not
depend on the chosen presentations of the source and the target. -/
public theorem isFiniteTypeOnReductions_isomorphismInvariant :
    IsomorphismInvariant.{u}
      (fun {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
        [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (φ : B →+* A) ↦
        FiniteTypeOnReductionsProperty φ)
      IsCountablyWeaklyAdmissible := by
  intro B A B' A' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  intro eB eA heB heBs heA heAs f hf _ _ _ _
  constructor
  · intro h _ _
    obtain ⟨_, hred⟩ := h
    exact ⟨(heA.comp hf).comp heBs, finiteType_redMap_transport eB eA heBs heA f hf hred⟩
  · intro h _ _
    obtain ⟨_, hred⟩ := h
    have hback := finiteType_redMap_transport eB.symm eA.symm heB heAs
      ((eA.toRingHom.comp f).comp eB.symm.toRingHom) ((heA.comp hf).comp heBs) hred
    refine ⟨hf, ?_⟩
    simp only [RingEquiv.symm_symm] at hback
    rwa [redMap_congr (show (eA.symm.toRingHom.comp
      ((eA.toRingHom.comp f).comp eB.symm.toRingHom)).comp eB.toRingHom = f by ext x; simp)
      ((heAs.comp ((heA.comp hf).comp heBs)).comp heB) hf] at hback

/-- **Finite type on reductions is a local property of morphisms of countably indexed weakly
admissible topological rings** (Stacks 0GC2). -/
public theorem isFiniteTypeOnReductions_propertyIsLocal' :
    PropertyIsLocal'.{u}
      (fun {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
        [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (φ : B →+* A) ↦
        FiniteTypeOnReductionsProperty φ) where
  isomorphismInvariant := isFiniteTypeOnReductions_isomorphismInvariant
  localizationPreserves := isFiniteTypeOnReductions_localizationPreserves
  faithfullyFlatDescent := isFiniteTypeOnReductions_faithfullyFlatDescent
  finiteProduct := isFiniteTypeOnReductions_finiteProductPreserves

end Local

end TopologicalRing

end
