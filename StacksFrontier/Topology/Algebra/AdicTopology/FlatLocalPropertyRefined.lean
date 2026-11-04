module

public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.AdicCompletion.Topology
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.RingHom.FinitePresentation
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Homology.Tor.Presentation
public import StacksFrontier.RingTheory.AdicCompletion.Basic
public import StacksFrontier.RingTheory.AdicCompletion.Flat
public import StacksFrontier.RingTheory.Flat.FibrewiseCriterion
public import StacksFrontier.RingTheory.Flat.Pi
public import StacksFrontier.RingTheory.WeaklyEtale.Flat
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletionOverAdic
public import StacksFrontier.Topology.Algebra.AdicTopology.FlatLocalProperty
public import StacksFrontier.Topology.Algebra.AdicTopology.LocalPropertiesRefined

/-!
# Flatness is a local property of morphisms of Noetherian adic rings: the refined forms

Flatness of ring homomorphisms is a local property of morphisms of Noetherian adic topological
rings, in the sense of `PropertyIsLocalNoetherian'`, and it is stable under composition.

These are the strengthened forms of declarations of
`StacksFrontier.Topology.Algebra.AdicTopology.FlatLocalProperty`: a declaration of that module whose
statement was strengthened keeps its original statement there, and its strengthened form lives
here under a primed name.

## Main results

* `TopologicalRing.flat_isomorphismInvariant`: flatness is unchanged by composing with a
  bijective ring homomorphism on either side.
* `TopologicalRing.flat_isLocalNoetherian'`: flatness is a local property of morphisms of
  Noetherian adic topological rings.
* `TopologicalRing.flat_isStableUnderCompositionNoetherian'`: flatness, as such a local
  property, is stable under composition.
-/

@[expose] public section

universe u

open TensorProduct CategoryTheory CategoryTheory.Limits

section Transport

end Transport

namespace TopologicalRing

/-- Flatness of a ring homomorphism is independent of the presentations of its source and its
target, for any class of rings: composing with a bijective ring homomorphism on either side
leaves flatness unchanged. -/
public theorem flat_isomorphismInvariant
    (C : ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
      [IsLinearTopology R R], Prop) :
    IsomorphismInvariant.{u}
      (fun {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
        [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (φ : B →+* A) ↦ φ.Flat) C := by
  intro B A B' A' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  intro eB eA _ _ _ _ f _ _ _ _ _
  exact ((RingHom.Flat.comp_iff_of_bijective_right eB.symm.bijective).trans
    (RingHom.Flat.comp_iff_of_bijective_left eA.bijective)).symm

/-- **Flatness is a local property of morphisms of Noetherian adic topological rings**: it is
independent of the presentations of the source and the target, ascends along completed étale
localization diagrams, descends along faithfully flat ones, and is preserved by finite products
of targets. -/
@[stacks 0GC9, sga "3 VIIB 1.3.4" "Flatness clause"]
public theorem flat_isLocalNoetherian' :
    PropertyIsLocalNoetherian'
      (fun {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
        [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (φ : B →+* A) ↦ φ.Flat) where
  isomorphismInvariant :=
    flat_isomorphismInvariant (fun R ↦ TopologicalRing.IsAdic R ∧ IsNoetherianRing R)
  localizationPreserves := flat_localizationPreserves
  faithfullyFlatDescent := flat_faithfullyFlatDescent
  finiteProduct := flat_finiteProductPreserves

/-- Flatness, as a local property of morphisms of Noetherian adic topological rings, is stable
under composition: the composite of two flat ring homomorphisms is flat. -/
@[stacks 0GCB]
public theorem flat_isStableUnderCompositionNoetherian' :
    PropertyIsStableUnderCompositionNoetherian'
      (fun {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
        [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (φ : B →+* A) ↦ φ.Flat) where
  isLocal := flat_isLocalNoetherian'
  comp _ _ _ _ _ _ _ hf hg := hg.comp hf

end TopologicalRing

end
