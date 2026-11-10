module

public import Mathlib.Topology.Algebra.IsUniformGroup.Constructions
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Restricted.FiniteTypeComposition
public import StacksFrontier.Topology.Algebra.AdicTopology.AdicFiniteTypeIsLocal
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletionOver
public import StacksFrontier.Topology.Algebra.AdicTopology.FiniteTypeIsLocalRefined
public import StacksFrontier.Topology.Algebra.AdicTopology.LocalPropertiesRefined
public import StacksFrontier.Topology.Algebra.AdicTopology.AdicRingMapRefined

/-!
# Adic morphisms topologically of finite type form a local property

Being adic and topologically of finite type is a local property of morphisms of weakly admissible
adic-star rings, in the sense of `AdicStarPropertyIsLocal'`, and it is stable under composition.

These are the strengthened and newly added declarations of the 2026-10 chapter-87 round that
belong with `StacksFrontier.Topology.Algebra.AdicTopology.AdicFiniteTypeIsLocal`. A declaration of
that module whose statement the round strengthened keeps its original statement there; its
strengthened form lives here under a primed name.

## Main results

* `TopologicalRing.adicTopologicallyFiniteType_isomorphismInvariant`: being adic and topologically
  of finite type is independent of the presentations of the source and the target.
* `TopologicalRing.adicTopologicallyFiniteType_isLocal'`: being adic and topologically of finite
  type is a local property.
* `TopologicalRing.adicTopologicallyFiniteType_isStableUnderComposition'`: this local property is
  stable under composition.
-/

@[expose] public section

namespace TopologicalRing

section

universe u

/-- Adicness of an arrow is independent of the presentations of its source and its target, for
any class of rings: this is `RingHom.isAdic_comp_ringEquiv_iff`, whose hypotheses do not
mention the class. -/
public theorem isAdic_isomorphismInvariant
    (C : ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
      [IsLinearTopology R R], Prop) :
    IsomorphismInvariant.{u}
      (fun {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
        [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (φ : B →+* A) ↦
        RingHom.IsAdic φ) C := by
  intro B A B' A' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eB eA heB heBs heA heAs f _ _ _ _ _
  exact RingHom.isAdic_comp_ringEquiv_iff eB eA heB heBs heA heAs f

/-- Being adic and topologically of finite type is independent of the presentations of the source
and the target. -/
@[stacks 0GBW "local_property"]
public theorem adicTopologicallyFiniteType_isomorphismInvariant :
    IsomorphismInvariant.{u}
      (fun {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
        [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (φ : B →+* A) ↦
        RingHom.IsAdic φ ∧ IsTopologicallyOfFiniteType φ)
      (fun R ↦ ∃ I : Ideal R, I.FG ∧ _root_.IsAdic I) :=
  IsomorphismInvariant.and
    (isAdic_isomorphismInvariant (fun R ↦ ∃ I : Ideal R, I.FG ∧ _root_.IsAdic I))
    (isTopologicallyOfFiniteType_isomorphismInvariant
      (fun R ↦ ∃ I : Ideal R, I.FG ∧ _root_.IsAdic I))

/-- Being adic and topologically of finite type is a local property of morphisms of weakly
admissible adic-star rings: it is independent of the presentations of the source and the target,
ascends along completed étale localization diagrams, descends along faithfully flat ones, and is
preserved by finite products of targets. -/
@[stacks 0GBW "local_property"]
public theorem adicTopologicallyFiniteType_isLocal' :
    AdicStarPropertyIsLocal'.{u}
      (fun {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
        [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (φ : B →+* A) ↦
        RingHom.IsAdic φ ∧ IsTopologicallyOfFiniteType φ) :=
  ⟨adicTopologicallyFiniteType_isomorphismInvariant,
    adicTopologicallyFiniteType_isLocal.localizationPreserves,
    adicTopologicallyFiniteType_isLocal.faithfullyFlatDescent,
    adicTopologicallyFiniteType_isLocal.finiteProduct⟩

/-- Being adic and topologically of finite type is stable under composition on weakly admissible
adic-star rings. -/
@[stacks 0GBZ]
public theorem adicTopologicallyFiniteType_isStableUnderComposition' :
    AdicStarPropertyIsStableUnderComposition'.{u}
      (fun {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
        [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (φ : B →+* A) ↦
        RingHom.IsAdic φ ∧ IsTopologicallyOfFiniteType φ) where
  isLocal := adicTopologicallyFiniteType_isLocal'
  comp _ _ _ _ _ _ f g hf_cont _ hf hg :=
    isAdic_and_isTopologicallyOfFiniteType_comp f g hf_cont hf hg

end

end TopologicalRing

end
