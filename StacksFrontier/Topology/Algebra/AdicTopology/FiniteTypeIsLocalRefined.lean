module

public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.RingHom.FinitePresentation
public import Mathlib.RingTheory.TensorProduct.Quotient
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.MorphismProperty.FaithfullyFlatRing
public import StacksFrontier.RingTheory.RingHom.QuotientBaseChange
public import StacksFrontier.Topology.Algebra.AdicTopology.FiniteTypeIsLocal
public import StacksFrontier.Topology.Algebra.AdicTopology.FiniteTypeRefined
public import StacksFrontier.Topology.Algebra.AdicTopology.LocalPropertiesRefined
public import StacksFrontier.Topology.Algebra.AdicTopology.TautIsLocalRefined

/-!
# Tautness with topological finite type is a local property

Tautness together with topological finite type is a local property of continuous ring maps
between countably indexed weakly admissible topological rings: it is independent of the
presentations of the source and the target, and satisfies the locality axioms.

## Main results

* `TopologicalRing.isTopologicallyOfFiniteType_isomorphismInvariant`: topological finite type is
  invariant under isomorphisms of the source and continuous isomorphisms of the target.
* `TopologicalRing.topologicallyFiniteType_isomorphismInvariant`: tautness together with
  topological finite type is invariant under such isomorphisms.
* `TopologicalRing.topologicallyFiniteType_propertyIsLocal'`: tautness together with topological
  finite type is a local property.
-/

@[expose] public section

namespace TopologicalRing

open Filter
open scoped TensorProduct

/-! ### Topological finite type across a commuting square -/

section CommSq

end CommSq

/-! ### The ring being completed sits densely in its completion -/

namespace CompletionOver

section OfTarget

universe u v

variable {B : Type u} {A : Type v} [CommRing B] [CommRing A] [TopologicalSpace B]

end OfTarget

section Dense

universe u v

variable {B : Type u} {A : Type v} [CommRing B] [TopologicalSpace B]
  [CommRing A]

end Dense

end CompletionOver

section FiniteTypeCompletion

universe u v

end FiniteTypeCompletion

/-! ### Finite type from étale -/

section Etale

end Etale

/-! ### Topological finite type for a finite product of targets -/

section Pi

end Pi

/-! ### Properties of a quotient of a faithfully flat or finitely presented map -/

section BaseChange

universe u

end BaseChange

/-! ### Presentation independence of topological finite type -/

section Invariance

universe u

/-- Topological finite type is carried along a ring isomorphism of the source and a continuous
ring isomorphism of the target. -/
private theorem isTopologicallyOfFiniteType_transport {B A B' A' : Type*}
    [CommRing B] [CommRing A] [CommRing B'] [CommRing A']
    [TopologicalSpace A] [TopologicalSpace A']
    (eB : B ≃+* B') (eA : A ≃+* A') (heA : Continuous eA)
    (f : B →+* A) (h : IsTopologicallyOfFiniteType f) :
    IsTopologicallyOfFiniteType ((eA.toRingHom.comp f).comp eB.symm.toRingHom) := by
  rcases h with ⟨n, p, hp, hd⟩
  let g : MvPolynomial (Fin n) B' →+* MvPolynomial (Fin n) B :=
    MvPolynomial.map eB.symm.toRingHom
  refine ⟨n, (eA.toRingHom.comp p).comp g, ?_, ?_⟩
  · ext x
    apply congrArg eA
    simpa [g] using congrArg (fun h : B →+* A ↦ h (eB.symm x)) hp
  · have hs : Function.Surjective g := (MvPolynomial.mapEquiv (Fin n) eB.symm).surjective
    let : TopologicalSpace (MvPolynomial (Fin n) B) := ⊥
    let : DiscreteTopology (MvPolynomial (Fin n) B) := discreteTopology_bot _
    have hd0 : DenseRange (p.comp g) := hd.comp hs.denseRange continuous_of_discreteTopology
    exact eA.surjective.denseRange.comp hd0 heA

/-- Topological finite type does not depend on the presentations of a continuous arrow, for any
class of rings. -/
public theorem isTopologicallyOfFiniteType_isomorphismInvariant
    (C : ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
      [IsLinearTopology R R], Prop) :
    IsomorphismInvariant.{u}
      (fun {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
        [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
        (f : B →+* A) ↦ IsTopologicallyOfFiniteType f)
      C := by
  intro B A B' A' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eB eA _ _ heA heAs f _ _ _ _ _
  constructor
  · exact isTopologicallyOfFiniteType_transport eB eA heA f
  · intro h
    have h' := isTopologicallyOfFiniteType_transport eB.symm eA.symm heAs
      ((eA.toRingHom.comp f).comp eB.symm.toRingHom) h
    convert h' using 1
    ext x
    simp

/-- Tautness together with topological finite type is independent of the presentations of the
source and the target. -/
@[stacks 0ANU "local_property"]
public theorem topologicallyFiniteType_isomorphismInvariant :
    IsomorphismInvariant.{u}
      (fun {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
        [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
        (f : B →+* A) ↦ RingHom.IsTaut f ∧ IsTopologicallyOfFiniteType f)
      IsCountablyWeaklyAdmissible :=
  IsomorphismInvariant.and isTaut_isomorphismInvariant
    (isTopologicallyOfFiniteType_isomorphismInvariant IsCountablyWeaklyAdmissible)

end Invariance

/-! ### The three locality axioms -/

section Local

universe u

/-- Tautness together with topological finite type is a local property of morphisms of countably
indexed weakly admissible topological rings. -/
@[stacks 0ANU "local_property"]
public theorem topologicallyFiniteType_propertyIsLocal' :
    PropertyIsLocal'.{u}
      (fun {B A : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
        [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
        (f : B →+* A) ↦ RingHom.IsTaut f ∧ IsTopologicallyOfFiniteType f) :=
  ⟨topologicallyFiniteType_isomorphismInvariant, topologicallyFiniteType_localizationPreserves,
    topologicallyFiniteType_faithfullyFlatDescent,
    topologicallyFiniteType_finiteProductPreserves⟩

end Local

end TopologicalRing

end
