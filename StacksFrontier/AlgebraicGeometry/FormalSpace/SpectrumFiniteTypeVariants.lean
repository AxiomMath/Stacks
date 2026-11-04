module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteTypeQuasiCompact
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumFiniteType
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumFiniteTypeRefined

/-!
# Quotient maps of formal spectrum morphisms of finite type

For a taut continuous homomorphism `φ : A → C` of weakly admissible topological rings such that
`Spf (φ)` is of finite type, the induced ring maps on quotients by weak ideals of definition are
of finite type.

## Main results

* `finiteType_quotientMap_of_isFiniteType_formalSpectrumMap'`: if `Spf (φ)` is of finite type,
  then for every weak ideal of definition `I` of `A` the ring map `A ⧸ I → C ⧸ J(I)` is of
  finite type.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace TopologicalRing

section Algebra

universe u v

variable {A : Type u} [CommRing A] [TopologicalSpace A]
  {B : Type v} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]

end Algebra

end TopologicalRing

namespace AlgebraicGeometry.FormalSpace

section Geometry

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {B S hS}

variable {A C : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsLinearTopology A A] [CommRing C] [TopologicalSpace C] [IsTopologicalRing C]
  [IsLinearTopology C C]

/-- **Stacks 0ANT, the ring-theoretic half of (1) ⟹ (2)** for a morphism of finite type. Let
`φ : A ⟶ C` be a taut continuous homomorphism of weakly admissible topological rings over `S`.
If `Spf (φ)` is of finite type — Definition 0AM4, part (2), locally of finite type together
with quasi-compact in the sense of Definition 0AJC — then for every weak ideal of definition
`I` of `A` the induced ring map `A ⧸ I → C ⧸ J(I)` is of finite type. -/
theorem finiteType_quotientMap_of_isFiniteType_formalSpectrumMap'
    (hA : TopologicalRing.IsWeaklyAdmissible A) (hC : TopologicalRing.IsWeaklyAdmissible C)
    (D : QuotientSystem B S hS A) (E : QuotientSystem B S hS C) (f : ContinuousHom D E)
    (hf : RingHom.IsTaut f.toRingHom) (hFT : IsFiniteType' B S hS (formalSpectrumMap hA f))
    (I : Ideal A) (hI : TopologicalRing.IsWeakIdealOfDefinition I) :
    (Ideal.quotientMap (Ideal.closure (I.map f.toRingHom)) f.toRingHom
      (Ideal.map_le_iff_le_comap.mp subset_closure)).FiniteType :=
  finiteType_quotientMap_of_isLocallyOfFiniteType_formalSpectrumMap hA hC D E f hf hFT.1 I hI

end Geometry

end AlgebraicGeometry.FormalSpace

end
