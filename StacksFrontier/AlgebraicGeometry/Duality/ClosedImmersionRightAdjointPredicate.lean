module

public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.ClosedQuotient
public import StacksFrontier.AlgebraicGeometry.Duality.QuasiCoherentPushforwardAdjoint
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportDerived

/-!
# What it means for a right adjoint of pushforward to be derived sheaf Hom

Let `i : Z ⟶ W` be a closed immersion of schemes and let `a` be a candidate right adjoint of
`Ri_* : D_QCoh(𝒪_Z) ⥤ D_QCoh(𝒪_W)`. [Stacks, Tag 0A9X] says that on the bounded-below part of
`D_QCoh(𝒪_W)` the functor `a` is derived sheaf Hom out of the structure sheaf of the closed
subscheme. This file defines the two notions in which that statement is phrased.

## Main definitions

* `Stacks.Duality.isBoundedBelowQuasiCoherent` — the bounded-below objects of `D_QCoh(𝒪_Z)`.
* `Stacks.Duality.IsDerivedSheafHomRightAdjoint` — the conclusion of [Stacks, Tag 0A9X] for one
  closed immersion and one candidate right adjoint: the right adjoint agrees, on bounded-below
  complexes with quasi-coherent cohomology, with the right derived functor of sheaf Hom with
  exact support of [Stacks, Tag 0A76].

## Implementation notes

Both derived categories are taken at `HasDerivedCategory.standard`, which is the instance at which
`RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces.derivedSheafHomExactSupport`
is stated; a consumer must introduce the same instance for the two statements to compose.

## References

* [Stacks Project, Tag 0A9X](https://stacks.math.columbia.edu/tag/0A9X)
* [Stacks Project, Tag 0A76](https://stacks.math.columbia.edu/tag/0A76)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Duality

/-- The bounded-below objects of `D_QCoh(𝒪_Z)`, as a property of its objects. The identification
of [Stacks, Tag 0A9X] holds on this part of the quasi-coherent derived category, sheaf Hom with
exact support preserving quasi-coherence only there. -/
abbrev isBoundedBelowQuasiCoherent (Z : Scheme.{u}) :
    ObjectProperty (quasiCoherentDerivedCategory Z) :=
  fun K => DerivedCategoryB.IsBoundedBelow K.obj

/-- **The conclusion of [Stacks, Tag 0A9X] for one closed immersion `i : Z ⟶ W` and one
candidate right adjoint `a` of `Ri_*`:** on the bounded-below part of `D_QCoh(𝒪_W)` the functor
`a` agrees with the right derived functor of sheaf Hom with exact support of
[Stacks, Tag 0A76], that is, with `R𝓗om_{𝒪_W}(𝒪_Z, -)`.

Both sides are compared after the inclusion into the ambient `D(𝒪_Z)`, which is fully faithful,
so this is the same as an isomorphism of the functors into `D_QCoh(𝒪_Z)` itself. -/
def IsDerivedSheafHomRightAdjoint {Z W : Scheme.{u}} (i : Z ⟶ W) [IsClosedImmersion i]
    (a : quasiCoherentDerivedCategory W ⥤ quasiCoherentDerivedCategory Z) : Prop :=
  Nonempty
    ((ObjectProperty.ι (isBoundedBelowQuasiCoherent W) ⋙ a ⋙
        (DerivedCategoryB.derivedCategoryB
          (SheafOfModules.isQuasicoherent Z.ringCatSheaf)).ι) ≅
      (ObjectProperty.ι (isBoundedBelowQuasiCoherent W) ⋙
        (DerivedCategoryB.derivedCategoryB
          (SheafOfModules.isQuasicoherent W.ringCatSheaf)).ι ⋙
        (Stacks.ClosedImmersion.closedQuotientOfClosedImmersion i).derivedSheafHomExactSupport))

end Stacks.Duality

end
