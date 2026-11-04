module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.GlobalCupProductCanonicalInstances
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.KunnethGlobalCupProduct

/-!
# The canonical global cup product is invertible over an affine base

Let `S` be an affine scheme and `A = Γ(S, 𝒪_S)`.  The global cup product of Cohomology,
Section 0FKU,

`μ : RΓ(S, U) ⊗^𝐋_A RΓ(S, V) ⟶ RΓ(S, U ⊗^𝐋_{𝒪_S} V)`,

in its parameter-free form `Stacks.Cohomology.GlobalKunneth.globalCupProductCanonical` — the one
the Künneth map of [Stacks, Tag 0G49] is built from — is an isomorphism at every pair of
complexes with quasi-coherent cohomology.  This is the step of the source's proofs of
[Stacks, Tag 0FLQ] and [Stacks, Tag 0FU4] in which affineness of the base is used.

`Stacks.Cohomology.DerivedKunneth.isIso_kunnethGlobalMapScheme` proves the corresponding fact
for the cup product of
`Stacks.Cohomology.DerivedSectionsLeftAdjoint.onePointComparisonOnARingedSpace`;
the canonical cup product is built from a different, though isomorphic, adjunction
`Stacks.Cohomology.DerivedSectionsLeftAdjoint.derivedBaseAdjunction` with the same two functors,
so the invertibility of its unit and counit is transported along the uniqueness of adjoints
(`CategoryTheory.Adjunction.rightAdjointUniq`), and its tensor comparison is a composite of
invertible comparisons.

## Main results

* `AlgebraicGeometry.FlatKunneth.isIso_derivedBaseAdjunction_unit_app`,
  `AlgebraicGeometry.FlatKunneth.isIso_derivedBaseAdjunction_counit_app`: the unit, and the counit
  on the quasi-coherent part, of `derivedBaseAdjunction` over an affine scheme.
* `AlgebraicGeometry.FlatKunneth.isIso_globalCupProductCanonical_app`: the statement above.

## References

* [Stacks Project, Section 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 0G49](https://stacks.math.columbia.edu/tag/0G49)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedGlobalCupProduct
open Stacks.Cohomology.DerivedSectionsLeftAdjoint
open Stacks.Cohomology.GlobalKunneth

universe u

namespace AlgebraicGeometry.FlatKunneth

attribute [local instance 100000] HasDerivedCategory.standard

variable (S : Scheme.{u}) [IsAffine S]

/-- **The unit of `L ⊣ RΓ(S, -)` is invertible over an affine scheme**, for the adjunction the
canonical global cup product is built from. -/
theorem isIso_derivedBaseAdjunction_unit_app
    (x : DerivedCategory (ModuleCat.{u} (baseRing S.toRingedSpace))) :
    IsIso ((derivedBaseAdjunction S.toRingedSpace).unit.app x) := by
  rw [← Adjunction.unit_rightAdjointUniq_hom_app (derivedSectionsAdjunction S.toRingedSpace)
    (derivedBaseAdjunction S.toRingedSpace) x]
  infer_instance

/-- **The counit of `L ⊣ RΓ(S, -)` is invertible on complexes with quasi-coherent cohomology over
an affine scheme**, for the adjunction the canonical global cup product is built from. -/
theorem isIso_derivedBaseAdjunction_counit_app
    (U : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.toRingedSpace)))
    (hU : ∀ j : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) j).obj U).IsQuasicoherent) :
    IsIso ((derivedBaseAdjunction S.toRingedSpace).counit.app U) := by
  have := AlgebraicGeometry.AffineDerivedSections.isIso_derivedSectionsAdjunction_counit_app
    S U hU
  have h := Adjunction.rightAdjointUniq_hom_app_counit (derivedSectionsAdjunction S.toRingedSpace)
    (derivedBaseAdjunction S.toRingedSpace) U
  rw [← h] at this
  exact IsIso.of_isIso_comp_left ((derivedBaseExtension S.toRingedSpace).map
    ((Adjunction.rightAdjointUniq (derivedSectionsAdjunction S.toRingedSpace)
      (derivedBaseAdjunction S.toRingedSpace)).hom.app U)) _

/-- **The canonical global cup product of Section 0FKU is invertible over an affine base**, at
every pair of complexes with quasi-coherent cohomology. -/
theorem isIso_globalCupProductCanonical_app
    (U V : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.toRingedSpace)))
    (hU : ∀ j : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) j).obj U).IsQuasicoherent)
    (hV : ∀ j : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) j).obj V).IsQuasicoherent) :
    IsIso ((globalCupProductCanonical S.toRingedSpace).app (U, V)) := by
  rw [← globalCupProduct_onePointComparisonCanonical]
  refine isIso_globalCupProduct_app (onePointComparisonCanonical S.toRingedSpace) U V
    (isIso_derivedBaseAdjunction_unit_app S _) ?_
    (isIso_derivedBaseAdjunction_counit_app S U hU)
    (isIso_derivedBaseAdjunction_counit_app S V hV)
  have h0 : IsIso
      (CochainComplex.DerivedTensor.RestrictScalars.restrictScalarsDerivedTensorComparison
        (basePointCommRingEquiv S.toRingedSpace)) := inferInstance
  have h0' : IsIso (Stacks.Cohomology.DerivedSectionsOnAPoint.onePointTensorComparison
      ↑(baseRing S.toRingedSpace)) := inferInstance
  have h0'' : IsIso (Functor.whiskerRight
        (CochainComplex.DerivedTensor.RestrictScalars.restrictScalarsDerivedTensorComparison
          (basePointCommRingEquiv S.toRingedSpace))
        (basePointExtension S.toRingedSpace)) := inferInstance
  have h0''' : IsIso (Functor.whiskerLeft
      ((basePointRestrict S.toRingedSpace).functor.mapDerivedCategory.prod
        (basePointRestrict S.toRingedSpace).functor.mapDerivedCategory)
      (Stacks.Cohomology.DerivedSectionsOnAPoint.onePointTensorComparison
        ↑(baseRing S.toRingedSpace))) := inferInstance
  have h1 : IsIso (baseTensorComparison S.toRingedSpace) :=
    @IsIso.comp_isIso _ _ _ _ _ _ _ h0'' h0'''
  have h2 : IsIso (Functor.whiskerRight (baseTensorComparison S.toRingedSpace)
      (derivedPullback (toBasePoint S.toRingedSpace))) := inferInstance
  have h3 : IsIso (Functor.whiskerLeft
      ((baseToPoint S.toRingedSpace).prod (baseToPoint S.toRingedSpace))
      (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso
        (toBasePoint S.toRingedSpace)).hom) :=
    (Functor.isoWhiskerLeft ((baseToPoint S.toRingedSpace).prod (baseToPoint S.toRingedSpace))
      (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso
        (toBasePoint S.toRingedSpace))).isIso_hom
  have hT : IsIso (onePointComparisonCanonical S.toRingedSpace).tensorComparison :=
    @IsIso.comp_isIso _ _ _ _ _ _ _ h2 h3
  exact NatIso.isIso_app_of_isIso _ _

end AlgebraicGeometry.FlatKunneth

end
