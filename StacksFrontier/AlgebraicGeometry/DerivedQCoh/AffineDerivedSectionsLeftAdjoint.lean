module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalenceStandard
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedPullback
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.ExtFinitenessLeray
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.DerivedSectionsLeftAdjoint
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaQuasiCoherent
import StacksCore.Tactic.StacksAttribute

/-!
# The left adjoint of derived global sections on an affine scheme

Let `S` be an affine scheme and `A = Γ(S, 𝒪_S)`. The ringed-space construction of
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPushforward/DerivedSectionsLeftAdjoint.lean`
provides, with no hypothesis on `S` at all, a left adjoint

`L : D(A) ⥤ D(𝒪_S)`,  `L ⊣ RΓ(S, -)`,

namely the derived pullback along the structure morphism to the one-point ringed space of
[Stacks, Tag 01BH]. This file proves, for `S` affine, the two properties of `L` that the global
cup product of Cohomology, Section 0FKU needs: `L` is fully faithful, and its essential image
contains every complex of `𝒪_S`-modules with quasi-coherent cohomology sheaves. Through
`Stacks.Cohomology.DerivedSectionsLeftAdjoint.isIso_derivedSectionsAdjunction_unit` and
`Stacks.Cohomology.DerivedSectionsLeftAdjoint.isIso_derivedSectionsAdjunction_counit_app_iff`
these say that the unit of `L ⊣ RΓ(S, -)` is invertible and that its counit is invertible at every
object of `D_QCoh(𝒪_S)`; so the adjunction restricts to the derived Spec–Γ equivalence of
[Stacks, Tag 06Z0] in the formulation the cup product consumes.

## Main results

* `AlgebraicGeometry.AffineDerivedSections.derivedSectionsLeftAdjointFullyFaithful`, with the two
  instances `AlgebraicGeometry.AffineDerivedSections.full_derivedSectionsLeftAdjoint` and
  `AlgebraicGeometry.AffineDerivedSections.faithful_derivedSectionsLeftAdjoint` — **`L` is fully
  faithful on an affine scheme.** Hence the unit of `L ⊣ RΓ(S, -)` is invertible, by Mathlib's
  instance `CategoryTheory.Adjunction.unit_isIso_of_L_fully_faithful`.
* `AlgebraicGeometry.AffineDerivedSections.essImage_derivedSectionsLeftAdjoint` — **every complex
  of `𝒪_S`-modules with quasi-coherent cohomology sheaves is in the essential image of `L`.**
* `AlgebraicGeometry.AffineDerivedSections.isIso_derivedSectionsAdjunction_counit_app` — hence the
  counit of `L ⊣ RΓ(S, -)` is invertible at every such complex.

## Implementation notes

*The right adjoints are compared, not the left ones.* `L` is the derived pullback along
`π : S ⟶ ({*}, A)`, while the known Tag 06Z0 adjunction
`AlgebraicGeometry.derivedTildeGlobalSectionsAdjunction` has derived sheafification `M ↦ M̃` as
its left adjoint. Identifying those two functors would need a comparison of the pullback along
the coefficient point with `AlgebraicGeometry.derivedTilde`, which the library does not have: it
would have to cross the universe gap that the implementation notes of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/AssociatedSheafComparison.lean` explicitly decline
to cross. The *right* adjoints, on the other hand, are both derived global sections over `A`, and
the comparison of those is already available. So the two left adjoints are identified by
uniqueness of left adjoints, `CategoryTheory.Adjunction.leftAdjointUniq`, and
`derivedSectionsLeftAdjointIso` is the resulting isomorphism of functors; full faithfulness and
the essential image are then transported along it.

*What the comparison of the right adjoints costs.* `derivedPushforwardBaseSectionsIso` is
[Stacks, Tag 0D5W] over the base ring, `AlgebraicGeometry.derivedGlobalSectionsOverPushforwardIso`
at `S.isoSpec.hom`, followed by `baseSectionsSchemeIso`, which says that `A`-linear derived global
sections of `S` are derived sections over `⊤` with no restriction of scalars at all: the scalar
map `A ≅ Γ(Spec A, 𝒪) ⟶ Γ(S, 𝒪_S)` through which `AlgebraicGeometry.globalSectionsOver` reads
sections is the identity for `S.isoSpec.hom`, which is `restrictScalarsOver_isoSpec_hom`, and
restriction of scalars along the identity is the identity functor,
`ModuleCat.restrictScalarsId'`. Both sides are then right derived functors of the same functor,
and `CategoryTheory.Functor.rightDerivedNatIso` identifies them.

*The spellings of the category of `𝒪_S`-modules.* `AlgebraicGeometry.Scheme.Modules S` and
`SheafOfModules (structureSheafRing S.toRingedSpace)` are definitionally equal but carry
separately declared instances, and instance search does not cross between them. Every right
derived functor below is therefore formed in the second spelling — that is where the localization
and additivity instances live — and the crossing happens only where a statement of
`AlgebraicGeometry.StandardModel`, which is phrased on `Scheme.Modules`, is applied. This is the
device recorded in the implementation notes of
`StacksFrontier/AlgebraicGeometry/ProperSupportCoherent/ExtFinitenessLeray.lean`.

*The derived category is the standard model,* pinned at a priority high enough to displace the
locally small one that arrives with the imports; see the implementation notes of
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/AffineDerivedEquivalenceStandard.lean`.

## References

* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 01BH](https://stacks.math.columbia.edu/tag/01BH)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
* [Stacks Project, Section 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
  (derivedPullback derivedPushforward derivedAdjunction)
open Stacks.Cohomology.DerivedProjectionFormula (ringedSpaceIsoOfSchemeIso)
open Stacks.Cohomology.DerivedPullbackAlongIso
  (derivedPullbackEquivalence derivedPullbackInvHomIso mapHomotopyCategoryIso)
open Stacks.Cohomology.DerivedSectionsLeftAdjoint
  (derivedBaseExtension derivedSectionsAdjunction)
open Stacks.Cohomology.DerivedSectionsLeray (sectionsOverOpen derivedSectionsOverOpenUnit)

universe u

namespace AlgebraicGeometry.AffineDerivedSections

attribute [local instance 10000] HasDerivedCategory.standard

variable (S : Scheme.{u}) [IsAffine S]

/-! ### Derived global sections of an affine scheme over its own ring of functions -/

/-- **The scalar map of `S.isoSpec.hom` is the identity.** `AlgebraicGeometry.globalSectionsOver`
reads global sections of `𝒪_X`-modules as modules over the base ring by restricting scalars along
`A ≅ Γ(Spec A, 𝒪) ⟶ Γ(X, 𝒪_X)`; for `A = Γ(S, 𝒪_S)` and the structure morphism
`S ⟶ Spec Γ(S, 𝒪_S)` of [Stacks, Tag 01I1] the second map inverts the first, so the composite is
the identity of `Γ(S, 𝒪_S)`. -/
theorem restrictScalarsOver_isoSpec_hom :
    (((Scheme.ΓSpecIso (CommRingCat.of Γ(S, ⊤))).inv ≫ S.isoSpec.hom.appTop)).hom =
      RingHom.id Γ(S, ⊤) := by
  have h : ((Scheme.ΓSpecIso (CommRingCat.of Γ(S, ⊤))).inv ≫ S.isoSpec.hom.appTop) =
      𝟙 (CommRingCat.of Γ(S, ⊤)) := by
    rw [Scheme.isoSpec_hom, Scheme.toSpecΓ_appTop]
    exact (Scheme.ΓSpecIso (CommRingCat.of Γ(S, ⊤))).inv_hom_id
  rw [h]
  rfl

/-- **`Γ(S, 𝒪_S)`-linear global sections of an affine scheme are plain global sections.** The
restriction of scalars that `AlgebraicGeometry.baseSections` postcomposes with is restriction
along the identity, by `restrictScalarsOver_isoSpec_hom`. -/
def baseSectionsIsoSectionsOverOpen :
    AlgebraicGeometry.baseSections S.isoSpec.hom ≅ sectionsOverOpen S.toRingedSpace ⊤ :=
  Functor.isoWhiskerLeft
      (SheafOfModules.evaluation (structureSheafRing S.toRingedSpace)
        (op (⊤ : Opens S.carrier)))
      (ModuleCat.restrictScalarsId'.{u} _ (restrictScalarsOver_isoSpec_hom S)) ≪≫
    Functor.rightUnitor
      (SheafOfModules.evaluation (structureSheafRing S.toRingedSpace)
        (op (⊤ : Opens S.carrier)))

/-- **`Γ(S, 𝒪_S)`-linear derived global sections of an affine scheme are the derived sections over
`⊤` of the ringed space underlying `S`.** Both are right derived functors of the functor of
`baseSectionsIsoSectionsOverOpen`, and a right derived functor is unique up to a canonical
isomorphism. -/
def baseSectionsSchemeIso :
    (AlgebraicGeometry.homotopyBaseSections S.isoSpec.hom).totalRightDerived DerivedCategory.Qh
        (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing S.toRingedSpace))
          (ComplexShape.up ℤ)) ≅
      Stacks.Cohomology.GlobalKunneth.baseSections S.toRingedSpace := by
  letI : (AlgebraicGeometry.baseSections S.isoSpec.hom).Additive := { map_add := rfl }
  letI : (sectionsOverOpen S.toRingedSpace ⊤).Additive := { map_add := rfl }
  exact Functor.rightDerivedNatIso _ _
    ((AlgebraicGeometry.homotopyBaseSections S.isoSpec.hom).totalRightDerivedUnit
      DerivedCategory.Qh
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing S.toRingedSpace))
        (ComplexShape.up ℤ)))
    (derivedSectionsOverOpenUnit S.toRingedSpace ⊤)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing S.toRingedSpace))
      (ComplexShape.up ℤ))
    (Functor.isoWhiskerRight
      (mapHomotopyCategoryIso (baseSectionsIsoSectionsOverOpen S) (ComplexShape.up ℤ))
      DerivedCategory.Qh)

/-! ### The two adjunctions have the same right adjoint -/

/-- **The right adjoint of the Tag 06Z0 adjunction, transported to `S` along `S.isoSpec`, is
`RΓ(S, -)`.** It is [Stacks, Tag 0D5W] over the base ring for `S.isoSpec.hom`, followed by the
identification `baseSectionsSchemeIso` of `Γ(S, 𝒪_S)`-linear derived global sections with derived
sections over `⊤`. -/
def derivedPushforwardBaseSectionsIso :
    derivedPushforward (ringedSpaceIsoOfSchemeIso S.isoSpec).hom ⋙
        derivedGlobalSectionsOver (𝟙 (Spec Γ(S, ⊤))) ≅
      Stacks.Cohomology.GlobalKunneth.baseSections S.toRingedSpace :=
  (derivedGlobalSectionsOverPushforwardIso S.isoSpec.hom).symm ≪≫ baseSectionsSchemeIso S

/-- **Derived sheafification, followed by the derived pullback along `S ≅ Spec Γ(S, 𝒪_S)`, is a
left adjoint of `RΓ(S, -)`.** The composite of the derived Spec–Γ adjunction of
[Stacks, Tag 06Z0] with the derived adjunction of [Stacks, Tag 079W] for the isomorphism of
ringed spaces underlying `S.isoSpec`, read through `derivedPushforwardBaseSectionsIso`. -/
def derivedTildePullbackAdjunction :
    (derivedTilde Γ(S, ⊤) ⋙ (StandardModel.derivedQuasicoherent Γ(S, ⊤)).ι) ⋙
        derivedPullback (ringedSpaceIsoOfSchemeIso S.isoSpec).hom ⊣
      Stacks.Cohomology.GlobalKunneth.baseSections S.toRingedSpace :=
  Adjunction.ofNatIsoRight
    ((derivedTildeGlobalSectionsAdjunction Γ(S, ⊤)).val.comp
      (derivedAdjunction (ringedSpaceIsoOfSchemeIso S.isoSpec).hom))
    (derivedPushforwardBaseSectionsIso S)

/-- **The left adjoint of `RΓ(S, -)` on an affine scheme is derived sheafification followed by the
derived pullback along `S ≅ Spec Γ(S, 𝒪_S)`.** Both are left adjoint to
`Stacks.Cohomology.GlobalKunneth.baseSections S.toRingedSpace`, and a left adjoint is unique up to
a canonical isomorphism. -/
def derivedSectionsLeftAdjointIso :
    derivedBaseExtension S.toRingedSpace ≅
      (derivedTilde Γ(S, ⊤) ⋙ (StandardModel.derivedQuasicoherent Γ(S, ⊤)).ι) ⋙
        derivedPullback (ringedSpaceIsoOfSchemeIso S.isoSpec).hom :=
  Adjunction.leftAdjointUniq (derivedSectionsAdjunction S.toRingedSpace)
    (derivedTildePullbackAdjunction S)

/-! ### Full faithfulness -/

/-- **The left adjoint of `RΓ(S, -)` is fully faithful on an affine scheme.** By
`derivedSectionsLeftAdjointIso` it is derived sheafification, which is fully faithful by
[Stacks, Tag 06Z0], followed by the derived pullback along an isomorphism of ringed spaces, which
is one half of an equivalence. -/
def derivedSectionsLeftAdjointFullyFaithful :
    (derivedBaseExtension S.toRingedSpace).FullyFaithful :=
  ((StandardModel.derivedTildeCompιFullyFaithful Γ(S, ⊤)).comp
      (derivedPullbackEquivalence
        (ringedSpaceIsoOfSchemeIso S.isoSpec)).fullyFaithfulFunctor).ofIso
    (derivedSectionsLeftAdjointIso S).symm

/-- **The left adjoint of `RΓ(S, -)` is full on an affine scheme**; see
`derivedSectionsLeftAdjointFullyFaithful`. -/
@[stacks 06Z0 "the left adjoint of derived global sections is fully faithful on an affine scheme"]
instance full_derivedSectionsLeftAdjoint :
    (derivedBaseExtension S.toRingedSpace).Full :=
  (derivedSectionsLeftAdjointFullyFaithful S).full

/-- **The left adjoint of `RΓ(S, -)` is faithful on an affine scheme**; see
`derivedSectionsLeftAdjointFullyFaithful`. -/
@[stacks 06Z0 "the left adjoint of derived global sections is fully faithful on an affine scheme"]
instance faithful_derivedSectionsLeftAdjoint :
    (derivedBaseExtension S.toRingedSpace).Faithful :=
  (derivedSectionsLeftAdjointFullyFaithful S).faithful

/-! ### The essential image -/

/-- **Every complex of `𝒪_S`-modules with quasi-coherent cohomology sheaves is in the essential
image of the left adjoint of `RΓ(S, -)`,** `S` being affine. This is the predicate
`AlgebraicGeometry.IsQCohAll` of the Künneth development, written out.

Pulling `U` back along `S ≅ Spec Γ(S, 𝒪_S)` keeps the cohomology sheaves quasi-coherent, by
[Stacks, Tag 08DW] part (1); over `Spec Γ(S, 𝒪_S)` the result is a derived sheafification by
[Stacks, Tag 06Z0], `AlgebraicGeometry.StandardModel.exists_iso_mapDerivedCategory`; and pushing
that back through `derivedSectionsLeftAdjointIso` and the round trip of the derived pullbacks
along the two directions of the isomorphism exhibits `U` itself. -/
@[stacks 06Z0 "the essential image of that left adjoint is the quasi-coherent part"]
theorem essImage_derivedSectionsLeftAdjoint
    (U : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.toRingedSpace)))
    (hU : ∀ j : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) j).obj U).IsQuasicoherent) :
    (derivedBaseExtension S.toRingedSpace).essImage U := by
  obtain ⟨M, ⟨eM⟩⟩ := StandardModel.exists_iso_mapDerivedCategory Γ(S, ⊤)
    ((derivedPullback (ringedSpaceIsoOfSchemeIso S.isoSpec).inv).obj U)
    fun j => Stacks.Duality.isQuasicoherent_homology_derivedPullback_anyModel
      S.isoSpec.inv U hU j
  refine ⟨M, ⟨(derivedSectionsLeftAdjointIso S).app M ≪≫ ?_⟩⟩
  exact (derivedPullback (ringedSpaceIsoOfSchemeIso S.isoSpec).hom).mapIso
      ((derivedTildeCompι Γ(S, ⊤)).app M ≪≫ eM) ≪≫
    (derivedPullbackInvHomIso (ringedSpaceIsoOfSchemeIso S.isoSpec)).app U

/-- **The counit of `L ⊣ RΓ(S, -)` is invertible at every complex of `𝒪_S`-modules with
quasi-coherent cohomology sheaves,** `S` being affine. For a fully faithful left adjoint the
counit is invertible exactly on the essential image, which is
`essImage_derivedSectionsLeftAdjoint`. -/
theorem isIso_derivedSectionsAdjunction_counit_app
    (U : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.toRingedSpace)))
    (hU : ∀ j : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) j).obj U).IsQuasicoherent) :
    IsIso ((derivedSectionsAdjunction S.toRingedSpace).counit.app U) :=
  (Adjunction.isIso_counit_app_iff_mem_essImage
    (derivedSectionsAdjunction S.toRingedSpace)).2
      (essImage_derivedSectionsLeftAdjoint S U hU)

end AlgebraicGeometry.AffineDerivedSections

end
