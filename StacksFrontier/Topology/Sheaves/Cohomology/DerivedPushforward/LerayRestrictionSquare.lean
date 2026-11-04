module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.LerayForDerivedSections
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.RestrictionOfDerivedSections

/-!
# Restriction in the open against the Leray comparison

Let `f : X ⟶ Y` be a morphism of ringed spaces and `V' ≤ V` opens of `Y`. The naturality in the
open of the Leray isomorphism
`Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsPushforwardIso` is reduced to the
corresponding equation of natural transformations out of `RΓ(f⁻¹ V, -)`, stated with the Leray
comparison `Stacks.Cohomology.DerivedSectionsLeray.lerayComparison`, and that equation to one
between transformations out of termwise sections over `f⁻¹ V`.

## Main results

All names below are in the namespace `Stacks.Cohomology.DerivedSectionsLeray`.

* `lerayComparison_comp_derivedSectionsOverOpenRestrict_of_unit`: the transformation form of the
  square follows from the corresponding equation after composition with the unit of
  `RΓ(f⁻¹ V, -)`.
* `lerayComparison_comp_derivedSectionsOverOpenRestrict_of_lerayUnit`: that equation in turn
  follows from one between two transformations out of termwise sections over `f⁻¹ V`.
* `derivedSectionsPushforwardIso_restrict_of_lerayComparison`: the object-wise square follows from
  the transformation form.

## References

* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
* [Stacks Project, Tag 0D68](https://stacks.math.columbia.edu/tag/0D68)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPushforward)

namespace Stacks.Cohomology.DerivedSectionsLeray

universe u

attribute [local instance] HasDerivedCategory.standard
  Stacks.Cohomology.HypercohomologyEdge.restrictScalars_preservesFiniteLimits
  Stacks.Cohomology.HypercohomologyEdge.restrictScalars_preservesFiniteColimits

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- The two sides of the Leray restriction square, as transformations out of the total right
derived functor `RΓ(f⁻¹ V, -)`, are equal as soon as they are equal after composition with
`Stacks.Cohomology.DerivedSectionsLeray.derivedPreimageSectionsUnit f V`. -/
theorem lerayComparison_comp_derivedSectionsOverOpenRestrict_of_unit
    {V V' : Opens Y.carrier} (hV : V' ≤ V)
    (hu : derivedPreimageSectionsUnit f V ≫ Functor.whiskerLeft DerivedCategory.Qh
        (lerayComparison f V ≫
          Functor.whiskerLeft (derivedPushforward f) (derivedSectionsOverOpenRestrict Y hV)) =
      derivedPreimageSectionsUnit f V ≫ Functor.whiskerLeft DerivedCategory.Qh
        (derivedPreimageSectionsRestrict f hV ≫
          Functor.whiskerRight (lerayComparison f V') (restrictScalarsDerived Y hV))) :
    lerayComparison f V ≫
        Functor.whiskerLeft (derivedPushforward f) (derivedSectionsOverOpenRestrict Y hV) =
      derivedPreimageSectionsRestrict f hV ≫
        Functor.whiskerRight (lerayComparison f V') (restrictScalarsDerived Y hV) :=
  derivedPreimageSectionsRestrict_ext f _ _ hu

/-- The two sides of the Leray restriction square, as transformations out of `RΓ(f⁻¹ V, -)`, are
equal as soon as the corresponding equation between transformations out of
`Stacks.Cohomology.DerivedSectionsLeray.homotopyPreimageSections` holds, with
`Stacks.Cohomology.DerivedSectionsLeray.lerayUnit f V` and
`Stacks.Cohomology.DerivedSectionsLeray.preimageSectionsRestrictUnit f hV` in place of the
derived transformations. -/
theorem lerayComparison_comp_derivedSectionsOverOpenRestrict_of_lerayUnit
    {V V' : Opens Y.carrier} (hV : V' ≤ V)
    (hu : lerayUnit f V ≫ Functor.whiskerLeft DerivedCategory.Qh
        (Functor.whiskerLeft (derivedPushforward f) (derivedSectionsOverOpenRestrict Y hV)) =
      preimageSectionsRestrictUnit f hV ≫ Functor.whiskerLeft DerivedCategory.Qh
        (Functor.whiskerRight (lerayComparison f V') (restrictScalarsDerived Y hV))) :
    lerayComparison f V ≫
        Functor.whiskerLeft (derivedPushforward f) (derivedSectionsOverOpenRestrict Y hV) =
      derivedPreimageSectionsRestrict f hV ≫
        Functor.whiskerRight (lerayComparison f V') (restrictScalarsDerived Y hV) := by
  refine lerayComparison_comp_derivedSectionsOverOpenRestrict_of_unit f hV ?_
  rwa [Functor.whiskerLeft_comp, Functor.whiskerLeft_comp, ← Category.assoc, ← Category.assoc,
    lerayComparison_fac, derivedPreimageSectionsRestrict_fac]

/-- If the Leray restriction square holds as an equation of natural transformations, then for
every `K` the corresponding square of the isomorphisms
`Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsPushforwardIso f V` and
`Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsPushforwardIso f V'` commutes. -/
theorem derivedSectionsPushforwardIso_restrict_of_lerayComparison
    {V V' : Opens Y.carrier} (hV : V' ≤ V)
    (h : lerayComparison f V ≫
        Functor.whiskerLeft (derivedPushforward f) (derivedSectionsOverOpenRestrict Y hV) =
      derivedPreimageSectionsRestrict f hV ≫
        Functor.whiskerRight (lerayComparison f V') (restrictScalarsDerived Y hV))
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    (derivedSectionsOverOpenRestrict Y hV).app ((derivedPushforward f).obj K) ≫
        (restrictScalarsDerived Y hV).map ((derivedSectionsPushforwardIso f V').hom.app K) =
      (derivedSectionsPushforwardIso f V).hom.app K ≫
        (derivedPreimageSectionsRestrict f hV).app K := by
  have hK := NatTrans.congr_app h K
  have hV1 := isIso_lerayComparison f V
  have hV2 := isIso_lerayComparison f V'
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hK
  rw [derivedSectionsPushforwardIso, derivedSectionsPushforwardIso]
  simp only [Iso.symm_hom, asIso_inv, NatIso.isIso_inv_app]
  rw [← cancel_epi ((lerayComparison f V).app K), IsIso.hom_inv_id_assoc,
    ← Category.assoc, hK, Category.assoc, ← Functor.map_comp, IsIso.hom_inv_id,
    CategoryTheory.Functor.map_id]
  exact Category.comp_id _

end Stacks.Cohomology.DerivedSectionsLeray

end
