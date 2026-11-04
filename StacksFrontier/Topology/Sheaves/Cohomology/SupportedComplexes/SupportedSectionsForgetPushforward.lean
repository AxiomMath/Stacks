module

public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.AbelianSupportedSectionsCounit
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.AbelianSupportedCounitForget

/-!
# Forgetting the module structure, realized on `Z` and pushed back

Let `Z` be a closed subset of a ringed space `X` and `i : Z ⟶ X` the inclusion.  Four
identifications relate the two ways of reading "the sections supported on `Z`, with the module
structure forgotten":

* `supportedSectionsOnClosedFunctor_comp_modulePushforward_iso` of the namespace
  `Stacks.SheafOfModules.SupportedSections`: `ℋ_Z` realized on `Z` and pushed forward is the
  supported-sections subsheaf, for modules;
* `Stacks.Cohomology.SupportedComplexes.abelianSupportedSectionsRealizedCompPushforwardIso`:
  the same, for abelian sheaves;
* `Stacks.Cohomology.AbelianSupportedCounit.abelianSupportedSectionsForgetIso`: forgetting
  commutes with the supported-sections endofunctor on `X`;
* `Stacks.Cohomology.SupportedComplexes.abelianSupportedSectionsOnClosedForgetIso`
  ([Stacks, Tag 0G6N]): forgetting commutes with `ℋ_Z` realized on `Z`.

This file proves that the square they form commutes, and carries that square to the homotopy
category of cochain complexes.

## Main results

* `forgetPushforwardSquare_app`: the square at a module.  Both composites are the identification
  of the underlying abelian sheaf of `i_*ℋ_Z(ℱ)` with `i_*ℋ_Z(ℱ_ab)`.
* `forgetPushforwardSquare_homotopy`: the same square after
  `CategoryTheory.Functor.mapHomotopyCategory`, with all four identifications read through
  `CategoryTheory.Functor.mapHomotopyCategoryCompIso`.  This is the degreewise input to the
  comparison of the two derivations of [Stacks, Tag 0G74] part (2) — the one stated on `Z` and the
  one with `i_*` folded in.

## Implementation notes

**Why the square holds.**  `abelianSupportedSectionsOnClosedForgetIso` is *defined* by cancelling
the fully faithful direct image `i_*` off the composite of the other three, so the square is its
defining property.  The proof reads that definition through
`CategoryTheory.Functor.fullyFaithfulCancelRight_hom_app` and `Functor.map_preimage`.

**The two comparisons with explicit instances.**  `forgetCompIsoOnClosed` and
`Stacks.Cohomology.AbelianSupportedCounitForget.forgetCompIso`
spell the instance arguments of `CategoryTheory.Functor.mapHomotopyCategoryCompIso` exactly as
`Stacks.Cohomology.SupportedComplexes.supportedSheafForgetUnit` and
`Stacks.Cohomology.AbelianSupportedCounit.abelianSupportedEndoForgetUnit` do.  This is not
cosmetic: the two spellings of the abelian sheaf category described in the implementation notes of
the module `UnderlyingAbelianLocalCohomologyComparison` of
`StacksDraft.Topology.Sheaves.Cohomology.SupportedComplexes` make instance search for the
additivity of `Φ ⋙ ℋ_Z` fail outright in a composite whose other factors are elaborated first, so
the comparisons must be written with the instances supplied, and written the *same* way as in the
two units, or the statements below do not meet them.

**No `@[stacks ...]` attribute is attached to any declaration here.**

## References

* [Stacks Project, Remark 17.13.5 (Tag 0G6N)](https://stacks.math.columbia.edu/tag/0G6N)
* [Stacks Project, Lemma 20.34.8 (Tag 0G74)](https://stacks.math.columbia.edu/tag/0G74)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.AbelianSupportedCounit
open Stacks.Cohomology.SupportedComplexes
open Stacks.SheafOfModules.SupportedSections

universe u

namespace Stacks.Cohomology.SupportedSectionsForgetPushforward

variable (X : RingedSpace.{u, u}) (Z : Set X.carrier) (hZ : IsClosed Z)

/-- Cancelling a composable pair whose composite is the identity at the head of the argument of a
functor, at an abstract category; stated at a variable category because the two spellings of the
objects involved are interchangeable only at default transparency. -/
lemma map_comp_head_id {C₀ D₀ : Type*} [Category* C₀] [Category* D₀] (W : C₀ ⥤ D₀)
    {A B : C₀} (a : A ⟶ B) (b : B ⟶ A) (hab : a ≫ b = 𝟙 A) {M : D₀} (r : W.obj A ⟶ M) :
    W.map a ≫ W.map b ≫ r = r := by
  rw [← Category.assoc, ← W.map_comp, hab, W.map_id, Category.id_comp]

/-- **Forgetting the module structure commutes with realizing the supported sections on `Z` and
pushing them back.**

Going down the module side — realize `ℋ_Z(ℱ)` on `Z`, push it to `X`, identify it with the
supported-sections subsheaf, then forget — is going down the abelian side: forget, take the
abelian supported-sections subsheaf, and identify it with the pushforward of `ℋ_Z(ℱ_ab)`.

This is the defining property of
`Stacks.Cohomology.SupportedComplexes.abelianSupportedSectionsOnClosedForgetIso`, which is
obtained by cancelling the fully faithful direct image off exactly this composite. -/
theorem forgetPushforwardSquare_app (F : _root_.SheafOfModules.{u} (structureSheafRing X)) :
    (_root_.SheafOfModules.toSheaf (structureSheafRing X)).map
          ((supportedSectionsOnClosedFunctor_comp_modulePushforward_iso X Z hZ).inv.app F) ≫
        (abelianClosedPushforward Z).map
          ((abelianSupportedSectionsOnClosedForgetIso X Z hZ).hom.app F) =
      (abelianSupportedSectionsForgetIso X Z).hom.app F ≫
        (abelianSupportedSectionsRealizedCompPushforwardIso Z hZ).inv.app
          ((_root_.SheafOfModules.toSheaf (structureSheafRing X)).obj F) := by
  have hff := closedInclusionPushforwardFullyFaithful (TopCat.of Z) _
    (ClosedImmersionSheaves.closedSubsetInclusion Z) hZ.isClosedEmbedding_subtypeVal
  have hfull : (abelianClosedPushforward Z).Full := hff.full
  have hfaith : (abelianClosedPushforward Z).Faithful := hff.faithful
  have key : (abelianClosedPushforward Z).map
        ((abelianSupportedSectionsOnClosedForgetIso X Z hZ).hom.app F) =
      (_root_.SheafOfModules.toSheaf (structureSheafRing X)).map
          ((supportedSectionsOnClosedFunctor_comp_modulePushforward_iso X Z hZ).hom.app F) ≫
        (abelianSupportedSectionsForgetIso X Z).hom.app F ≫
        (abelianSupportedSectionsRealizedCompPushforwardIso Z hZ).inv.app
          ((_root_.SheafOfModules.toSheaf (structureSheafRing X)).obj F) := by
    show (abelianClosedPushforward Z).map
        ((supportedSectionsOnClosedForgetIso X Z hZ).hom.app F) = _
    unfold supportedSectionsOnClosedForgetIso
    refine Eq.trans (Functor.map_preimage _ _) ?_
    rfl
  rw [key]
  exact map_comp_head_id _ _ _ (Iso.inv_hom_id_app _ _) _

/-- The comparison of homotopy categories attached to
`Stacks.Cohomology.SupportedComplexes.abelianSupportedSectionsOnClosedForgetIso`, with the
instance arguments spelled exactly as in
`Stacks.Cohomology.SupportedComplexes.supportedSheafForgetUnit`. -/
abbrev forgetCompIsoOnClosed :
    (supportedSectionsOnClosedFunctor X Z hZ).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (_root_.SheafOfModules.toSheaf
          (structureSheafRing (closedSubsetRingedSpace X Z))).mapHomotopyCategory
            (ComplexShape.up ℤ) ≅
      (_root_.SheafOfModules.toSheaf (structureSheafRing X) ⋙
        abelianSupportedSectionsOnClosed X Z hZ).mapHomotopyCategory (ComplexShape.up ℤ) :=
  @Functor.mapHomotopyCategoryCompIso _ _ _ _ _ _ _ _ _ _ _ _ _
    (abelianSupportedSectionsOnClosedForgetIso X Z hZ)
    (by exact supportedSectionsOnClosedFunctor_additive X Z hZ)
    (by exact inferInstanceAs
      (_root_.SheafOfModules.toSheaf
        (structureSheafRing (closedSubsetRingedSpace X Z))).Additive)
    (by exact forget_abelianSupportedSectionsOnClosed_additive X Z hZ)
    (ComplexShape.up ℤ)

/-- **The square of `forgetPushforwardSquare_app` on the homotopy category of cochain
complexes.**

Each of the four identifications is read through
`CategoryTheory.Functor.mapHomotopyCategoryCompIso`, and the direct images through
`CategoryTheory.Functor.mapHomotopyCategory`.  Every morphism in sight is the quotient of the
corresponding morphism of complexes, so the identity is the degreewise one applied to the
representing complex. -/
theorem forgetPushforwardSquare_homotopy
    (K : HomotopyCategory (_root_.SheafOfModules.{u} (structureSheafRing X))
      (ComplexShape.up ℤ)) :
    ((_root_.SheafOfModules.toSheaf (structureSheafRing X)).mapHomotopyCategory
          (ComplexShape.up ℤ)).map
        ((Functor.mapHomotopyCategoryCompIso
          (supportedSectionsOnClosedFunctor_comp_modulePushforward_iso X Z hZ)
          (ComplexShape.up ℤ)).inv.app K) ≫
      ((abelianClosedPushforward Z).mapHomotopyCategory (ComplexShape.up ℤ)).map
        ((forgetCompIsoOnClosed X Z hZ).hom.app K) =
    (AbelianSupportedCounitForget.forgetCompIso X Z).hom.app K ≫
      (Functor.mapHomotopyCategoryCompIso
          (abelianSupportedSectionsRealizedCompPushforwardIso Z hZ)
          (ComplexShape.up ℤ)).inv.app
        (((_root_.SheafOfModules.toSheaf (structureSheafRing X)).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj K) := by
  refine congrArg (HomotopyCategory.quotient
    (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) (ComplexShape.up ℤ)).map
    (HomologicalComplex.hom_ext _ _ fun i => ?_)
  exact forgetPushforwardSquare_app X Z hZ (K.as.X i)

end Stacks.Cohomology.SupportedSectionsForgetPushforward

end
