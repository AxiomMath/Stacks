module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.OpenSubschemeSingleModelCrossing
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.OpenSubschemeDerivedScalars

/-!
# The unit composites of the two sides of the open-subscheme model composition

The tail of conclusion (c) of [Stacks, Tag 0EX3] needs the geometric comparison
`…TopDegreeBaseChange.openSubschemeSectionsComparisonLE` expressed through the **bare-pair**
comparison `…TopDegreeBaseChange.openSubschemeBareComparisonOf`, the one
`…TopDegreeBaseChange.singleCompDerivedOpenSubscheme_hom_app_comp_compRightDerivedNatIso_hom`
— brick (i) of the 2b(B) match — is stated at. The identity owed is

> `openSubschemeSectionsComparisonLE f V e`, followed by
> `Stacks.EdgeCompat.preimageSectionsModelComparison (f.resLE V U e) ⊤` whiskered by the derived
> restriction on the left and by the derived restriction of scalars along `topIso` at `V` on the
> right, equals `Stacks.EdgeCompat.preimageSectionsModelComparison f V`, then
> `…preimageSectionsRestrictSourceModelComparison f V e`, then
> `…TopDegreeBaseChange.derivedSectionsImageTopIso` inverted and whiskered by the downstairs
> scalars, then `…TopDegreeBaseChange.derivedScalarsReconciliation`, then
> `…TopDegreeBaseChange.openSubschemeBareComparisonOf` whiskered by the two scalars layers.

Both sides are transformations out of the total right derived functor
`Stacks.Cohomology.DerivedSectionsLeray.derivedPreimageSections f V`, so
`CategoryTheory.Functor.rightDerived_ext` reduces that identity to the identity of their two
composites with the derivation unit. **This file computes those two composites.** The identity
itself is not proved here; what is left of it after this file is one coherence identity between
two degreewise composites, written out in `BaseChangeSectionsTail.lean`'s ledger.

Nothing is assumed of `f`, of `V`, of `U` or of the module anywhere in this file.

## Main definitions

* `…TopDegreeBaseChange.bareUnitImageTop` — `…TopDegreeBaseChange.openSubschemeBareUnitOf`
  re-typed at the sections functor over `U.ι ''ᵁ ⊤` of `X`. The re-typing is not cosmetic, see the
  implementation notes.

## Main results

* `…TopDegreeBaseChange.openSubschemeSectionsComparisonLE_comp_upstairsModel_unit` — **the left
  side's unit composite**: it is `…TopDegreeBaseChange.openSubschemeUnitOfNatTransUnit` at the
  degreewise crossing and at `Stacks.EdgeCompat.preimageSectionsCompUnit` for the restricted
  morphism over `⊤`.
* `…TopDegreeBaseChange.modelComposition_unit` — **the right side's unit composite**: three
  degreewise prefixes — the restriction of sections to `U`, the crossing of the two sections
  functors inverted, and the degreewise reconciliation of the scalars — followed by two
  applications of
  `Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.exactPostcomposeUnit` to
  `…TopDegreeBaseChange.openSubschemeBareUnitOf`.
* `…TopDegreeBaseChange.derivedSectionsImageTopIso_inv_unit`,
  `…preimageSectionsRestrictSourceCompUnit_comp_derivedSectionsImageTopIso_inv`,
  `…scalarsUnitA_comp_derivedScalarsReconciliation` and
  `…scalarsUnitB_comp_openSubschemeBareComparisonOf` — the three middle steps of that
  computation, each absorbing one factor of the composition into the unit.

## Implementation notes

*How the five factors are absorbed.* Factors one and two are right derived descents and go by
`CategoryTheory.Functor.rightDerived_fac`. Factors three and five are whiskerings of a
transformation of the right derived functors upstairs, and go by
`Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.exactPostcomposeUnit_comp` — three
applications in all — together with `…exactPostcomposeUnit_whiskerRight`, which pulls out the
degreewise prefix that inverting `derivedSectionsImageTopIso` leaves. Factor four is a
`CategoryTheory.Functor.rightDerivedNatIso` and goes by
`CategoryTheory.Functor.rightDerivedNatTrans_fac`. The two reassociation steps are private
lemmas at variables, the discipline this subtree records for goals of this shape.

*Why `openSubschemeBareUnitOf` has to be re-typed.* Its degreewise source is written
`openSubschemeRestrictionOf X U ⋙ sectionsOverOpen (U : Scheme) ⊤`, which **is**
`sectionsOverOpen X (U.ι ''ᵁ ⊤)` by `rfl`; but keyed on the first spelling the composite with
`…TopDegreeBaseChange.resLETopRestrictScalars` is reported as missing a
`CategoryTheory.Functor.Additive` instance — a recurring problem with pairs of
spellings like these. `bareUnitImageTop` works around it and proves nothing.

*No `@[stacks …]` attribute is placed.* Conclusion (c) of [Stacks, Tag 0EX3] is proved elsewhere,
as `…TopDegreeBaseChange.isIso_topDirectImageBaseChangeMap` (`BaseChangeTopDegreeConclusion.lean`),
by a route that does not use this file.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction (opensMap)
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (exists_quasiIso_isKInjective)
open Stacks.Cohomology.HypercohomologyEdge.HomologyComparison
  (exactPostcomposeUnit exactPostcomposeUnit_comp exactPostcomposeUnit_whiskerRight)
open Stacks.Cohomology.DerivedSectionsLeray
  (sectionsOverOpen derivedSectionsOverOpen derivedSectionsOverOpenUnit preimageSections
   derivedPreimageSections derivedPreimageSectionsUnit sectionsRestrictScalars)
open Stacks.EdgeCompat (preimageRestrictScalars preimageSectionsModelComparison
  preimageSectionsRestrictSourceModelComparison preimageSectionsCompUnit
  preimageSectionsRestrictSourceCompUnit preimageSectionsRestrictSource
  derivedPreimageSectionsUnitComp)

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

variable {X S : Scheme.{u}} (f : X ⟶ S) (V : S.Opens) {U : X.Opens} (e : U ≤ f ⁻¹ᵁ V)

/-- One step of a chain of right derived descents, at variables. -/
private theorem whiskerLeft_step {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (L : C ⥤ D) {F : C ⥤ E} {G H K : D ⥤ E} {α : F ⟶ L ⋙ G} {A : G ⟶ H} {β : F ⟶ L ⋙ H}
    (h : α ≫ Functor.whiskerLeft L A = β) (B : H ⟶ K) :
    α ≫ Functor.whiskerLeft L (A ≫ B) = β ≫ Functor.whiskerLeft L B := by
  rw [Functor.whiskerLeft_comp, ← Category.assoc, h]

/-- The same with a degreewise prefix already split off, at variables. -/
private theorem comp_step {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (L : C ⥤ D) {F F' : C ⥤ E} {G H : D ⥤ E} (p : F ⟶ F') {q : F' ⟶ L ⋙ G} {A : G ⟶ H}
    {β : F' ⟶ L ⋙ H} (h : q ≫ Functor.whiskerLeft L A = β) :
    (p ≫ q) ≫ Functor.whiskerLeft L A = p ≫ β := by
  rw [Category.assoc, h]

/-- The derivation unit of `derivedPreimageSections f V`, followed by
`openSubschemeSectionsComparisonLE f V e` and the whiskered comparison
`preimageSectionsModelComparison (f.resLE V U e) ⊤`, is `openSubschemeUnitOfNatTransUnit` at the
degreewise crossing `preimageSectionsOpenSubschemeLE f V e` and at `preimageSectionsCompUnit` for
`f.resLE V U e` over `⊤`. -/
theorem openSubschemeSectionsComparisonLE_comp_upstairsModel_unit :
    derivedPreimageSectionsUnit f.toLRSHom.toShHom V ≫
        Functor.whiskerLeft DerivedCategory.Qh
          (openSubschemeSectionsComparisonLE f V e ≫
            Functor.whiskerLeft (openSubschemeRestrictionOf X U).mapDerivedCategory
              (Functor.whiskerRight
                (preimageSectionsModelComparison (f.resLE V U e).toLRSHom.toShHom ⊤)
                (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom).mapDerivedCategory)) =
      openSubschemeUnitOfNatTransUnit f V e (preimageSectionsOpenSubschemeLE f V e)
        (preimageSectionsCompUnit (f.resLE V U e).toLRSHom.toShHom ⊤) := by
  have h2 : derivedPreimageSectionsUnit (f.resLE V U e).toLRSHom.toShHom ⊤ ≫
      Functor.whiskerLeft DerivedCategory.Qh
        (preimageSectionsModelComparison (f.resLE V U e).toLRSHom.toShHom ⊤) =
      preimageSectionsCompUnit (f.resLE V U e).toLRSHom.toShHom ⊤ :=
    Functor.rightDerived_fac _ _ _ _ _
  refine (whiskerLeft_step _ (Functor.rightDerived_fac _ _ _ _ _) _).trans (Eq.symm ?_)
  rw [← h2]
  exact openSubschemeUnitOfNatTransUnit_comp f V e (preimageSectionsOpenSubschemeLE f V e)
    (derivedPreimageSectionsUnit (f.resLE V U e).toLRSHom.toShHom ⊤)
    (preimageSectionsModelComparison (f.resLE V U e).toLRSHom.toShHom ⊤)

/-- The inverse half of the equation characterizing `derivedSectionsImageTopIso`. -/
theorem derivedSectionsImageTopIso_inv_unit :
    derivedSectionsOverOpenUnit X.toRingedSpace U ≫
        Functor.whiskerLeft DerivedCategory.Qh (derivedSectionsImageTopIso X U).inv =
      Functor.whiskerRight
          (NatTrans.mapHomotopyCategory (sectionsImageTopNatIsoOf X U).inv
            (ComplexShape.up ℤ)) DerivedCategory.Qh ≫
        imageTopCompUnit X U :=
  Functor.rightDerivedNatTrans_fac (derivedSectionsOverOpen X.toRingedSpace U)
    (derivedSectionsOverOpen X.toRingedSpace (U.ι ''ᵁ ⊤) ⋙
      (imageTopRestrictScalarsOf X U).mapDerivedCategory)
    (derivedSectionsOverOpenUnit X.toRingedSpace U) (imageTopCompUnit X U)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (ComplexShape.up ℤ)) _

/-- **`openSubschemeBareUnitOf` re-typed at the sections functor over `U.ι ''ᵁ ⊤` of `X`.** The
degreewise functor `openSubschemeRestrictionOf X U ⋙ sectionsOverOpen (U : Scheme) ⊤` **is**
`sectionsOverOpen X (U.ι ''ᵁ ⊤)`, by `rfl`, but keyed on the first spelling the composite with
`resLETopRestrictScalars` is reported as missing a `Functor.Additive` instance — hence the
re-typing. Nothing is proved here; only the spelling changes. -/
def bareUnitImageTop :
    (sectionsOverOpen X.toRingedSpace (U.ι ''ᵁ ⊤)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ ((openSubschemeRestrictionOf X U).mapDerivedCategory ⋙
        derivedSectionsOverOpen (U : Scheme).toRingedSpace ⊤) :=
  openSubschemeBareUnitOf X U

/-- The third step: the crossing of the two sections functors, absorbed into side A's unit. -/
theorem preimageSectionsRestrictSourceCompUnit_comp_derivedSectionsImageTopIso_inv :
    exactPostcomposeUnit (sectionsOverOpen X.toRingedSpace U) (restrictSourceScalars f V e)
        (derivedSectionsOverOpen X.toRingedSpace U)
        (derivedSectionsOverOpenUnit X.toRingedSpace U) ≫
        Functor.whiskerLeft DerivedCategory.Qh
          (Functor.whiskerRight (derivedSectionsImageTopIso X U).inv
            (restrictSourceScalars f V e).mapDerivedCategory) =
      Functor.whiskerRight
          (NatTrans.mapHomotopyCategory
            (Functor.whiskerRight (sectionsImageTopNatIsoOf X U).inv
              (restrictSourceScalars f V e)) (ComplexShape.up ℤ)) DerivedCategory.Qh ≫
        scalarsUnitA f V e :=
  (exactPostcomposeUnit_comp (sectionsOverOpen X.toRingedSpace U) (restrictSourceScalars f V e)
        _ _ (derivedSectionsOverOpenUnit X.toRingedSpace U)
        (derivedSectionsImageTopIso X U).inv).trans
    ((congrArg (exactPostcomposeUnit (sectionsOverOpen X.toRingedSpace U)
          (restrictSourceScalars f V e) _)
        (derivedSectionsImageTopIso_inv_unit (X := X) (U := U))).trans
      (exactPostcomposeUnit_whiskerRight _ _ _ _ _ _))

/-- The fifth step: the bare comparison of the two models of `RΓ(U, -)`, absorbed. -/
theorem scalarsUnitB_comp_openSubschemeBareComparisonOf :
    exactPostcomposeUnit (sectionsOverOpen X.toRingedSpace (U.ι ''ᵁ ⊤) ⋙
          resLETopRestrictScalars f V e) (baseTopRestrictScalars V) _ (resLETopUnit f V e) ≫
        Functor.whiskerLeft DerivedCategory.Qh
          (Functor.whiskerRight (openSubschemeBareComparisonOf X U)
            ((resLETopRestrictScalars f V e).mapDerivedCategory ⋙
              (baseTopRestrictScalars V).mapDerivedCategory)) =
      exactPostcomposeUnit (sectionsOverOpen X.toRingedSpace (U.ι ''ᵁ ⊤) ⋙
          resLETopRestrictScalars f V e) (baseTopRestrictScalars V) _
        (exactPostcomposeUnit (sectionsOverOpen X.toRingedSpace (U.ι ''ᵁ ⊤))
          (resLETopRestrictScalars f V e) _ (bareUnitImageTop (X := X) (U := U))) :=
  (exactPostcomposeUnit_comp (sectionsOverOpen X.toRingedSpace (U.ι ''ᵁ ⊤) ⋙
          resLETopRestrictScalars f V e) (baseTopRestrictScalars V) _ _ (resLETopUnit f V e)
        (Functor.whiskerRight (openSubschemeBareComparisonOf X U)
          (resLETopRestrictScalars f V e).mapDerivedCategory)).trans
    (congrArg (exactPostcomposeUnit (sectionsOverOpen X.toRingedSpace (U.ι ''ᵁ ⊤) ⋙
        resLETopRestrictScalars f V e) (baseTopRestrictScalars V) _)
      ((exactPostcomposeUnit_comp (sectionsOverOpen X.toRingedSpace (U.ι ''ᵁ ⊤))
            (resLETopRestrictScalars f V e) _ _
            (derivedSectionsOverOpenUnit X.toRingedSpace (U.ι ''ᵁ ⊤))
            (openSubschemeBareComparisonOf X U)).trans
        (congrArg (exactPostcomposeUnit (sectionsOverOpen X.toRingedSpace (U.ι ''ᵁ ⊤))
            (resLETopRestrictScalars f V e) _)
          (Functor.rightDerived_fac _ _ _ _ _))))

/-- The fourth step: the derived reconciliation of the two readings of the scalars. -/
theorem scalarsUnitA_comp_derivedScalarsReconciliation :
    scalarsUnitA f V e ≫
        Functor.whiskerLeft DerivedCategory.Qh (derivedScalarsReconciliation f V e).hom =
      Functor.whiskerRight
          (NatTrans.mapHomotopyCategory
            (Functor.whiskerLeft (sectionsOverOpen X.toRingedSpace (U.ι ''ᵁ ⊤))
              (scalarsReconciliation f V e).hom) (ComplexShape.up ℤ)) DerivedCategory.Qh ≫
        scalarsUnitB f V e :=
  Functor.rightDerivedNatTrans_fac _ _ (scalarsUnitA f V e) (scalarsUnitB f V e)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (ComplexShape.up ℤ)) _

/-- The five steps composed: the unit composite of the right-hand side of the gluing. -/
theorem modelComposition_unit :
    derivedPreimageSectionsUnit f.toLRSHom.toShHom V ≫
        Functor.whiskerLeft DerivedCategory.Qh
          (preimageSectionsModelComparison f.toLRSHom.toShHom V ≫
            preimageSectionsRestrictSourceModelComparison f.toLRSHom.toShHom V e ≫
              Functor.whiskerRight (derivedSectionsImageTopIso X U).inv
                  (restrictSourceScalars f V e).mapDerivedCategory ≫
                (derivedScalarsReconciliation f V e).hom ≫
                  Functor.whiskerRight (openSubschemeBareComparisonOf X U)
                    ((resLETopRestrictScalars f V e).mapDerivedCategory ⋙
                      (baseTopRestrictScalars V).mapDerivedCategory)) =
      Functor.whiskerRight
          (NatTrans.mapHomotopyCategory (preimageSectionsRestrictSource f.toLRSHom.toShHom V e)
            (ComplexShape.up ℤ)) DerivedCategory.Qh ≫
        Functor.whiskerRight
            (NatTrans.mapHomotopyCategory
              (Functor.whiskerRight (sectionsImageTopNatIsoOf X U).inv
                (restrictSourceScalars f V e)) (ComplexShape.up ℤ)) DerivedCategory.Qh ≫
          Functor.whiskerRight
              (NatTrans.mapHomotopyCategory
                (Functor.whiskerLeft (sectionsOverOpen X.toRingedSpace (U.ι ''ᵁ ⊤))
                  (scalarsReconciliation f V e).hom) (ComplexShape.up ℤ))
              DerivedCategory.Qh ≫
            exactPostcomposeUnit (sectionsOverOpen X.toRingedSpace (U.ι ''ᵁ ⊤) ⋙
                resLETopRestrictScalars f V e) (baseTopRestrictScalars V) _
              (exactPostcomposeUnit (sectionsOverOpen X.toRingedSpace (U.ι ''ᵁ ⊤))
                (resLETopRestrictScalars f V e) _ (bareUnitImageTop (X := X) (U := U))) := by
  have r1 : derivedPreimageSectionsUnit f.toLRSHom.toShHom V ≫
      Functor.whiskerLeft DerivedCategory.Qh
        (preimageSectionsModelComparison f.toLRSHom.toShHom V) =
      preimageSectionsCompUnit f.toLRSHom.toShHom V :=
    Functor.rightDerived_fac _ _ _ _ _
  have r2 : preimageSectionsCompUnit f.toLRSHom.toShHom V ≫
      Functor.whiskerLeft DerivedCategory.Qh
        (preimageSectionsRestrictSourceModelComparison f.toLRSHom.toShHom V e) =
      Functor.whiskerRight
          (NatTrans.mapHomotopyCategory (preimageSectionsRestrictSource f.toLRSHom.toShHom V e)
            (ComplexShape.up ℤ)) DerivedCategory.Qh ≫
        preimageSectionsRestrictSourceCompUnit f.toLRSHom.toShHom V e :=
    Functor.rightDerived_fac _ _ _ _ _
  refine (whiskerLeft_step _ r1 _).trans ((whiskerLeft_step _ r2 _).trans ?_)
  refine (comp_step _ _ (whiskerLeft_step _
    (preimageSectionsRestrictSourceCompUnit_comp_derivedSectionsImageTopIso_inv f V e) _)).trans
      (congrArg _ ?_)
  refine (comp_step _ _ (whiskerLeft_step _
    (scalarsUnitA_comp_derivedScalarsReconciliation f V e) _)).trans (congrArg _ ?_)
  exact comp_step _ _ (scalarsUnitB_comp_openSubschemeBareComparisonOf f V e)

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
