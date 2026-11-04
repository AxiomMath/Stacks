module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.OpenSubschemeModelCompositionUnit

/-!
# The four pieces of the open-subscheme model composition's coherence identity

The tail of conclusion (c) of [Stacks, Tag 0EX3] needs the geometric comparison
`…TopDegreeBaseChange.openSubschemeSectionsComparisonLE` expressed through the **bare-pair**
comparison `…TopDegreeBaseChange.openSubschemeBareComparisonOf`, the one
`…TopDegreeBaseChange.singleCompDerivedOpenSubscheme_hom_app_comp_compRightDerivedNatIso_hom`
is stated at.
`CategoryTheory.Functor.rightDerived_ext` reduces that identity to the identity of the two unit
composites `OpenSubschemeModelCompositionUnit.lean` computes, and what is left of it is one
coherence identity between them. **This file is that identity's four pieces, each proved**; the
identity itself and the gluing are composed from them in
`OpenSubschemeModelCompositionGlue.lean` — `…TopDegreeBaseChange.modelComposition_coherence` and
`…openSubschemeSectionsComparisonLE_eq_modelComposition` — one declaration downstream, for the
reason the implementation notes give.

Nothing is assumed of `f`, of `V`, of `U` or of the module anywhere in this file.

## Main results

* `…TopDegreeBaseChange.preimageSectionsOpenSubschemeLE_eq` — the degreewise crossing read as the
  three degreewise prefixes the right-hand side meets: the restriction of sections to `U`, the
  crossing of the two sections functors inverted, and the reconciliation of the scalars. It holds
  by definition.
* `…TopDegreeBaseChange.whiskerRight_mapHomotopyCategory_preimageSectionsOpenSubschemeLE` — the
  same read on the homotopy category and localized, where it is the three prefixes of
  `…TopDegreeBaseChange.modelComposition_unit`.
* `…TopDegreeBaseChange.openSubschemeBareUnitOf_eq` — the two-fold
  `Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.exactPostcomposeUnit` on
  `…TopDegreeBaseChange.openSubschemeBareUnitOf`, read at the spellings of the open subscheme.
  It holds by definition.
* `…TopDegreeBaseChange.openSubschemeBareUnitOf_eq_precomposeTail` and `…_eq_precomposeTail'` —
  **that two-fold unit is the tail of `…TopDegreeBaseChange.openSubschemeUnitOfNatTransUnit`**, by
  `Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.exactPostcomposeUnit_precompose_comp`;
  the primed form reads the target at the open subscheme's spelling as well.
* `…TopDegreeBaseChange.openSubschemeUnitOfNatTransUnit_eq_precomposeTail` — the left side's unit
  composite is the degreewise crossing followed by that tail. It holds by definition.

## Implementation notes

*Why the coherence identity is one application of a general transport, and nothing
mathematical.* Writing `r` for the restriction to the open subscheme, the left side's unit
composite is the degreewise crossing followed by `…openSubschemeUnitOfNatTransUnit` at
`Stacks.EdgeCompat.preimageSectionsCompUnit (f.resLE V U e) ⊤`, and the latter is itself an
`exactPostcomposeUnit`; the right side's is the three degreewise prefixes followed by
`exactPostcomposeUnit` applied twice to `openSubschemeBareUnitOf X U`. Both tails are therefore
the same two-step postcomposition of the unit of `RΓ((f.resLE V U e)⁻¹⊤, -)` by the two exact
restrictions of scalars, taken in the two possible orders — precomposing `r` first, or
postcomposing the scalars first — and that is
`Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.exactPostcomposeUnit_precompose_comp`,
proved at variables of abstract categories. The three prefixes agree factor for factor by
`preimageSectionsOpenSubschemeLE_eq`. So the identity is these four results composed, with
`CategoryTheory.NatTrans.mapHomotopyCategory_comp` and one reassociation.

***Why the declarations below are split.*** The two sides spell the same functors
differently throughout — `U.ι ''ᵁ ⊤` of `X` against `⊤` of the open subscheme,
`(f.resLE V U e)⁻¹⊤` against `⊤`, and the ascribed
`…resLETopRestrictScalars`/`…baseTopRestrictScalars` against
`Stacks.EdgeCompat.preimageRestrictScalars` and the bare
`CategoryTheory.ModuleCat.restrictScalars` — and crossing one such pair is definitional but costs
a large part of a declaration's 200,000 heartbeats (a single factor of the flattened
component identity is `rfl` in about five seconds). Five crossings are needed: the two-fold unit's
term, its source functor, its target functor, the prefix's target, and the model composition's
target. Each of the declarations below pays exactly one, and they are split for that reason alone.
Composing them needs a sixth, and `OpenSubschemeModelCompositionGlue.lean` is the declaration that
pays it: in `theorem _ : A = B` Lean elaborates `A`, then `B` against `A`'s type, so the equation's
type index is `A`'s and the crossing is made once, during the statement's elaboration — provided
the **open-subscheme** side, the spelling all four results below live at, is written first. The
proof is then syntactic. Four arrangements that put the crossing in the statement *and again* in
the proof exhaust the budget on the second: the term built with `have` and
discharged by `exact` (`timeout at isDefEq`), the same in term mode (`timeout at whnf`), a `rw`
chain (refused outright — the motive is not type-correct at `implicit` transparency,
`preimageRestrictScalars` being keyed on the ascribed spelling of its source ring), and the
component route of `CategoryTheory.NatTrans.ext` plus `simp only` (which flattens both sides to the
same factors in the same order, but leaves `Functor.whiskerRight_app` unapplied on the whiskered
unit — silently — and `rw [Functor.whiskerRight_app]` is refused there too).

*Two routes not taken.* `CategoryTheory.NatTrans.ext` with the `ext` tactic exhausts
the heartbeats at `whnf` on the coherence goal where `NatTrans.ext (funext fun K => ?_)` succeeds;
and instantiating `exactPostcomposeUnit_precompose_comp` at
`(sectionsOverOpen (U : Scheme) ⊤, resLETopRestrictScalars f V e)` is **refused**,
`(resLETopRestrictScalars f V e).Additive` being reported `failed to synthesize` when the
intermediate category is spelled from the first factor's target although it is found by
`inferInstance` standing alone — the instance-spelling problem, at a sixth pair. The
instantiation below is at `(sectionsOverOpen (U : Scheme) ((opensMap (f.resLE V U e)).obj ⊤),
preimageRestrictScalars (f.resLE V U e) ⊤)`, the pair `…DerivedSectionsLeray.preimageSections` is
built from, where the two spellings agree by construction and no ascription is needed.

*No `@[stacks …]` attribute is placed.* Conclusion (c) of [Stacks, Tag 0EX3] is proved elsewhere,
as `…TopDegreeBaseChange.isIso_topDirectImageBaseChangeMap` (`BaseChangeTopDegreeConclusion.lean`),
by a route that does not use this file.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction (opensMap)
open Stacks.Cohomology.HypercohomologyEdge.HomologyComparison
  (exactPostcomposeUnit exactPostcomposeUnit_precompose_comp)
open Stacks.Cohomology.DerivedSectionsLeray
  (sectionsOverOpen derivedSectionsOverOpen derivedSectionsOverOpenUnit preimageSections)
open Stacks.EdgeCompat (preimageRestrictScalars preimageSectionsCompUnit
  preimageSectionsRestrictSource)

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

variable {X S : Scheme.{u}} (f : X ⟶ S) (V : S.Opens) {U : X.Opens} (e : U ≤ f ⁻¹ᵁ V)


/-- Three transformations' degreewise actions on the homotopy category, localized, at variables,
where the two splittings are free. -/
private theorem whiskerRight_mapHomotopyCategory_comp_three {A B : Type*} [Category* A]
    [Preadditive A] [Category* B] [Preadditive B] {E : Type*} [Category* E]
    {ι : Type*} (c : ComplexShape ι) {F G H K : A ⥤ B} [F.Additive] [G.Additive] [H.Additive]
    [K.Additive] (a : F ⟶ G) (b : G ⟶ H) (d : H ⟶ K) (Φ : HomotopyCategory B c ⥤ E) :
    Functor.whiskerRight (NatTrans.mapHomotopyCategory (a ≫ b ≫ d) c) Φ =
      Functor.whiskerRight (NatTrans.mapHomotopyCategory a c) Φ ≫
        Functor.whiskerRight (NatTrans.mapHomotopyCategory b c) Φ ≫
          Functor.whiskerRight (NatTrans.mapHomotopyCategory d c) Φ := by
  rw [NatTrans.mapHomotopyCategory_comp, NatTrans.mapHomotopyCategory_comp,
    Functor.whiskerRight_comp, Functor.whiskerRight_comp]

/-- **The degreewise crossing read as the three prefixes of the model composition.** The crossing
`…TopDegreeBaseChange.preimageSectionsOpenSubschemeLE` is the restriction of sections from `f⁻¹V`
down to `U` read over `Γ(V, 𝒪_S)`, then the crossing of the two sections functors inverted, then
the reconciliation of the two readings of the scalars — which are, factor for factor, the three
degreewise prefixes `…TopDegreeBaseChange.modelComposition_unit` produces.

The equality holds by definition: `Stacks.EdgeCompat.preimageSectionsRestrictSource` and
`…TopDegreeBaseChange.preimageSectionsRestrictLE` differ only by the
`AlgebraicGeometry.Scheme.Hom.appLE` reading of a composite of two restrictions of scalars,
`…sectionsImageTopNatIsoOf` is `…sectionsOnImageTopNatIso`, and `…scalarsReconciliation` is the
very square the crossing carries. -/
theorem preimageSectionsOpenSubschemeLE_eq :
    (show preimageSections f.toLRSHom.toShHom V ⟶
        openSubschemeRestrictionOf X U ⋙
          preimageSections (f.resLE V U e).toLRSHom.toShHom ⊤ ⋙
            ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom from
      preimageSectionsOpenSubschemeLE f V e) =
      preimageSectionsRestrictSource f.toLRSHom.toShHom V e ≫
        Functor.whiskerRight (sectionsImageTopNatIsoOf X U).inv
            (restrictSourceScalars f V e) ≫
          Functor.whiskerLeft (sectionsOverOpen X.toRingedSpace (U.ι ''ᵁ ⊤))
            (scalarsReconciliation f V e).hom := rfl

/-- **The three degreewise prefixes split off the left side's unit composite.** The leading factor
of `…TopDegreeBaseChange.openSubschemeUnitOfNatTransUnit` at the degreewise crossing is the three
prefixes of `…TopDegreeBaseChange.modelComposition_unit`: `preimageSectionsOpenSubschemeLE_eq` read
on the homotopy category and localized, the two splittings being
`CategoryTheory.NatTrans.mapHomotopyCategory_comp`. -/
theorem whiskerRight_mapHomotopyCategory_preimageSectionsOpenSubschemeLE :
    Functor.whiskerRight (NatTrans.mapHomotopyCategory
        (show preimageSections f.toLRSHom.toShHom V ⟶
            openSubschemeRestrictionOf X U ⋙
              preimageSections (f.resLE V U e).toLRSHom.toShHom ⊤ ⋙
                ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom from
          preimageSectionsOpenSubschemeLE f V e) (ComplexShape.up ℤ)) DerivedCategory.Qh =
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
              DerivedCategory.Qh :=
  (congrArg (fun z => Functor.whiskerRight
      (NatTrans.mapHomotopyCategory z (ComplexShape.up ℤ)) DerivedCategory.Qh)
      (preimageSectionsOpenSubschemeLE_eq f V e)).trans
    (whiskerRight_mapHomotopyCategory_comp_three (ComplexShape.up ℤ)
      (preimageSectionsRestrictSource f.toLRSHom.toShHom V e)
      (Functor.whiskerRight (sectionsImageTopNatIsoOf X U).inv (restrictSourceScalars f V e))
      (Functor.whiskerLeft (sectionsOverOpen X.toRingedSpace (U.ι ''ᵁ ⊤))
        (scalarsReconciliation f V e).hom) DerivedCategory.Qh)

/-- **The two-fold `exactPostcomposeUnit` on `openSubschemeBareUnitOf`, read at the open
subscheme's own spellings.** The ascribed `…TopDegreeBaseChange.resLETopRestrictScalars` and
`…baseTopRestrictScalars` are `Stacks.EdgeCompat.preimageRestrictScalars (f.resLE V U e) ⊤` and
`CategoryTheory.ModuleCat.restrictScalars (AlgebraicGeometry.Scheme.Opens.topIso V).inv.hom`,
`…TopDegreeBaseChange.bareUnitImageTop` is `…openSubschemeBareUnitOf`, and
`sectionsOverOpen X (U.ι ''ᵁ ⊤)` is restriction to the open subscheme followed by sections over
`⊤`, with `(opensMap (f.resLE V U e)).obj ⊤` the open `⊤`. So the equality holds by definition; it
carries a name because the crossing costs a declaration's worth of heartbeats, see this module's
implementation notes. -/
theorem openSubschemeBareUnitOf_eq :
    (exactPostcomposeUnit (sectionsOverOpen X.toRingedSpace (U.ι ''ᵁ ⊤) ⋙
            resLETopRestrictScalars f V e) (baseTopRestrictScalars V) _
          (exactPostcomposeUnit (sectionsOverOpen X.toRingedSpace (U.ι ''ᵁ ⊤))
            (resLETopRestrictScalars f V e) _ (bareUnitImageTop (X := X) (U := U))) :
        (openSubschemeRestrictionOf X U ⋙
              preimageSections (f.resLE V U e).toLRSHom.toShHom ⊤ ⋙
                ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom).mapHomotopyCategory
            (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ _) =
      exactPostcomposeUnit ((openSubschemeRestrictionOf X U ⋙
            sectionsOverOpen (U : Scheme).toRingedSpace
              ((opensMap (f.resLE V U e).toLRSHom.toShHom).obj ⊤)) ⋙
          preimageRestrictScalars (f.resLE V U e).toLRSHom.toShHom ⊤)
        (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom) _
        (exactPostcomposeUnit (openSubschemeRestrictionOf X U ⋙
            sectionsOverOpen (U : Scheme).toRingedSpace
              ((opensMap (f.resLE V U e).toLRSHom.toShHom).obj ⊤))
          (preimageRestrictScalars (f.resLE V U e).toLRSHom.toShHom ⊤)
          ((openSubschemeRestrictionOf X U).mapDerivedCategory ⋙
            derivedSectionsOverOpen (U : Scheme).toRingedSpace
              ((opensMap (f.resLE V U e).toLRSHom.toShHom).obj ⊤))
          (Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso
                (Iso.refl (openSubschemeRestrictionOf X U ⋙
                  sectionsOverOpen (U : Scheme).toRingedSpace
                    ((opensMap (f.resLE V U e).toLRSHom.toShHom).obj ⊤)))
                (ComplexShape.up ℤ)).inv DerivedCategory.Qh ≫
            Functor.whiskerLeft ((openSubschemeRestrictionOf X U).mapHomotopyCategory
                (ComplexShape.up ℤ))
              (derivedSectionsOverOpenUnit (U : Scheme).toRingedSpace
                ((opensMap (f.resLE V U e).toLRSHom.toShHom).obj ⊤)) ≫
              Functor.whiskerRight (openSubschemeRestrictionOf X U).mapDerivedCategoryFactorsh.inv
                (derivedSectionsOverOpen (U : Scheme).toRingedSpace
                  ((opensMap (f.resLE V U e).toLRSHom.toShHom).obj ⊤)))) := rfl

/-- **The two-fold unit is the tail of `openSubschemeUnitOfNatTransUnit`.**
`openSubschemeBareUnitOf_eq` composed with
`Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.exactPostcomposeUnit_precompose_comp`:
postcomposing the two exact restrictions of scalars onto the bare unit is the same as
precomposing the restriction to the open subscheme onto
`Stacks.EdgeCompat.preimageSectionsCompUnit (f.resLE V U e) ⊤`. -/
theorem openSubschemeBareUnitOf_eq_precomposeTail :
    (exactPostcomposeUnit (sectionsOverOpen X.toRingedSpace (U.ι ''ᵁ ⊤) ⋙
            resLETopRestrictScalars f V e) (baseTopRestrictScalars V) _
          (exactPostcomposeUnit (sectionsOverOpen X.toRingedSpace (U.ι ''ᵁ ⊤))
            (resLETopRestrictScalars f V e) _ (bareUnitImageTop (X := X) (U := U))) :
        (openSubschemeRestrictionOf X U ⋙
              preimageSections (f.resLE V U e).toLRSHom.toShHom ⊤ ⋙
                ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom).mapHomotopyCategory
            (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ _) =
      (Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso
              (Iso.refl (openSubschemeRestrictionOf X U ⋙
                (sectionsOverOpen (U : Scheme).toRingedSpace
                    ((opensMap (f.resLE V U e).toLRSHom.toShHom).obj ⊤) ⋙
                  preimageRestrictScalars (f.resLE V U e).toLRSHom.toShHom ⊤) ⋙
                ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom))
              (ComplexShape.up ℤ)).inv DerivedCategory.Qh ≫
            Functor.whiskerLeft ((openSubschemeRestrictionOf X U).mapHomotopyCategory
                (ComplexShape.up ℤ))
              (Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso
                    (Iso.refl ((sectionsOverOpen (U : Scheme).toRingedSpace
                          ((opensMap (f.resLE V U e).toLRSHom.toShHom).obj ⊤) ⋙
                        preimageRestrictScalars (f.resLE V U e).toLRSHom.toShHom ⊤) ⋙
                      ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom))
                    (ComplexShape.up ℤ)).inv DerivedCategory.Qh ≫
                Functor.whiskerLeft ((sectionsOverOpen (U : Scheme).toRingedSpace
                      ((opensMap (f.resLE V U e).toLRSHom.toShHom).obj ⊤) ⋙
                    preimageRestrictScalars
                      (f.resLE V U e).toLRSHom.toShHom ⊤).mapHomotopyCategory (ComplexShape.up ℤ))
                  (ModuleCat.restrictScalars
                    (Scheme.Opens.topIso V).inv.hom).mapDerivedCategoryFactorsh.inv)) ≫
        Functor.whiskerLeft ((openSubschemeRestrictionOf X U).mapHomotopyCategory
              (ComplexShape.up ℤ))
            (Functor.whiskerRight (exactPostcomposeUnit
                (sectionsOverOpen (U : Scheme).toRingedSpace
                  ((opensMap (f.resLE V U e).toLRSHom.toShHom).obj ⊤))
                (preimageRestrictScalars (f.resLE V U e).toLRSHom.toShHom ⊤)
                (derivedSectionsOverOpen (U : Scheme).toRingedSpace
                  ((opensMap (f.resLE V U e).toLRSHom.toShHom).obj ⊤))
                (derivedSectionsOverOpenUnit (U : Scheme).toRingedSpace
                  ((opensMap (f.resLE V U e).toLRSHom.toShHom).obj ⊤)))
              (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom).mapDerivedCategory) ≫
          Functor.whiskerRight (openSubschemeRestrictionOf X U).mapDerivedCategoryFactorsh.inv
            ((derivedSectionsOverOpen (U : Scheme).toRingedSpace
                  ((opensMap (f.resLE V U e).toLRSHom.toShHom).obj ⊤) ⋙
                (preimageRestrictScalars
                  (f.resLE V U e).toLRSHom.toShHom ⊤).mapDerivedCategory) ⋙
              (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom).mapDerivedCategory) :=
  (openSubschemeBareUnitOf_eq f V e).trans
    (exactPostcomposeUnit_precompose_comp (openSubschemeRestrictionOf X U)
        (sectionsOverOpen (U : Scheme).toRingedSpace
          ((opensMap (f.resLE V U e).toLRSHom.toShHom).obj ⊤))
        (preimageRestrictScalars (f.resLE V U e).toLRSHom.toShHom ⊤)
        (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom)
        (derivedSectionsOverOpen (U : Scheme).toRingedSpace
          ((opensMap (f.resLE V U e).toLRSHom.toShHom).obj ⊤))
        (derivedSectionsOverOpenUnit (U : Scheme).toRingedSpace
          ((opensMap (f.resLE V U e).toLRSHom.toShHom).obj ⊤)))

/-- `openSubschemeBareUnitOf_eq_precomposeTail` with the target read at the open subscheme's
spelling too, which is the one `…TopDegreeBaseChange.openSubschemeUnitOfNatTransUnit` carries.
Equal by definition; one pair of spellings is crossed per declaration, see this module's
implementation notes. -/
theorem openSubschemeBareUnitOf_eq_precomposeTail' :
    (exactPostcomposeUnit (sectionsOverOpen X.toRingedSpace (U.ι ''ᵁ ⊤) ⋙
            resLETopRestrictScalars f V e) (baseTopRestrictScalars V) _
          (exactPostcomposeUnit (sectionsOverOpen X.toRingedSpace (U.ι ''ᵁ ⊤))
            (resLETopRestrictScalars f V e) _ (bareUnitImageTop (X := X) (U := U))) :
        (openSubschemeRestrictionOf X U ⋙
              preimageSections (f.resLE V U e).toLRSHom.toShHom ⊤ ⋙
                ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom).mapHomotopyCategory
            (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ 
          DerivedCategory.Qh ⋙
            ((openSubschemeRestrictionOf X U).mapDerivedCategory ⋙
              (derivedSectionsOverOpen (U : Scheme).toRingedSpace
                  ((opensMap (f.resLE V U e).toLRSHom.toShHom).obj ⊤) ⋙
                (preimageRestrictScalars
                  (f.resLE V U e).toLRSHom.toShHom ⊤).mapDerivedCategory) ⋙
              (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom).mapDerivedCategory)) =
      (Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso
              (Iso.refl (openSubschemeRestrictionOf X U ⋙
                (sectionsOverOpen (U : Scheme).toRingedSpace
                    ((opensMap (f.resLE V U e).toLRSHom.toShHom).obj ⊤) ⋙
                  preimageRestrictScalars (f.resLE V U e).toLRSHom.toShHom ⊤) ⋙
                ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom))
              (ComplexShape.up ℤ)).inv DerivedCategory.Qh ≫
            Functor.whiskerLeft ((openSubschemeRestrictionOf X U).mapHomotopyCategory
                (ComplexShape.up ℤ))
              (Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso
                    (Iso.refl ((sectionsOverOpen (U : Scheme).toRingedSpace
                          ((opensMap (f.resLE V U e).toLRSHom.toShHom).obj ⊤) ⋙
                        preimageRestrictScalars (f.resLE V U e).toLRSHom.toShHom ⊤) ⋙
                      ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom))
                    (ComplexShape.up ℤ)).inv DerivedCategory.Qh ≫
                Functor.whiskerLeft ((sectionsOverOpen (U : Scheme).toRingedSpace
                      ((opensMap (f.resLE V U e).toLRSHom.toShHom).obj ⊤) ⋙
                    preimageRestrictScalars
                      (f.resLE V U e).toLRSHom.toShHom ⊤).mapHomotopyCategory (ComplexShape.up ℤ))
                  (ModuleCat.restrictScalars
                    (Scheme.Opens.topIso V).inv.hom).mapDerivedCategoryFactorsh.inv)) ≫
        Functor.whiskerLeft ((openSubschemeRestrictionOf X U).mapHomotopyCategory
              (ComplexShape.up ℤ))
            (Functor.whiskerRight (exactPostcomposeUnit
                (sectionsOverOpen (U : Scheme).toRingedSpace
                  ((opensMap (f.resLE V U e).toLRSHom.toShHom).obj ⊤))
                (preimageRestrictScalars (f.resLE V U e).toLRSHom.toShHom ⊤)
                (derivedSectionsOverOpen (U : Scheme).toRingedSpace
                  ((opensMap (f.resLE V U e).toLRSHom.toShHom).obj ⊤))
                (derivedSectionsOverOpenUnit (U : Scheme).toRingedSpace
                  ((opensMap (f.resLE V U e).toLRSHom.toShHom).obj ⊤)))
              (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom).mapDerivedCategory) ≫
          Functor.whiskerRight (openSubschemeRestrictionOf X U).mapDerivedCategoryFactorsh.inv
            ((derivedSectionsOverOpen (U : Scheme).toRingedSpace
                  ((opensMap (f.resLE V U e).toLRSHom.toShHom).obj ⊤) ⋙
                (preimageRestrictScalars
                  (f.resLE V U e).toLRSHom.toShHom ⊤).mapDerivedCategory) ⋙
              (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom).mapDerivedCategory) :=
  openSubschemeBareUnitOf_eq_precomposeTail f V e

/-- **The left side's unit composite read at the open subscheme's own spellings.** The three
factors of `…TopDegreeBaseChange.openSubschemeUnitOfNatTransUnit` after the degreewise crossing are
the two-step splitting of the two exact restrictions of scalars off the homotopy category, the unit
of `RΓ((f.resLE V U e)⁻¹⊤, -)` postcomposed with the scalars, and
`CategoryTheory.Functor.mapDerivedCategoryFactorsh` of the restriction inverted — which is the
shape `exactPostcomposeUnit_precompose_comp` produces. The equality holds by definition. -/
theorem openSubschemeUnitOfNatTransUnit_eq_precomposeTail :
    openSubschemeUnitOfNatTransUnit f V e (preimageSectionsOpenSubschemeLE f V e)
        (preimageSectionsCompUnit (f.resLE V U e).toLRSHom.toShHom ⊤) =
      Functor.whiskerRight (NatTrans.mapHomotopyCategory
          (show preimageSections f.toLRSHom.toShHom V ⟶
              openSubschemeRestrictionOf X U ⋙
                preimageSections (f.resLE V U e).toLRSHom.toShHom ⊤ ⋙
                  ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom from
            preimageSectionsOpenSubschemeLE f V e) (ComplexShape.up ℤ)) DerivedCategory.Qh ≫
        (Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso
                (Iso.refl (openSubschemeRestrictionOf X U ⋙
                  (sectionsOverOpen (U : Scheme).toRingedSpace
                      ((opensMap (f.resLE V U e).toLRSHom.toShHom).obj ⊤) ⋙
                    preimageRestrictScalars (f.resLE V U e).toLRSHom.toShHom ⊤) ⋙
                  ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom))
                (ComplexShape.up ℤ)).inv DerivedCategory.Qh ≫
              Functor.whiskerLeft ((openSubschemeRestrictionOf X U).mapHomotopyCategory
                  (ComplexShape.up ℤ))
                (Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso
                      (Iso.refl ((sectionsOverOpen (U : Scheme).toRingedSpace
                            ((opensMap (f.resLE V U e).toLRSHom.toShHom).obj ⊤) ⋙
                          preimageRestrictScalars (f.resLE V U e).toLRSHom.toShHom ⊤) ⋙
                        ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom))
                      (ComplexShape.up ℤ)).inv DerivedCategory.Qh ≫
                  Functor.whiskerLeft ((sectionsOverOpen (U : Scheme).toRingedSpace
                        ((opensMap (f.resLE V U e).toLRSHom.toShHom).obj ⊤) ⋙
                      preimageRestrictScalars
                        (f.resLE V U e).toLRSHom.toShHom ⊤).mapHomotopyCategory (ComplexShape.up ℤ))
                    (ModuleCat.restrictScalars
                      (Scheme.Opens.topIso V).inv.hom).mapDerivedCategoryFactorsh.inv)) ≫
          Functor.whiskerLeft ((openSubschemeRestrictionOf X U).mapHomotopyCategory
                (ComplexShape.up ℤ))
              (Functor.whiskerRight (exactPostcomposeUnit
                  (sectionsOverOpen (U : Scheme).toRingedSpace
                    ((opensMap (f.resLE V U e).toLRSHom.toShHom).obj ⊤))
                  (preimageRestrictScalars (f.resLE V U e).toLRSHom.toShHom ⊤)
                  (derivedSectionsOverOpen (U : Scheme).toRingedSpace
                    ((opensMap (f.resLE V U e).toLRSHom.toShHom).obj ⊤))
                  (derivedSectionsOverOpenUnit (U : Scheme).toRingedSpace
                    ((opensMap (f.resLE V U e).toLRSHom.toShHom).obj ⊤)))
                (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom).mapDerivedCategory) ≫
            Functor.whiskerRight (openSubschemeRestrictionOf X U).mapDerivedCategoryFactorsh.inv
              ((derivedSectionsOverOpen (U : Scheme).toRingedSpace
                    ((opensMap (f.resLE V U e).toLRSHom.toShHom).obj ⊤) ⋙
                  (preimageRestrictScalars
                    (f.resLE V U e).toLRSHom.toShHom ⊤).mapDerivedCategory) ⋙
                (ModuleCat.restrictScalars
                  (Scheme.Opens.topIso V).inv.hom).mapDerivedCategory) := rfl

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
