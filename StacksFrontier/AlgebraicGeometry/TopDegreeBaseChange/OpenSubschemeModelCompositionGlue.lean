module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.OpenSubschemeModelComposition

/-!
# The open-subscheme model composition, glued

The tail of conclusion (c) of [Stacks, Tag 0EX3] needs the geometric comparison
`…TopDegreeBaseChange.openSubschemeSectionsComparisonLE` expressed through the **bare-pair**
comparison `…TopDegreeBaseChange.openSubschemeBareComparisonOf`, the one
`…TopDegreeBaseChange.singleCompDerivedOpenSubscheme_hom_app_comp_compRightDerivedNatIso_hom`
— brick (i) of the 2b(B) match — is stated at. `OpenSubschemeModelCompositionUnit.lean` computes
the two sides' composites with the derivation unit, and `OpenSubschemeModelComposition.lean` lands
the four pieces of the coherence identity between them. **This file composes those pieces and
performs the gluing.**

Nothing is assumed of `f`, of `V`, of `U` or of the module anywhere in this file.

## Main results

* `…TopDegreeBaseChange.modelComposition_coherence` — **the coherence identity**: the left side's
  unit composite, `…TopDegreeBaseChange.openSubschemeUnitOfNatTransUnit` at the degreewise crossing
  and at `Stacks.EdgeCompat.preimageSectionsCompUnit` for the restricted morphism over `⊤`, is the
  three degreewise prefixes followed by the two-fold
  `Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.exactPostcomposeUnit` on
  `…TopDegreeBaseChange.openSubschemeBareUnitOf` — which is the right side's unit composite, as
  `…TopDegreeBaseChange.modelComposition_unit` computes it.
* `…TopDegreeBaseChange.openSubschemeSectionsComparisonLE_eq_modelComposition` — **the gluing.**
  The geometric comparison, followed by the upstairs model comparison whiskered by the derived
  restriction and the derived restriction of scalars, is the three model comparisons, the crossing
  of the two sections functors inverted, the derived reconciliation of the two readings of the
  scalars, and the bare comparison whiskered by the two scalars layers.

## Implementation notes

*The side order of the coherence identity is what makes it fit, and the ledger of
`BaseChangeSectionsTail.lean` predicted otherwise.* The two sides spell the same functors
differently at five places, and crossing one such pair is definitional but costs a large part of a
declaration's 200,000 heartbeats. Each of the four pieces of `OpenSubschemeModelComposition.lean`
pays exactly one, and one might expect composing them to need a sixth crossing in the composing
declaration, which would be over budget.

It does **not**. In `theorem _ : A = B` Lean elaborates `A`, then elaborates `B`
against `A`'s type, so the equation's type index is `A`'s — and with the **open-subscheme** side
written first, that index is the spelling all three input lemmas
(`…openSubschemeUnitOfNatTransUnit_eq_precomposeTail`,
`…whiskerRight_mapHomotopyCategory_preimageSectionsOpenSubschemeLE` and
`…openSubschemeBareUnitOf_eq_precomposeTail'`) already live at. The one crossing the statement
makes is then paid once, during its elaboration, and the proof — `glue_prefix3_tail`, the
reassociation at variables this subtree uses throughout — crosses nothing further. The four
arrangements the ledger records all put the crossing in the statement *and* again in the proof,
which is why the `exact` timed out at `isDefEq` with the budget already spent. No ascribed `def`
for restriction of scalars along `(f.resLE V U e)^♯` was needed, and
`…TopDegreeBaseChange.modelComposition_unit` was not restated.

*Why the gluing is then free.* Both sides are transformations out of the total right derived
functor `Stacks.Cohomology.DerivedSectionsLeray.derivedPreimageSections f V`, so
`…DerivedSectionsLeray.lerayComparison_ext` reduces it to the identity of the two unit composites,
and that is the two unit computations with the coherence identity between them — three
`Eq.trans` and nothing else.

*No `@[stacks …]` attribute is placed.* Conclusion (c) of [Stacks, Tag 0EX3] is proved elsewhere,
as `…TopDegreeBaseChange.isIso_topDirectImageBaseChangeMap` (`BaseChangeTopDegreeConclusion.lean`),
by a route that does not use this file.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction (opensMap)
open Stacks.Cohomology.HypercohomologyEdge.HomologyComparison (exactPostcomposeUnit)
open Stacks.Cohomology.DerivedSectionsLeray
  (sectionsOverOpen derivedPreimageSections lerayComparison_ext)
open Stacks.EdgeCompat (preimageSectionsCompUnit preimageSectionsRestrictSource
  preimageSectionsModelComparison preimageSectionsRestrictSourceModelComparison)

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

variable {X S : Scheme.{u}} (f : X ⟶ S) (V : S.Opens) {U : X.Opens} (e : U ≤ f ⁻¹ᵁ V)

/-- **A prefix split into three and a tail replaced, at variables**, where the reassociation is
free and no definitional crossing is made: the three hypotheses' types fix every category and every
object, so the application is syntactic. -/
private theorem glue_prefix3_tail {C : Type*} [Category* C] {A B₁ B₂ B D : C}
    {z : A ⟶ D} {x : A ⟶ B} {y y' : B ⟶ D}
    {p : A ⟶ B₁} {q : B₁ ⟶ B₂} {s : B₂ ⟶ B}
    (hz : z = x ≫ y) (hx : x = p ≫ q ≫ s) (hy : y' = y) :
    z = p ≫ q ≫ s ≫ y' := by
  rw [hz, hx, hy]
  simp only [Category.assoc]

/-- **The coherence identity of the open-subscheme model composition.** The unit composite of the
geometric side — `…TopDegreeBaseChange.openSubschemeUnitOfNatTransUnit` at the degreewise crossing
and at `Stacks.EdgeCompat.preimageSectionsCompUnit` for `f.resLE V U e` over `⊤`, which is what
`…TopDegreeBaseChange.openSubschemeSectionsComparisonLE_comp_upstairsModel_unit` computes — is the
three degreewise prefixes of `…TopDegreeBaseChange.modelComposition_unit` followed by the two-fold
`Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.exactPostcomposeUnit` on
`…TopDegreeBaseChange.openSubschemeBareUnitOf`.

The four pieces of `OpenSubschemeModelComposition.lean` composed:
`…openSubschemeUnitOfNatTransUnit_eq_precomposeTail` splits the tail off,
`…whiskerRight_mapHomotopyCategory_preimageSectionsOpenSubschemeLE` splits the prefix into three,
and `…openSubschemeBareUnitOf_eq_precomposeTail'` identifies the tail with the two-fold unit.
Nothing is assumed of `f`, of `V`, of `U` or of the module. -/
theorem modelComposition_coherence :
    openSubschemeUnitOfNatTransUnit f V e (preimageSectionsOpenSubschemeLE f V e)
        (preimageSectionsCompUnit (f.resLE V U e).toLRSHom.toShHom ⊤) =
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
                (resLETopRestrictScalars f V e) _ (bareUnitImageTop (X := X) (U := U))) :=
  glue_prefix3_tail (openSubschemeUnitOfNatTransUnit_eq_precomposeTail f V e)
    (whiskerRight_mapHomotopyCategory_preimageSectionsOpenSubschemeLE f V e)
    (openSubschemeBareUnitOf_eq_precomposeTail' f V e)

/-- **The gluing: the geometric comparison read through the bare-pair comparison.** For a morphism
`f : X ⟶ S` of schemes, an open `V ⊆ S` and an open `U ≤ f⁻¹V` of `X`,

> `…TopDegreeBaseChange.openSubschemeSectionsComparisonLE f V e`, then
> `Stacks.EdgeCompat.preimageSectionsModelComparison (f.resLE V U e) ⊤` whiskered by the derived
> restriction to the open subscheme on the left and by the derived restriction of scalars along
> `AlgebraicGeometry.Scheme.Opens.topIso` at `V` on the right, equals
> `Stacks.EdgeCompat.preimageSectionsModelComparison f V`, then
> `Stacks.EdgeCompat.preimageSectionsRestrictSourceModelComparison f V e`, then
> `…TopDegreeBaseChange.derivedSectionsImageTopIso` inverted and whiskered by the downstairs
> scalars, then `…TopDegreeBaseChange.derivedScalarsReconciliation`, then
> `…TopDegreeBaseChange.openSubschemeBareComparisonOf` whiskered by the two scalars layers.

Both sides come out of the total right derived functor
`Stacks.Cohomology.DerivedSectionsLeray.derivedPreimageSections f V`, so
`…DerivedSectionsLeray.lerayComparison_ext` reduces the identity to the two unit composites, which
are `…TopDegreeBaseChange.openSubschemeSectionsComparisonLE_comp_upstairsModel_unit` and
`…TopDegreeBaseChange.modelComposition_unit` with `modelComposition_coherence` between them.

**Nothing is assumed of `f`, of `V`, of `U` or of the module**; no affineness, no acyclicity, no
boundedness and no quasi-coherence occurs. -/
theorem openSubschemeSectionsComparisonLE_eq_modelComposition :
    openSubschemeSectionsComparisonLE f V e ≫
        Functor.whiskerLeft (openSubschemeRestrictionOf X U).mapDerivedCategory
          (Functor.whiskerRight
            (preimageSectionsModelComparison (f.resLE V U e).toLRSHom.toShHom ⊤)
            (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom).mapDerivedCategory) =
      preimageSectionsModelComparison f.toLRSHom.toShHom V ≫
        preimageSectionsRestrictSourceModelComparison f.toLRSHom.toShHom V e ≫
          Functor.whiskerRight (derivedSectionsImageTopIso X U).inv
              (restrictSourceScalars f V e).mapDerivedCategory ≫
            (derivedScalarsReconciliation f V e).hom ≫
              Functor.whiskerRight (openSubschemeBareComparisonOf X U)
                ((resLETopRestrictScalars f V e).mapDerivedCategory ⋙
                  (baseTopRestrictScalars V).mapDerivedCategory) :=
  lerayComparison_ext f.toLRSHom.toShHom V _ _
    ((openSubschemeSectionsComparisonLE_comp_upstairsModel_unit f V e).trans
      ((modelComposition_coherence f V e).trans (modelComposition_unit f V e).symm))

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
