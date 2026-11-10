module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.OpenSubschemeModelCompositionGlue

/-!
# The gluing solved as far as it can be solved for the bare comparison

`…TopDegreeBaseChange.openSubschemeSectionsComparisonLE_eq_modelComposition`
(`OpenSubschemeModelCompositionGlue.lean`) reads

> `openSubschemeSectionsComparisonLE f V e`, then the upstairs model comparison whiskered, equals
> `C₁ ≫ C₂ ≫ C₃ ≫ C₄ ≫ D`,

where `C₁` is `Stacks.EdgeCompat.preimageSectionsModelComparison f V`, `C₂` is the `α` layer
`Stacks.EdgeCompat.preimageSectionsRestrictSourceModelComparison f V e`, `C₃` is
`…TopDegreeBaseChange.derivedSectionsImageTopIso` inverted and whiskered, `C₄` is
`…TopDegreeBaseChange.derivedScalarsReconciliation`, and `D` is
`…TopDegreeBaseChange.openSubschemeBareComparisonOf` whiskered by the two scalars layers — the
factor brick (i) of the 2b(B) match of [Stacks, Tag 0EX3] (c) carries, through
`…TopDegreeBaseChange.singleCompDerivedOpenSubscheme_inv_app_restriction` and the join
`…TopDegreeBaseChange.factorFourFive_comp_openSubschemeCrossing_eq`.

**The gluing cannot be solved for `D`, and this file identifies which factor stops it.** `C₃`
and `C₄` are isomorphisms by construction, and `C₁` is one unconditionally — this file proves
that. `C₂` is **not**: it is `CategoryTheory.Functor.rightDerivedNatTrans` along the
degreewise `Stacks.EdgeCompat.preimageSectionsRestrictSource f V e`, the restriction of sections
from `f⁻¹V` down to `U`, which at a proper `U < f⁻¹V` is not invertible — the same phenomenon as for
`…TopDegreeBaseChange.preimageSectionsOpenSubschemeLE` — and no `IsIso`
instance for it is synthesisable. At the instance the 2b(B) match meets, `U` **is**
proper: the gluing enters there at `(f, V, U, e) := (h', f'⁻¹V, f''⁻¹W, hle)`, whose
`f''⁻¹W ⊊ (h')⁻¹(f'⁻¹V)` is what makes the transport of the match a morphism and not an
isomorphism.

So what is available is the gluing solved for `C₂ ≫ C₃ ≫ C₄ ≫ D`, which is what this file proves.
A chase that wants the bare comparison alone must carry `C₂` with it, in the forward direction.

## Main results

* `Stacks.EdgeCompat.isIso_preimageSectionsModelComparison` — the comparison of the two models of
  `RΓ(f⁻¹V, -) ⋙ res_{f^♯}` is an isomorphism, with **no hypothesis at all**. It is
  `CategoryTheory.Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc` at the registered
  `Stacks.EdgeCompat.isRightDerivedFunctor_preimageSectionsCompUnitComp`; the comparison is a
  `CategoryTheory.Functor.rightDerivedDesc` between two right derived functors of the **same**
  degreewise functor, which is why nothing is assumed.
* `…TopDegreeBaseChange.alphaLayer_comp_openSubschemeBareComparisonOf_eq` — **the gluing solved
  for its last four factors.** The `α` layer, then the crossing of the two sections functors
  inverted, then the reconciliation of the three spellings of the one ring map, then the bare
  comparison whiskered by the two scalars layers, is the total model comparison **inverted**, then
  `…TopDegreeBaseChange.openSubschemeSectionsComparisonLE f V e`, then the upstairs model
  comparison whiskered. Nothing is assumed of `f`, of `V`, of `U` or of the module.

## Implementation notes

*Only one inverse is taken, and it is the one that exists.* The transposition is
`CategoryTheory.IsIso.inv_comp_eq` at `C₁` alone; `C₂`, `C₃`, `C₄` and `D` are left untouched and
in the order the gluing writes them, so no inverse of the bare comparison occurs — its
invertibility is not available (see `OpenSubschemeSingleModelCrossing.lean`) and is not needed
anywhere.

*The statement is written with the gluing's own right-hand side first*, which is the spelling its
four factors already live at, so the one elaboration of the equation makes no definitional
crossing and the proof is a single transposition.

*No `@[stacks …]` attribute is placed.* Conclusion (c) of [Stacks, Tag 0EX3] is proved elsewhere,
as `…TopDegreeBaseChange.isIso_topDirectImageBaseChangeMap` (`BaseChangeTopDegreeConclusion.lean`),
by a route that does not use this file.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction (opensMap)
open Stacks.Cohomology.DerivedSectionsLeray (sectionsOverOpen derivedPreimageSections)

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.EdgeCompat

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) (V : Opens Y.carrier)

/-- **The comparison of the two models of `RΓ(f⁻¹V, -)` over `Γ(V, 𝒪_Y)` is an isomorphism**, with
no hypothesis on `f`, on `V` or on anything else. Both
`Stacks.Cohomology.DerivedSectionsLeray.derivedPreimageSections f V` and
`RΓ(f⁻¹V, -) ⋙ res_{f^♯}` are right derived functors of the same degreewise functor
`…DerivedSectionsLeray.preimageSections f V`, the second by
`isRightDerivedFunctor_preimageSectionsCompUnitComp`, and
`preimageSectionsModelComparison` is the `CategoryTheory.Functor.rightDerivedDesc` between them;
so this is `CategoryTheory.Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc`.

It is registered as an instance because `inferInstance` does not otherwise find `IsIso`
of `preimageSectionsModelComparison`. -/
instance isIso_preimageSectionsModelComparison :
    IsIso (preimageSectionsModelComparison f V) :=
  (Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc _ _ _ _ _).mp inferInstance

end Stacks.EdgeCompat

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

open Stacks.EdgeCompat (preimageSectionsModelComparison
  preimageSectionsRestrictSourceModelComparison)

variable {X S : Scheme.{u}} (f : X ⟶ S) (V : S.Opens) {U : X.Opens} (e : U ≤ f ⁻¹ᵁ V)

/-- **The gluing solved for its last four factors.** For a morphism `f : X ⟶ S` of schemes, an
open `V ⊆ S` and an open `U ≤ f⁻¹V` of `X`,

> the `α` layer `Stacks.EdgeCompat.preimageSectionsRestrictSourceModelComparison f V e`, then
> `…TopDegreeBaseChange.derivedSectionsImageTopIso` inverted and whiskered by the downstairs
> scalars, then `…TopDegreeBaseChange.derivedScalarsReconciliation`, then
> `…TopDegreeBaseChange.openSubschemeBareComparisonOf` whiskered by the two scalars layers, is
> `Stacks.EdgeCompat.preimageSectionsModelComparison f V` **inverted**, then
> `…TopDegreeBaseChange.openSubschemeSectionsComparisonLE f V e`, then
> `Stacks.EdgeCompat.preimageSectionsModelComparison (f.resLE V U e) ⊤` whiskered by the derived
> restriction to the open subscheme and the derived restriction of scalars along
> `AlgebraicGeometry.Scheme.Opens.topIso` at `V`.

This is `…TopDegreeBaseChange.openSubschemeSectionsComparisonLE_eq_modelComposition` transposed at
the one factor known to be invertible, `isIso_preimageSectionsModelComparison`. The `α` layer is
**not** moved: it is `CategoryTheory.Functor.rightDerivedNatTrans` along the restriction of
sections from `f⁻¹V` to `U`, which at a proper `U` is not invertible and has no `IsIso` instance,
and the match of [Stacks, Tag 0EX3] (c) meets the gluing at a proper `U`. No inverse
of `openSubschemeBareComparisonOf` is taken.

**Nothing is assumed** of `f`, of `V`, of `U` or of the module. -/
theorem alphaLayer_comp_openSubschemeBareComparisonOf_eq :
    preimageSectionsRestrictSourceModelComparison f.toLRSHom.toShHom V e ≫
        Functor.whiskerRight (derivedSectionsImageTopIso X U).inv
            (restrictSourceScalars f V e).mapDerivedCategory ≫
          (derivedScalarsReconciliation f V e).hom ≫
            Functor.whiskerRight (openSubschemeBareComparisonOf X U)
              ((resLETopRestrictScalars f V e).mapDerivedCategory ⋙
                (baseTopRestrictScalars V).mapDerivedCategory) =
      CategoryTheory.inv (preimageSectionsModelComparison f.toLRSHom.toShHom V) ≫
        openSubschemeSectionsComparisonLE f V e ≫
          Functor.whiskerLeft (openSubschemeRestrictionOf X U).mapDerivedCategory
            (Functor.whiskerRight
              (preimageSectionsModelComparison (f.resLE V U e).toLRSHom.toShHom ⊤)
              (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom).mapDerivedCategory) :=
  ((IsIso.inv_comp_eq _).mpr
    (openSubschemeSectionsComparisonLE_eq_modelComposition f V e)).symm

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
