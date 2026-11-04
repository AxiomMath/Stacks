module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.LerayOpenSubschemeDerivedLE
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedFunctors.CompositeSingleModelCrossing
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.LocalizationIsomorphisms

/-!
# The crossing of the two models of `Rⁿ Γ(U, -)` under restriction to the open subscheme `U`

`Stacks.Cohomology.DerivedCompTransport.singleCompDerived_hom_app_comp_compRightDerivedNatIso_hom`
compares the two models of the classical right derived functor of a composite `r ⋙ w`, for `r`
exact, additive and preserving injective objects, with the two models at `w` alone read at `r(-)`.
This file instantiates it at the pair

> `r = restriction of sheaves of modules to an open subscheme U of X`,
> `w = sections over the whole of U`,

whose degreewise composite is sections over `U.ι ''ᵁ ⊤` on `X` — on the nose, no comparison being
involved. The outcome is that the crossing of the two models of `RⁿΓ(U, -)` computed on `X`
corresponds, under `Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso`, to the
crossing computed on the open subscheme `U` and read at the restricted module.

Nothing is assumed of `X`, of `U` or of the module: `r` preserves injective objects by
[Stacks, Tag 01E1], and the brick asks nothing of `w` beyond additivity.

## Main definitions

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedSectionsImageTopOf` — derived sections over
  `U.ι ''ᵁ ⊤` on `X`, with its target *declared* at the open subscheme's own global-sections ring.
  The ascription is not cosmetic, see the implementation notes.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedSectionsImageTopUnitOf` — its unit, with its
  source declared at the composite `r ⋙ w` rather than at sections over `U.ι ''ᵁ ⊤`.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.openSubschemeBareComparisonOf` — the comparison
  `RΓ(U.ι ''ᵁ ⊤, -) ⟶ D(restriction) ⋙ RΓ(U, ⊤, -)` of the two unbounded models, by
  `CategoryTheory.Functor.rightDerivedDesc`.

## Main results

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.openSubschemeBareComparisonOf_fac_app` — the
  factorization that characterizes it, which is **exactly the coherence `hθ` the brick asks for**:
  the degreewise crossing of the composite inverted under `Qh`, the unit of `RΓ(U, ⊤, -)` at the
  restriction, and `RΓ(U, ⊤, -)` of `CategoryTheory.Functor.mapDerivedCategoryFactorsh` inverted.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange`
  `.singleCompDerivedOpenSubscheme_hom_app_comp_compRightDerivedNatIso_hom` — **the brick at this
  pair.**
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange`
  `.singleCompDerivedOpenSubscheme_inv_app_restriction` — **the brick solved for the crossing on
  the open subscheme**, which is the form a chase of conclusion (c) of [Stacks, Tag 0EX3] meets it
  in: the crossing on `U` **inverted**, at the restricted module, is
  `compRightDerivedNatIso` inverted, the crossing on `X` inverted, and the two `Hⁿ` prefixes. It
  asks for no invertibility beyond that of the two crossings and of `compRightDerivedNatIso`, which
  are isomorphisms by construction; in particular it does **not** need
  `openSubschemeBareComparisonOf` to be invertible.

## Implementation notes

*Why the derived functor and its unit are re-declared with ascribed types.* The degreewise
composite `openSubschemeRestrictionOf X U ⋙ sectionsOverOpen (U : Scheme).toRingedSpace ⊤` **is**
`sectionsOverOpen X.toRingedSpace (U.ι ''ᵁ ⊤)`, by `rfl` — one of the four `rfl` identities
`LerayOpenSubschemeSections.lean` records — but the two present their value category as
`ModuleCat Γ(U, 𝒪_U)` and as `ModuleCat Γ(U.ι ''ᵁ ⊤, 𝒪_X)` respectively. Passing
`…DerivedSectionsLeray.derivedSectionsOverOpen X.toRingedSpace (U.ι ''ᵁ ⊤)` directly as the brick's
`Rw` is **refused**: `HasDerivedCategory` is then asked for at the first spelling and reported as
`failed to synthesize`, even with that very instance introduced by `haveI` in the local context
(both with and without the universe levels written out). Giving the functor a name whose
*declared* target carries the wanted spelling, and its unit likewise, removes the question — the
conversion runs once, in term mode at default transparency. This is the same cure
`openSubschemeRestrictionOf` itself is, and the third such spelling pair in this development.

*The `IsRightDerivedFunctor` instance is re-registered because the class is indexed by the unit
term.* `derivedSectionsImageTopUnitOf` is the existing unit and nothing else, but it is a different
term, so the existing instance does not apply to it; `inferInstanceAs` crosses them in one line. This
is the pattern `EdgeCompatPreimageRestrict.lean` records for
`…EdgeCompat.preimageSectionsCompUnitComp`.

*Why the brick is solved for its last factor and not for its first two.* A chase of conclusion (c)
of [Stacks, Tag 0EX3] meets the crossing on the open subscheme both positively — as factor (4) of
`Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward_inv_eq_lerayComparison` — and
inverted, as its factor (1). Solving the brick for its last factor **uninverted** would need
`openSubschemeBareComparisonOf` to be invertible, and that is **not available**: the instance
`((openSubschemeRestrictionOf X U).mapDerivedCategory ⋙ RΓ(U, ⊤, -)).IsRightDerivedFunctor`
`(openSubschemeBareUnitOf X U)` is not synthesisable, and the precomposition counterpart of
`Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.exactPostcomposeUnit` that would supply
it does not exist in the library (there is no `exactPrecompose`, `PrecomposeUnit` or
`isRightDerivedFunctor_precomp`; its one nontrivial input, that restriction to an open
carries a K-injective complex to a K-injective complex, *is* available, as
`Stacks.PseudoCoherence.isKInjective_restrictComplex` at ringed-space generality). Solving for the
**inverted** crossing needs none of that: `singleCompDerivedCompHomologyIsoRightDerived` and
`compRightDerivedNatIso` are isomorphisms by construction, so transposing the brick moves the two
`Hⁿ` prefixes to the right with no inverse of either taken. A chase that meets the crossing
positively transposes its own equation instead.

*No `@[stacks …]` attribute is placed.* [Stacks, Tag 01E1] carries its attribute where restriction
is proved to preserve injectives, and conclusion (c) of [Stacks, Tag 0EX3] is proved elsewhere, as
`…TopDegreeBaseChange.isIso_topDirectImageBaseChangeMap` (`BaseChangeTopDegreeConclusion.lean`), by
a route that does not use this file.

## References

* [Stacks Project, Tag 01E1](https://stacks.math.columbia.edu/tag/01E1)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.HigherDirectImage (moduleRestriction)
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (exists_quasiIso_isKInjective)
open Stacks.Cohomology.DerivedSectionsLeray
  (sectionsOverOpen derivedSectionsOverOpen derivedSectionsOverOpenUnit)

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

/-- **[Stacks, Tag 01E1] for the ascribed restriction to an open subscheme.** Restriction of
sheaves of modules to an open subscheme preserves injective objects. This is
`Stacks.Cohomology.HigherDirectImage.moduleRestriction_preservesInjectiveObjects` carried across
the ascription of `openSubschemeRestrictionOf`, which instance search does not unfold. -/
instance openSubschemeRestrictionOf_preservesInjectiveObjects (X : Scheme.{u}) (U : X.Opens) :
    (openSubschemeRestrictionOf X U).PreservesInjectiveObjects :=
  inferInstanceAs ((moduleRestriction X.toRingedSpace U).PreservesInjectiveObjects)

variable (X : Scheme.{u}) (U : X.Opens)

/-! ### The derived functor of the degreewise composite, at the open subscheme's own ring -/

/-- **Derived sections over `U.ι ''ᵁ ⊤` on `X`, with the value category declared as modules over
`Γ(U, 𝒪_U)`.** This is `Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpen`
`X.toRingedSpace (U.ι ''ᵁ ⊤)` and nothing else; the ascription is forced by instance synthesis, see
this module's implementation notes. -/
def derivedSectionsImageTopOf :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) ⥤
      DerivedCategory (ModuleCat.{u}
        ((structureSheafRing (U : Scheme).toRingedSpace).obj.obj (op ⊤))) :=
  derivedSectionsOverOpen X.toRingedSpace (U.ι ''ᵁ ⊤)

/-- **The unit of `derivedSectionsImageTopOf`, with its source declared at the composite.** This is
`Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpenUnit X.toRingedSpace (U.ι ''ᵁ ⊤)`
read at the spelling `openSubschemeRestrictionOf X U ⋙ sectionsOverOpen (U : Scheme) ⊤` of the
degreewise functor, the two being equal by `rfl`. -/
def derivedSectionsImageTopUnitOf :
    (openSubschemeRestrictionOf X U ⋙
          sectionsOverOpen (U : Scheme).toRingedSpace ⊤).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ derivedSectionsImageTopOf X U :=
  derivedSectionsOverOpenUnit X.toRingedSpace (U.ι ''ᵁ ⊤)

/-- `derivedSectionsImageTopOf` is a right derived functor of the degreewise composite at
`derivedSectionsImageTopUnitOf`. `CategoryTheory.Functor.IsRightDerivedFunctor` is indexed by the
unit term, so the existing instance does not apply to the re-declared unit; this crosses them. -/
instance isRightDerivedFunctor_derivedSectionsImageTopUnitOf :
    (derivedSectionsImageTopOf X U).IsRightDerivedFunctor (derivedSectionsImageTopUnitOf X U)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
        (ComplexShape.up ℤ)) :=
  inferInstanceAs ((derivedSectionsOverOpen X.toRingedSpace (U.ι ''ᵁ ⊤)).IsRightDerivedFunctor
    (derivedSectionsOverOpenUnit X.toRingedSpace (U.ι ''ᵁ ⊤)) _)

/-! ### The comparison of the two unbounded models -/

/-- **The transformation the universal property consumes.** The degreewise crossing of the
composite — `CategoryTheory.Functor.mapHomotopyCategoryCompIso` at the identity, inverted and
localized — then the unit of `RΓ(U, ⊤, -)` at the restriction on the homotopy category, then
`RΓ(U, ⊤, -)` applied to `CategoryTheory.Functor.mapDerivedCategoryFactorsh` inverted.

These are exactly, and in this order, the three factors of the coherence the brick
`Stacks.Cohomology.DerivedCompTransport.singleCompDerived_hom_app_comp_compRightDerivedNatIso_hom`
asks of its comparison, which is why `openSubschemeBareComparisonOf_fac_app` discharges it with no
work. -/
def openSubschemeBareUnitOf :
    (openSubschemeRestrictionOf X U ⋙
          sectionsOverOpen (U : Scheme).toRingedSpace ⊤).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙
        ((openSubschemeRestrictionOf X U).mapDerivedCategory ⋙
          derivedSectionsOverOpen (U : Scheme).toRingedSpace ⊤) :=
  Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso
      (Iso.refl (openSubschemeRestrictionOf X U ⋙
        sectionsOverOpen (U : Scheme).toRingedSpace ⊤)) (ComplexShape.up ℤ)).inv
      DerivedCategory.Qh ≫
    Functor.whiskerLeft ((openSubschemeRestrictionOf X U).mapHomotopyCategory (ComplexShape.up ℤ))
      (derivedSectionsOverOpenUnit (U : Scheme).toRingedSpace ⊤) ≫
    Functor.whiskerRight (openSubschemeRestrictionOf X U).mapDerivedCategoryFactorsh.inv
      (derivedSectionsOverOpen (U : Scheme).toRingedSpace ⊤)

/-- **The comparison of the two unbounded models of `RΓ(U, -)`**: derived sections over
`U.ι ''ᵁ ⊤` on `X` into derived restriction to the open subscheme `U` followed by derived global
sections of `U`, induced by `openSubschemeBareUnitOf` through the universal property of the total
right derived functor of the degreewise composite. By `openSubschemeBareComparisonOf_fac_app` its
composite with the unit is `openSubschemeBareUnitOf`, and that equation determines it. -/
def openSubschemeBareComparisonOf :
    derivedSectionsImageTopOf X U ⟶
      (openSubschemeRestrictionOf X U).mapDerivedCategory ⋙
        derivedSectionsOverOpen (U : Scheme).toRingedSpace ⊤ :=
  (derivedSectionsImageTopOf X U).rightDerivedDesc (derivedSectionsImageTopUnitOf X U)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (ComplexShape.up ℤ)) _ (openSubschemeBareUnitOf X U)

/-- **The equation characterizing `openSubschemeBareComparisonOf`, pointwise — and the coherence
the brick asks for.** Composing the comparison with the unit of derived sections over `U.ι ''ᵁ ⊤`
recovers the three factors of `openSubschemeBareUnitOf`, written out. -/
theorem openSubschemeBareComparisonOf_fac_app
    (L : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (ComplexShape.up ℤ)) :
    (derivedSectionsImageTopUnitOf X U).app L ≫
        (openSubschemeBareComparisonOf X U).app (DerivedCategory.Qh.obj L) =
      DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
            (Iso.refl (openSubschemeRestrictionOf X U ⋙
              sectionsOverOpen (U : Scheme).toRingedSpace ⊤))
            (ComplexShape.up ℤ)).inv.app L) ≫
        (derivedSectionsOverOpenUnit (U : Scheme).toRingedSpace ⊤).app
            (((openSubschemeRestrictionOf X U).mapHomotopyCategory (ComplexShape.up ℤ)).obj L) ≫
          (derivedSectionsOverOpen (U : Scheme).toRingedSpace ⊤).map
            ((openSubschemeRestrictionOf X U).mapDerivedCategoryFactorsh.inv.app L) :=
  (derivedSectionsImageTopOf X U).rightDerived_fac_app (derivedSectionsImageTopUnitOf X U)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (ComplexShape.up ℤ)) _ (openSubschemeBareUnitOf X U) L

/-! ### The crossing -/

/-- **The crossing of the two models of `RⁿΓ(U, -)` is compatible with restriction to the open
subscheme `U`.** For a scheme `X`, an open `U ⊆ X`, a degree `n` and a sheaf of modules `M` on `X`,

> the crossing of the two models of `Rⁿ Γ(U.ι ''ᵁ ⊤, -)` on `X`, followed by
> `Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso` for the pair
> (restriction to `U`, global sections of `U`), is the degree-`n` cohomology of
> `openSubschemeBareComparisonOf` at `M[0]`, then of derived global sections of `U` applied to
> `CategoryTheory.Functor.mapDerivedCategorySingleFunctor`, then the crossing of the two models of
> `Rⁿ Γ(U, -)` on the open subscheme, read at the restriction of `M`.

This is
`Stacks.Cohomology.DerivedCompTransport.singleCompDerived_hom_app_comp_compRightDerivedNatIso_hom`
at the pair, with `openSubschemeBareComparisonOf_fac_app` as its coherence. **Nothing is assumed of
`X`, of `U`, of `M` or of `n`**; in particular no affineness, no acyclicity, no boundedness and no
quasi-coherence occur, and the K-injective resolutions on both sides are the unconditional
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.exists_quasiIso_isKInjective`. -/
theorem singleCompDerivedOpenSubscheme_hom_app_comp_compRightDerivedNatIso_hom (n : ℕ)
    (M : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) :
    (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
            (openSubschemeRestrictionOf X U ⋙ sectionsOverOpen (U : Scheme).toRingedSpace ⊤)
            (derivedSectionsImageTopOf X U) (derivedSectionsImageTopUnitOf X U)
            (exists_quasiIso_isKInjective X.toRingedSpace) n).hom.app M ≫
        (Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso
          (openSubschemeRestrictionOf X U)
          (sectionsOverOpen (U : Scheme).toRingedSpace ⊤) n).hom.app M =
      (DerivedCategory.homologyFunctor
              (ModuleCat.{u}
                ((structureSheafRing (U : Scheme).toRingedSpace).obj.obj (op ⊤))) (n : ℤ)).map
            ((openSubschemeBareComparisonOf X U).app
              ((DerivedCategory.singleFunctor
                (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj M)) ≫
          (DerivedCategory.homologyFunctor
                (ModuleCat.{u}
                  ((structureSheafRing (U : Scheme).toRingedSpace).obj.obj (op ⊤))) (n : ℤ)).map
              ((derivedSectionsOverOpen (U : Scheme).toRingedSpace ⊤).map
                (((openSubschemeRestrictionOf X U).mapDerivedCategorySingleFunctor 0).hom.app M)) ≫
            (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
              (sectionsOverOpen (U : Scheme).toRingedSpace ⊤)
              (derivedSectionsOverOpen (U : Scheme).toRingedSpace ⊤)
              (derivedSectionsOverOpenUnit (U : Scheme).toRingedSpace ⊤)
              (exists_quasiIso_isKInjective (U : Scheme).toRingedSpace) n).hom.app
              ((openSubschemeRestrictionOf X U).obj M) :=
  Stacks.Cohomology.DerivedCompTransport.singleCompDerived_hom_app_comp_compRightDerivedNatIso_hom
    (openSubschemeRestrictionOf X U) (sectionsOverOpen (U : Scheme).toRingedSpace ⊤)
    (derivedSectionsImageTopOf X U) (derivedSectionsImageTopUnitOf X U)
    (derivedSectionsOverOpen (U : Scheme).toRingedSpace ⊤)
    (derivedSectionsOverOpenUnit (U : Scheme).toRingedSpace ⊤)
    (openSubschemeBareComparisonOf X U) (exists_quasiIso_isKInjective X.toRingedSpace)
    (exists_quasiIso_isKInjective (U : Scheme).toRingedSpace)
    (openSubschemeBareComparisonOf_fac_app X U) n M

/-- **Transposing a three-fold identity at the two ends that are isomorphisms.** From
`i ≫ j = Xm ≫ Ym ≫ k` with `i`, `j` and `k` isomorphisms, the inverse of `k` is `j` and `i`
inverted followed by `Xm` and `Ym`; nothing is assumed of `Xm` or of `Ym`, which is the whole point
— see this module's implementation notes. Stated at variables of an abstract category so that its
application checks against the goal at default transparency. -/
private theorem inv_eq_of_hom_comp_eq {C : Type*} [Category C] {S₀ S₁ S₂ P T : C}
    (i : S₀ ≅ P) (j : P ≅ T) (k : S₂ ≅ T) (Xm : S₀ ⟶ S₁) (Ym : S₁ ⟶ S₂)
    (h : i.hom ≫ j.hom = Xm ≫ Ym ≫ k.hom) :
    k.inv = j.inv ≫ i.inv ≫ Xm ≫ Ym := by
  symm
  calc j.inv ≫ i.inv ≫ Xm ≫ Ym
      = j.inv ≫ i.inv ≫ (Xm ≫ Ym ≫ k.hom) ≫ k.inv := by simp
    _ = j.inv ≫ i.inv ≫ (i.hom ≫ j.hom) ≫ k.inv := by rw [h]
    _ = k.inv := by simp

/-- **The brick solved for the crossing on the open subscheme, inverted.** For a scheme `X`, an
open `U ⊆ X`, a degree `n` and a sheaf of modules `M` on `X`,

> the crossing of the two models of `Rⁿ Γ(U, -)` on the open subscheme, **inverted**, read at the
> restriction of `M`, is `Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso` inverted,
> then the crossing of the two models of `Rⁿ Γ(U.ι ''ᵁ ⊤, -)` on `X` inverted, then the degree-`n`
> cohomology of `openSubschemeBareComparisonOf` at `M[0]`, then of derived global sections of `U`
> applied to `CategoryTheory.Functor.mapDerivedCategorySingleFunctor`.

This is `singleCompDerivedOpenSubscheme_hom_app_comp_compRightDerivedNatIso_hom` transposed at its
three isomorphism factors. **Nothing is assumed of `X`, of `U`, of `M` or of `n`**, and in
particular nothing about `openSubschemeBareComparisonOf` — whose invertibility is not available
and is not needed; see the implementation notes. -/
theorem singleCompDerivedOpenSubscheme_inv_app_restriction (n : ℕ)
    (M : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) :
    (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
          (sectionsOverOpen (U : Scheme).toRingedSpace ⊤)
          (derivedSectionsOverOpen (U : Scheme).toRingedSpace ⊤)
          (derivedSectionsOverOpenUnit (U : Scheme).toRingedSpace ⊤)
          (exists_quasiIso_isKInjective (U : Scheme).toRingedSpace) n).inv.app
        ((openSubschemeRestrictionOf X U).obj M) =
      (Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso
            (openSubschemeRestrictionOf X U)
            (sectionsOverOpen (U : Scheme).toRingedSpace ⊤) n).inv.app M ≫
        (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
              (openSubschemeRestrictionOf X U ⋙ sectionsOverOpen (U : Scheme).toRingedSpace ⊤)
              (derivedSectionsImageTopOf X U) (derivedSectionsImageTopUnitOf X U)
              (exists_quasiIso_isKInjective X.toRingedSpace) n).inv.app M ≫
          (DerivedCategory.homologyFunctor (ModuleCat.{u}
                ((structureSheafRing (U : Scheme).toRingedSpace).obj.obj (op ⊤))) (n : ℤ)).map
              ((openSubschemeBareComparisonOf X U).app
                ((DerivedCategory.singleFunctor
                  (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj M)) ≫
            (DerivedCategory.homologyFunctor (ModuleCat.{u}
                  ((structureSheafRing (U : Scheme).toRingedSpace).obj.obj (op ⊤))) (n : ℤ)).map
                ((derivedSectionsOverOpen (U : Scheme).toRingedSpace ⊤).map
                  (((openSubschemeRestrictionOf X U).mapDerivedCategorySingleFunctor 0).hom.app
                    M)) :=
  inv_eq_of_hom_comp_eq
    ((Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
      (openSubschemeRestrictionOf X U ⋙ sectionsOverOpen (U : Scheme).toRingedSpace ⊤)
      (derivedSectionsImageTopOf X U) (derivedSectionsImageTopUnitOf X U)
      (exists_quasiIso_isKInjective X.toRingedSpace) n).app M)
    ((Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso
      (openSubschemeRestrictionOf X U)
      (sectionsOverOpen (U : Scheme).toRingedSpace ⊤) n).app M)
    ((Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
      (sectionsOverOpen (U : Scheme).toRingedSpace ⊤)
      (derivedSectionsOverOpen (U : Scheme).toRingedSpace ⊤)
      (derivedSectionsOverOpenUnit (U : Scheme).toRingedSpace ⊤)
      (exists_quasiIso_isKInjective (U : Scheme).toRingedSpace) n).app
        ((openSubschemeRestrictionOf X U).obj M))
    _ _
    (singleCompDerivedOpenSubscheme_hom_app_comp_compRightDerivedNatIso_hom X U n M)

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
