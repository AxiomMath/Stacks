module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.OpenSubschemeModelCrossingTransport
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.PreimageSectionsCollapseMirrorScalars

/-!
# Factors (4) and (5) of [Stacks, Tag 089W] joined to brick (i) of the 2b(B) match

`Stacks.EdgeCompat.singleCompDerivedPreimageSectionsComp_hom_app_comp`
`_restrictScalarsRightDerivedIso_inv` (`PreimageSectionsCollapseMirrorScalars.lean`) composes the
last two factors of
`Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward_inv_eq_lerayComparison` — the `ψ`
side's reading of [Stacks, Tag 089W] inverted — and leaves standing one crossing of the two models
of `RⁿΓ(g⁻¹⊤, -)` on the **source** scheme, with the restriction of scalars along `g^♯` outside it.

`…TopDegreeBaseChange.singleCompDerivedOpenSubscheme_inv_app_pullbackRestriction`
(`OpenSubschemeModelCrossingTransport.lean`) — brick (i) of the 2b(B) match, read at the module
factor (4) sits at — is that same crossing, **inverted**, when the source scheme is the open
subscheme `f''⁻¹W` of the match: the two are the same isomorphism, the six crossings
between the two spellings (`…toSheafedSpace` against `…toRingedSpace`,
`(opensMap g).obj ⊤` against `⊤`, and the four arguments of the crossing built from them) each
being `rfl`.

This file joins them. Brick (i) is solved for the crossing's **inverse**, and the crossing occurs
in the `ψ` side's factor (4) in the **forward** direction, so the join transposes the chase's own
equation rather than inverting brick (i)'s right-hand side — whose leading
`…TopDegreeBaseChange.openSubschemeBareComparisonOf` factor is not invertible, as
`OpenSubschemeSingleModelCrossing.lean` records. No inverse of anything brick (i) produces is
taken.

## Main results

* `…TopDegreeBaseChange.factorFourFive_comp_openSubschemeCrossing_eq` — **the join.** For
  `h' : X'' ⟶ X'`, opens `U'` of `X'` and `U''` of `X''` with `U'' ≤ (h')⁻¹U'`, a module `F'` on
  `X'` and a degree `n`,

  > factor (4) of [Stacks, Tag 089W] inverted at the module
  > `(h'.resLE U' U'' hle)^*(F'|_{U'})`, then its factor (5), then the restriction of scalars
  > along `(h'.resLE U' U'' hle)^♯` applied to brick (i)'s six factors, is the degree-`n`
  > cohomology of `Stacks.EdgeCompat.preimageSectionsModelComparison` at that module's single
  > complex, followed by the edge morphism of the restriction of scalars.

  Nothing is assumed of `h'`, of the two opens, of `F'` or of `n` — no affineness, no acyclicity,
  no boundedness and no quasi-coherence.

## Implementation notes

*The transposition, and why it is the cheap direction.* The crossing of the two models of
`RⁿΓ(U'', -)` is an isomorphism by construction, so an equation carrying it in the forward
direction may be transposed by postcomposing its inverse, and brick (i) *is* a factorisation of
that inverse. Solving brick (i) for the forward direction instead would need
`…TopDegreeBaseChange.openSubschemeBareComparisonOf` to be invertible, which it is not;
the transposition needs none of it. The cancellation is performed by `comp_map_cancel` below, at
variables of abstract categories, so that neither the statement's spelling crossings nor the
functor applications are re-made inside the proof.

*The index functor of the collapse mirror is the identity.* The mirror is stated for a functor
`E : Dc ⥤ (modules upstairs)` and a point `Z : Dc`, because Grothendieck's comparison
`Stacks.Cohomology.AffineBase.rightDerivedCompNatIso` is; only `E.obj Z` occurs in its conclusion,
so it is instantiated here at `E := 𝟭 _` and `Z := ` the module, where `E.obj Z` is the module by
definition and no transport is needed.

*No `@[stacks …]` attribute is placed.* [Stacks, Tag 089W] carries its own where it is proved, and
conclusion (c) of [Stacks, Tag 0EX3] is proved elsewhere, as
`…TopDegreeBaseChange.isIso_topDirectImageBaseChangeMap` (`BaseChangeTopDegreeConclusion.lean`), by
a route that does not use this file.

## References

* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (exists_quasiIso_isKInjective)
open Stacks.Cohomology.DerivedSectionsLeray
open Stacks.Cohomology.HypercohomologyEdge.HomologyComparison (derivedHomologyComparison)

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] RingedSpaceModuleAdjunction.preservesLimits_modulePushforward
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

/-- **Transposing an equation that carries an isomorphism's component forward, against a known
factorisation of that component's inverse, on the far side of a functor.** Given
`η.inv.app Nm = y` and `a ≫ b = p ≫ q ≫ F.map (η.hom.app Nm)`, the composite
`a ≫ b ≫ F.map y` is `p ≫ q`. Nothing is assumed of `y` beyond the factorisation, so no inverse
of any of its factors is taken. Stated at variables of abstract categories, where the
reassociations are free and no definitional crossing is made. -/
private theorem comp_map_cancel {Cx C D : Type*} [Category* Cx] [Category* C] [Category* D]
    (F : C ⥤ D) {E₁ E₂ : Cx ⥤ C} (η : E₁ ≅ E₂) (Nm : Cx)
    {y : E₂.obj Nm ⟶ E₁.obj Nm} (hy : η.inv.app Nm = y)
    {T₀ T₁ P : D} {a : T₀ ⟶ T₁} {b : T₁ ⟶ F.obj (E₂.obj Nm)} {p : T₀ ⟶ P}
    {q : P ⟶ F.obj (E₁.obj Nm)}
    (h : a ≫ b = p ≫ q ≫ F.map (η.hom.app Nm)) :
    a ≫ b ≫ F.map y = p ≫ q := by
  subst hy
  rw [← Category.assoc, h]
  simp only [Category.assoc]
  rw [← F.map_comp, η.hom_inv_id_app, F.map_id, Category.comp_id]

variable {X' X'' : Scheme.{u}} (h' : X'' ⟶ X') {U' : X'.Opens} {U'' : X''.Opens}
  (hle : U'' ≤ h' ⁻¹ᵁ U') (F' : X'.Modules)

open Stacks.EdgeCompat in
/-- **The join of [Stacks, Tag 089W]'s factors (4) and (5) with brick (i) of the 2b(B) match.**
For `h' : X'' ⟶ X'`, opens `U'` of `X'` and `U''` of `X''` with `U'' ≤ (h')⁻¹U'`, a module `F'` on
`X'`, a degree `n` and `g := h'.resLE U' U'' hle`,

> the crossing of the two models of `Rⁿ(Γ(U', ⊤, -) ∘ g_*)` at `g^*(F'|_{U'})` — factor (4) of
> `Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward_inv_eq_lerayComparison` — then
> `Stacks.Cohomology.AffineComparison.restrictScalarsRightDerivedIso` inverted — its factor (5) —
> then restriction of scalars along `g^♯` applied to the six factors of
> `…TopDegreeBaseChange.singleCompDerivedOpenSubscheme_inv_app_pullbackRestriction`, is the
> degree-`n` cohomology of `Stacks.EdgeCompat.preimageSectionsModelComparison g ⊤` at the single
> complex of `g^*(F'|_{U'})`, followed by the edge morphism of the restriction of scalars along
> `g^♯`.

Both of the right-hand side's factors are read on the ambient `X''` once brick (i)'s own factors
are unfolded, which is where the `γ⁺` side of conclusion (c) of [Stacks, Tag 0EX3] reads the same
place. The crossing brick (i) moves occurs here in the forward direction and brick (i) is a
factorisation of its inverse, so the equation is transposed rather than brick (i) inverted: **no
inverse of `…TopDegreeBaseChange.openSubschemeBareComparisonOf` is taken**, that factor
not being invertible.

**Nothing is assumed** of `h'`, of `U'`, of `U''`, of `F'` or of `n`; in particular no affineness,
no acyclicity, no boundedness and no quasi-coherence. -/
theorem factorFourFive_comp_openSubschemeCrossing_eq (n : ℕ) :
    (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
            (modulePushforward (h'.resLE U' U'' hle).toLRSHom.toShHom ⋙
              sectionsOverOpen (U' : Scheme).toSheafedSpace ⊤)
            (derivedPreimageSections (h'.resLE U' U'' hle).toLRSHom.toShHom ⊤)
            (derivedPreimageSectionsUnit (h'.resLE U' U'' hle).toLRSHom.toShHom ⊤)
            (exists_quasiIso_isKInjective (U'' : Scheme).toSheafedSpace) n).hom.app
          ((Scheme.Modules.pullback (h'.resLE U' U'' hle)).obj
            ((Scheme.Modules.restrictFunctor U'.ι).obj F')) ≫
        (Stacks.Cohomology.AffineComparison.restrictScalarsRightDerivedIso (h'.resLE U' U'' hle)
            ((Scheme.Modules.pullback (h'.resLE U' U'' hle)).obj
              ((Scheme.Modules.restrictFunctor U'.ι).obj F')) n).inv ≫
          (Stacks.EdgeCompat.preimageRestrictScalars
              (h'.resLE U' U'' hle).toLRSHom.toShHom ⊤).map
            (((sectionsOverOpen (U'' : Scheme).toRingedSpace ⊤).rightDerived n).map
                (openSubschemeRestrictionPullbackIso h' hle F').inv ≫
              (Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso
                    (openSubschemeRestrictionOf X'' U'')
                    (sectionsOverOpen (U'' : Scheme).toRingedSpace ⊤) n).inv.app
                  ((Scheme.Modules.pullback h').obj F') ≫
                (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
                      (openSubschemeRestrictionOf X'' U'' ⋙
                        sectionsOverOpen (U'' : Scheme).toRingedSpace ⊤)
                      (derivedSectionsImageTopOf X'' U'')
                      (derivedSectionsImageTopUnitOf X'' U'')
                      (exists_quasiIso_isKInjective X''.toRingedSpace) n).inv.app
                    ((Scheme.Modules.pullback h').obj F') ≫
                  (DerivedCategory.homologyFunctor (ModuleCat.{u}
                        ((structureSheafRing (U'' : Scheme).toRingedSpace).obj.obj (op ⊤)))
                        (n : ℤ)).map
                      ((openSubschemeBareComparisonOf X'' U'').app
                        ((DerivedCategory.singleFunctor
                          (SheafOfModules.{u} (structureSheafRing X''.toRingedSpace)) 0).obj
                            ((Scheme.Modules.pullback h').obj F'))) ≫
                    (DerivedCategory.homologyFunctor (ModuleCat.{u}
                          ((structureSheafRing (U'' : Scheme).toRingedSpace).obj.obj (op ⊤)))
                          (n : ℤ)).map
                        ((derivedSectionsOverOpen (U'' : Scheme).toRingedSpace ⊤).map
                          (((openSubschemeRestrictionOf X'' U'').mapDerivedCategorySingleFunctor
                            0).hom.app ((Scheme.Modules.pullback h').obj F'))) ≫
                      (DerivedCategory.homologyFunctor (ModuleCat.{u}
                            ((structureSheafRing (U'' : Scheme).toRingedSpace).obj.obj (op ⊤)))
                            (n : ℤ)).map
                          ((derivedSectionsOverOpen (U'' : Scheme).toRingedSpace ⊤).map
                            ((DerivedCategory.singleFunctor
                              (SheafOfModules.{u}
                                (structureSheafRing (U'' : Scheme).toRingedSpace)) 0).map
                              (openSubschemeRestrictionPullbackIso h' hle F').hom))) =
      (DerivedCategory.homologyFunctor
            (ModuleCat.{u} ((structureSheafRing (U' : Scheme).toSheafedSpace).obj.obj (op ⊤)))
            (n : ℤ)).map
          ((Stacks.EdgeCompat.preimageSectionsModelComparison
              (h'.resLE U' U'' hle).toLRSHom.toShHom ⊤).app
            ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (structureSheafRing (U'' : Scheme).toSheafedSpace)) 0).obj
                ((Scheme.Modules.pullback (h'.resLE U' U'' hle)).obj
                  ((Scheme.Modules.restrictFunctor U'.ι).obj F')))) ≫
        (derivedHomologyComparison
              (Stacks.EdgeCompat.preimageRestrictScalars
                (h'.resLE U' U'' hle).toLRSHom.toShHom ⊤)
              (Stacks.EdgeCompat.preimageRestrictScalars
                (h'.resLE U' U'' hle).toLRSHom.toShHom ⊤).mapDerivedCategory
              (Stacks.EdgeCompat.preimageRestrictScalars
                (h'.resLE U' U'' hle).toLRSHom.toShHom ⊤).mapDerivedCategoryFactorsh.inv
              (Stacks.EdgeCompat.exists_quasiIso_isKInjective_preimageSectionsRing
                (h'.resLE U' U'' hle).toLRSHom.toShHom ⊤) (n : ℤ)).app
            ((derivedSectionsOverOpen (U'' : Scheme).toSheafedSpace
                ((opensMap (h'.resLE U' U'' hle).toLRSHom.toShHom).obj ⊤)).obj
              ((DerivedCategory.singleFunctor
                (SheafOfModules.{u} (structureSheafRing (U'' : Scheme).toSheafedSpace)) 0).obj
                  ((Scheme.Modules.pullback (h'.resLE U' U'' hle)).obj
                    ((Scheme.Modules.restrictFunctor U'.ι).obj F')))) :=
  comp_map_cancel _ _ _
    (singleCompDerivedOpenSubscheme_inv_app_pullbackRestriction h' hle F' n)
    (singleCompDerivedPreimageSectionsComp_hom_app_comp_restrictScalarsRightDerivedIso_inv
      (h'.resLE U' U'' hle) n (E := Functor.id _)
      ((Scheme.Modules.pullback (h'.resLE U' U'' hle)).obj
        ((Scheme.Modules.restrictFunctor U'.ι).obj F')))

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
