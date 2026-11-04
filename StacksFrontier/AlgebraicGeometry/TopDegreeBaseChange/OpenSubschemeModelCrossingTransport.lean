module

public import StacksFrontier.AlgebraicGeometry.PullbackInvertible.Basic
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.OpenSubschemeSingleModelCrossing
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.SchemeRestriction

/-!
# The open-subscheme model crossing, carried to the modules the `ψ` side sits at

`…TopDegreeBaseChange.singleCompDerivedOpenSubscheme_inv_app_restriction`
(`OpenSubschemeSingleModelCrossing.lean`) — brick (i) of the 2b(B) match of [Stacks, Tag 0EX3] (c),
solved for the crossing of the two models of `RⁿΓ(U, -)` on the open subscheme **inverted** — is
natural in a module on the **ambient** scheme and is read at
`…TopDegreeBaseChange.openSubschemeRestrictionOf X U` of it. The `ψ` side's reading of
[Stacks, Tag 089W], `Stacks.Cohomology.AffineComparison`
`.cohomologyIsoPushforward_inv_eq_lerayComparison` at `g := h'.resLE (f'⁻¹V) (f''⁻¹W)`, meets that
crossing twice, and at **neither** place is the module syntactically a restriction from the ambient
scheme: its factor (4) sits at `N = g^*(F'|_{f'⁻¹V})` and its factor (1) at `g_* N`.

This file carries brick (i) to those two modules by the naturality of the crossing.

## Main results

* `…TopDegreeBaseChange.openSubschemeRestrictionOf_eq_restrictFunctor` — the two spellings of
  restriction to an open subscheme are one functor. This is
  `Stacks.AlgebraicGeometry.SchemeHigherDirectImage.restrictFunctor_eq_moduleRestriction`
  inverted, `openSubschemeRestrictionOf` being the ringed-space `moduleRestriction` ascribed.
* `…TopDegreeBaseChange.openSubschemeRestrictionPullbackIso` — **the upstairs transport at brick
  (i)'s spelling**: restricting `(h')^* F'` to `U''` is pulling back `F'|_{U'}` along
  `h'.resLE U' U'' hle`. This is `Stacks.Modules.restrictPullbackObjIso`, the isomorphism
  `…TopDegreeBaseChange.restrictPullbackRightDerivedPlusIso` is built from, with its source
  read at `openSubschemeRestrictionOf`.
* `…TopDegreeBaseChange.singleCompDerivedOpenSubscheme_inv_app_pullbackRestriction` — **brick (i)
  at the module factor (4) sits at.** The crossing on `U''` inverted, read at
  `(h'.resLE U' U'' hle)^*(F'|_{U'})`, is the classical derived functor applied to the transport
  inverted, then brick (i)'s four factors, then the derived sections of `U''` applied to the
  transport.
* `…TopDegreeBaseChange.singleCompDerivedOpenSubscheme_rightDerived_map_comp_inv_app` — **brick
  (i) carried across an arbitrary transport**, which is the form factor (1) consumes: for any
  morphism `μ` out of the restriction of `M` to `U`, the classical derived functor of `μ` followed
  by the crossing inverted at `μ`'s target is brick (i)'s four factors followed by derived
  sections of `μ`. Nothing is assumed of `μ`.

Nothing is assumed of the schemes, the opens, the modules, the degree or the transport anywhere in
this file.

## Implementation notes

*The one spelling crossing is paid once, inside the transport.* `Scheme.Modules.restrictFunctor`
and `openSubschemeRestrictionOf` are equal functors that are **not** interchangeable for instance
synthesis, and they are not interchangeable for the elaborator either: passing
`Stacks.Modules.restrictPullbackObjIso h' hle F'` directly where the `openSubschemeRestrictionOf`
reading of its source is expected is a type mismatch. So the crossing is a
transport and not a substitution. It is made once, by `CategoryTheory.eqToIso` on the functor
equality — the pattern `…SchemeHigherDirectImage.higherDirectImageRestrictIso` already uses — and
every statement below names only `openSubschemeRestrictionPullbackIso`.

*Why factor (1)'s transport is taken as an arbitrary morphism and not as an isomorphism.* The
transport there is the five comparisons of
`…TopDegreeBaseChange.unit_resLE_eq_restrictFunctor_map_unit`, whose third factor is
`(h' ∣_{U'})_*` of the **unit** of `(U''.homOfLE e)^* ⊣ (U''.homOfLE e)_*` for the inclusion
`U'' ≤ (h')⁻¹U'`. That unit is a restriction to a smaller open and is invertible only when the
inclusion is an equality, so the composite is a morphism and not an isomorphism; and the pullback
square of the situation does not make the inclusion an equality, since
`(h')⁻¹(f'⁻¹V) = (f'')⁻¹(h⁻¹V)` and `W` is a proper affine open of `h⁻¹V`. Naturality is therefore
used in the direction that needs no inverse, which is available because the `ψ` tail carries the
transport in exactly the position in front of the crossing that naturality consumes.

*Both statements are written with the crossing on the left.* In `theorem _ : A = B` Lean
elaborates `A` and then `B` against `A`'s type, so the side whose spelling the inputs already live
at is written first; here that is the crossing, whose module argument is a variable in brick (i)
and in the naturality square alike, so neither proof makes a definitional crossing.

*No `@[stacks …]` attribute is placed.* Conclusion (c) of [Stacks, Tag 0EX3] is proved elsewhere,
as `…TopDegreeBaseChange.isIso_topDirectImageBaseChangeMap` (`BaseChangeTopDegreeConclusion.lean`),
by a route that does not use this file.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (exists_quasiIso_isKInjective)
open Stacks.Cohomology.DerivedSectionsLeray
  (sectionsOverOpen derivedSectionsOverOpen derivedSectionsOverOpenUnit)

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

/-- **The two spellings of restriction to an open subscheme are one functor.**
`…TopDegreeBaseChange.openSubschemeRestrictionOf X U` is the ringed-space
`Stacks.Cohomology.HigherDirectImage.moduleRestriction X.toRingedSpace U` with its target
ascribed, so this is
`Stacks.AlgebraicGeometry.SchemeHigherDirectImage.restrictFunctor_eq_moduleRestriction` inverted.
Nothing is assumed of `X` or of `U`. -/
theorem openSubschemeRestrictionOf_eq_restrictFunctor (X : Scheme.{u}) (U : X.Opens) :
    openSubschemeRestrictionOf X U = Scheme.Modules.restrictFunctor U.ι :=
  (SchemeHigherDirectImage.restrictFunctor_eq_moduleRestriction X U).symm

variable {X' X'' : Scheme.{u}} (h' : X'' ⟶ X') {U' : X'.Opens} {U'' : X''.Opens}
  (hle : U'' ≤ h' ⁻¹ᵁ U') (F' : X'.Modules)

/-- **The upstairs transport, at brick (i)'s spelling of restriction.** For `h' : X'' ⟶ X'`, an
open `U'` of `X'`, an open `U''` of `X''` with `U'' ≤ (h')⁻¹U'` and a module `F'` on `X'`,

> restricting `(h')^* F'` to the open subscheme `U''` is pulling back `F'|_{U'}` along
> `h'.resLE U' U'' hle`.

This is `Stacks.Modules.restrictPullbackObjIso h' hle F'` — the isomorphism
`…TopDegreeBaseChange.restrictPullbackRightDerivedPlusIso` is built from, and the transport the
`ψ` tail of [Stacks, Tag 0EX3] (c) carries upstairs — with its **source** read through
`…TopDegreeBaseChange.openSubschemeRestrictionOf`, which is the spelling brick (i) is stated at.
The two spellings are equal by `openSubschemeRestrictionOf_eq_restrictFunctor` and not
interchangeable for the elaborator, so the crossing is made here, once. Nothing is assumed. -/
def openSubschemeRestrictionPullbackIso :
    (openSubschemeRestrictionOf X'' U'').obj ((Scheme.Modules.pullback h').obj F') ≅
      (Scheme.Modules.pullback (h'.resLE U' U'' hle)).obj
        ((Scheme.Modules.restrictFunctor U'.ι).obj F') :=
  eqToIso (by rw [openSubschemeRestrictionOf_eq_restrictFunctor X'' U'']) ≪≫
    Stacks.Modules.restrictPullbackObjIso h' hle F'

/-- **The component of an inverse natural isomorphism moved along a morphism of the index.** For
`η : F ≅ G` and `μ : M ⟶ P`, the naturality square of `η.inv` with a known factorisation of its
component at `M` substituted and reassociated. Stated at variables of abstract categories, where
the reassociation is free and no definitional crossing is made. -/
private theorem map_comp_inv_app_eq {C D : Type*} [Category* C] [Category* D] {F G : C ⥤ D}
    (η : F ≅ G) {M P : C} (μ : M ⟶ P) {T₁ T₂ T₃ : D}
    {a : G.obj M ⟶ T₁} {b : T₁ ⟶ T₂} {c : T₂ ⟶ T₃} {d : T₃ ⟶ F.obj M}
    (h : η.inv.app M = a ≫ b ≫ c ≫ d) :
    G.map μ ≫ η.inv.app P = a ≫ b ≫ c ≫ d ≫ F.map μ := by
  rw [η.inv.naturality μ, h]
  simp only [Category.assoc]

/-- **The component of an inverse natural isomorphism moved along an isomorphism of the index**, in
the direction that solves for the component at the source, with a known factorisation substituted
and reassociated. Stated at variables of abstract categories for the reason recorded at
`map_comp_inv_app_eq`. -/
private theorem inv_app_transport_eq {C D : Type*} [Category* C] [Category* D] {F G : C ⥤ D}
    (η : F ≅ G) {N M : C} (ρ : N ≅ M) {T₁ T₂ T₃ : D}
    {a : G.obj M ⟶ T₁} {b : T₁ ⟶ T₂} {c : T₂ ⟶ T₃} {d : T₃ ⟶ F.obj M}
    (h : η.inv.app M = a ≫ b ≫ c ≫ d) :
    η.inv.app N = G.map ρ.hom ≫ a ≫ b ≫ c ≫ d ≫ F.map ρ.inv := by
  simpa using G.map ρ.hom ≫= map_comp_inv_app_eq η ρ.inv h

/-- **Brick (i) at the module factor (4) of [Stacks, Tag 089W] sits at.** For `h' : X'' ⟶ X'`,
opens `U'` of `X'` and `U''` of `X''` with `U'' ≤ (h')⁻¹U'`, a module `F'` on `X'` and a degree
`n`,

> the crossing of the two models of `RⁿΓ(U'', -)` on the open subscheme, **inverted**, read at
> `(h'.resLE U' U'' hle)^*(F'|_{U'})`, is the classical right derived functor of sections over
> `U''` applied to `openSubschemeRestrictionPullbackIso` inverted, then the four factors
> `…TopDegreeBaseChange.singleCompDerivedOpenSubscheme_inv_app_restriction` gives at
> `(h')^* F'`, then the degree-`n` cohomology of derived sections over `U''` applied to the single
> complex of that transport.

This is brick (i) carried along the upstairs transport by the naturality of the crossing; the
transport being an isomorphism, the naturality square solves for the component at the `ψ` side's
module. **Nothing is assumed** of `h'`, of the two opens, of `F'` or of `n`; in particular
nothing about `…TopDegreeBaseChange.openSubschemeBareComparisonOf`, whose invertibility brick (i)
does not need. -/
theorem singleCompDerivedOpenSubscheme_inv_app_pullbackRestriction (n : ℕ) :
    (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
          (sectionsOverOpen (U'' : Scheme).toRingedSpace ⊤)
          (derivedSectionsOverOpen (U'' : Scheme).toRingedSpace ⊤)
          (derivedSectionsOverOpenUnit (U'' : Scheme).toRingedSpace ⊤)
          (exists_quasiIso_isKInjective (U'' : Scheme).toRingedSpace) n).inv.app
        ((Scheme.Modules.pullback (h'.resLE U' U'' hle)).obj
          ((Scheme.Modules.restrictFunctor U'.ι).obj F')) =
      ((sectionsOverOpen (U'' : Scheme).toRingedSpace ⊤).rightDerived n).map
          (openSubschemeRestrictionPullbackIso h' hle F').inv ≫
        (Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso
              (openSubschemeRestrictionOf X'' U'')
              (sectionsOverOpen (U'' : Scheme).toRingedSpace ⊤) n).inv.app
            ((Scheme.Modules.pullback h').obj F') ≫
          (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
                (openSubschemeRestrictionOf X'' U'' ⋙
                  sectionsOverOpen (U'' : Scheme).toRingedSpace ⊤)
                (derivedSectionsImageTopOf X'' U'') (derivedSectionsImageTopUnitOf X'' U'')
                (exists_quasiIso_isKInjective X''.toRingedSpace) n).inv.app
              ((Scheme.Modules.pullback h').obj F') ≫
            (DerivedCategory.homologyFunctor (ModuleCat.{u}
                  ((structureSheafRing (U'' : Scheme).toRingedSpace).obj.obj (op ⊤))) (n : ℤ)).map
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
                        (openSubschemeRestrictionPullbackIso h' hle F').hom)) :=
  inv_app_transport_eq _ (openSubschemeRestrictionPullbackIso h' hle F').symm
    (singleCompDerivedOpenSubscheme_inv_app_restriction X'' U'' n
      ((Scheme.Modules.pullback h').obj F'))

variable (X : Scheme.{u}) (U : X.Opens)

/-- **Brick (i) carried across an arbitrary transport**, which is the form factor (1) of
[Stacks, Tag 089W] consumes. For a scheme `X`, an open `U`, a degree `n`, a module `M` on `X`, a
module `P` on the open subscheme and **any** morphism `μ : M|_U ⟶ P`,

> the classical right derived functor of sections over `U` applied to `μ`, followed by the
> crossing of the two models of `RⁿΓ(U, -)` inverted at `P`, is the four factors
> `…TopDegreeBaseChange.singleCompDerivedOpenSubscheme_inv_app_restriction` gives at `M`, followed
> by the degree-`n` cohomology of derived sections over `U` applied to the single complex of `μ`.

This is brick (i) with the naturality square of the crossing's inverse spliced on, in the
direction that takes **no** inverse of `μ`. That is what factor (1) needs: its transport is the
five comparisons of `…TopDegreeBaseChange.unit_resLE_eq_restrictFunctor_map_unit`, one of which is
the unit of an open immersion of open subschemes and so not invertible — see this module's
implementation notes. **Nothing is assumed** of `X`, of `U`, of `n`, of `M`, of `P` or of `μ`. -/
theorem singleCompDerivedOpenSubscheme_rightDerived_map_comp_inv_app (n : ℕ)
    (M : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    (P : SheafOfModules.{u} (structureSheafRing (U : Scheme).toRingedSpace))
    (μ : (openSubschemeRestrictionOf X U).obj M ⟶ P) :
    ((sectionsOverOpen (U : Scheme).toRingedSpace ⊤).rightDerived n).map μ ≫
        (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
            (sectionsOverOpen (U : Scheme).toRingedSpace ⊤)
            (derivedSectionsOverOpen (U : Scheme).toRingedSpace ⊤)
            (derivedSectionsOverOpenUnit (U : Scheme).toRingedSpace ⊤)
            (exists_quasiIso_isKInjective (U : Scheme).toRingedSpace) n).inv.app P =
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
                    M)) ≫
              (DerivedCategory.homologyFunctor (ModuleCat.{u}
                    ((structureSheafRing (U : Scheme).toRingedSpace).obj.obj (op ⊤)))
                    (n : ℤ)).map
                  ((derivedSectionsOverOpen (U : Scheme).toRingedSpace ⊤).map
                    ((DerivedCategory.singleFunctor
                      (SheafOfModules.{u}
                        (structureSheafRing (U : Scheme).toRingedSpace)) 0).map μ)) :=
  map_comp_inv_app_eq _ μ (singleCompDerivedOpenSubscheme_inv_app_restriction X U n M)

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
