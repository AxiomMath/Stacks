module

public import Mathlib.CategoryTheory.Sites.Over
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.RestrictScalarsCoextensionOverSlice
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictScalarsCoextension

/-!
# Coextension of scalars commutes with restriction to a slice, sheaf level

Let `(C, J)` be a site, let `φ : O ⟶ O'` be a morphism of *sheaves* of rings on `(C, J)`, let
`F` be a sheaf of `O`-modules, and let `U : C`. Restricting a sheaf to the slice `Over U` means:
restricting its underlying presheaf along `Over.forget U : Over U ⥤ C` (exactly as at the
presheaf level, `Stacks.PresheafOfModules.CoextendScalars.restrictToOver`), and observing that
the result is again a sheaf, now for the induced topology `J.over U` on `Over U`
(`GrothendieckTopology.over`). This file compares, over `(Over U, J.over U)`:

* restricting `coextendScalars φ` applied to `F` to `Over U`, against
* applying `coextendScalars` for the restricted ring morphism `φ|_U : O|_U ⟶ O'|_U` to the
  restricted module `F|_U`,

i.e. the sheaf-level analogue of the presheaf-level comparison isomorphism
`Stacks.PresheafOfModules.CoextendScalars.coextOverSliceIso`.

## Main definitions

* `Stacks.SheafOfModules.CoextendScalars.ringOver`: the sheaf of rings `O`, restricted to
  `Over U` (for the induced topology `J.over U`).
* `Stacks.SheafOfModules.CoextendScalars.ringPhiOver`: the restriction of a morphism of sheaves
  of rings `φ : O ⟶ O'` to `Over U`.
* `Stacks.SheafOfModules.CoextendScalars.restrictToOverModules`: the restriction-to-`Over U`
  functor on sheaves of modules, `SheafOfModules O ⥤ SheafOfModules (ringOver O U)`.
* `Stacks.SheafOfModules.CoextendScalars.coextOverSliceIsoSheaf`: the sheaf-level comparison
  isomorphism
  `(restrictToOverModules O' U).obj ((coextendScalars φ).obj F) ≅
    (coextendScalars (ringPhiOver φ U)).obj ((restrictToOverModules O U).obj F)`.

## Main results

* `Stacks.SheafOfModules.CoextendScalars.restrictToOver_isSheaf`: the restriction of a sheaf of
  `O`-modules to `Over U` is a sheaf for `J.over U`.

## Implementation notes

`restrictToOverModules` is built from `PresheafOfModules.pushforward₀` rather than from
Mathlib's `SheafOfModules.pushforward` or `SheafOfModules.over`, so that on underlying presheaves
of modules it agrees by `rfl` with `Stacks.PresheafOfModules.CoextendScalars.restrictToOver`.

## References

* [Stacks Project, Tag 0996](https://stacks.math.columbia.edu/tag/0996), Lemma 20.26.1 part (2).
-/

@[expose] public section

open CategoryTheory

namespace Stacks.SheafOfModules.CoextendScalars

universe u

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C} {O O' : Sheaf J RingCat.{u}}

open Stacks.PresheafOfModules.CoextendScalars

/-- The sheaf of rings `O`, restricted to the slice `Over U`, for the induced topology
`J.over U`. -/
noncomputable def ringOver (O : Sheaf J RingCat.{u}) (U : C) : Sheaf (J.over U) RingCat.{u} :=
  (J.overPullback RingCat.{u} U).obj O

/-- `ringOver O U` agrees, on underlying presheaves, with the presheaf-level restriction of the
ring presheaf `O.obj` to `Over U` (pure precomposition along `Over.forget U`). -/
theorem ringOver_obj (O : Sheaf J RingCat.{u}) (U : C) :
    (ringOver O U).obj = (Over.forget U).op ⋙ O.obj := rfl

/-- The restriction of a morphism of sheaves of rings `φ : O ⟶ O'` to the slice `Over U`. -/
noncomputable def ringPhiOver (φ : O ⟶ O') (U : C) : ringOver O U ⟶ ringOver O' U :=
  (J.overPullback RingCat.{u} U).map φ

/-- `ringPhiOver φ U` agrees, on underlying presheaves, with the presheaf-level
`restrictPhi φ.hom U`. -/
theorem ringPhiOver_hom (φ : O ⟶ O') (U : C) :
    (ringPhiOver φ U).hom = restrictPhi φ.hom U := rfl

/-- The underlying presheaf of modules of a sheaf of `O`-modules, restricted to `Over U`, is a
sheaf for the induced topology `J.over U`. -/
theorem restrictToOver_isSheaf (F : SheafOfModules.{u} O) (U : C) :
    Presheaf.IsSheaf (J.over U) (restrictToOver U F.val).presheaf :=
  (Over.forget U).op_comp_isSheaf_of_isSheaf (J.over U) J F.val.presheaf F.isSheaf

/-- **Restriction to a slice, sheaf-of-modules level.** The restriction-to-`Over U` functor on
sheaves of modules: on underlying presheaves of modules it is `restrictToOver U`. -/
noncomputable def restrictToOverModules (O : Sheaf J RingCat.{u}) (U : C) :
    SheafOfModules.{u} O ⥤ SheafOfModules.{u} (ringOver O U) where
  obj F := { val := restrictToOver U F.val, isSheaf := restrictToOver_isSheaf F U }
  map {_ _} η := { val := (PresheafOfModules.pushforward₀ (Over.forget U) O.obj).map η.val }
  map_id F :=
    SheafOfModules.hom_ext ((PresheafOfModules.pushforward₀ (Over.forget U) O.obj).map_id F.val)
  map_comp η θ := SheafOfModules.hom_ext
    ((PresheafOfModules.pushforward₀ (Over.forget U) O.obj).map_comp η.val θ.val)

/-- **Stacks Tag 0996, Lemma 20.26.1 part (2), sheaf level.** The sheaf-level analogue of
`Stacks.PresheafOfModules.CoextendScalars.coextOverSliceIso`: restricting `coextendScalars φ`
applied to `F` to the slice `Over U` agrees with applying `coextendScalars` for the restricted
ring morphism `φ|_U` to the restricted module `F|_U`. -/
noncomputable def coextOverSliceIsoSheaf (φ : O ⟶ O') (F : SheafOfModules.{u} O) (U : C) :
    (restrictToOverModules O' U).obj ((coextendScalars φ).obj F) ≅
      (coextendScalars (ringPhiOver φ U)).obj ((restrictToOverModules O U).obj F) :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso (coextOverSliceIso φ.hom F.val U)

end Stacks.SheafOfModules.CoextendScalars
