module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Homology.Additive
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictScalarsCoextensionOverSlice
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Slice.RestrictionOfComplexes

/-!
# The bespoke slice restriction agrees with Mathlib's canonical one

`Stacks.SheafOfModules.CoextendScalars.restrictToOverModules` (built in
`RestrictScalarsCoextensionOverSlice.lean` directly from
`PresheafOfModules.pushforward₀ (Over.forget U)`, precisely in order to keep every step of that
file's comparison a `rfl`) and Mathlib's canonical `SheafOfModules.overFunctor`/`.over`
(`Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`, used throughout this
project's `AlgebraicGeometry.RingedSite.restrictComplex` and hence
`SheafHomComplex.sectionsIso`) are *not* the same functor on the nose: `overFunctor` is, by
definition, `restrictToOverModules` followed by restriction of scalars along the identity
morphism of the restricted ring sheaf, and that extra step is only *canonically*, not
*definitionally*, trivial (`ModuleCat.restrictScalarsId'` is a genuine natural isomorphism,
not `Iso.refl`).

This file supplies the missing comparison: a natural isomorphism
`restrictToOverModules O U ≅ SheafOfModules.overFunctor O U`, built by threading
`ModuleCat.restrictScalarsId'App` through the presheaf level
(`presheafRestrictScalarsIdObj`/`presheafRestrictScalarsId`) and then transporting across the
fully faithful forgetful functor `SheafOfModules.fullyFaithfulForget`, exactly as
`coextOverSliceIsoSheaf` itself was transported. It then lifts this comparison to cochain
complexes (`NatIso.mapHomologicalComplex`), matching the shape of
`AlgebraicGeometry.RingedSite.restrictComplex`.

## Main results

* `Stacks.SheafOfModules.CoextendScalars.presheafRestrictScalarsId`: restriction of scalars of
  presheaves of modules along the identity morphism of a presheaf of rings is naturally
  isomorphic to the identity functor.
* `Stacks.SheafOfModules.CoextendScalars.restrictToOverModulesIsoOverFunctor`: the comparison
  isomorphism itself, `restrictToOverModules O U ≅ SheafOfModules.overFunctor O U`.
* `Stacks.SheafOfModules.CoextendScalars.restrictComplexIsoRestrictToOverModulesComplex`: its
  lift to cochain complexes.

## Implementation notes

The ring-sheaf level needs no bridge at all: `ringOver O U` and `O.over U` are not merely
isomorphic but the *same term* (`Stacks.SheafOfModules.CoextendScalars.ringOver` and Mathlib's
`Sheaf.over` are both literally `(J.overPullback RingCat.{u} U).obj O`,
`Mathlib.CategoryTheory.Sites.Over`), so no comparison is stated for it. The module level is
the one genuine (but mechanical) gap, and it is exactly the shape of
`ModuleCat.restrictScalarsId'`: we only ever need to cancel a restriction of scalars along an
identity ring morphism, never anything about the slice-restriction functors themselves.

## References

* [Stacks Project, Tag 0996](https://stacks.math.columbia.edu/tag/0996), Lemma 20.26.1 part (2).
-/

@[expose] public section

open CategoryTheory

universe u

namespace Stacks.SheafOfModules.CoextendScalars

open Stacks.PresheafOfModules.CoextendScalars

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}

/-- At a fixed presheaf of modules `M`, restricting scalars along the identity morphism of the
presheaf of rings `R` identifies to `M` itself. Built degreewise from
`ModuleCat.restrictScalarsId'App`, whose components act as the identity on elements
(`restrictScalarsId'App_hom_apply`), which is what makes the naturality square close by `rfl`
after unfolding `PresheafOfModules.restrictScalarsObj`'s action on morphisms. -/
noncomputable def presheafRestrictScalarsIdObj {R : Cᵒᵖ ⥤ RingCat.{u}}
    (M : PresheafOfModules.{u} R) :
    (PresheafOfModules.restrictScalars (𝟙 R)).obj M ≅ M :=
  PresheafOfModules.isoMk
    (fun X => ModuleCat.restrictScalarsId'App (RingHom.id _) rfl (M.obj X))
    (fun _ _ f => by
      ext x
      rfl)

/-- Restriction of scalars of presheaves of modules along the identity morphism of a presheaf
of rings `R` is naturally isomorphic to the identity functor. -/
noncomputable def presheafRestrictScalarsId (R : Cᵒᵖ ⥤ RingCat.{u}) :
    PresheafOfModules.restrictScalars (𝟙 R) ≅ 𝟭 (PresheafOfModules.{u} R) :=
  NatIso.ofComponents presheafRestrictScalarsIdObj
    (fun {M N} φ => by
      ext X x
      rfl)

/-- **The convention bridge, presheaf level, functorial form.** Restricting a presheaf of
`O.obj`-modules to `Over U` the bespoke way (`restrictToOver U`, pure precomposition) agrees
with Mathlib's canonical `PresheafOfModules.pushforward` along the identity morphism of the
restricted ring presheaf: the latter is, by definition, the former followed by restriction of
scalars along that identity, and `presheafRestrictScalarsId` cancels that extra step. Built at
the functor level (rather than degreewise) so that its naturality is free, coming from
`isoWhiskerLeft` and `Functor.rightUnitor`. -/
noncomputable def restrictToOverPushforwardIdIso (O : Sheaf J RingCat.{u}) (U : C) :
    PresheafOfModules.pushforward
        (F := Over.forget U) (𝟙 ((Over.forget U).op ⋙ O.obj)) ≅
      PresheafOfModules.pushforward₀ (Over.forget U) O.obj :=
  Functor.isoWhiskerLeft (PresheafOfModules.pushforward₀ (Over.forget U) O.obj)
      (presheafRestrictScalarsId ((Over.forget U).op ⋙ O.obj)) ≪≫
    Functor.rightUnitor (PresheafOfModules.pushforward₀ (Over.forget U) O.obj)

/-- **The convention bridge, object level.** For a single `M : SheafOfModules O`, restricting
`M` to the slice `Over U` the bespoke way (`restrictToOverModules`) agrees with restricting it
Mathlib's canonical way (`SheafOfModules.overFunctor`). On underlying presheaves, both sides are
related by `restrictToOverPushforwardIdIso`'s component at `M.val`; the comparison is then
transported across the fully faithful forgetful functor `SheafOfModules.fullyFaithfulForget`. -/
noncomputable def restrictToOverModulesObjIsoOverFunctorObj (O : Sheaf J RingCat.{u}) (U : C)
    (M : SheafOfModules.{u} O) :
    (restrictToOverModules O U).obj M ≅ (SheafOfModules.overFunctor O U).obj M :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    ((restrictToOverPushforwardIdIso O U).app M.val).symm

/-- **The convention bridge.** `Stacks.SheafOfModules.CoextendScalars.restrictToOverModules`
(the bespoke restriction-to-`Over U` functor underlying Fact B,
`coextOverSliceIsoSheaf`) is naturally isomorphic to Mathlib's canonical
`SheafOfModules.overFunctor`/`.over` (the restriction-to-`Over U` functor that
`AlgebraicGeometry.RingedSite.restrictComplex` and `SheafHomComplex.sectionsIso` are phrased
in terms of). Naturality is checked after applying the faithful forgetful functor
`SheafOfModules.fullyFaithfulForget`, where it reduces to the naturality of
`restrictToOverPushforwardIdIso.inv` (itself free, being built from `isoWhiskerLeft`/
`Functor.rightUnitor`). -/
noncomputable def restrictToOverModulesIsoOverFunctor (O : Sheaf J RingCat.{u}) (U : C) :
    restrictToOverModules O U ≅ SheafOfModules.overFunctor O U :=
  NatIso.ofComponents (restrictToOverModulesObjIsoOverFunctorObj O U)
    (fun {M N} η => by
      apply (SheafOfModules.fullyFaithfulForget _).map_injective
      exact (restrictToOverPushforwardIdIso O U).inv.naturality η.val)


/-- A copy, at this file's single universe `u`, of the generic `PreservesZeroMorphisms`
instance that `SheafOfModules.overFunctor_additive` (four independently-quantified universes)
already supplies. Registered explicitly (and at high priority) so that the two explicit
instance arguments of `restrictComplexIsoRestrictToOverModulesComplex` below have a concrete,
single-universe instance to be elaborated against, rather than the generic four-universe one. -/
noncomputable instance (priority := high) overFunctor_preservesZeroMorphisms
    (O : Sheaf J RingCat.{u}) (U : C) :
    (SheafOfModules.overFunctor O U).PreservesZeroMorphisms where
  map_zero X Y := by
    apply SheafOfModules.hom_ext
    rfl

/-- **Restriction to a slice the bespoke way is additive.** Needed so that
`NatIso.mapHomologicalComplex` below can find the `PreservesZeroMorphisms` instances it requires
on both sides of the comparison (`SheafOfModules.overFunctor` already has one,
`SheafOfModules.overFunctor_additive`). On Homs, `restrictToOverModules`'s action is pure
reindexing of components, so additivity holds by `rfl`, exactly as for `overFunctor_additive`. -/
noncomputable instance restrictToOverModules_additive (O : Sheaf J RingCat.{u}) (U : C) :
    (restrictToOverModules O U).Additive where
  map_add := by intros; rfl

/-- Restricting a cochain complex of `O`-modules to the slice `Over U` along
`restrictToOverModules O U` agrees, up to isomorphism, with `AlgebraicGeometry.RingedSite`'s
`restrictComplex`, which is built from `SheafOfModules.overFunctor`.

The two `PreservesZeroMorphisms` instances are explicit binders, passed to
`NatIso.mapHomologicalComplex` positionally, because instance search cannot unify
`ringOver O U` with `O.over U` (these are equal only after unfolding a `def`). -/
noncomputable def restrictComplexIsoRestrictToOverModulesComplex (O : Sheaf J RingCat.{u}) (U : C)
    (K : CochainComplex (SheafOfModules.{u} O) ℤ)
    [h₁ : (restrictToOverModules O U).PreservesZeroMorphisms]
    [h₂ : (SheafOfModules.overFunctor O U).PreservesZeroMorphisms] :
    ((restrictToOverModules O U).mapHomologicalComplex (ComplexShape.up ℤ)).obj K ≅
      ((SheafOfModules.overFunctor O U).mapHomologicalComplex (ComplexShape.up ℤ)).obj K :=
  (@NatIso.mapHomologicalComplex _ _ _ _ _ _ _ (restrictToOverModules O U)
    (SheafOfModules.overFunctor O U) h₁ h₂
    (restrictToOverModulesIsoOverFunctor O U) (ComplexShape.up ℤ)).app K

end Stacks.SheafOfModules.CoextendScalars

end
