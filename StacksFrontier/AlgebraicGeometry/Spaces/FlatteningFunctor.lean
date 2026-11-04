module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHom
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModule
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullback

/-!
# The flattening situation of a quasi-coherent module on an algebraic space

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site and let
`F` be a quasi-coherent `𝒪_X`-module.  Every scheme `T` over `Y` gives a base change
`X_T = X ×_Y T` and, along the projection `X_T ⟶ X`, a pulled-back module `F_T`.  Since the base
change of a flat module is flat, Stacks 0CWX obtains from this a functor

`F_flat : (Sch/Y)ᵒᵖ ⥤ Sets`, `T ↦ {*}` if `F_T` is flat over `T` and `∅` otherwise.

This file supplies the standing data of that situation, the base-changed module `F_T`, the
flatness condition at a test scheme in the chartwise sense of Stacks 05VV, and the functor.

## Main definitions

* `AlgebraicGeometry.Space.FlatnessSituation`: **the standing data of Stacks 0CWX**, a
  morphism of algebraic spaces together with a quasi-coherent module on its source.
* `AlgebraicGeometry.Space.FlatnessSituation.baseChangeModule`: the base change `F_T` of the
  module to a test scheme `T` over `Y`, the pullback of `F` along the projection `X_T ⟶ X`.
* `AlgebraicGeometry.Space.FlatnessSituation.IsFlatAfterBaseChange`: the condition that `F_T`
  is flat over `T`, which is the condition cutting out the locus of Stacks 0CWX.
* `AlgebraicGeometry.Space.FlatnessSituation.flatFunctor`: **the functor `F_flat` of
  Stacks 0CWX**.

## Main results

* `AlgebraicGeometry.Space.FlatnessSituation.isFlatAfterBaseChange_of_hom`: flatness of the
  base change is inherited along a morphism of test schemes.  This is the assertion "the base
  change of a flat module is flat" that makes `F_flat` a functor, and it is the final assertion
  of Stacks 05VW.
* `AlgebraicGeometry.Space.FlatnessSituation.nonempty_flatFunctor_obj_iff` and the instance
  `AlgebraicGeometry.Space.FlatnessSituation.flatFunctor_obj_subsingleton`: the value of
  `F_flat` at a test scheme has at most one element, and has one exactly when the base change
  of the module is flat there — the `{*}`/`∅` description of the source.

`AlgebraicGeometry.Space.FlatnessSituation.baseChangeModule_eq` and
`AlgebraicGeometry.Space.FlatnessSituation.isFlatAfterBaseChange_iff` unfold the two
definitions, which the elaborator does not do on its own.

## Implementation notes

The big fppf site, the base scheme and the proof that the site contains it are `variable`s
rather than fields of the standing data, as everywhere else in this development, so that the
situation lives over a fixed site and the ambient base-change API applies to it unchanged.

Test schemes over `Y` are `AlgebraicGeometry.Space.SchemesOver`, the costructured arrows from
`AlgebraicGeometry.schemeSpaceFunctor` — a scheme of the big fppf site regarded as an
algebraic space — so a morphism of test schemes is a morphism of schemes commuting with the two
maps to `Y`.  The base change itself is the ambient machinery of
`StacksFrontier/AlgebraicGeometry/Quot/RelativeHom.lean`:
`AlgebraicGeometry.Space.baseChangeSpace` is the fibre product `X ×_Y T`, with
`AlgebraicGeometry.Space.baseChangeProjection` the projection to `X` and
`AlgebraicGeometry.Space.baseChangeInclusion` the projection to `T`.  Those constructions are
stated for an arbitrary morphism of algebraic spaces, so the situation does not re-bind them:
they are applied to its morphism `D.f` directly, and nothing here needs an identification of a
bound copy with the ambient one.

The pullback of the module is `AlgebraicGeometry.Space.modulePullback`, the inverse image of
Stacks 03LU for the small étale ringed sites.  That functor exists only at module universe
`m = u`, the universe of the structure rings — the direct image it is adjoint to is assembled
from the comparison equivalence of Stacks 03G1, which is available only at `Type u` — so the
module of the standing data is taken at `Modules.{u, u}`, although
`AlgebraicGeometry.Space.Modules` itself leaves the module universe free.  The same universe is
the only one at which `AlgebraicGeometry.Space.IsFlatOver` can be stated.

Flatness is `AlgebraicGeometry.Space.IsFlatOver`, the chartwise form of Stacks 05VV, applied to
the projection `X_T ⟶ T` and to `F_T`.  The scheme-level counterpart of this file is
`AlgebraicGeometry.FlatnessSituation` of
`StacksFrontier/AlgebraicGeometry/Flatness/FlatteningFunctor/Basic.lean`, which is Stacks 05MW;
the names here follow it.

The functoriality of `F_flat` — the parenthetical "since the base change of a flat module is
flat" of the source — is the final assertion of Stacks 05VW,
`AlgebraicGeometry.Space.isFlatOver_modulePullback` of
`StacksFrontier/AlgebraicGeometry/Spaces/FlatModuleBaseChange.lean`, applied to the cartesian
square of a morphism `U ⟶ T` of test schemes,
`AlgebraicGeometry.Space.isPullback_baseChangeMap`.  Two further inputs are needed and both are
unconditional here: that result asks for quasi-coherence of the module it base changes and of
the base change itself, which is where quasi-coherence of `F` in the standing data is used,
through Stacks 03GA
(`AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite`); and
`F_U` is only *isomorphic* to the pullback of `F_T` along `X_U ⟶ X_T`, by the composition
comparison `AlgebraicGeometry.Space.modulePullbackTriangle` of Stacks 03LU, so flatness is
moved across that isomorphism by `AlgebraicGeometry.Space.IsFlatOver.of_iso`.

The functor itself is the subterminal presheaf
`AlgebraicGeometry.Space.subterminalSchemesOverFunctor` of
`StacksFrontier/AlgebraicGeometry/Spaces/ModuleMapSituation.lean`, the shape shared with the four
base-change loci of the sibling situation Stacks 083F of the same section: the value at a test
scheme is a subtype of a one-element type, hence `{*}` when the condition holds and `∅`
otherwise, and the restriction maps carry no information.

## References

* [Stacks Project, Tag 0CWX](https://stacks.math.columbia.edu/tag/0CWX)
* [Stacks Project, Tag 05VV](https://stacks.math.columbia.edu/tag/05VV)
* [Stacks Project, Tag 05VW](https://stacks.math.columbia.edu/tag/05VW)
* [Stacks Project, Tag 083F](https://stacks.math.columbia.edu/tag/083F)
* [Stacks Project, Tag 05MW](https://stacks.math.columbia.edu/tag/05MW)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0CWX.** The standing data of Stacks 0CWX: a morphism `f : X ⟶ Y` of algebraic
spaces over `S` and a quasi-coherent `𝒪_X`-module `F`, whose base changes to the schemes over
`Y` are tested for flatness. -/
@[stacks_fixed 0CWX "standing data"]
structure FlatnessSituation where
  /-- The source algebraic space, carrying the module. -/
  X : AlgebraicSpaces B S hS
  /-- The target algebraic space, over which the test schemes live. -/
  Y : AlgebraicSpaces B S hS
  /-- The morphism of algebraic spaces being base changed along. -/
  f : X ⟶ Y
  /-- The module whose base changes are tested for flatness. -/
  F : Modules.{u, u} B S hS X.1 X.2
  /-- The module is quasi-coherent, as in the source. -/
  quasicoherent : F.IsQuasicoherentOnSite

namespace FlatnessSituation

variable {B S hS}

/-- **Stacks 0CWX.** The base change `F_T` of the module to a test scheme `T` over `Y`: the
pullback of `F` along the projection `X_T = X ×_Y T ⟶ X`. -/
@[stacks 0CWX "the base change F_T of the module to a test scheme over the target"]
def baseChangeModule (D : FlatnessSituation.{u} B S hS) (T : SchemesOver D.Y) :
    Modules.{u, u} B S hS (baseChangeSpace D.f T).1 (baseChangeSpace D.f T).2 :=
  (modulePullback B S hS (baseChangeProjection D.f T)).obj D.F

/-- The base change of the module is the inverse image of Stacks 03LU along the projection of
the fibre product, stated as an equation; the elaborator does not unfold the definition on its
own. -/
@[simp]
theorem baseChangeModule_eq (D : FlatnessSituation.{u} B S hS) (T : SchemesOver D.Y) :
    D.baseChangeModule T = (modulePullback B S hS (baseChangeProjection D.f T)).obj D.F :=
  rfl

/-- The base-changed module `F_T` is flat over the test scheme `T`, in the chartwise sense of
Stacks 05VV, relative to the projection `X_T ⟶ T`. -/
def IsFlatAfterBaseChange (D : FlatnessSituation.{u} B S hS) (T : SchemesOver D.Y) : Prop :=
  IsFlatOver B S hS (baseChangeSpace D.f T).2 (baseChangeInclusion D.f T).hom
    (D.baseChangeModule T)

/-- Flatness after base change is flatness of Stacks 05VV for the projection to the test
scheme, stated as an equivalence; the elaborator does not unfold the definition on its own. -/
theorem isFlatAfterBaseChange_iff (D : FlatnessSituation.{u} B S hS) (T : SchemesOver D.Y) :
    D.IsFlatAfterBaseChange T ↔
      IsFlatOver B S hS (baseChangeSpace D.f T).2 (baseChangeInclusion D.f T).hom
        (D.baseChangeModule T) :=
  Iff.rfl

/-- **The base change of a flat module is flat.**  If `F_T` is flat over a test scheme `T`, then
`F_U` is flat over `U` for every test scheme `U` over `T`.  This is the assertion the source
appeals to in order to obtain the functor `F_flat`.

The square of `X_U ⟶ X_T` over `U ⟶ T` is cartesian, so the final assertion of Stacks 05VW gives
flatness over `U` of the pullback of `F_T` along `X_U ⟶ X_T`; that pullback is `F_U` up to the
composition comparison of Stacks 03LU, across which flatness moves.  The quasi-coherence of
`F_T` and of its pullback that Stacks 05VW asks for come from quasi-coherence of `F` by
Stacks 03GA. -/
theorem isFlatAfterBaseChange_of_hom (D : FlatnessSituation.{u} B S hS)
    {T U : SchemesOver D.Y} (g : U ⟶ T) (h : D.IsFlatAfterBaseChange T) :
    D.IsFlatAfterBaseChange U := by
  have hT : (D.baseChangeModule T).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
      (baseChangeProjection D.f T) D.F D.quasicoherent
  have := isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
    (baseChangeMap D.f g) (D.baseChangeModule T) hT
  exact IsFlatOver.of_iso B S hS (baseChangeSpace D.f U).2
    ((modulePullbackTriangle B S hS (baseChangeMap_comp_projection D.f g)).app D.F).symm
    (isFlatOver_modulePullback B S hS (isPullback_baseChangeMap D.f g)
      (D.baseChangeModule T) h)

/-- **Stacks 0CWX.**  The flattening functor

`F_flat : (Sch/Y)ᵒᵖ ⥤ Sets`, `T ↦ {*}` if `F_T` is flat over `T` and `∅` otherwise.

Its value at a test scheme is a subtype of a one-element type, cut out by flatness of the base
change there; that this is stable under a morphism of test schemes, which is what makes the
assignment a functor, is
`AlgebraicGeometry.Space.FlatnessSituation.isFlatAfterBaseChange_of_hom`. -/
@[stacks 0CWX "the functor F_flat"]
def flatFunctor (D : FlatnessSituation.{u} B S hS) : (SchemesOver D.Y)ᵒᵖ ⥤ Type u :=
  subterminalSchemesOverFunctor B S hS D.Y D.IsFlatAfterBaseChange
    fun g h => D.isFlatAfterBaseChange_of_hom g h

/-- The value of the flattening functor at a test scheme is nonempty exactly when the base
change of the module is flat there.  Together with
`AlgebraicGeometry.Space.FlatnessSituation.flatFunctor_obj_subsingleton` this is the `{*}`/`∅`
description of the source. -/
@[simp]
theorem nonempty_flatFunctor_obj_iff (D : FlatnessSituation.{u} B S hS) (T : SchemesOver D.Y) :
    Nonempty (D.flatFunctor.obj (Opposite.op T)) ↔ D.IsFlatAfterBaseChange T :=
  nonempty_subterminalSchemesOverFunctor_obj_iff B S hS D.Y _ _ T

/-- Every value of the flattening functor has at most one element. -/
instance flatFunctor_obj_subsingleton (D : FlatnessSituation.{u} B S hS)
    (T : (SchemesOver D.Y)ᵒᵖ) : Subsingleton (D.flatFunctor.obj T) :=
  subterminalSchemesOverFunctor_obj_subsingleton B S hS D.Y _ _ T

/-- The value of the flattening functor at a test scheme is empty exactly when the base change
of the module is not flat there. -/
theorem isEmpty_flatFunctor_obj_iff (D : FlatnessSituation.{u} B S hS) (T : SchemesOver D.Y) :
    IsEmpty (D.flatFunctor.obj (Opposite.op T)) ↔ ¬ D.IsFlatAfterBaseChange T := by
  rw [← not_nonempty_iff, nonempty_flatFunctor_obj_iff]

end FlatnessSituation

end AlgebraicGeometry.Space

end
