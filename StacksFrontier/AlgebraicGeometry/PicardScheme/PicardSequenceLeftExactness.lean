module

public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.SquishingPicardExactness
public import StacksFrontier.AlgebraicGeometry.PicardScheme.PicardFunctor

/-!
# Left exactness of the Picard sequence of a morphism with invariant structure sheaf

Let `f : X' ⟶ X` be a morphism of schemes whose comparison map `𝒪_X ⟶ f_*𝒪_{X'}` is an
isomorphism. Then pullback of Picard classes along `f` is injective: an invertible
`𝒪_X`-module whose pullback is trivial was already trivial.

For a morphism `f : X ⟶ S` of a big fppf site all of whose base-change projections
`X_T ⟶ T` have this property, that injectivity is exactness at `Pic(T)` of

`0 ⟶ Pic(T) ⟶ Pic(X_T) ⟶ Pic_{X/S}(T)`,

the first arrow being pullback along `X_T ⟶ T` and the second the canonical map to the Picard
functor.

## Main results

* `Stacks.Picard.isIso_unitsPushforwardMap_of_isIso_c` — the map `𝒪_X^* ⟶ f_*𝒪_{X'}^*` of
  sheaves of units is an isomorphism as soon as the comparison map of structure sheaves is.
* `Stacks.Picard.schemePullbackClassHom_eq_zero_iff_of_isIso_c` — pullback of Picard classes
  then has trivial kernel, and `Stacks.Picard.injective_schemePullbackClass_of_isIso_c` the
  same read as injectivity.
* `Stacks.PicardFunctor.injective_schemePullbackClass_baseChangeProj` — exactness at `Pic(T)`
  of the Picard sequence of a morphism of a big fppf site.

## Implementation notes

The argument is cohomological rather than through the pushforward of modules. Under the
identification of `Pic(Y)` with `H¹(Y, 𝒪_Y^*)` of Tag 09NU, pullback of Picard classes is the
map induced by `𝒪_X^* ⟶ f_*𝒪_{X'}^*` followed by the first Leray edge map
`H¹(X, f_*𝒪_{X'}^*) ⟶ H¹(X', 𝒪_{X'}^*)`. The edge map is injective with no hypothesis, and the
first map is an isomorphism once `𝒪_X ⟶ f_*𝒪_{X'}` is, the units of a sheaf of rings being a
functor of it. The source argues instead that the unit `𝒩 ⟶ f_*f^*𝒩` is locally an
isomorphism, which needs the projection formula for an invertible module along an arbitrary
morphism; the cohomological route needs only functoriality.

## What is proved elsewhere

Exactness at `Pic(X_T)`, that a Picard class of `X_T` dying in `Pic_{X/S}(T)` is pulled back
from `T`, is not proved here: no declaration below states it. It is
`Stacks.PicardFunctor.exact_schemePullbackClass_baseChangeProj_toPicardFunctorHom_of_isIso_c`
in `StacksFrontier/AlgebraicGeometry/PicardScheme/PicardSequenceMiddleExactness.lean`, which
follows the source — building a module on `T` from the transition morphisms of a trivialisation
over an fppf covering, using the hypothesis on structure sheaves to read a comparison on
`X_{T_i ×_T T_j}` as one on `T_i ×_T T_j` — and discharges the descent step with
`AlgebraicGeometry.QuasicoherentDescentData.isEffective_fpqcPrecoverage`, the unconditional
effectivity half of Tag 023T.

## References

* [Stacks Project, Tag 0B9M](https://stacks.math.columbia.edu/tag/0B9M)
* [Stacks Project, Tag 0B9L](https://stacks.math.columbia.edu/tag/0B9L)
* [Stacks Project, Tag 09NU](https://stacks.math.columbia.edu/tag/09NU)
* [Stacks Project, Tag 01F2](https://stacks.math.columbia.edu/tag/01F2)
* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Picard

open Stacks.Cohomology.AbelianColimit (H'functor)
open Stacks.Cohomology.LerayLowDegree (abelianSheafHasSheafify)
open Stacks.GluePicard (h1UnitsAddEquivOfScheme)
open Stacks.GlueSquishUnits (ringPushforwardMap unitsPushforwardMap)
open Stacks.SquishSheafSequence (h1NativeUnitsPullback_eq_zero_iff)
open Stacks.Picard.FirstCohomology (h1NativeUnitsPullback h1UnitsAddEquivOfScheme_naturality)

attribute [local instance] abelianSheafHasSheafify

variable {X' X : Scheme.{u}}

/-- A functor carries an isomorphism to an isomorphism. -/
private theorem isIso_map {C D : Type*} [Category C] [Category D] (F : C ⥤ D) {A B : C}
    {g : A ⟶ B} (hg : IsIso g) : IsIso (F.map g) := by
  have := hg
  infer_instance

/-- A morphism that a functor into abelian groups carries to an isomorphism vanishes only at
zero. -/
private theorem map_apply_eq_zero_iff {C : Type*} [Category C] (F : C ⥤ AddCommGrpCat.{u})
    {A B : C} {g : A ⟶ B} (hg : IsIso g) (x : F.obj A) : F.map g x = 0 ↔ x = 0 := by
  have := hg
  exact map_eq_zero_iff (ConcreteCategory.hom (F.map g))
    ((ConcreteCategory.bijective_of_isIso (F.map g)).1)

/-- The comparison map of the structure sheaves of a morphism of schemes, read as a morphism of
sheaves of rings, is an isomorphism as soon as the comparison map itself is. -/
theorem isIso_ringPushforwardMap_of_isIso_c (f : X' ⟶ X) (hc : IsIso f.toLRSHom.toHom.c) :
    IsIso (ringPushforwardMap f) := by
  let F := TopCat.Sheaf.forget CommRingCat.{u} X.toLocallyRingedSpace.toRingedSpace
  have h : F.map (ringPushforwardMap f) = f.toLRSHom.toHom.c := F.map_preimage _
  have hmap : IsIso (F.map (ringPushforwardMap f)) := by
    rw [h]; exact hc
  exact isIso_of_reflects_iso _ F

/-- The map `𝒪_X^* ⟶ f_*𝒪_{X'}^*` of sheaves of units is an isomorphism as soon as the
comparison map `𝒪_X ⟶ f_*𝒪_{X'}` of structure sheaves is: the units of a sheaf of rings are a
functor of it. -/
theorem isIso_unitsPushforwardMap_of_isIso_c (f : X' ⟶ X) (hc : IsIso f.toLRSHom.toHom.c) :
    IsIso (unitsPushforwardMap f) := by
  unfold unitsPushforwardMap
  exact isIso_map _ (isIso_map _ (isIso_map _ (isIso_ringPushforwardMap_of_isIso_c f hc)))

/-- **Pullback of Picard classes has trivial kernel when the comparison map
`𝒪_X ⟶ f_*𝒪_{X'}` is an isomorphism**: an invertible `𝒪_X`-module whose pullback along `f` is
trivial is itself trivial. -/
theorem schemePullbackClassHom_eq_zero_iff_of_isIso_c (f : X' ⟶ X)
    (hc : IsIso f.toLRSHom.toHom.c) (L : ofScheme X) :
    schemePullbackClassHom f L = 0 ↔ L = 0 := by
  have hL : h1UnitsAddEquivOfScheme X ((h1UnitsAddEquivOfScheme X).symm L) = L :=
    (h1UnitsAddEquivOfScheme X).apply_symm_apply L
  have hpull : schemePullbackClassHom f L =
      h1UnitsAddEquivOfScheme X'
        (h1NativeUnitsPullback f ((h1UnitsAddEquivOfScheme X).symm L)) :=
    ((h1UnitsAddEquivOfScheme_naturality f ((h1UnitsAddEquivOfScheme X).symm L)).trans
      (congrArg (fun y => schemePullbackClassHom f y) hL)).symm
  rw [hpull, AddEquiv.map_eq_zero_iff, h1NativeUnitsPullback_eq_zero_iff]
  exact (map_apply_eq_zero_iff _ (isIso_unitsPushforwardMap_of_isIso_c f hc) _).trans
    (h1UnitsAddEquivOfScheme X).symm.map_eq_zero_iff

/-- **Pullback of Picard classes along a morphism of schemes whose comparison map
`𝒪_X ⟶ f_*𝒪_{X'}` is an isomorphism is injective.** -/
theorem injective_schemePullbackClass_of_isIso_c (f : X' ⟶ X)
    (hc : IsIso f.toLRSHom.toHom.c) : Function.Injective (schemePullbackClass f) :=
  (injective_iff_map_eq_zero (schemePullbackClassHom f)).2
    fun L hL => (schemePullbackClassHom_eq_zero_iff_of_isIso_c f hc L).1 hL

end Stacks.Picard

namespace Stacks.PicardFunctor

variable (B : BigFppfSite.{u}) {X S : Scheme.{u}} (hX : B.Contains X) (hS : B.Contains S)
  (f : B.obj hX ⟶ B.obj hS)

/-- The projection `X_T ⟶ T` from the base change of `X ⟶ S` along a test scheme `T`. -/
abbrev baseChangeProj (T : BigFppfOver B S hS) :
    baseChange B hX hS f T ⟶ (BigFppfOver.toScheme B S hS).obj T :=
  pullback.snd (B.inclusion.map f) (B.inclusion.map T.hom)

/-- **Stacks Project, Tag 0B9M.** If the comparison map `𝒪_T ⟶ f_{T,*}𝒪_{X_T}` is an
isomorphism for every `S`-scheme `T` of the site, then pullback along `X_T ⟶ T` is injective on
Picard groups; this is exactness at `Pic(T)` of
`0 ⟶ Pic(T) ⟶ Pic(X_T) ⟶ Pic_{X/S}(T)`. -/
@[stacks 0B9M "left exactness"]
theorem injective_schemePullbackClass_baseChangeProj
    (hO : ∀ T : BigFppfOver B S hS,
      IsIso (baseChangeProj B hX hS f T).toLRSHom.toHom.c)
    (T : BigFppfOver B S hS) :
    Function.Injective (Stacks.Picard.schemePullbackClass (baseChangeProj B hX hS f T)) :=
  Stacks.Picard.injective_schemePullbackClass_of_isIso_c _ (hO T)

end Stacks.PicardFunctor

end
