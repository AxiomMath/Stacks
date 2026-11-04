module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackDeformationBridge.PullbackDifferenceRetraction

/-!
# The quotient square of the pullback unit, read on `X_T`

Let `ξ = (T, 𝒢)` be an object of `Coh_{X/Y}` (Stacks 08KB), `h : T ⟶ T'` and `h₂ : T ⟶ T'₂` split
first order thickenings with retractions `r`, `r₂`, and `g : T'₂ ⟶ T'` under `T` with
`r₂ = g ≫ r`. On the quotients `i_*𝒢` and `i₂_*𝒢` of the extensions attached to a lift and to its
pullback along `g`, the unit `𝒢' ⟶ (X_g)_*(X_g)^*𝒢'` is the map
`AlgebraicGeometry.Space.CoherentSituation.thickeningLiftPullbackQuotientMap`. Read on `X_T`
through `ρ = X_r`, `ρ₂ = X_{r₂}` and `ρ_*(X_g)_* ≅ ρ₂_*`, it is `ρ_*i_*𝒢 ≅ 𝒢 ≅ ρ₂_*i₂_*𝒢`, the
identifications `AlgebraicGeometry.Space.CoherentSituation.thickenedModuleRetractionIso` through
which the classes of lifts are read on `X_T`.

## Main results

* `retraction_map_thickeningLiftPullbackQuotientMap_comp_eq`: the quotient square of the unit,
  read on `X_T`, is `ρ_*i_*𝒢 ≅ 𝒢 ≅ ρ₂_*i₂_*𝒢`.

## Implementation notes

The associativity coherence of Stacks 03LU for the quotient map is
`retraction_map_thickeningLiftPullbackQuotientMap_eq_comp_inv`, stated with `c_* k_* ≅ 𝟭` written
as `AlgebraicGeometry.Space.thickenedPushforwardRetractionIso` and its component written
`β.hom.app M`. The spelling needed here has `β.app M` (through
`AlgebraicGeometry.Space.CoherentSituation.thickenedModuleRetractionIso`) and the quotient map and
`ρ_*(X_g)_* ≅ ρ₂_*` as the abbreviations of `PullbackDifference`. Comparing `(β.app M).hom` with
`β.hom.app M` for the concrete `β` by unfolding does not finish within the kernel's default budget;
so does reading the abbreviations against the coherence directly. Each crossing is made once, over
variables (`CategoryTheory.map_comp_hom_app_eq_of_eq`,
`CategoryTheory.comp_eq_hom_comp_inv_of_eq_app`): every factor is a variable, each identification a
separate equation proved by `rfl` at the concrete terms, and `subst` inside.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 08KB](https://stacks.math.columbia.edu/tag/08KB)
* [Stacks Project, Tag 08VW](https://stacks.math.columbia.edu/tag/08VW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Deformation.ToposThickening

attribute [local instance 2000] CategoryTheory.instHasWeakSheafifyOfHasSheafify
attribute [local instance 6000] IsIso.epi_of_iso IsIso.mono_of_iso
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 5000] Abelian.has_kernels Abelian.has_cokernels

-- So that the instance arguments of the terms written here are those of
-- `retraction_map_thickeningLiftPullbackQuotientMap_eq_comp_inv`.
attribute [local instance 10000]
  AlgebraicGeometry.Space.smallEtaleRingedTopos_hasSheafCompose_forget_ringCat
  AlgebraicGeometry.Space.smallEtaleRingedTopos_hasSheafCompose_forget₂_commRingCat
  AlgebraicGeometry.Space.smallEtaleRingedTopos_hasSheafCompose_forget_addCommGrpCat
  AlgebraicGeometry.Space.smallEtaleRingedTopos_hasSheafCompose_forget_commRingCat
  AlgebraicGeometry.Space.smallEtaleRingedTopos_hasWeakSheafify_addCommGrpCat
  AlgebraicGeometry.Space.smallEtaleRingedTopos_hasSheafify_addCommGrpCat
  AlgebraicGeometry.Space.smallEtaleRingedTopos_wEqualsLocallyBijective_addCommGrpCat

universe u

namespace CategoryTheory

/-- **A map followed by a component, through equalities of its two factors**: if
`ρ(q') ≫ c'_Y = R`, `q = q'` and `c = c'`, then `ρ(q) ≫ c_Y = R`. Stated with every factor a
variable, so that the two spellings of each factor are compared on their own. -/
theorem map_comp_hom_app_eq_of_eq {A M₁ M₂ : Type*} [Category* A] [Category* M₁] [Category* M₂]
    {ρ : M₁ ⥤ A} {ρ₂ : M₂ ⥤ A} {γ : M₂ ⥤ M₁} {X : M₁} {Y : M₂} {q q' : X ⟶ γ.obj Y}
    {c c' : γ ⋙ ρ ≅ ρ₂} {R : ρ.obj X ⟶ ρ₂.obj Y} (hq : q = q') (hc : c = c')
    (H : ρ.map q' ≫ c'.hom.app Y = R) : ρ.map q ≫ c.hom.app Y = R := by
  subst hq hc
  exact H

/-- **Components of `β : P ⋙ S ⋙ ρ ≅ 𝟭` read as isomorphisms**: if `L ≫ L'` is
`β_M ≫ β₂_M⁻¹`, it is `e.hom ≫ e₂.inv` for `e = β.app M` and `e₂ = β₂.app M`, with `e`, `e₂`
stated at `(S ⋙ ρ)(P M) ≅ M`. Stated with every factor a variable, so that `β.hom.app M` and
`(β.app M).hom` are compared only here. -/
theorem comp_eq_hom_comp_inv_of_eq_app {A T M₁ T₂ M₂ : Type*} [Category* A] [Category* T]
    [Category* M₁] [Category* T₂] [Category* M₂] {P : A ⥤ T} {S : T ⥤ M₁} {ρ : M₁ ⥤ A}
    {P₂ : A ⥤ T₂} {S₂ : T₂ ⥤ M₂} {ρ₂ : M₂ ⥤ A} {β : P ⋙ (S ⋙ ρ) ≅ 𝟭 A}
    {β₂ : P₂ ⋙ (S₂ ⋙ ρ₂) ≅ 𝟭 A} {M Z : A} {L : ρ.obj (S.obj (P.obj M)) ⟶ Z}
    {L' : Z ⟶ ρ₂.obj (S₂.obj (P₂.obj M))} {e : (S ⋙ ρ).obj (P.obj M) ≅ M}
    {e₂ : (S₂ ⋙ ρ₂).obj (P₂.obj M) ≅ M} (he : e = β.app M) (he₂ : e₂ = β₂.app M)
    (H : L ≫ L' = β.hom.app M ≫ β₂.inv.app M) :
    L ≫ L' = e.hom ≫ e₂.inv := by
  subst he he₂
  exact H

end CategoryTheory

namespace AlgebraicGeometry.Space.CoherentSituation

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {D : CoherentSituation B S hS} {ξ : CoherentObject D} {T' T'₂ : SchemesOver D.Y}
  {h : ξ.T ⟶ T'} {h₂ : ξ.T ⟶ T'₂} (g : T'₂ ⟶ T') (hg : h₂ ≫ g = h)
  {r : T' ⟶ ξ.T} {r₂ : T'₂ ⟶ ξ.T} (hr : h ≫ r = 𝟙 ξ.T) (hr₂ : h₂ ≫ r₂ = 𝟙 ξ.T)
  (hgr : r₂ = g ≫ r)

/-- `retraction_map_thickeningLiftPullbackQuotientMap_eq_comp_inv` with the quotient map and
`ρ_*(X_g)_* ≅ ρ₂_*` written as `thickeningLiftPullbackQuotientMap` and
`retractionPushforwardCompIso`. -/
theorem retraction_map_thickeningLiftPullbackQuotientMap_comp :
    (smallEtaleRingedToposHom B S hS
      (D.relativeSquareSituation.relativeMap r)).pushforwardModules.map
        (thickeningLiftPullbackQuotientMap g hg) ≫
      (retractionPushforwardCompIso g hgr).hom.app
        ((structureRestrict (smallEtaleRingedToposHom B S hS
          (D.relativeSquareSituation.relativeMap h₂))).obj
          ((thickenedModulesFunctor (smallEtaleRingedToposHom B S hS
            (D.relativeSquareSituation.relativeMap h₂))).obj ξ.F)) =
    (thickenedPushforwardRetractionIso (D.relativeSquareSituation.relativeMap h)
        (D.relativeSquareSituation.relativeMap r)
        (relativeMap_comp_relativeMap_retraction h r hr)).hom.app ξ.F ≫
      (thickenedPushforwardRetractionIso (D.relativeSquareSituation.relativeMap h₂)
        (D.relativeSquareSituation.relativeMap r₂)
        (relativeMap_comp_relativeMap_retraction h₂ r₂ hr₂)).inv.app ξ.F :=
  map_comp_hom_app_eq_of_eq
    (q' := (structureRestrict (smallEtaleRingedToposHom B S hS
        (D.relativeSquareSituation.relativeMap h))).map
          ((smallEtaleThickenedModulesCompIso (D.relativeSquareSituation.relativeMap h₂)
            (D.relativeSquareSituation.relativeMap g) (D.relativeSquareSituation.relativeMap h)
            (relativeMap_comp_of_comp_eq g hg)).inv.app ξ.F) ≫
        ((smallEtaleThickeningTargetOfEq (D.relativeSquareSituation.relativeMap h₂)
            (D.relativeSquareSituation.relativeMap g) (D.relativeSquareSituation.relativeMap h)
            (relativeMap_comp_of_comp_eq g hg)).restrictIso
          ((thickenedModulesFunctor (smallEtaleRingedToposHom B S hS
            (D.relativeSquareSituation.relativeMap h₂))).obj ξ.F)).inv)
    (c' := pushforwardModulesCompAt B S hS (D.relativeSquareSituation.relativeMap g)
        (D.relativeSquareSituation.relativeMap r) ≪≫
      eqToIso (congrArg (fun x : D.relativeSquareSituation.space T'₂ ⟶
          D.relativeSquareSituation.space ξ.T =>
        (smallEtaleRingedToposHom B S hS x).pushforwardModules)
        (relativeMap_comp_of_eq_comp g hgr)))
    rfl rfl (retraction_map_thickeningLiftPullbackQuotientMap_eq_comp_inv g hg hr hr₂ hgr)

/-- **The quotient square of the unit `𝒢' ⟶ (X_g)_*(X_g)^*𝒢'`, read on `X_T`**: for
`r₂ = g ≫ r`, `ρ_*` of the quotient map
`AlgebraicGeometry.Space.CoherentSituation.thickeningLiftPullbackQuotientMap` followed by
`ρ_*(X_g)_* ≅ ρ₂_*` is `ρ_*i_*𝒢 ≅ 𝒢 ≅ ρ₂_*i₂_*𝒢`, through the identifications
`AlgebraicGeometry.Space.CoherentSituation.thickenedModuleRetractionIso` of the third terms of the
extensions read on `X_T` (the associativity coherence of Stacks 03LU). -/
theorem retraction_map_thickeningLiftPullbackQuotientMap_comp_eq :
    (smallEtaleRingedToposHom B S hS
      (D.relativeSquareSituation.relativeMap r)).pushforwardModules.map
        (thickeningLiftPullbackQuotientMap g hg) ≫
      (retractionPushforwardCompIso g hgr).hom.app
        ((structureRestrict (smallEtaleRingedToposHom B S hS
          (D.relativeSquareSituation.relativeMap h₂))).obj
          ((thickenedModulesFunctor (smallEtaleRingedToposHom B S hS
            (D.relativeSquareSituation.relativeMap h₂))).obj ξ.F)) =
    (thickenedModuleRetractionIso h r hr).hom ≫ (thickenedModuleRetractionIso h₂ r₂ hr₂).inv :=
  comp_eq_hom_comp_inv_of_eq_app
    (P := thickenedModulesFunctor (smallEtaleRingedToposHom B S hS
      (D.relativeSquareSituation.relativeMap h)))
    (S := structureRestrict (smallEtaleRingedToposHom B S hS
      (D.relativeSquareSituation.relativeMap h)))
    (ρ := (smallEtaleRingedToposHom B S hS
      (D.relativeSquareSituation.relativeMap r)).pushforwardModules)
    (P₂ := thickenedModulesFunctor (smallEtaleRingedToposHom B S hS
      (D.relativeSquareSituation.relativeMap h₂)))
    (S₂ := structureRestrict (smallEtaleRingedToposHom B S hS
      (D.relativeSquareSituation.relativeMap h₂)))
    (ρ₂ := (smallEtaleRingedToposHom B S hS
      (D.relativeSquareSituation.relativeMap r₂)).pushforwardModules)
    (β := thickenedPushforwardRetractionIso (D.relativeSquareSituation.relativeMap h)
      (D.relativeSquareSituation.relativeMap r) (relativeMap_comp_relativeMap_retraction h r hr))
    (β₂ := thickenedPushforwardRetractionIso (D.relativeSquareSituation.relativeMap h₂)
      (D.relativeSquareSituation.relativeMap r₂)
      (relativeMap_comp_relativeMap_retraction h₂ r₂ hr₂))
    (M := ξ.F) (e := thickenedModuleRetractionIso h r hr)
    (e₂ := thickenedModuleRetractionIso h₂ r₂ hr₂) rfl rfl
    (retraction_map_thickeningLiftPullbackQuotientMap_comp g hg hr hr₂ hgr)

end AlgebraicGeometry.Space.CoherentSituation

end
