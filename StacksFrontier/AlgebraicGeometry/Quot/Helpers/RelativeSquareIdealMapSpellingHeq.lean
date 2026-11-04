module

public import StacksFrontier.AlgebraicGeometry.Quot.Helpers.CoherentStackRelativeIdealSquare
public import StacksFrontier.AlgebraicGeometry.Quot.Helpers.SmallEtaleModuleMapHeq

/-!
# The two spellings of the pulled-back ideals of a thickening of represented spaces

The ideal of a first order thickening `i : Z ⟶ Z'` of algebraic spaces, pulled back along
`t : T ⟶ Z'`, is written with the represented spaces `⟨yoneda.obj U, _⟩` and
`AlgebraicGeometry.Space.representedSpaceMap` in `AlgebraicGeometry.Space.affineThickeningIdeal`,
and with `AlgebraicGeometry.schemeSpaceFunctor` in the domain of
`AlgebraicGeometry.Space.thickeningIdealMap`. This module identifies the two spellings.

## Main results

* `AlgebraicGeometry.Space.toRingedToposModulesHom_pullbackModules_obj_idealOfThickening_heq`: the
  pullbacks of the ideals of heterogeneously equal first order thickenings along heterogeneously
  equal maps are heterogeneously equal.
* `AlgebraicGeometry.Space.CoherentSituation.relativeSquareIdealMap_middle_heq`: the inverse images
  along `π : X_T ⟶ T` of `λ_g`, read in the two spellings, are heterogeneously equal.

## References

* [Stacks Project, Tag 08WA](https://stacks.math.columbia.edu/tag/08WA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Deformation.ToposThickening
open Stacks.Sheaves.RingedToposModules.RingedToposHom (pullbackModules)

attribute [local instance 2000] CategoryTheory.instHasWeakSheafifyOfHasSheafify

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- For first order thickenings `i : Z ⟶ Z'` and `i₀ : Z₀ ⟶ Z₀'` of algebraic spaces,
heterogeneously equal along `Z = Z₀` and `Z' = Z₀'`, and heterogeneously equal maps `t : T ⟶ Z'`
and `t₀ : T ⟶ Z₀'`, the pullbacks `t^*𝒥` and `t₀^*𝒥₀` of the ideals are heterogeneously equal. -/
theorem toRingedToposModulesHom_pullbackModules_obj_idealOfThickening_heq
    {T Z Z' Z₀ Z₀' : AlgebraicSpaces B S hS} (eZ : Z = Z₀) (eZ' : Z' = Z₀')
    {i : Z ⟶ Z'} {i₀ : Z₀ ⟶ Z₀'} (ei : i ≍ i₀)
    (hiso : IsIso (Subfunctor.toRange i.hom))
    (hfo : IsFirstOrderThickening B S hS Z' (Subfunctor.range i.hom))
    (hiso₀ : IsIso (Subfunctor.toRange i₀.hom))
    (hfo₀ : IsFirstOrderThickening B S hS Z₀' (Subfunctor.range i₀.hom))
    {t : T ⟶ Z'} {t₀ : T ⟶ Z₀'} (et : t ≍ t₀) :
    (smallEtaleRingedToposHom B S hS t).toRingedToposModulesHom.pullbackModules.obj
        (smallEtaleRingedToposHomFirstOrderThickening B S hS i hiso hfo).idealOfThickening.I ≍
      (smallEtaleRingedToposHom B S hS t₀).toRingedToposModulesHom.pullbackModules.obj
        (smallEtaleRingedToposHomFirstOrderThickening B S hS i₀ hiso₀
          hfo₀).idealOfThickening.I := by
  subst eZ eZ'
  cases ei
  cases et
  rfl

namespace CoherentSituation

attribute [local instance] pointTopology

attribute [local instance 10000] relBaseTop_hasSheafCompose_forget_ringCat
  relBaseTop_hasSheafCompose_forget₂_commRingCat relBaseTop_hasSheafCompose_forget_addCommGrpCat
  relBaseBottom_hasSheafCompose_forget_ringCat relBaseBottom_hasSheafCompose_forget₂_commRingCat
attribute [local instance 10000] smallEtaleRingedTopos_hasSheafCompose_forget_ringCat
  smallEtaleRingedTopos_hasSheafCompose_forget₂_commRingCat
  smallEtaleRingedTopos_hasSheafCompose_forget_addCommGrpCat
  smallEtaleRingedTopos_hasSheafCompose_forget_commRingCat
  smallEtaleRingedTopos_hasWeakSheafify_addCommGrpCat
  smallEtaleRingedTopos_hasSheafify_addCommGrpCat
  smallEtaleRingedTopos_wEqualsLocallyBijective_addCommGrpCat

variable {D : CoherentSituation B S hS}
  {ξ : CoherentObject D} {T'₁ T'₂ : SchemesOver D.Y} (h₁ : ξ.T ⟶ T'₁) (h₂ : ξ.T ⟶ T'₂)
  (g : T'₂ ⟶ T'₁) (hg : h₂ ≫ g = h₁)
  (hh₁ : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h₁.left))
  (hh₂ : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h₂.left))
  [IsAffine ((BigFppfOver.toScheme B S hS).obj ξ.T.left)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T'₁.left)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T'₂.left)]

/-- The middle factor `π^*(λ_g)` of `relativeSquareIdealMap` in the two spellings: `λ_g` read
between the pullbacks `t_k^*𝒥_k` of the ideals of `AlgebraicGeometry.Space.affineThickeningIdeal`
(represented spaces), as in
`AlgebraicGeometry.Space.CoherentSituation.relativeSquareIdealMap_reduction`, and between those of
its own domain (`AlgebraicGeometry.schemeSpaceFunctor`), as in
`AlgebraicGeometry.Space.CoherentSituation.relativeSquareIdealMap`, has heterogeneously equal
inverse images along `π : X_T ⟶ T`. -/
theorem relativeSquareIdealMap_middle_heq :
    (smallEtaleRingedToposHom B S hS
        (D.relativeSquareSituation.projection ξ.T)).toRingedToposModulesHom.pullbackModules.map
        (thickeningIdealMap h₁.left h₂.left g.left (left_comp_left_eq_of_comp_eq g hg)
          (isIso_toRange_testSchemeMap h₁ hh₁)
          (isFirstOrderThickening_range_yoneda_map B S hS _ hh₁)
          (isIso_toRange_testSchemeMap h₂ hh₂)
          (isFirstOrderThickening_range_yoneda_map B S hS _ hh₂)
          hh₁ hh₂ :
          (smallEtaleRingedToposHom B S hS
              ((schemeSpaceFunctor B S hS).map h₁.left)).toRingedToposModulesHom.pullbackModules.obj
              (affineThickeningIdeal h₁.left (isIso_toRange_testSchemeMap h₁ hh₁)
                (isFirstOrderThickening_range_yoneda_map B S hS _ hh₁)).I ⟶
            (smallEtaleRingedToposHom B S hS
              ((schemeSpaceFunctor B S hS).map h₂.left)).toRingedToposModulesHom.pullbackModules.obj
              (affineThickeningIdeal h₂.left (isIso_toRange_testSchemeMap h₂ hh₂)
                (isFirstOrderThickening_range_yoneda_map B S hS _ hh₂)).I) ≍
      (smallEtaleRingedToposHom B S hS
        (D.relativeSquareSituation.projection ξ.T)).toRingedToposModulesHom.pullbackModules.map
        (thickeningIdealMap h₁.left h₂.left g.left (left_comp_left_eq_of_comp_eq g hg)
          (isIso_toRange_testSchemeMap h₁ hh₁)
          (isFirstOrderThickening_range_yoneda_map B S hS _ hh₁)
          (isIso_toRange_testSchemeMap h₂ hh₂)
          (isFirstOrderThickening_range_yoneda_map B S hS _ hh₂)
          hh₁ hh₂) :=
  toRingedToposModulesHom_pullbackModules_map_heq rfl HEq.rfl
    (toRingedToposModulesHom_pullbackModules_obj_idealOfThickening_heq rfl rfl HEq.rfl _ _ _ _
      HEq.rfl)
    (toRingedToposModulesHom_pullbackModules_obj_idealOfThickening_heq rfl rfl HEq.rfl _ _ _ _
      HEq.rfl)
    HEq.rfl

end CoherentSituation

end AlgebraicGeometry.Space

end
