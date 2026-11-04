module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleRingedObjectRestriction

/-!
# Functoriality of the object restriction of the small étale site

`AlgebraicGeometry.SmallEtale.objRestrict` carries a module on the small étale site of a scheme
`S` to a module on the small étale site of the scheme `Y` of an object `U` of that site. This file
identifies it with the restriction of modules along `AlgebraicGeometry.SmallEtale.postcompose`
and proves it functorial in the object: for a morphism `g : U' ⟶ U` of the small étale site of
`S`, restricting to `Y` and then to the scheme `Y'` of `U'` over `Y` is restricting to `Y'` over
`S`.

## Main definitions

* `AlgebraicGeometry.SmallEtale.objRestrictPost`: restriction of modules along
  `AlgebraicGeometry.SmallEtale.postcompose`, the functor `Y_étale ⥤ S_étale` composing a
  structure morphism with that of `U`.
* `AlgebraicGeometry.SmallEtale.objOver`: a morphism `g : U' ⟶ U` of the small étale site of `S`,
  read as an object of the small étale site of the scheme `Y` of `U`.
* `AlgebraicGeometry.SmallEtale.postcomposeCompIso`: post-composition along `g` and then along
  `U` is post-composition along `U'`.

## Main results

* `AlgebraicGeometry.SmallEtale.objRestrictPostIso`: the restriction `𝒢 ↦ 𝒢|_{Y_étale}` is the
  restriction of modules along `AlgebraicGeometry.SmallEtale.postcompose`.
* `AlgebraicGeometry.SmallEtale.objRestrictComp`: the restriction is functorial in the object,
  `(𝒢|_{Y_étale})|_{Y'_étale} ≅ 𝒢|_{Y'_étale}` for `g : U' ⟶ U`, naturally in `𝒢`.

## References

* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Object

variable (U : SmallEtale B S hS)

/-! ### The object restriction as a restriction along post-composition -/

/-- Including the small étale site of the scheme of `U` into the localization of `S_étale` at `U`
and then forgetting the arrow to `U` is a continuous functor into `S_étale`. -/
instance isContinuous_localizationEquivalence_comp_forget :
    ((localizationEquivalence B S hS U).functor ⋙ Over.forget U).IsContinuous
      (topology B (objScheme B S hS U) (contains_objScheme B S hS U)) (topology B S hS) :=
  Functor.isContinuous_comp _ _ _ ((topology B S hS).over U) _

/-- Post-composition with the structure morphism of `U` is continuous. -/
instance isContinuous_postcompose :
    (postcompose B S hS U).IsContinuous
      (topology B (objScheme B S hS U) (contains_objScheme B S hS U)) (topology B S hS) :=
  inferInstanceAs (((localizationEquivalence B S hS U).functor ⋙ Over.forget U).IsContinuous
    (topology B (objScheme B S hS U) (contains_objScheme B S hS U)) (topology B S hS))

/-- Restriction of modules along `AlgebraicGeometry.SmallEtale.postcompose`, with the identity
comparison of structure sheaves: a module on `S_étale` read on the small étale site of the scheme
`Y` of `U`, an object of `Y_étale` being viewed over `S` through the structure morphism of `U`. -/
noncomputable abbrev objRestrictPost :
    SheafOfModules.{u} (structureSheaf B S hS) ⥤
      SheafOfModules.{u} (structureSheaf B (objScheme B S hS U)
        (contains_objScheme B S hS U)) :=
  SheafOfModules.pushforward.{u} (F := postcompose B S hS U) (𝟙 _)

/-- The restriction `AlgebraicGeometry.SmallEtale.objRestrict`, `𝒢 ↦ 𝒢|_{Y_étale}`, is the
restriction of modules along `AlgebraicGeometry.SmallEtale.postcompose`. -/
noncomputable def objRestrictPostIso :
    objRestrict B S hS U ≅ objRestrictPost B S hS U :=
  SheafOfModules.pushforwardComp.{u}
      (F := (localizationEquivalence B S hS U).functor) (G := Over.forget U)
      (𝟙 (Stacks.SheafOfModules.reindexRing
        (topology B (objScheme B S hS U) (contains_objScheme B S hS U))
        (localizationEquivalence B S hS U) ((structureSheaf B S hS).over U)))
      (𝟙 ((structureSheaf B S hS).over U)) ≪≫
    SheafOfModules.pushforwardCongr (Category.comp_id _)

end Object

section Morphism

variable {U U' : SmallEtale B S hS} (g : U' ⟶ U)

/-! ### A morphism of the site, read over the scheme of its target -/

/-- A morphism `g : U' ⟶ U` of the small étale site of `S`, read as an object of the small étale
site of the scheme `Y` of `U` through `AlgebraicGeometry.SmallEtale.localizationEquivalence`. -/
noncomputable def objOver :
    SmallEtale B (objScheme B S hS U) (contains_objScheme B S hS U) :=
  (localizationEquivalence B S hS U).inverse.obj (Over.mk g)

/-- `objOver g` has the same underlying scheme as `U'`. -/
theorem objScheme_objOver :
    objScheme B (objScheme B S hS U) (contains_objScheme B S hS U) (objOver B S hS g) =
      objScheme B S hS U' := rfl

/-- The structure morphism of `objOver g` over the scheme of `U` is the morphism of schemes
underlying `g`. -/
theorem objHom_objOver :
    objHom B (objScheme B S hS U) (contains_objScheme B S hS U) (objOver B S hS g) =
      g.hom.left.hom := rfl

/-! ### Functoriality of post-composition -/

/-- Post-composition along `g` followed by post-composition along `U` is post-composition along
`U'`. -/
noncomputable def postcomposeCompIso :
    postcompose B (objScheme B S hS U) (contains_objScheme B S hS U) (objOver B S hS g) ⋙
        postcompose B S hS U ≅
      postcompose B S hS U' :=
  NatIso.ofComponents
    (fun W ↦ ObjectProperty.isoMk (BigEtaleOver.IsEtaleOver B S hS)
      (Over.isoMk (Iso.refl _) ((Category.id_comp _).trans
        ((Category.assoc W.obj.hom g.hom.left U.obj.hom).trans
          (congrArg (fun k ↦ W.obj.hom ≫ k) (Over.w g.hom))).symm)))
    (by intros; ext; rfl)

/-- Post-composition along `g` is continuous, `objOver g` being an object of the small étale site
of the scheme of `U`. -/
instance isContinuous_postcompose_objOver :
    (postcompose B (objScheme B S hS U) (contains_objScheme B S hS U)
        (objOver B S hS g)).IsContinuous
      (topology B (objScheme B S hS U') (contains_objScheme B S hS U'))
      (topology B (objScheme B S hS U) (contains_objScheme B S hS U)) :=
  isContinuous_postcompose B (objScheme B S hS U) (contains_objScheme B S hS U)
    (objOver B S hS g)

/-- Post-composition along `g` followed by post-composition along `U` is continuous. -/
instance isContinuous_postcompose_comp :
    (postcompose B (objScheme B S hS U) (contains_objScheme B S hS U) (objOver B S hS g) ⋙
        postcompose B S hS U).IsContinuous
      (topology B (objScheme B S hS U') (contains_objScheme B S hS U')) (topology B S hS) :=
  Functor.isContinuous_comp _ _ _
    (topology B (objScheme B S hS U) (contains_objScheme B S hS U)) _

/-! ### Functoriality of the crossover -/

/-- Restricting a module on `S_étale` along the structure morphism of `U` and then along `g` is
restricting it along the structure morphism of `U'`. -/
noncomputable def objRestrictPostComp :
    objRestrictPost B S hS U ⋙
        objRestrictPost B (objScheme B S hS U) (contains_objScheme B S hS U)
          (objOver B S hS g) ≅
      objRestrictPost B S hS U' :=
  letI : (postcompose B (objScheme B S hS U) (contains_objScheme B S hS U)
        (objOver B S hS g) ⋙ postcompose B S hS U).IsContinuous
      (topology B (objScheme B (objScheme B S hS U) (contains_objScheme B S hS U)
          (objOver B S hS g))
        (contains_objScheme B (objScheme B S hS U) (contains_objScheme B S hS U)
          (objOver B S hS g)))
      (topology B S hS) := isContinuous_postcompose_comp B S hS g
  haveI := Functor.isContinuous_of_iso (postcomposeCompIso B S hS g)
    (topology B (objScheme B (objScheme B S hS U) (contains_objScheme B S hS U)
        (objOver B S hS g))
      (contains_objScheme B (objScheme B S hS U) (contains_objScheme B S hS U)
        (objOver B S hS g)))
    (topology B S hS)
  SheafOfModules.pushforwardComp.{u}
      (F := postcompose B (objScheme B S hS U) (contains_objScheme B S hS U)
        (objOver B S hS g))
      (G := postcompose B S hS U)
      (𝟙 _) (𝟙 _) ≪≫
    SheafOfModules.pushforwardCongr (Category.comp_id _) ≪≫
    SheafOfModules.pushforwardCongr₂ _ (postcomposeCompIso B S hS g).symm
      (Category.id_comp _)

/-- For a morphism `g : U' ⟶ U` of the small étale site of `S`, restricting a module on `S_étale`
to the small étale site of the scheme `Y` of `U` and then to the small étale site of the scheme of
`U'` over `Y` is restricting it to the latter over `S`, naturally in the module. -/
noncomputable def objRestrictComp :
    objRestrict B S hS U ⋙
        objRestrict B (objScheme B S hS U) (contains_objScheme B S hS U)
          (objOver B S hS g) ≅
      objRestrict B S hS U' :=
  Functor.isoWhiskerRight (objRestrictPostIso B S hS U) _ ≪≫
    Functor.isoWhiskerLeft _ (objRestrictPostIso B (objScheme B S hS U)
      (contains_objScheme B S hS U) (objOver B S hS g)) ≪≫
    objRestrictPostComp B S hS g ≪≫ (objRestrictPostIso B S hS U').symm

end Morphism

end AlgebraicGeometry.SmallEtale

end
