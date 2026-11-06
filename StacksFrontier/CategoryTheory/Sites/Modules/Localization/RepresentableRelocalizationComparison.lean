module

public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.RelocalizationObject
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.RepresentableRelocalizationRinged

/-!
# Components of the comparisons of inverse images along a relocalization

Let `X` be a ringed site and `f : V ⟶ U` a morphism of its site. This file computes the
components of the comparisons between the inverse image of the relocalization along `h_f^#`, the
inverse image of the localization of `(Sh(C)/h_U^#, O_{h_U^#})` at the object `h_V^#/h_U^#`, and
the inverse image of the relocalization of the ringed site along `f`.

## Main results

* `representableRelocalizationObjectPullbackIso_hom_app` and
  `representableRelocalizationObjectPullbackIso_inv_app`: the components of
  `representableRelocalizationObjectPullbackIso` are the images under
  `CategoryTheory.OverShriek.sheafEquivalence` of those of
  `AlgebraicGeometry.RingedTopos.localizationAtRelocalizationObjectInverseImageIso`.
* `starIteratedSlice_relocalizeToposInverseImageIso_cancel`: the inverse of
  `CategoryTheory.starIteratedSliceForwardIsoPullback` followed by the inverse of
  `CategoryTheory.OverShriek.relocalizeToposInverseImageIso` is the inverse of
  `CategoryTheory.OverShriek.inverseImageCompSheafFunctorToOverIso`.
* `representableRelocalizationSliceInverseImageIso_hom_app`: the components of
  `representableRelocalizationSliceInverseImageIso`.
* `representableRelocalizationSheafMapCompInverseImageIso_hom_app_split`: the components of
  `representableRelocalizationSheafMapCompInverseImageIso`, split into five factors.
* `representableRelocalizationSheafMapCompInverseImageIso_hom_app`: the same components, as the
  image under `CategoryTheory.OverShriek.sheafEquivalence` of a composite of
  `AlgebraicGeometry.RingedTopos.relocalizationInverseImageSliceIso`, two counits and
  `CategoryTheory.OverShriek.inverseImageCompSheafFunctorToOverIso`.

## References

* [Stacks Project, Tag 04J4](https://stacks.math.columbia.edu/tag/04J4)
* [Stacks Project, Tag 04J5](https://stacks.math.columbia.edu/tag/04J5)
* [Stacks Project, Tag 04IL](https://stacks.math.columbia.edu/tag/04IL)
* [Stacks Project, Tag 04IR](https://stacks.math.columbia.edu/tag/04IR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u}) {U V : X.C} (f : V ⟶ U)

/-! ### The comparison at an object of the localization at `h_U^#` -/

/-- The five factors of `representableRelocalizationObjectPullbackIso` at an object: three
whiskered associators, of which the innermost is carried into `Functor.map`, and the two factors
of the underlying comparison. -/
private theorem objPullback_split (C : (representableLocalizedRingedTopos X U).Topos) :
    (representableRelocalizationObjectPullbackIso X f).hom.app C =
      𝟙 _ ≫ 𝟙 _ ≫
        (CategoryTheory.OverShriek.sheafEquivalence (U := V) X.J).inverse.map (𝟙 _) ≫
          (CategoryTheory.OverShriek.sheafEquivalence (U := V) X.J).inverse.map
              ((representableRelocalizationSliceEquivalence X f).functor.map
                ((RingedTopos.localizationInverseImageIso
                  (representableLocalizedRingedTopos X U)
                  (representableRelocalizationObject X f)).hom.app C)) ≫
            (CategoryTheory.OverShriek.sheafEquivalence (U := V) X.J).inverse.map
              ((representableRelocalizationStarIso X f).hom.app C) :=
  rfl

/-- `objPullback_split` for the inverse comparison. -/
private theorem objPullback_inv_split (C : (representableLocalizedRingedTopos X U).Topos) :
    (representableRelocalizationObjectPullbackIso X f).inv.app C =
      ((((CategoryTheory.OverShriek.sheafEquivalence (U := V) X.J).inverse.map
                ((representableRelocalizationStarIso X f).inv.app C) ≫
              (CategoryTheory.OverShriek.sheafEquivalence (U := V) X.J).inverse.map
                ((representableRelocalizationSliceEquivalence X f).functor.map
                  ((RingedTopos.localizationInverseImageIso
                    (representableLocalizedRingedTopos X U)
                    (representableRelocalizationObject X f)).inv.app C))) ≫
            (CategoryTheory.OverShriek.sheafEquivalence (U := V) X.J).inverse.map (𝟙 _)) ≫
          𝟙 _) ≫ 𝟙 _ :=
  rfl

/-- The three factors of `localizationAtRelocalizationObjectInverseImageIso` at an object. -/
private theorem atObj_split (C : (representableLocalizedRingedTopos X U).Topos) :
    (X.ringedTopos.localizationAtRelocalizationObjectInverseImageIso
          (X.representableSheafMap f)).hom.app C =
      𝟙 _ ≫
        (representableRelocalizationSliceEquivalence X f).functor.map
            ((RingedTopos.localizationInverseImageIso
              (representableLocalizedRingedTopos X U)
              (representableRelocalizationObject X f)).hom.app C) ≫
          (representableRelocalizationStarIso X f).hom.app C :=
  rfl

/-- `atObj_split` for the inverse comparison. -/
private theorem atObj_inv_split (C : (representableLocalizedRingedTopos X U).Topos) :
    (X.ringedTopos.localizationAtRelocalizationObjectInverseImageIso
          (X.representableSheafMap f)).inv.app C =
      ((representableRelocalizationStarIso X f).inv.app C ≫
          (representableRelocalizationSliceEquivalence X f).functor.map
            ((RingedTopos.localizationInverseImageIso
              (representableLocalizedRingedTopos X U)
              (representableRelocalizationObject X f)).inv.app C)) ≫ 𝟙 _ :=
  rfl

/-- The component at an object of the localization at `h_U^#` of the comparison
`representableRelocalizationObjectPullbackIso` of the inverse image of the localization at
`h_V^#/h_U^#` with base change along `h_f^#` is the identification
`CategoryTheory.OverShriek.sheafEquivalence` of `Sh(C)/h_V^#` with `Sh(C/V)` applied to
`AlgebraicGeometry.RingedTopos.localizationAtRelocalizationObjectInverseImageIso`. -/
theorem representableRelocalizationObjectPullbackIso_hom_app
    (C : (representableLocalizedRingedTopos X U).Topos) :
    (representableRelocalizationObjectPullbackIso X f).hom.app C =
      (CategoryTheory.OverShriek.sheafEquivalence (U := V) X.J).inverse.map
        ((X.ringedTopos.localizationAtRelocalizationObjectInverseImageIso
          (X.representableSheafMap f)).hom.app C) := by
  rw [objPullback_split, atObj_split]
  simp only [Category.id_comp, ← Functor.map_comp]
  rfl

/-- `representableRelocalizationObjectPullbackIso_hom_app` for the inverse comparison. -/
theorem representableRelocalizationObjectPullbackIso_inv_app
    (C : (representableLocalizedRingedTopos X U).Topos) :
    (representableRelocalizationObjectPullbackIso X f).inv.app C =
      (CategoryTheory.OverShriek.sheafEquivalence (U := V) X.J).inverse.map
        ((X.ringedTopos.localizationAtRelocalizationObjectInverseImageIso
          (X.representableSheafMap f)).inv.app C) := by
  rw [objPullback_inv_split, atObj_inv_split]
  simp only [Category.comp_id, ← Functor.map_comp]
  rfl

/-! ### The comparison in the slice direction -/

/-- The inverse of the iterated-slice comparison `starIteratedSliceForwardIsoPullback` of the
product with `h_V^#/h_U^#` with base change along `h_f^#`, followed by the inverse of the
description `CategoryTheory.OverShriek.relocalizeToposInverseImageIso` of the relocalization's
inverse image, is the inverse of `CategoryTheory.OverShriek.inverseImageCompSheafFunctorToOverIso`.
-/
theorem starIteratedSlice_relocalizeToposInverseImageIso_cancel
    (D : Sheaf (X.J.over U) (Type u)) :
    (starIteratedSliceForwardIsoPullback (representableSheafMap X f)).inv.app
          ((CategoryTheory.OverShriek.sheafFunctorToOver (U := U) X.J).obj D) ≫
        (CategoryTheory.OverShriek.relocalizeToposInverseImageIso f X.J).inv.app D =
      (CategoryTheory.OverShriek.inverseImageCompSheafFunctorToOverIso f X.J).inv.app D :=
  Eq.trans
    (congrArg (fun z => (starIteratedSliceForwardIsoPullback (representableSheafMap X f)).inv.app
        ((CategoryTheory.OverShriek.sheafFunctorToOver (U := U) X.J).obj D) ≫ z)
      (show (CategoryTheory.OverShriek.relocalizeToposInverseImageIso f X.J).inv.app D =
          (starIteratedSliceForwardIsoPullback (representableSheafMap X f)).hom.app
              ((CategoryTheory.OverShriek.sheafFunctorToOver (U := U) X.J).obj D) ≫
            (CategoryTheory.OverShriek.inverseImageCompSheafFunctorToOverIso f X.J).inv.app D from
        rfl))
    (Eq.trans (Category.assoc _ _ _).symm
      (Eq.trans
        (congrArg (fun z => z ≫
            (CategoryTheory.OverShriek.inverseImageCompSheafFunctorToOverIso f X.J).inv.app D)
          ((starIteratedSliceForwardIsoPullback (representableSheafMap X f)).inv_hom_id_app
            ((CategoryTheory.OverShriek.sheafFunctorToOver (U := U) X.J).obj D)))
        (Category.id_comp _)))

/-- The four factors of `representableRelocalizationSliceInverseImageIso` at an object. -/
private theorem sliceISI_split (D : Sheaf (X.J.over U) (Type u)) :
    (representableRelocalizationSliceInverseImageIso X f).hom.app D =
      (X.ringedTopos.localizationAtRelocalizationObjectInverseImageIso
            (X.representableSheafMap f)).hom.app
          ((X.representableLocalizationEquivalence U).functor.obj D) ≫
        (Over.pullback (representableSheafMap X f)).map
            ((representableSliceEquivalence X U).counitIso.hom.app
              ((CategoryTheory.OverShriek.sheafFunctorToOver (U := U) X.J).obj D)) ≫
          (starIteratedSliceForwardIsoPullback (representableSheafMap X f)).inv.app
              ((CategoryTheory.OverShriek.sheafFunctorToOver (U := U) X.J).obj D) ≫
            (CategoryTheory.OverShriek.relocalizeToposInverseImageIso f X.J).inv.app D := by
  refine Eq.trans ?_ (CategoryTheory.whisker_eq _ (Category.id_comp _))
  rfl

/-- The component of `representableRelocalizationSliceInverseImageIso` at a sheaf on `C/U` is
`AlgebraicGeometry.RingedTopos.localizationAtRelocalizationObjectInverseImageIso` at the
corresponding object of the localization at `h_U^#`, followed by base change along `h_f^#`
applied to the counit of `representableSliceEquivalence X U`, followed by
`CategoryTheory.OverShriek.inverseImageCompSheafFunctorToOverIso`. -/
theorem representableRelocalizationSliceInverseImageIso_hom_app
    (D : Sheaf (X.J.over U) (Type u)) :
    (representableRelocalizationSliceInverseImageIso X f).hom.app D =
      (X.ringedTopos.localizationAtRelocalizationObjectInverseImageIso
            (X.representableSheafMap f)).hom.app
          ((X.representableLocalizationEquivalence U).functor.obj D) ≫
        (Over.pullback (representableSheafMap X f)).map
            ((representableSliceEquivalence X U).counitIso.hom.app
              ((CategoryTheory.OverShriek.sheafFunctorToOver (U := U) X.J).obj D)) ≫
          (CategoryTheory.OverShriek.inverseImageCompSheafFunctorToOverIso f X.J).inv.app D := by
  rw [sliceISI_split, starIteratedSlice_relocalizeToposInverseImageIso_cancel]

/-! ### The comparison for a morphism of sheaves -/

/-- The component of `representableRelocalizationSheafMapCompInverseImageIso` at an object of the
localization at `h_U^#` is the composite of the base-change comparison
`AlgebraicGeometry.RingedTopos.relocalizationInverseImageSliceIso`, the inverse of
`representableRelocalizationObjectPullbackIso`, the counit of
`representableLocalizationEquivalence U`, `representableRelocalizationSliceInverseImageIso`, and
the inverse unit of `CategoryTheory.OverShriek.sheafEquivalence` at `V`. -/
theorem representableRelocalizationSheafMapCompInverseImageIso_hom_app_split
    (C : (representableLocalizedRingedTopos X U).Topos) :
    (representableRelocalizationSheafMapCompInverseImageIso X f).hom.app C =
      (CategoryTheory.OverShriek.sheafEquivalence (U := V) X.J).inverse.map
          ((RingedTopos.relocalizationInverseImageSliceIso X.ringedTopos
            (representableSheafMap X f)).hom.app C) ≫
        (representableRelocalizationObjectPullbackIso X f).inv.app C ≫
          (CategoryTheory.OverShriek.sheafEquivalence (U := V) X.J).inverse.map
              (((representableRelocalizationToposLocalization X f).inverseImage ⋙
                  ((RingedTopos.localizationEquivalence (representableLocalizedRingedTopos X U)
                      (representableRelocalizationObject X f)).functor ⋙
                    (representableRelocalizationSliceEquivalence X f).functor)).map
                ((X.representableLocalizationEquivalence U).counitIso.inv.app C)) ≫
            (CategoryTheory.OverShriek.sheafEquivalence (U := V) X.J).inverse.map
                ((representableRelocalizationSliceInverseImageIso X f).hom.app
                  ((X.representableLocalizationEquivalence U).inverse.obj C)) ≫
              (CategoryTheory.OverShriek.sheafEquivalence (U := V) X.J).unitInv.app
                ((X.relocalizationRingedToposHom f).toToposHom.inverseImage.obj
                  ((X.representableLocalizationEquivalence U).inverse.obj C)) :=
  rfl

set_option maxHeartbeats 1000000 in
/-- `representableRelocalizationSheafMapCompInverseImageIso_hom_app_split` with every factor
written through `CategoryTheory.OverShriek.sheafEquivalence`, and in the spelling of
`AlgebraicGeometry.RingedTopos.localizationAtRelocalizationObjectInverseImageIso`. -/
private theorem hom_app_split_uniform (C : (representableLocalizedRingedTopos X U).Topos) :
    (representableRelocalizationSheafMapCompInverseImageIso X f).hom.app C =
      ((CategoryTheory.OverShriek.sheafEquivalence (U := V) X.J).inverse.map
            ((RingedTopos.relocalizationInverseImageSliceIso X.ringedTopos
              (representableSheafMap X f)).hom.app C) ≫
          (CategoryTheory.OverShriek.sheafEquivalence (U := V) X.J).inverse.map
              ((X.ringedTopos.localizationAtRelocalizationObjectInverseImageIso
                (X.representableSheafMap f)).inv.app C) ≫
            (((CategoryTheory.OverShriek.sheafEquivalence (U := V) X.J).inverse.map
                (((RingedTopos.localizationMorphism
                        (RingedTopos.localizedRingedTopos X.ringedTopos
                          (representableSheaf X U))
                        (X.ringedTopos.relocalizationObject
                          (representableSheafMap X f))).toToposHom.inverseImage ⋙
                    (RingedTopos.localizationEquivalence
                        (RingedTopos.localizedRingedTopos X.ringedTopos
                          (representableSheaf X U))
                        (X.ringedTopos.relocalizationObject
                          (representableSheafMap X f))).functor ⋙
                      (X.ringedTopos.relocalizationSliceEquivalence
                        (representableSheafMap X f)).functor).map
                  ((X.representableLocalizationEquivalence U).counitIso.inv.app C))) : _) ≫
              (CategoryTheory.OverShriek.sheafEquivalence (U := V) X.J).inverse.map
                ((X.ringedTopos.localizationAtRelocalizationObjectInverseImageIso
                      (X.representableSheafMap f)).hom.app
                    (((X.representableLocalizationEquivalence U).inverse ⋙
                      (X.representableLocalizationEquivalence U).functor).obj C) ≫
                  (Over.pullback (representableSheafMap X f)).map
                      ((RingedTopos.localizationEquivalence X.ringedTopos
                          (representableSheaf X U)).counitIso.hom.app
                        ((CategoryTheory.OverShriek.sheafFunctorToOver (U := U) X.J).obj
                          ((X.representableLocalizationEquivalence U).inverse.obj C))) ≫
                    (CategoryTheory.OverShriek.inverseImageCompSheafFunctorToOverIso
                        f X.J).inv.app
                      ((X.representableLocalizationEquivalence U).inverse.obj C))) ≫
        (CategoryTheory.OverShriek.sheafEquivalence (U := V) X.J).unitInv.app
          ((X.relocalizationRingedToposHom f).toToposHom.inverseImage.obj
            ((X.representableLocalizationEquivalence U).inverse.obj C)) := by
  rw [representableRelocalizationSheafMapCompInverseImageIso_hom_app_split]
  simp only [representableRelocalizationObjectPullbackIso_inv_app,
    representableRelocalizationSliceInverseImageIso_hom_app]
  rfl

/-- The component of `representableRelocalizationSheafMapCompInverseImageIso` at an object `C` of
the localization at `h_U^#` is the identification `CategoryTheory.OverShriek.sheafEquivalence` of
`Sh(C)/h_V^#` with `Sh(C/V)` applied to: the base-change comparison
`AlgebraicGeometry.RingedTopos.relocalizationInverseImageSliceIso` at `C`, then base change along
`h_f^#` applied to the counit of `representableLocalizationEquivalence U` followed by the counit
of the localization equivalence at `h_U^#`, then
`CategoryTheory.OverShriek.inverseImageCompSheafFunctorToOverIso`; followed by the inverse unit
of `CategoryTheory.OverShriek.sheafEquivalence` at `V`. -/
theorem representableRelocalizationSheafMapCompInverseImageIso_hom_app
    (C : (representableLocalizedRingedTopos X U).Topos) :
    (representableRelocalizationSheafMapCompInverseImageIso X f).hom.app C =
      (CategoryTheory.OverShriek.sheafEquivalence (U := V) X.J).inverse.map
          ((RingedTopos.relocalizationInverseImageSliceIso X.ringedTopos
                (representableSheafMap X f)).hom.app C ≫
            (Over.pullback (representableSheafMap X f)).map
                ((RingedTopos.localizationEquivalence X.ringedTopos
                      (representableSheaf X U)).functor.map
                    ((X.representableLocalizationEquivalence U).counitIso.inv.app C) ≫
                  (RingedTopos.localizationEquivalence X.ringedTopos
                      (representableSheaf X U)).counitIso.hom.app
                    ((CategoryTheory.OverShriek.sheafFunctorToOver (U := U) X.J).obj
                      ((X.representableLocalizationEquivalence U).inverse.obj C))) ≫
              (CategoryTheory.OverShriek.inverseImageCompSheafFunctorToOverIso f X.J).inv.app
                ((X.representableLocalizationEquivalence U).inverse.obj C)) ≫
        (CategoryTheory.OverShriek.sheafEquivalence (U := V) X.J).unitInv.app
          ((X.relocalizationRingedToposHom f).toToposHom.inverseImage.obj
            ((X.representableLocalizationEquivalence U).inverse.obj C)) := by
  rw [hom_app_split_uniform]
  refine CategoryTheory.eq_whisker ?_ _
  simp only [← Functor.map_comp]
  refine congrArg (CategoryTheory.OverShriek.sheafEquivalence (U := V) X.J).inverse.map ?_
  refine CategoryTheory.whisker_eq _ ?_
  rw [NatTrans.naturality_assoc]
  simp only [Functor.id_obj]
  rw [Iso.inv_hom_id_app_assoc]
  exact (Functor.map_comp_assoc (Over.pullback (representableSheafMap X f)) _ _ _).symm

end AlgebraicGeometry.RingedSite

end
