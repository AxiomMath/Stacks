module

public import StacksFrontier.AlgebraicGeometry.Recovery04IH.LocalizationMorphismsLocallyRinged
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeTopos
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.RepresentableLocalization
public import StacksFrontier.CategoryTheory.Sites.Modules.RelocalizationTriangle

/-!
# Relocalizing a ringed site and relocalizing its ringed topos at a representable sheaf

Let `(C, J, O)` be a ringed site and `f : V ⟶ U` a morphism of `C`. There are two relocalization
triangles over `(Sh(C, J), O)`:

* the one of Stacks 04IY, built from the localizations of the ringed *site* at `V` and at `U`,
  whose upper edge is restriction along `Over.map f`;
* the one of Stacks 04J4, built from the localizations of the ringed *topos* at the sheaves
  `h_V^#` and `h_U^#`, whose upper edge is the localization of `(Sh(C)/h_U^#, O_{h_U^#})` at the
  object `h_V^#/h_U^#`.

Stacks 04J5 says that these two triangles agree via the identifications of Stacks 04J3 of the
localization of the ringed site at an object with the localization of its ringed topos at the
associated sheaf. This file proves both halves of that assertion: the agreement of the upper
edges on inverse images, and the agreement of their structure maps.

## Main definitions

* `AlgebraicGeometry.RingedSite.representableSheafMap`: the map `h_V^# ⟶ h_U^#` of associated
  sheaves induced by `f`.
* `AlgebraicGeometry.RingedSite.representableRelocalizationObject`: the object `h_V^#/h_U^#` of
  the localization of the ringed topos at `h_U^#`.
* `AlgebraicGeometry.RingedSite.representableRelocalizationEquivalence`: the identification of
  the topos of the localization at `h_V^#/h_U^#` with `Sh(C/V)`, obtained from Stacks 04IE's
  slice identification, the iterated slice equivalence and Stacks 00Y1.

## Main results

* `AlgebraicGeometry.RingedSite.representableRelocalizationInverseImageIso`: **Stacks 04J5** on
  inverse images. Read through the identification of Stacks 04J3 at `U` and the identification
  above at `V`, the inverse image of the localization of `(Sh(C)/h_U^#, O_{h_U^#})` at
  `h_V^#/h_U^#` is the inverse image of the relocalization of the ringed site along `f`.
* `AlgebraicGeometry.RingedSite.representableRelocalization_fSharpSet`: **Stacks 04J5** on
  structure maps. The two upper edges have the same structure map, both being the identity on
  underlying sheaves of sets.

## Implementation notes

The comparison of inverse images is assembled from three existing descriptions and no new
computation. Stacks 04IE describes the inverse image of a localization of a ringed topos at a
sheaf as `toOver` of that sheaf; Stacks 04IR identifies `toOver` of `h_V^#/h_U^#`, transported
through the slice identification and the iterated slice equivalence, with base change along
`h_f^#`; and Stacks 04IS identifies that base change with restriction along `Over.map f`.

`representableRelocalizationStarIso` is the second of those three steps. It is proved by
uniqueness of right adjoints: the left adjoint of `toOver (h_V^#/h_U^#)` followed by the
transport is `Over.map h_f^#` followed by the slice identification, on the nose, so no
coherence is left over.

That the two structure maps agree is the assertion of Stacks 04J5 which does not follow from
Stacks 04IS. Both are the identity on underlying sheaves of sets: the structure sheaf of a
localization is the restriction of the structure sheaf along the relevant functor of sites in
both presentations, so the comparison of the inverse image with it is the identity once the
ring operations are forgotten.

Universes follow Stacks 04J3: site objects, site morphisms and sections of `O` are taken in one
universe `u`, which is what Stacks 0791 needs in order to return a sheaf equivalence.

## References

* [Stacks Project, Tag 04J5](https://stacks.math.columbia.edu/tag/04J5)
* [Stacks Project, Tag 04IS](https://stacks.math.columbia.edu/tag/04IS)
* [Stacks Project, Tag 04IY](https://stacks.math.columbia.edu/tag/04IY)
* [Stacks Project, Tag 04J3](https://stacks.math.columbia.edu/tag/04J3)
* [Stacks Project, Tag 04J4](https://stacks.math.columbia.edu/tag/04J4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.RingedSite

universe u

variable (X : RingedSite.{u, u, u})

/-- The map `h_V^# ⟶ h_U^#` of associated sheaves induced by a morphism `f : V ⟶ U`. -/
noncomputable abbrev representableSheafMap {U V : X.C} (f : V ⟶ U) :
    representableSheaf X V ⟶ representableSheaf X U :=
  (presheafToSheaf X.J (Type u)).map (yoneda.map f)

/-- The identification of the localization of the ringed topos at `h_U^#` with the slice topos
`Sh(C)/h_U^#`. -/
noncomputable abbrev representableSliceEquivalence (U : X.C) :
    (RingedTopos.localizedRingedTopos X.ringedTopos (representableSheaf X U)).Topos ≌
      Over (representableSheaf X U) :=
  RingedTopos.localizationEquivalence X.ringedTopos (representableSheaf X U)

/-- The object `h_V^#/h_U^#` of the localization of the ringed topos at `h_U^#`: the object
`h_V^# ⟶ h_U^#` of the slice topos, read through the identification of Stacks 04IE. -/
noncomputable def representableRelocalizationObject {U V : X.C} (f : V ⟶ U) :
    (RingedTopos.localizedRingedTopos X.ringedTopos (representableSheaf X U)).Topos :=
  (representableSliceEquivalence X U).inverse.obj (Over.mk (representableSheafMap X f))

/-- Slices at `h_V^#/h_U^#` are slices at `h_V^#`: the slice of the localization at `h_U^#` at
the object `h_V^#/h_U^#` is the slice of `Sh(C)/h_U^#` at `h_V^# ⟶ h_U^#`, which is `Sh(C)/h_V^#`
by the iterated slice equivalence. -/
noncomputable def representableRelocalizationSliceEquivalence {U V : X.C} (f : V ⟶ U) :
    Over (representableRelocalizationObject X f) ≌ Over (representableSheaf X V) :=
  (Over.postEquiv (X := representableRelocalizationObject X f)
      (representableSliceEquivalence X U)).trans
    ((Over.mapIso
        ((representableSliceEquivalence X U).counitIso.app
          (Over.mk (representableSheafMap X f)))).trans
      (Over.mk (representableSheafMap X f)).iteratedSliceEquiv)

/-- Postcomposition with `h_f^#`, followed by the identification of `Sh(C)/h_U^#` with the
localization at `h_U^#`, is the forgetful functor of the slice at `h_V^#/h_U^#` read through
`representableRelocalizationSliceEquivalence`. The two functors agree on the nose: both send
`(A ⟶ h_V^#)` to the fibre construction applied to `(A ⟶ h_V^# ⟶ h_U^#)`. -/
noncomputable def representableRelocalizationForgetIso {U V : X.C} (f : V ⟶ U) :
    Over.map (representableSheafMap X f) ⋙ (representableSliceEquivalence X U).inverse ≅
      (representableRelocalizationSliceEquivalence X f).inverse ⋙
        Over.forget (representableRelocalizationObject X f) :=
  Iso.refl _

/-- **The inverse image of the localization at `h_V^#/h_U^#` is base change along `h_f^#`.**
Taking the product with `h_V^#/h_U^#` and transporting the result to `Sh(C)/h_V^#` is base
change along `h_f^#` composed with the identification of the localization at `h_U^#` with
`Sh(C)/h_U^#`. Both functors are right adjoint to `representableRelocalizationForgetIso`'s two
equal left adjoints. -/
noncomputable def representableRelocalizationStarIso {U V : X.C} (f : V ⟶ U) :
    toOver (representableRelocalizationObject X f) ⋙
        (representableRelocalizationSliceEquivalence X f).functor ≅
      (representableSliceEquivalence X U).functor ⋙
        Over.pullback (representableSheafMap X f) :=
  Adjunction.rightAdjointUniq
    (((representableRelocalizationSliceEquivalence X f).symm.toAdjunction.comp
        (forgetAdjToOver (representableRelocalizationObject X f))).ofNatIsoLeft
      (representableRelocalizationForgetIso X f).symm)
    ((Over.mapPullbackAdj (representableSheafMap X f)).comp
      (representableSliceEquivalence X U).symm.toAdjunction)

/-- **The identification of the localization at `h_V^#/h_U^#` with `Sh(C/V)`**: the slice
identification of Stacks 04IE, the iterated slice equivalence, and Stacks 00Y1's identification
of `Sh(C)/h_V^#` with `Sh(C/V)`. -/
noncomputable def representableRelocalizationEquivalence {U V : X.C} (f : V ⟶ U) :
    (RingedTopos.localizedRingedTopos
        (RingedTopos.localizedRingedTopos X.ringedTopos (representableSheaf X U))
        (representableRelocalizationObject X f)).Topos ≌ Sheaf (X.J.over V) (Type u) :=
  (RingedTopos.localizationEquivalence
      (RingedTopos.localizedRingedTopos X.ringedTopos (representableSheaf X U))
      (representableRelocalizationObject X f)).trans
    ((representableRelocalizationSliceEquivalence X f).trans
      (CategoryTheory.OverShriek.sheafEquivalence (U := V) X.J).symm)

/-- The comparison of inverse images with values in the slice topos `Sh(C)/h_V^#`, before it is
carried to `Sh(C/V)` by Stacks 00Y1. -/
noncomputable def representableRelocalizationSliceInverseImageIso {U V : X.C} (f : V ⟶ U) :
    (X.representableLocalizationEquivalence U).functor ⋙
        ((RingedTopos.localizationMorphism
            (RingedTopos.localizedRingedTopos X.ringedTopos (representableSheaf X U))
            (representableRelocalizationObject X f)).toToposHom.inverseImage ⋙
          (RingedTopos.localizationEquivalence
              (RingedTopos.localizedRingedTopos X.ringedTopos (representableSheaf X U))
              (representableRelocalizationObject X f)).functor ⋙
            (representableRelocalizationSliceEquivalence X f).functor) ≅
      (X.relocalizationRingedToposHom f).toToposHom.inverseImage ⋙
        CategoryTheory.OverShriek.sheafFunctorToOver (U := V) X.J :=
  Functor.isoWhiskerLeft _
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          (RingedTopos.localizationInverseImageIso
            (RingedTopos.localizedRingedTopos X.ringedTopos (representableSheaf X U))
            (representableRelocalizationObject X f))
          (representableRelocalizationSliceEquivalence X f).functor ≪≫
        representableRelocalizationStarIso X f) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (CategoryTheory.OverShriek.sheafFunctorToOver (U := U) X.J)
          (representableSliceEquivalence X U).counitIso ≪≫
        Functor.rightUnitor _) (Over.pullback (representableSheafMap X f)) ≪≫
    Functor.isoWhiskerLeft (CategoryTheory.OverShriek.sheafFunctorToOver (U := U) X.J)
      (starIteratedSliceForwardIsoPullback (representableSheafMap X f)).symm ≪≫
    (CategoryTheory.OverShriek.relocalizeToposInverseImageIso f X.J).symm

/-- **Stacks 04J5**, on inverse images. Read through the identification of Stacks 04J3 of
`Sh(C/U)` with the localization of the ringed topos at `h_U^#`, and through the identification
of the localization at `h_V^#/h_U^#` with `Sh(C/V)`, the inverse image of the localization of
`(Sh(C)/h_U^#, O_{h_U^#})` at the object `h_V^#/h_U^#` is the inverse image of the
relocalization of the ringed site along `f : V ⟶ U`. -/
@[stacks 04J5 "the two relocalizations have the same inverse image, via the identifications
  of 04J3"]
noncomputable def representableRelocalizationInverseImageIso {U V : X.C} (f : V ⟶ U) :
    (X.representableLocalizationEquivalence U).functor ⋙
        (RingedTopos.localizationMorphism
            (RingedTopos.localizedRingedTopos X.ringedTopos (representableSheaf X U))
            (representableRelocalizationObject X f)).toToposHom.inverseImage ⋙
          (representableRelocalizationEquivalence X f).functor ≅
      (X.relocalizationRingedToposHom f).toToposHom.inverseImage :=
  Functor.isoWhiskerLeft _
      (Functor.isoWhiskerLeft _ (Functor.associator _ _ _).symm ≪≫
        (Functor.associator _ _ _).symm) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (representableRelocalizationSliceInverseImageIso X f)
      (CategoryTheory.OverShriek.sheafEquivalence (U := V) X.J).inverse ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (CategoryTheory.OverShriek.sheafEquivalence (U := V) X.J).unitIso.symm ≪≫
    Functor.rightUnitor _

/-- **Stacks 04J5**, on direct images. Read through the same two identifications, the direct
image of the localization of `(Sh(C)/h_U^#, O_{h_U^#})` at `h_V^#/h_U^#` is the direct image of
the relocalization of the ringed site along `f : V ⟶ U`. The two inverse images agree, so the
two direct images agree by uniqueness of right adjoints. -/
@[stacks 04J5 "the two relocalizations have the same direct image"]
noncomputable def representableRelocalizationPushforwardIso {U V : X.C} (f : V ⟶ U) :
    ((representableRelocalizationEquivalence X f).inverse ⋙
          (RingedTopos.localizationMorphism
            (RingedTopos.localizedRingedTopos X.ringedTopos (representableSheaf X U))
            (representableRelocalizationObject X f)).toToposHom.pushforward) ⋙
        (X.representableLocalizationEquivalence U).inverse ≅
      (X.relocalizationRingedToposHom f).toToposHom.pushforward :=
  Adjunction.rightAdjointUniq
    (((X.representableLocalizationEquivalence U).toAdjunction.comp
        ((RingedTopos.localizationMorphism
              (RingedTopos.localizedRingedTopos X.ringedTopos (representableSheaf X U))
              (representableRelocalizationObject X f)).toToposHom.adj.comp
          (representableRelocalizationEquivalence X f).toAdjunction)).ofNatIsoLeft
      (representableRelocalizationInverseImageIso X f))
    (X.relocalizationRingedToposHom f).toToposHom.adj

/-- **Stacks 04J5**, on structure maps: the two relocalizations have the same structure map
`j^♯`, both being the identity on underlying sheaves of sets. For the localization of the ringed
topos at `h_V^#/h_U^#` the structure sheaf is the restriction of `O_{h_U^#}` along the
projection from the site of elements, and for the relocalization of the ringed site it is the
restriction of `O|_U` along `Over.map f`; in both cases the structure map is the comparison of
an inverse image with that restriction, which is the identity on sections. -/
@[stacks 04J5 "the two maps j^sharp agree, both being the identity"]
theorem representableRelocalization_fSharpSet {U V : X.C} (f : V ⟶ U) :
    RingedToposHom.fSharpSet
          (RingedTopos.localizationMorphism
            (RingedTopos.localizedRingedTopos X.ringedTopos (representableSheaf X U))
            (representableRelocalizationObject X f)) =
        𝟙 ((RingedTopos.localizationMorphism
              (RingedTopos.localizedRingedTopos X.ringedTopos (representableSheaf X U))
              (representableRelocalizationObject X f)).toToposHom.inverseImage.obj
            ((RingedTopos.localizedRingedTopos X.ringedTopos
              (representableSheaf X U)).forgetRing.obj
                (RingedTopos.localizedRingedTopos X.ringedTopos (representableSheaf X U)).O)) ∧
      RingedToposHom.fSharpSet (X.relocalizationRingedToposHom f) =
        𝟙 ((X.relocalizationRingedToposHom f).toToposHom.inverseImage.obj
          ((ringedTopos (X.over U)).forgetRing.obj (X.over U).O)) :=
  ⟨RingedTopos.fSharpSet_localizationMorphism _ _, X.fSharpSet_relocalizationRingedToposHom f⟩

end AlgebraicGeometry.RingedSite

end
