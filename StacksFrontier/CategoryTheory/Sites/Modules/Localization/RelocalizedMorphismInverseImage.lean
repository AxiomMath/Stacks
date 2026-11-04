module

public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.LocalizedRepresentableTwoIso
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.RelocalizedNaturalitySquare
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.RepresentableRelocalizationRinged
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 04J9 on inverse images

Let `(f, f♯) : (C, O) ⟶ (D, O')` be a morphism of ringed sites, `V` an object of `D`, `U` an
object of `C` and `c : U ⟶ u(V)` a morphism of `C`. Stacks 04J1 relocalizes the morphism of
ringed *sites* to `f_c`, and Stacks 04J8 relocalizes the morphism of ringed *topoi* to `f_s`
along the map `s : h_U^# ⟶ f^{-1}h_V^#` that `c` induces. Stacks 04J9 says that the two
resulting squares agree through the identifications of Stacks 04J3.

This file proves the part of that assertion which needs no coherence between the comparisons
and the structure maps: the two relocalized morphisms **have the same inverse image**. The
comparison is pasted from Stacks 04J5 on inverse images and Stacks 04J7 on inverse images, both
of which hold unconditionally, and the pasting is strict — the inverse image of a composite of
morphisms of ringed topoi is the composite of the inverse images on the nose, so the associators
of the paste are identities and only two whiskerings remain.

## Main definitions

* `AlgebraicGeometry.RingedSite.Hom.relocCompareInverseImageIso`: Stacks 04J5's comparison of the
  two relocalizations, in the sheaf-morphism description, at the map `s` that Stacks 04J9
  relocalizes at rather than at the representable map `h_c^#`.
* `AlgebraicGeometry.RingedSite.Hom.relocalizedCompInverseImageIso`: **Stacks 04J9** on inverse
  images.

## Implementation notes

`Hom.compareMid` and `Hom.relocalizationSheafMap` are composites, and the inverse image of each
is the corresponding composite of inverse images by `rfl`. These equations are stated as the
theorems `Hom.compareMid_relocalization_inverseImage_eq` and
`Hom.relocalizationSheafMap_inverseImage_eq`, so that the comparison is built from `eqToIso`s
between closed terms.

An inverse-image comparison is not yet a 2-isomorphism of ringed topoi, which also asks that the
comparison carry the structure map of the one composite to that of the other, and Stacks 04J9
asks further that the two localization squares agree under it. The form of the full assertion
that takes these compatibilities as hypotheses is
`AlgebraicGeometry.RingedSite.Hom.exists_relocalizedComparison`; the part of Stacks 04J9 on
structure maps is `AlgebraicGeometry.RingedSite.Hom.relocalized_fSharpInverseImage_forget`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.RingedToposHom

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] AlgebraicGeometry.RingedTopos.isContinuous_elementPostcomp
  AlgebraicGeometry.RingedTopos.isCocontinuous_elementPostcomp
  CategoryTheory.Functor.isContinuous_overPost_of_isContinuous

variable {X Y : RingedSite.{u, u, u}} (f : RingedSite.Hom X Y) {V : Y.C} {U : X.C}
  (c : U ⟶ f.u.obj V)

/-- **The inverse image of the middle identification composed with the relocalization of the
ringed site.** `Hom.compareMid` is the identification of Stacks 04J3 at `u(V)` followed by the
relocalization of Stacks 04J4 along Stacks 04D3's isomorphism, so its inverse image preceded by
that of the relocalization of Stacks 04IY along `c` splits off the relocalization as a left
factor. -/
theorem Hom.compareMid_relocalization_inverseImage_eq :
    (AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos (X.over U))
        (Y := ringedTopos (X.over (f.u.obj V)))
        (Z := RingedTopos.localizedRingedTopos X.ringedTopos
          (f.inverseImageRepresentableSheaf V))
        (f.compareMid V) (X.relocalizationRingedToposHom c)).toToposHom.inverseImage =
      (X.ringedTopos.relocalizationMorphism
          (f.inverseImageRepresentableSheafIso V).inv).toToposHom.inverseImage ⋙
        (AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos (X.over U))
          (Y := ringedTopos (X.over (f.u.obj V)))
          (Z := RingedTopos.localizedRingedTopos X.ringedTopos
            (representableSheaf X (f.u.obj V)))
          (representableLocalizationRingedMorphism X (f.u.obj V))
          (X.relocalizationRingedToposHom c)).toToposHom.inverseImage :=
  rfl

/-- **The inverse image of the relocalization at `s`, split along Stacks 04D3.** The map
`s = h_c^# ≫ e⁻¹` at which Stacks 04J8 relocalizes is a composite, and relocalizing twice is
relocalizing along the composite on the nose, so the inverse image of the relocalization at `s`
splits off the relocalization along `e⁻¹` as a left factor. -/
theorem Hom.relocalizationSheafMap_inverseImage_eq :
    (AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos (X.over U))
        (Y := RingedTopos.localizedRingedTopos X.ringedTopos (representableSheaf X U))
        (Z := RingedTopos.localizedRingedTopos X.ringedTopos
          (f.inverseImageRepresentableSheaf V))
        (X.ringedTopos.relocalizationMorphism (f.relocalizationSheafMap c))
        (representableLocalizationRingedMorphism X U)).toToposHom.inverseImage =
      (X.ringedTopos.relocalizationMorphism
          (f.inverseImageRepresentableSheafIso V).inv).toToposHom.inverseImage ⋙
        (AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos (X.over U))
          (Y := RingedTopos.localizedRingedTopos X.ringedTopos (representableSheaf X U))
          (Z := RingedTopos.localizedRingedTopos X.ringedTopos
            (representableSheaf X (f.u.obj V)))
          (X.ringedTopos.relocalizationMorphism (representableSheafMap X c))
          (representableLocalizationRingedMorphism X U)).toToposHom.inverseImage :=
  rfl

/-- **Stacks 04J5 on inverse images, at the map that Stacks 04J9 relocalizes at.** The middle
identification of Stacks 04J3 preceded by the relocalization of the ringed site along `c` has
the same inverse image as the relocalization of the ringed topos along
`s : h_U^# ⟶ f^{-1}h_V^#` preceded by the identification of Stacks 04J3 at `U`. -/
noncomputable def Hom.relocCompareInverseImageIso :
    (AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos (X.over U))
        (Y := ringedTopos (X.over (f.u.obj V)))
        (Z := RingedTopos.localizedRingedTopos X.ringedTopos
          (f.inverseImageRepresentableSheaf V))
        (f.compareMid V) (X.relocalizationRingedToposHom c)).toToposHom.inverseImage ≅
      (AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos (X.over U))
        (Y := RingedTopos.localizedRingedTopos X.ringedTopos (representableSheaf X U))
        (Z := RingedTopos.localizedRingedTopos X.ringedTopos
          (f.inverseImageRepresentableSheaf V))
        (X.ringedTopos.relocalizationMorphism (f.relocalizationSheafMap c))
        (representableLocalizationRingedMorphism X U)).toToposHom.inverseImage :=
  eqToIso (f.compareMid_relocalization_inverseImage_eq c) ≪≫
    Functor.isoWhiskerLeft
      (X.ringedTopos.relocalizationMorphism
        (f.inverseImageRepresentableSheafIso V).inv).toToposHom.inverseImage
      (representableRelocalizationSheafMapCompInverseImageIso X c).symm ≪≫
    eqToIso (f.relocalizationSheafMap_inverseImage_eq c).symm

/-- The relocalized morphism of Stacks 04J1 followed by the identification of Stacks 04J3 at `V`,
and the relocalized morphism of Stacks 04J8 preceded by the identification of Stacks 04J3 at `U`,
have the same inverse image. -/
@[stacks 04J9 "on inverse images: the relocalized morphism of 04J1 and the relocalized morphism
  of 04J8 have the same inverse image, through the identifications of 04J3 at `U` and at `V`,
  the comparison being pasted from 04J5 and 04J7 on inverse images. The upgrade of this
  comparison to a 2-isomorphism of ringed topoi, and the agreement of the two localization
  squares under it, are not established here"]
noncomputable def Hom.relocalizedCompInverseImageIso :
    (AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos (X.over U))
        (Y := ringedTopos (Y.over V))
        (Z := RingedTopos.localizedRingedTopos Y.ringedTopos (representableSheaf Y V))
        (representableLocalizationRingedMorphism Y V)
        (f.relocalized c)).toToposHom.inverseImage ≅
      (AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos (X.over U))
        (Y := RingedTopos.localizedRingedTopos X.ringedTopos (representableSheaf X U))
        (Z := RingedTopos.localizedRingedTopos Y.ringedTopos (representableSheaf Y V))
        (f.ringedToposHom.relocalized (f.relocalizationSheafMap c))
        (representableLocalizationRingedMorphism X U)).toToposHom.inverseImage :=
  Functor.isoWhiskerRight (f.localizedRepresentableCompInverseImageIso V).symm
      (X.relocalizationRingedToposHom c).toToposHom.inverseImage ≪≫
    Functor.isoWhiskerLeft
      (f.ringedToposHom.localized (representableSheaf Y V)).toToposHom.inverseImage
      (f.relocCompareInverseImageIso c)

end AlgebraicGeometry.RingedSite

end
