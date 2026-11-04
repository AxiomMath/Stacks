module

public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.RingedToposRelocalizedMorphism
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.SliceEquivalence
public import StacksFrontier.CategoryTheory.Sites.RelocalizationMorphism
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The localization of a localized ringed topos at the object `G/F`

Let `X` be a ringed topos presented by a site `(C, J)` and let `s : G ⟶ F` be a morphism of
sheaves of sets on `C`. Stacks 04J4 asserts that the relocalization morphism
`(Sh(C)/G, O_G) ⟶ (Sh(C)/F, O_F)` along `s` is the *localization* of `(Sh(C)/F, O_F)` at the
object `G/F` of its topos. This file builds that localization, computes its inverse image —
read through the identification of Stacks 04IE of the localization of `X` at `F` with the slice
topos `Sh(C)/F`, and through the identification below of the localization at `G/F` with
`Sh(C)/G`, it is base change along `s` — and proves that the resulting triangle over `X`
commutes, both on inverse images and on the three structure maps.

## Main definitions

* `AlgebraicGeometry.RingedTopos.relocalizationObject`: the object `G/F` of the localization of
  `X` at `F`, namely the object `s : G ⟶ F` of the slice topos read through Stacks 04IE.
* `AlgebraicGeometry.RingedTopos.relocalizationSliceEquivalence`: slices at `G/F` are slices at
  `G`, by the iterated slice equivalence.
* `AlgebraicGeometry.RingedTopos.relocalizationStarIso`: taking the product with `G/F` and
  transporting the result to `Sh(C)/G` is base change along `s`.
* `AlgebraicGeometry.RingedTopos.relocalizationObjectEquivalence`: the identification of the
  topos of the localization at `G/F` with the topos of the localization of `X` at `G`.
* `AlgebraicGeometry.RingedTopos.relocalizationShriekAdjunction`: the lower shriek of the
  relocalization along `s`, obtained from the lower shriek of the localization at `G/F`.

## Main results

* `AlgebraicGeometry.RingedTopos.localizationAtRelocalizationObjectInverseImageIso`:
  **Stacks 04J4** for the localization at `G/F`. The inverse image of the localization morphism
  of `(Sh(C)/F, O_F)` at `G/F`, read through the two identifications with slice topoi, is base
  change along `s`.
* `AlgebraicGeometry.RingedTopos.relocalizationObjectTriangleInverseImageIso`: **Stacks 04J4**,
  the triangle whose upper edge is the localization at `G/F` commutes on inverse images: the
  composite of that localization with `j_F`, read through
  `relocalizationObjectEquivalence`, is `j_G`.
* `AlgebraicGeometry.RingedTopos.relocalizationObjectTriangle_fSharpInverseImage`:
  **Stacks 04J4**, it commutes on structure maps, both of them being the identity on underlying
  sheaves of sets.
* `AlgebraicGeometry.RingedTopos.relocalizationObjectInverseImageIso`: **Stacks 04J4**, the
  inverse image of the localization at `G/F`, read through `relocalizationObjectEquivalence`, is
  the inverse image of the relocalization along `s`.

## Implementation notes

Nothing here is specific to a representable sheaf: the computation is carried out for an
arbitrary morphism of sheaves `s`, the representable case being `s = h_f^#`.

The double slice is handled by `CategoryTheory.Over.postEquiv`, which transports the slice at
`G/F` across Stacks 04IE, followed by `CategoryTheory.Over.mapIso` of the counit of that
identification and `CategoryTheory.Over.iteratedSliceEquiv`, which says that `(Sh(C)/F)/(G/F)`
is `Sh(C)/G`.

That the triangle commutes on inverse images uses no further geometry: the inverse image of
`j_F` is `toOver F` (Stacks 04IE), the inverse image of the localization at `G/F` is base change
along `s`, and `CategoryTheory.toOverCompPullbackIso` says that the product with `F` followed by
base change along `s` is the product with `G`, which is the inverse image of `j_G`. Its
commutativity on structure maps is the observation that the structure map of a localization
morphism is the identity on underlying sheaves of sets, so both composites are identities.

`relocalizationStarIso` is a uniqueness-of-right-adjoints argument. The left adjoint of
`toOver (G/F)` followed by the transport is `Over.map s` followed by Stacks 04IE's
identification, on the nose — that is `relocalizationForgetIso`, which is `Iso.refl` — so
`CategoryTheory.Adjunction.rightAdjointUniq` applies with no coherence left over.

Universes follow the localization: site objects, site morphisms and sections of `O` are all
taken in one universe `u`, which is what Stacks 0791 needs in order to return a sheaf
equivalence, and which is what keeps the localization of the localization inside
`RingedTopos.{u, u, u}`.

## References

* [Stacks Project, Tag 04J4](https://stacks.math.columbia.edu/tag/04J4)
* [Stacks Project, Tag 04IE](https://stacks.math.columbia.edu/tag/04IE)
* [Stacks Project, Tag 04IR](https://stacks.math.columbia.edu/tag/04IR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.RingedTopos

variable (X : RingedTopos.{u, u, u}) {G F : X.Topos}

/-- The object `G/F` of the localization of `X` at `F`: the object `s : G ⟶ F` of the slice
topos `Sh(C)/F`, read through the identification of Stacks 04IE. -/
noncomputable def relocalizationObject (s : G ⟶ F) : (X.localizedRingedTopos F).Topos :=
  (localizationEquivalence X F).inverse.obj (Over.mk s)

/-- **Slices at `G/F` are slices at `G`**: the slice of the localization of `X` at `F` at the
object `G/F` is the slice of `Sh(C)/F` at `s : G ⟶ F`, which is `Sh(C)/G` by the iterated slice
equivalence. -/
noncomputable def relocalizationSliceEquivalence (s : G ⟶ F) :
    Over (X.relocalizationObject s) ≌ Over G :=
  (Over.postEquiv (X := X.relocalizationObject s) (localizationEquivalence X F)).trans
    ((Over.mapIso ((localizationEquivalence X F).counitIso.app (Over.mk s))).trans
      (Over.mk s).iteratedSliceEquiv)

/-- Postcomposition with `s`, followed by the identification of `Sh(C)/F` with the localization
at `F`, is the forgetful functor of the slice at `G/F` read through
`relocalizationSliceEquivalence`. The two functors agree on the nose: both send `(A ⟶ G)` to the
fibre construction applied to `(A ⟶ G ⟶ F)`. -/
noncomputable def relocalizationForgetIso (s : G ⟶ F) :
    Over.map s ⋙ (localizationEquivalence X F).inverse ≅
      (X.relocalizationSliceEquivalence s).inverse ⋙
        Over.forget (X.relocalizationObject s) :=
  Iso.refl _

/-- **The product with `G/F` is base change along `s`.** Taking the product with `G/F` and
transporting the result to `Sh(C)/G` is base change along `s` composed with the identification
of the localization at `F` with `Sh(C)/F`. Both functors are right adjoint to the two equal left
adjoints of `relocalizationForgetIso`. -/
noncomputable def relocalizationStarIso (s : G ⟶ F) :
    toOver (X.relocalizationObject s) ⋙ (X.relocalizationSliceEquivalence s).functor ≅
      (localizationEquivalence X F).functor ⋙ Over.pullback s :=
  Adjunction.rightAdjointUniq
    (((X.relocalizationSliceEquivalence s).symm.toAdjunction.comp
        (forgetAdjToOver (X.relocalizationObject s))).ofNatIsoLeft
      (X.relocalizationForgetIso s).symm)
    ((Over.mapPullbackAdj s).comp (localizationEquivalence X F).symm.toAdjunction)

/-- **The inverse image of the localization at `G/F`.** Read through the identification of
Stacks 04IE of the localization of `X` at `F` with `Sh(C)/F`, and through the identification of
the slice at `G/F` with `Sh(C)/G`, the inverse image of the localization morphism of
`(Sh(C)/F, O_F)` at the object `G/F` is base change along `s`.

This is Stacks 04IR for the slice topos `Sh(C)/F`: the inverse image of a localization at an
object is the product with that object (`localizationInverseImageIso`), and the product with
`G/F` is base change along `s` (`relocalizationStarIso`). -/
@[stacks 04J4 "the localization at `G/F` has base change along `s` as its inverse image",
  sga "4 IV 5.2"]
noncomputable def localizationAtRelocalizationObjectInverseImageIso (s : G ⟶ F) :
    (localizationMorphism (X.localizedRingedTopos F)
            (X.relocalizationObject s)).toToposHom.inverseImage ⋙
        ((localizationEquivalence (X.localizedRingedTopos F)
            (X.relocalizationObject s)).functor ⋙
          (X.relocalizationSliceEquivalence s).functor) ≅
      (localizationEquivalence X F).functor ⋙ Over.pullback s :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (localizationInverseImageIso (X.localizedRingedTopos F) (X.relocalizationObject s))
      (X.relocalizationSliceEquivalence s).functor ≪≫
    X.relocalizationStarIso s

/-- **The topos of the localization at `G/F` is the topos of the localization at `G`.** Stacks
04IE identifies the first with the slice of `Sh(C)/F` at `s`, which the iterated slice
equivalence identifies with `Sh(C)/G`, which Stacks 04IE identifies with the second. -/
noncomputable def relocalizationObjectEquivalence (s : G ⟶ F) :
    ((X.localizedRingedTopos F).localizedRingedTopos (X.relocalizationObject s)).Topos ≌
      (X.localizedRingedTopos G).Topos :=
  (localizationEquivalence (X.localizedRingedTopos F) (X.relocalizationObject s)).trans
    ((X.relocalizationSliceEquivalence s).trans (localizationEquivalence X G).symm)

/-- The relocalization triangle with the localization at `G/F` as its upper edge, on inverse
images: the composite of the localization of `(Sh(C)/F, O_F)` at the object
`G/F` with the localization morphism `j_F`, read through `relocalizationObjectEquivalence`, is
the localization morphism `j_G`.

The inverse image of `j_F` is the product with `F` and that of `j_G` the product with `G`, both
by Stacks 04IE; the inverse image of the localization at `G/F` is base change along `s`; and the
product with `F` followed by base change along `s` is the product with `G`. -/
@[stacks 04J4 "the triangle whose upper edge is the localization at `G/F` commutes on inverse
  images"]
noncomputable def relocalizationObjectTriangleInverseImageIso (s : G ⟶ F) :
    ((X.localizationMorphism F).comp
          (localizationMorphism (X.localizedRingedTopos F)
            (X.relocalizationObject s))).toToposHom.inverseImage ⋙
        (X.relocalizationObjectEquivalence s).functor ≅
      (X.localizationMorphism G).toToposHom.inverseImage :=
  Functor.isoWhiskerLeft (X.localizationMorphism F).toToposHom.inverseImage
      (Functor.isoWhiskerRight (X.localizationAtRelocalizationObjectInverseImageIso s)
        (localizationEquivalence X G).inverse) ≪≫
    Functor.isoWhiskerRight (localizationInverseImageIso X F)
      (Over.pullback s ⋙ (localizationEquivalence X G).inverse) ≪≫
    Functor.isoWhiskerRight (toOverCompPullbackIso s) (localizationEquivalence X G).inverse ≪≫
    Functor.isoWhiskerRight (localizationInverseImageIso X G).symm
      (localizationEquivalence X G).inverse ≪≫
    Functor.isoWhiskerLeft (X.localizationMorphism G).toToposHom.inverseImage
      (localizationEquivalence X G).unitIso.symm

/-- The relocalization triangle with the localization at `G/F` as its upper edge, on structure
maps: both edges from the localization at `G/F` to `X` have the identity as
their structure map on underlying sheaves of sets, so the triangle commutes as a triangle of
*ringed* topoi and not merely of topoi.

Each of the three localization morphisms in the triangle has the identity as its structure map
on underlying sheaves of sets, and the structure map of a composite is the restriction of the
first factor's followed by the second factor's. -/
@[stacks 04J4 "the triangle commutes on structure maps, both of them being the identity"]
theorem relocalizationObjectTriangle_fSharpInverseImage (s : G ⟶ F) :
    ((X.localizedRingedTopos F).localizedRingedTopos
          (X.relocalizationObject s)).forgetRing.map
        ((X.localizationMorphism F).comp (localizationMorphism (X.localizedRingedTopos F)
          (X.relocalizationObject s))).fSharpInverseImage =
      𝟙 (((X.localizedRingedTopos F).localizedRingedTopos
            (X.relocalizationObject s)).forgetRing.obj
          ((X.localizedRingedTopos F).localizedRingedTopos (X.relocalizationObject s)).O) ∧
      (X.localizedRingedTopos G).forgetRing.map (X.localizationMorphism G).fSharpInverseImage =
        𝟙 ((X.localizedRingedTopos G).forgetRing.obj (X.localizedRingedTopos G).O) := by
  refine ⟨?_, RingedToposHom.forgetRing_localizationMorphism_fSharpInverseImage X G⟩
  have hF := RingedToposHom.forgetRing_localizationMorphism_fSharpInverseImage X F
  have hW := RingedToposHom.forgetRing_localizationMorphism_fSharpInverseImage
    (X.localizedRingedTopos F) (X.relocalizationObject s)
  refine Eq.trans (RingedToposHom.comp_fSharpInverseImage_forget
    (X := (X.localizedRingedTopos F).localizedRingedTopos (X.relocalizationObject s))
    (Y := X.localizedRingedTopos F) (Z := X)
    (X.localizationMorphism F)
    (localizationMorphism (X.localizedRingedTopos F) (X.relocalizationObject s))) ?_
  exact (congrArg (fun z ↦ (localizationMorphism (X.localizedRingedTopos F)
          (X.relocalizationObject s)).toToposHom.inverseImage.map
            ((X.localizedRingedTopos F).forgetRing.map
              (X.localizationMorphism F).fSharpInverseImage) ≫ z) hW).trans
    ((Category.comp_id _).trans
      ((congrArg (fun z ↦ (localizationMorphism (X.localizedRingedTopos F)
            (X.relocalizationObject s)).toToposHom.inverseImage.map z) hF).trans
        ((localizationMorphism (X.localizedRingedTopos F)
          (X.relocalizationObject s)).toToposHom.inverseImage.map_id _)))

/-- **The two relocalizations have the same inverse image.** Read through
`relocalizationObjectEquivalence`, the inverse image of the localization of `(Sh(C)/F, O_F)` at
the object `G/F` is the inverse image of the relocalization morphism along `s`.

Both are base change along `s` on slice topoi — the first by
`localizationAtRelocalizationObjectInverseImageIso`, the second by
`relocalizationInverseImageSliceIso` — so the two agree once the equivalence at `G` is
cancelled. -/
@[stacks 04J4 "the localization at `G/F` and the relocalization have the same inverse image"]
noncomputable def relocalizationObjectInverseImageIso (s : G ⟶ F) :
    (localizationMorphism (X.localizedRingedTopos F)
          (X.relocalizationObject s)).toToposHom.inverseImage ⋙
        (X.relocalizationObjectEquivalence s).functor ≅
      (X.relocalizationMorphism s).toToposHom.inverseImage :=
  (Functor.isoWhiskerLeft
        (localizationMorphism (X.localizedRingedTopos F)
          (X.relocalizationObject s)).toToposHom.inverseImage
        (Functor.associator
          (localizationEquivalence (X.localizedRingedTopos F) (X.relocalizationObject s)).functor
          (X.relocalizationSliceEquivalence s).functor
          (localizationEquivalence X G).inverse)).symm ≪≫
    (Functor.associator
      (localizationMorphism (X.localizedRingedTopos F)
        (X.relocalizationObject s)).toToposHom.inverseImage
      ((localizationEquivalence (X.localizedRingedTopos F)
          (X.relocalizationObject s)).functor ⋙ (X.relocalizationSliceEquivalence s).functor)
      (localizationEquivalence X G).inverse).symm ≪≫
    Functor.isoWhiskerRight (X.localizationAtRelocalizationObjectInverseImageIso s)
      (localizationEquivalence X G).inverse ≪≫
    Functor.isoWhiskerRight (X.relocalizationInverseImageSliceIso s).symm
      (localizationEquivalence X G).inverse ≪≫
    Functor.associator (X.relocalizationMorphism s).toToposHom.inverseImage
      (localizationEquivalence X G).functor (localizationEquivalence X G).inverse ≪≫
    Functor.isoWhiskerLeft (X.relocalizationMorphism s).toToposHom.inverseImage
      (localizationEquivalence X G).unitIso.symm ≪≫
    Functor.rightUnitor _

/-- **The lower shriek of the relocalization along `s`.** The inverse image of the
relocalization morphism has a left adjoint: it is the inverse image of the localization at
`G/F` read through `relocalizationObjectEquivalence`, and that has the lower shriek of a
localization as its left adjoint. -/
noncomputable def relocalizationShriekAdjunction (s : G ⟶ F) :
    (X.relocalizationObjectEquivalence s).inverse ⋙
        ((localizationEquivalence (X.localizedRingedTopos F)
            (X.relocalizationObject s)).functor ⋙
          Over.forget (X.relocalizationObject s)) ⊣
      (X.relocalizationMorphism s).toToposHom.inverseImage :=
  ((X.relocalizationObjectEquivalence s).symm.toAdjunction.comp
      (localizationShriekAdjunction (X.localizedRingedTopos F)
        (X.relocalizationObject s))).ofNatIsoRight
    (X.relocalizationObjectInverseImageIso s)

end AlgebraicGeometry.RingedTopos

end
