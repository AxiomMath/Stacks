module

public import StacksFrontier.AlgebraicGeometry.Etale.OpenCovarianceTransitivity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.QcSeparatedObjectSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleLimitColimitSheaf

/-! # Stacks 09YQ in degree zero over a quasi-compact quasi-separated etale object of a level

Let `I` be a directed set, let `(X_i)` be an inverse system of schemes over `I` whose transition
morphisms are affine and let `X = lim X_i`.  Fix a level `i₀` and an object `V₀` of the small
etale site of `X_{i₀}` whose underlying scheme is quasi-compact and quasi-separated.  `V₀` is
*not* an object of the small affine etale site of `X_{i₀}` unless it is affine, and the levels of
the system of sites of Stacks 0EYL are categories of representatives of the small *affine* etale
sites; so neither the levels nor the colimit site contains `V₀`, nor its base changes `V_n` to
the lower levels, nor its base change `V_X` to `X`.

`Stacks.WeakSites.ColimitGlobalSections.sectionOver_colimit_of_oneHypercoverOf'` computes the
sections over such an object -- it is the degree-zero statement of Stacks 09YQ at the level of an
abstract inverse system of sites, with the object supplied by *ambient* sites of the levels and of
the colimit together with a single finite datum of objects of the level `i₀` covering it
everywhere.  This file instantiates it at the etale system.

## Main definitions

* `transitionBaseChangeEtaleObj`, `toLimitBaseChangeEtaleObj`: the base changes `V_n` and `V_X`
  **as data**, with `transitionBaseChangeEtaleObj_isPullback` and
  `toLimitBaseChangeEtaleObj_isPullback` their fibre-product squares.
* `levelToSmallEtale`: the crossing from a level of the system to the small etale site of its
  scheme, and `levelRaisedSheaf` the resulting restriction of sheaves.  This is the level-side
  counterpart of `Stacks.EtaleCohomology.AffineLimitCohomology.limitToSmallEtale`, and it is not
  a universe raising followed by Stacks 04HR: a level is a category of *representatives*, so the
  first factor is the level equivalence, whose continuity is
  `Stacks.EtaleCohomology.affineEtaleSiteColimit_levelToSmallEtale_isContinuous`.
* `imageIsoObjOfPreimageOver`, with `transitionImage_isoObjOfPreimageOver` and
  `toLimitImage_isoObjOfPreimageOver` its two geometric instances: the image of the object of an
  affine open `O` of `V₀` is the object of the preimage open in the base change of `V₀`.

## Main results

* `isOneHypercoverOf_image`: **the images of a datum of affine opens of `V₀` are a
  one-hypercover of the base change of `V₀`.**  Stated once for an abstract base change and
  applied twice, to the transitions and to the limit; those two are
  `isOneHypercoverOf_transitionImage` and `isOneHypercoverOf_toLimitImage`.
* `exists_oneHypercoverOf_datum`: the two of them for ONE finite datum, which is what
  `sectionOver_colimit_of_oneHypercoverOf'` consumes.
* `sectionOver_colimit_of_qcqs_etale_object`: **Stacks 09YQ in degree zero over `V₀`.**  The
  sections of `𝒢 = colim f_i^{-1}F_i` over `V_X` are the filtered colimit of the sections of the
  `F_n` over the `V_n`.

## Implementation notes

The one computation of the file is `map_comp_imageIso`, and everything else is bookkeeping around
it.  The transported one-hypercover needs its two projections expressed through the isomorphisms
that pin the images (`Stacks.WeakSites.ColimitGlobalSections.IsOneHypercoverOf.of_iso`), and that
is not a formal consequence of anything: the images are pinned by fibre-product squares, so the
equation has to be read off the universal property.  It is proved by three reductions and two
pinning identities --- `Mono` of the open immersion of an affine open into the ambient object
reduces to morphisms into `V_n`, the fibre-product square of `V_n` reduces those to their two
projections, the projection to `X_n` is automatic for morphisms of a site over `X_n`, and the
projection to `V₀` is `isoObjOfPreimageOver_hom_comp_ι` against the naturality of the chosen
fibre-product projections of the system.

**The abstract base change is what halves the file.** The level side and the limit side of the
statement differ only in which scheme the base change is taken to and in which of the two
fibre-product fields of `Stacks.EtaleCohomology.AffineEtaleSiteColimit` supplies the square --
`transition_isPullback` or `toLimit_isPullback`, which sit beside each other for exactly this
reason.  Every declaration before the geometric sections is therefore stated for a bare affine
`g : R ⟶ T` with a functor `Ψ` to the small affine etale site of `R`, a natural transformation
`Fst` to the `T`-side and a square at every object, and is applied twice.

Nothing here touches degrees above zero.  What this file performs in degree zero is the descent
that carries the statement from the objects of a cover to the object itself.  Above degree zero
that is NOT the argument: this development's route is the Mayer-Vietoris dévissage
`isCohomologyColimit_of_degreeZero_of_affineOpensAcyclic` of the namespace
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology`,
which runs on Mathlib's small étale site of the level, where the level is always a terminal object
(`Stacks.EtaleCohomology.etaleMkIdIsTerminal`, stated for any scheme with no affineness
hypothesis) and so no descent from objects arises at all — the missing-terminal-object obstruction
is specific to the small *affine* site.  That dévissage remains conditional on its three
hypotheses, which is why `@[stacks 09YQ]` is not claimed here.

## References

* [Stacks 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
* [Stacks 09YN](https://stacks.math.columbia.edu/tag/09YN)
* [Stacks 0EYL](https://stacks.math.columbia.edu/tag/0EYL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w₂ w₁ v u

namespace Stacks.EtaleCohomology.QcSeparatedColimit

open AlgebraicGeometry
open Stacks.EtaleCohomology.AffineLimitCohomology
open Stacks.EtaleCohomology.QcqsLimitCohomology
open Stacks.EtaleCohomology.QcSeparatedSections
open Stacks.WeakSites.ColimitGlobalSections
open CategoryTheory.Sites.InverseSystem

/-! ### The object of an affine open, in the small affine etale site -/

section AffineOpens

variable (B : AlgebraicGeometry.BigEtaleSite.{u}) {T : Scheme.{u}} (hT : B.Contains T)
  (V₀ : AlgebraicGeometry.SmallEtale B T hT)

/-- **The object of the small affine etale site attached to an affine open of `V₀`.** This is
`Stacks.EtaleCohomology.QcSeparatedSections.etaleObjOfAffineOpen` read one step earlier, before
the inclusion of Stacks 04HR: the objects of a datum at a level have to be objects of the small
*affine* etale site, the levels of the system of Stacks 0EYL being representatives of that site,
while the one-hypercover they form lives in the small etale site, where `V₀` is. -/
def affObj (O : ((AlgebraicGeometry.SmallEtale.toScheme B T hT).obj V₀).Opens)
    (hO : AlgebraicGeometry.IsAffineOpen O) : AlgebraicGeometry.SmallAffineEtale B T hT :=
  objOfAffineOpenOver B T hT (contains_toScheme_obj B hT V₀)
    (B.inclusion.map V₀.obj.hom) O hO

/-- The image of `affObj` under the inclusion of Stacks 04HR is the object of the open in the
small etale site. -/
theorem inclusion_obj_affObj (O : ((AlgebraicGeometry.SmallEtale.toScheme B T hT).obj V₀).Opens)
    (hO : AlgebraicGeometry.IsAffineOpen O) :
    (AlgebraicGeometry.SmallAffineEtale.inclusion B T hT).obj (affObj B hT V₀ O hO) =
      etaleObjOfAffineOpen B T hT V₀ O hO :=
  rfl

/-- The structure morphism of `affObj` is the open immersion followed by that of `V₀`. -/
theorem structMap_affObj (O : ((AlgebraicGeometry.SmallEtale.toScheme B T hT).obj V₀).Opens)
    (hO : AlgebraicGeometry.IsAffineOpen O) :
    structMap B T hT (affObj B hT V₀ O hO) = O.ι ≫ B.inclusion.map V₀.obj.hom :=
  structMap_objOfAffineOpenOver B T hT (contains_toScheme_obj B hT V₀)
    (B.inclusion.map V₀.obj.hom) O hO

/-- **The inclusion of one affine open of `V₀` in another, in the small affine etale site.** The
inclusion of Stacks 04HR is a full subcategory inclusion, so this is
`Stacks.EtaleCohomology.QcSeparatedSections.etaleObjLe`. -/
def affObjLe (O O' : ((AlgebraicGeometry.SmallEtale.toScheme B T hT).obj V₀).Opens)
    (hO : AlgebraicGeometry.IsAffineOpen O) (hO' : AlgebraicGeometry.IsAffineOpen O')
    (hle : O ≤ O') : affObj B hT V₀ O hO ⟶ affObj B hT V₀ O' hO' :=
  ObjectProperty.homMk (etaleObjLe B T hT V₀ O O' hO hO' hle)

/-- The inclusion of the small affine etale site into the small etale site sends `affObjLe` to
`etaleObjLe`. -/
@[simp]
theorem inclusion_map_affObjLe
    (O O' : ((AlgebraicGeometry.SmallEtale.toScheme B T hT).obj V₀).Opens)
    (hO : AlgebraicGeometry.IsAffineOpen O) (hO' : AlgebraicGeometry.IsAffineOpen O')
    (hle : O ≤ O') :
    (AlgebraicGeometry.SmallAffineEtale.inclusion B T hT).map
        (affObjLe B hT V₀ O O' hO hO' hle) = etaleObjLe B T hT V₀ O O' hO hO' hle :=
  rfl

/-- **The underlying morphism of schemes of an identification with the object of an affine open
of `V₀`**, with its target read as the open itself.

It is `AlgebraicGeometry.SmallAffineEtale.toScheme` applied to the identification and nothing
else; what it adds is the *type*.  The target of that functor at the object of an open is the open
only after the object is unfolded, so a goal mentioning the composite with a morphism out of the
open is well typed at default transparency but not at the reducible transparency `rw` revalidates
its motive at, and every rewrite through such a composite fails with an application type mismatch
between two expressions that print identically.  Naming the morphism at the type the opens have
keeps the rewrites of the consumers on the opens. -/
def affObjIsoScheme {W : AlgebraicGeometry.SmallAffineEtale B T hT}
    (O : ((AlgebraicGeometry.SmallEtale.toScheme B T hT).obj V₀).Opens)
    (hO : AlgebraicGeometry.IsAffineOpen O) (e : W ≅ affObj B hT V₀ O hO) :
    (AlgebraicGeometry.SmallAffineEtale.toScheme B T hT).obj W ⟶ O.toScheme :=
  (AlgebraicGeometry.SmallAffineEtale.toScheme B T hT).map e.hom

/-- **An identification with the object of an affine open is compatible with the inclusions of the
opens.** If a morphism `t` becomes the inclusion of `O'` in `O` after the two identifications,
then on underlying schemes it becomes the inclusion of the opens.

This is `CategoryTheory.Functor.map_comp` on either side of the hypothesis and nothing else; what
it is for is that both sides are written at the types the opens have, so a consumer can rewrite
with it. -/
theorem comp_affObjIsoScheme {W W' : AlgebraicGeometry.SmallAffineEtale B T hT} (t : W' ⟶ W)
    (O O' : ((AlgebraicGeometry.SmallEtale.toScheme B T hT).obj V₀).Opens)
    (hO : AlgebraicGeometry.IsAffineOpen O) (hO' : AlgebraicGeometry.IsAffineOpen O')
    (hle : O' ≤ O) (e : W ≅ affObj B hT V₀ O hO) (e' : W' ≅ affObj B hT V₀ O' hO')
    (ht : t ≫ e.hom = e'.hom ≫ affObjLe B hT V₀ O' O hO' hO hle) :
    (AlgebraicGeometry.SmallAffineEtale.toScheme B T hT).map t ≫
        affObjIsoScheme B hT V₀ O hO e =
      affObjIsoScheme B hT V₀ O' hO' e' ≫
        ((AlgebraicGeometry.SmallEtale.toScheme B T hT).obj V₀).homOfLE hle :=
  ((AlgebraicGeometry.SmallAffineEtale.toScheme B T hT).map_comp _ _).symm.trans
    ((congrArg (AlgebraicGeometry.SmallAffineEtale.toScheme B T hT).map ht).trans
      ((AlgebraicGeometry.SmallAffineEtale.toScheme B T hT).map_comp _ _))

end AffineOpens

/-! ### The images of the objects of affine opens along an abstract base change -/

section Abstract

variable (B : AlgebraicGeometry.BigEtaleSite.{u}) {T R : Scheme.{u}}
  (hT : B.Contains T) (hR : B.Contains R) (g : R ⟶ T) [IsAffineHom g]
  (V₀ : AlgebraicGeometry.SmallEtale B T hT)
  {C₀ : Type w₁} [Category.{w₂} C₀]
  (E : C₀ ⥤ AlgebraicGeometry.SmallAffineEtale B T hT)
  (Ψ : C₀ ⥤ AlgebraicGeometry.SmallAffineEtale B R hR)
  (Fst : Ψ ⋙ AlgebraicGeometry.SmallAffineEtale.toScheme B R hR ⟶
    E ⋙ AlgebraicGeometry.SmallAffineEtale.toScheme B T hT)
  (hsq : ∀ Y : C₀, IsPullback (Fst.app Y) (structMap B R hR (Ψ.obj Y))
    (structMap B T hT (E.obj Y)) g)
  (VR : AlgebraicGeometry.SmallEtale B R hR)
  (qR : (AlgebraicGeometry.SmallEtale.toScheme B R hR).obj VR ⟶
    (AlgebraicGeometry.SmallEtale.toScheme B T hT).obj V₀) [IsAffineHom qR]
  (hVsq : IsPullback qR (B.inclusion.map VR.obj.hom) (B.inclusion.map V₀.obj.hom) g)

include hsq in
/-- **The square the identification of an image asks for.** Given an identification `e` of the
`T`-side image of `Y` with the object of an affine open `O` of `V₀`, the structure morphism of the
`R`-side image of `Y` sits in a fibre-product square over `O.ι ≫ V₀ ⟶ T` and `g`.

This is `isPullback_transitionImage_structMap` with `isoObjOfPreimage` replaced by
`isoObjOfPreimageOver`: the cospan is the composite of the open immersion with the structure
morphism of `V₀` rather than an open immersion of `T` itself, because the opens of the datum are
opens of `V₀` and not of the level. As there, `e` is an identification over `T` for free, a
morphism of the site being a morphism over `T` by definition. -/
theorem isPullback_image_structMap_over (Y : C₀)
    (O : ((AlgebraicGeometry.SmallEtale.toScheme B T hT).obj V₀).Opens)
    (hO : AlgebraicGeometry.IsAffineOpen O) (e : E.obj Y ≅ affObj B hT V₀ O hO) :
    IsPullback (Fst.app Y ≫ affObjIsoScheme B hT V₀ O hO e)
      (structMap B R hR (Ψ.obj Y)) (O.ι ≫ B.inclusion.map V₀.obj.hom) g := by
  refine (hsq Y).of_iso (Iso.refl _)
    ((AlgebraicGeometry.SmallAffineEtale.toScheme B T hT).mapIso e)
    (Iso.refl _) (Iso.refl _) (by simp [affObjIsoScheme]) (by simp) ?_ (by simp)
  have h1 := toScheme_map_comp_structMap B T hT e.hom
  rw [structMap_affObj] at h1
  exact (Category.comp_id _).trans h1.symm

include hsq hVsq in
/-- **The image of the object of an affine open of `V₀` is the object of the preimage open in the
base change of `V₀`.** The relative counterpart of `transitionImage_isoObjOfPreimage`, whose
opens are opens of the level: here they are opens of `V₀`, so the image sits inside the base
change `VR` of `V₀` and not inside `R`.

`isoObjOfPreimageOver` does the geometry; this only feeds it the square. -/
def imageIsoObjOfPreimageOver (Y : C₀)
    (O : ((AlgebraicGeometry.SmallEtale.toScheme B T hT).obj V₀).Opens)
    (hO : AlgebraicGeometry.IsAffineOpen O) (e : E.obj Y ≅ affObj B hT V₀ O hO) :
    Ψ.obj Y ≅ affObj B hR VR (qR ⁻¹ᵁ O) (hO.preimage qR) :=
  isoObjOfPreimageOver B R hR g (B.inclusion.map V₀.obj.hom)
    (contains_toScheme_obj B hR VR) (B.inclusion.map VR.obj.hom) qR hVsq O hO (Ψ.obj Y) _
    (isPullback_image_structMap_over B hT hR g V₀ E Ψ Fst hsq Y O hO e)

include hsq hVsq in
/-- **The underlying morphism of schemes of the identification of an image with the object of a
preimage open**, with its target read as the preimage open itself.

It is `AlgebraicGeometry.SmallAffineEtale.toScheme` applied to `imageIsoObjOfPreimageOver` and
nothing else; what it adds is the *type*.  The target of that functor at the object of an open is
the open only after the object is unfolded, so a goal mentioning the composite with a morphism out
of the open is well typed at default transparency but not at the reducible transparency `rw`
revalidates its motive at, and every rewrite through such a composite fails with an application
type mismatch between two expressions that print identically.  Naming the morphism at the type the
opens have keeps the consumers' rewrites on the opens. -/
def imageIsoScheme (Y : C₀)
    (O : ((AlgebraicGeometry.SmallEtale.toScheme B T hT).obj V₀).Opens)
    (hO : AlgebraicGeometry.IsAffineOpen O) (e : E.obj Y ≅ affObj B hT V₀ O hO) :
    (AlgebraicGeometry.SmallAffineEtale.toScheme B R hR).obj (Ψ.obj Y) ⟶
      (qR ⁻¹ᵁ O).toScheme :=
  (AlgebraicGeometry.SmallAffineEtale.toScheme B R hR).map
    (imageIsoObjOfPreimageOver B hT hR g V₀ E Ψ Fst hsq VR qR hVsq Y O hO e).hom

include hsq hVsq in
/-- **The identification of an image with the object of a preimage open, read through the
restriction of the base-change projection.** The underlying morphism of schemes of the
identification, followed by the restriction of `qR` to the open `O`, is the chosen projection of
the image followed by the identification on the `T`-side.

This is the pinning identity the transported one-hypercover needs, and it is
`CategoryTheory.IsPullback.isoIsPullback_hom_fst` for the fibre-product square
`isoObjOfPreimageOver` is built from -- the vertical pasting of
`AlgebraicGeometry.isPullback_morphismRestrict` with the square of the base change.  The companion
identity on the other projection -- the one to `R` -- is not stated: it holds for any morphism of
the site, being `toScheme_map_comp_structMap`.

It is phrased with `AlgebraicGeometry.morphismRestrict` rather than with the open immersion of the
preimage open followed by `qR`, which is the same morphism
(`AlgebraicGeometry.morphismRestrict_ι`) but not the same *term*: `morphismRestrict` lands in the
open, which is where the consumers rewrite. -/
theorem imageIso_pin (Y : C₀)
    (O : ((AlgebraicGeometry.SmallEtale.toScheme B T hT).obj V₀).Opens)
    (hO : AlgebraicGeometry.IsAffineOpen O) (e : E.obj Y ≅ affObj B hT V₀ O hO) :
    imageIsoScheme B hT hR g V₀ E Ψ Fst hsq VR qR hVsq Y O hO e ≫
        AlgebraicGeometry.morphismRestrict qR O =
      Fst.app Y ≫ affObjIsoScheme B hT V₀ O hO e :=
  (isPullback_image_structMap_over B hT hR g V₀ E Ψ Fst hsq Y O hO e).isoIsPullback_hom_fst _ _
    ((AlgebraicGeometry.isPullback_morphismRestrict qR O).paste_vert hVsq)

/-- The underlying morphism of schemes of the inclusion of one affine open of `V₀` in another is
the inclusion of the opens. -/
@[simp]
theorem toScheme_map_affObjLe
    (O O' : ((AlgebraicGeometry.SmallEtale.toScheme B T hT).obj V₀).Opens)
    (hO : AlgebraicGeometry.IsAffineOpen O) (hO' : AlgebraicGeometry.IsAffineOpen O')
    (hle : O ≤ O') :
    (AlgebraicGeometry.SmallAffineEtale.toScheme B T hT).map
        (affObjLe B hT V₀ O O' hO hO' hle) =
      ((AlgebraicGeometry.SmallEtale.toScheme B T hT).obj V₀).homOfLE hle :=
  rfl

include hsq hVsq in
/-- **The projections of the datum, transported to the images.** This is the equation
`Stacks.WeakSites.ColimitGlobalSections.IsOneHypercoverOf.of_iso` asks for, and the only
computation of this file.

The hypothesis `ht` says that `t` is, after the two identifications on the `T`-side, the inclusion
of the open `O'` in the open `O`; the conclusion says that the image of `t` is, after the
identifications of the images, the inclusion of the preimage opens.

Three reductions and no guesswork.  `AlgebraicGeometry.SmallAffineEtale.toScheme` is faithful, so
it is enough to compare the two sides on underlying schemes; the underlying scheme of the object of
the preimage open is a fibre product -- the vertical pasting used by `imageIso_pin` -- so it is
enough to compare their two projections; the projection to `R` is the structure morphism of the
source for either side, every morphism of the site being one over `R`, and the projection to the
open `O` is `imageIso_pin` against the naturality of `Fst` and
`AlgebraicGeometry.morphismRestrict_homOfLE`. -/
theorem map_comp_imageIso {Y Y' : C₀} (t : Y' ⟶ Y)
    (O O' : ((AlgebraicGeometry.SmallEtale.toScheme B T hT).obj V₀).Opens)
    (hO : AlgebraicGeometry.IsAffineOpen O) (hO' : AlgebraicGeometry.IsAffineOpen O')
    (hle : O' ≤ O) (e : E.obj Y ≅ affObj B hT V₀ O hO)
    (e' : E.obj Y' ≅ affObj B hT V₀ O' hO')
    (ht : E.map t ≫ e.hom = e'.hom ≫ affObjLe B hT V₀ O' O hO' hO hle) :
    Ψ.map t ≫
        (imageIsoObjOfPreimageOver B hT hR g V₀ E Ψ Fst hsq VR qR hVsq Y O hO e).hom =
      (imageIsoObjOfPreimageOver B hT hR g V₀ E Ψ Fst hsq VR qR hVsq Y' O' hO' e').hom ≫
        affObjLe B hR VR (qR ⁻¹ᵁ O') (qR ⁻¹ᵁ O) (hO'.preimage qR) (hO.preimage qR)
          (qR.preimage_mono hle) := by
  have hnat : (AlgebraicGeometry.SmallAffineEtale.toScheme B R hR).map (Ψ.map t) ≫ Fst.app Y =
      Fst.app Y' ≫ (AlgebraicGeometry.SmallAffineEtale.toScheme B T hT).map (E.map t) :=
    Fst.naturality t
  refine (AlgebraicGeometry.SmallAffineEtale.toScheme B R hR).map_injective ?_
  show (AlgebraicGeometry.SmallAffineEtale.toScheme B R hR).map (Ψ.map t) ≫
      imageIsoScheme B hT hR g V₀ E Ψ Fst hsq VR qR hVsq Y O hO e =
    imageIsoScheme B hT hR g V₀ E Ψ Fst hsq VR qR hVsq Y' O' hO' e' ≫
      ((AlgebraicGeometry.SmallEtale.toScheme B R hR).obj VR).homOfLE (qR.preimage_mono hle)
  refine ((AlgebraicGeometry.isPullback_morphismRestrict qR O).paste_vert hVsq).hom_ext ?_ ?_
  · have hL : ((AlgebraicGeometry.SmallAffineEtale.toScheme B R hR).map (Ψ.map t) ≫
          imageIsoScheme B hT hR g V₀ E Ψ Fst hsq VR qR hVsq Y O hO e) ≫
        AlgebraicGeometry.morphismRestrict qR O =
        Fst.app Y' ≫ affObjIsoScheme B hT V₀ O' hO' e' ≫
          ((AlgebraicGeometry.SmallEtale.toScheme B T hT).obj V₀).homOfLE hle := by
      rw [Category.assoc, imageIso_pin, ← Category.assoc, hnat, Category.assoc,
        comp_affObjIsoScheme B hT V₀ (E.map t) O O' hO hO' hle e e' ht]
    have hRgt : (imageIsoScheme B hT hR g V₀ E Ψ Fst hsq VR qR hVsq Y' O' hO' e' ≫
          ((AlgebraicGeometry.SmallEtale.toScheme B R hR).obj VR).homOfLE
            (qR.preimage_mono hle)) ≫ AlgebraicGeometry.morphismRestrict qR O =
        Fst.app Y' ≫ affObjIsoScheme B hT V₀ O' hO' e' ≫
          ((AlgebraicGeometry.SmallEtale.toScheme B T hT).obj V₀).homOfLE hle := by
      rw [Category.assoc, ← AlgebraicGeometry.morphismRestrict_homOfLE, ← Category.assoc,
        imageIso_pin, Category.assoc]
    exact hL.trans hRgt.symm
  · show ((AlgebraicGeometry.SmallAffineEtale.toScheme B R hR).map (Ψ.map t) ≫
        (AlgebraicGeometry.SmallAffineEtale.toScheme B R hR).map
          (imageIsoObjOfPreimageOver B hT hR g V₀ E Ψ Fst hsq VR qR hVsq Y O hO e).hom) ≫
      structMap B R hR (affObj B hR VR (qR ⁻¹ᵁ O) (hO.preimage qR)) =
      ((AlgebraicGeometry.SmallAffineEtale.toScheme B R hR).map
          (imageIsoObjOfPreimageOver B hT hR g V₀ E Ψ Fst hsq VR qR hVsq Y' O' hO' e').hom ≫
        (AlgebraicGeometry.SmallAffineEtale.toScheme B R hR).map
          (affObjLe B hR VR (qR ⁻¹ᵁ O') (qR ⁻¹ᵁ O) (hO'.preimage qR) (hO.preimage qR)
            (qR.preimage_mono hle))) ≫
      structMap B R hR (affObj B hR VR (qR ⁻¹ᵁ O) (hO.preimage qR))
    simp only [Category.assoc, toScheme_map_comp_structMap]

include hsq hVsq in
/-- The identification of an image with the object of a preimage open, read in the small etale
site of `R`, where the ambient object `VR` lives. -/
def imageEtaleIso (Y : C₀)
    (O : ((AlgebraicGeometry.SmallEtale.toScheme B T hT).obj V₀).Opens)
    (hO : AlgebraicGeometry.IsAffineOpen O) (e : E.obj Y ≅ affObj B hT V₀ O hO) :
    (AlgebraicGeometry.SmallAffineEtale.inclusion B R hR).obj (Ψ.obj Y) ≅
      etaleObjOfAffineOpen B R hR VR (qR ⁻¹ᵁ O) (hO.preimage qR) :=
  (AlgebraicGeometry.SmallAffineEtale.inclusion B R hR).mapIso
    (imageIsoObjOfPreimageOver B hT hR g V₀ E Ψ Fst hsq VR qR hVsq Y O hO e)

include hsq hVsq in
/-- `map_comp_imageIso` read in the small etale site of `R`.  The inclusion of Stacks 04HR is a
functor, so this is the affine statement with `CategoryTheory.Functor.map_comp` on either side and
nothing else; the two identifications and the inclusion of the preimage opens are its images on
the nose. -/
theorem map_comp_imageEtaleIso {Y Y' : C₀} (t : Y' ⟶ Y)
    (O O' : ((AlgebraicGeometry.SmallEtale.toScheme B T hT).obj V₀).Opens)
    (hO : AlgebraicGeometry.IsAffineOpen O) (hO' : AlgebraicGeometry.IsAffineOpen O')
    (hle : O' ≤ O) (e : E.obj Y ≅ affObj B hT V₀ O hO)
    (e' : E.obj Y' ≅ affObj B hT V₀ O' hO')
    (ht : E.map t ≫ e.hom = e'.hom ≫ affObjLe B hT V₀ O' O hO' hO hle) :
    (AlgebraicGeometry.SmallAffineEtale.inclusion B R hR).map (Ψ.map t) ≫
        (imageEtaleIso B hT hR g V₀ E Ψ Fst hsq VR qR hVsq Y O hO e).hom =
      (imageEtaleIso B hT hR g V₀ E Ψ Fst hsq VR qR hVsq Y' O' hO' e').hom ≫
        etaleObjLe B R hR VR (qR ⁻¹ᵁ O') (qR ⁻¹ᵁ O) (hO'.preimage qR) (hO.preimage qR)
          (qR.preimage_mono hle) :=
  ((AlgebraicGeometry.SmallAffineEtale.inclusion B R hR).map_comp _ _).symm.trans
    ((congrArg (AlgebraicGeometry.SmallAffineEtale.inclusion B R hR).map
        (map_comp_imageIso B hT hR g V₀ E Ψ Fst hsq VR qR hVsq t O O' hO hO' hle e e' ht)).trans
      ((AlgebraicGeometry.SmallAffineEtale.inclusion B R hR).map_comp _ _))

include hsq hVsq in
/-- **The images of a datum of affine opens of `V₀` are a one-hypercover of the base change of
`V₀`.** A family of affine opens covering `V₀`, with affine opens covering each pairwise overlap,
whose objects are identified with the `T`-side images of a family of objects of `C₀`: then the
`R`-side images of that family, with the identifications of `imageEtaleIso` for legs, are a
one-hypercover of `VR` in the small etale site of `R`.

This is `Stacks.EtaleCohomology.QcSeparatedSections.isOneHypercoverOf_etaleObjOfAffineOpen` for the
preimage datum -- which is a datum by `preimage_oneHypercover_data`, the base-change projection
being affine -- carried along the identifications by
`Stacks.WeakSites.ColimitGlobalSections.IsOneHypercoverOf.of_iso`.  The legs are not a hypothesis
but the composites `of_iso` asks for, so its covering clause and its agreement clause come for
free; the two projection equations are `map_comp_imageEtaleIso`. -/
theorem isOneHypercoverOf_image {κ ν : Type u}
    (O : κ → ((AlgebraicGeometry.SmallEtale.toScheme B T hT).obj V₀).Opens)
    (P : κ → κ → ν → ((AlgebraicGeometry.SmallEtale.toScheme B T hT).obj V₀).Opens)
    (hOaff : ∀ k, AlgebraicGeometry.IsAffineOpen (O k))
    (hPaff : ∀ k l m, AlgebraicGeometry.IsAffineOpen (P k l m))
    (hOtop : (⨆ k, O k) = ⊤) (hPsup : ∀ k l, (⨆ m, P k l m) = O k ⊓ O l)
    (hPle : ∀ k l m, P k l m ≤ O k ⊓ O l)
    (W : κ → C₀) (Q : κ → κ → ν → C₀)
    (q₁ : ∀ k l m, Q k l m ⟶ W k) (q₂ : ∀ k l m, Q k l m ⟶ W l)
    (eW : ∀ k, E.obj (W k) ≅ affObj B hT V₀ (O k) (hOaff k))
    (eQ : ∀ k l m, E.obj (Q k l m) ≅ affObj B hT V₀ (P k l m) (hPaff k l m))
    (h₁ : ∀ k l m, E.map (q₁ k l m) ≫ (eW k).hom =
      (eQ k l m).hom ≫ affObjLe B hT V₀ (P k l m) (O k) (hPaff k l m) (hOaff k)
        ((hPle k l m).trans inf_le_left))
    (h₂ : ∀ k l m, E.map (q₂ k l m) ≫ (eW l).hom =
      (eQ k l m).hom ≫ affObjLe B hT V₀ (P k l m) (O l) (hPaff k l m) (hOaff l)
        ((hPle k l m).trans inf_le_right)) :
    IsOneHypercoverOf (AlgebraicGeometry.SmallEtale.topology B R hR) VR
      (fun k => (AlgebraicGeometry.SmallAffineEtale.inclusion B R hR).obj (Ψ.obj (W k)))
      (fun k => (imageEtaleIso B hT hR g V₀ E Ψ Fst hsq VR qR hVsq (W k) (O k) (hOaff k)
          (eW k)).hom ≫
        etaleObjToAmbient B R hR VR (qR ⁻¹ᵁ O k) ((hOaff k).preimage qR))
      (fun k l m =>
        (AlgebraicGeometry.SmallAffineEtale.inclusion B R hR).obj (Ψ.obj (Q k l m)))
      (fun k l m =>
        (AlgebraicGeometry.SmallAffineEtale.inclusion B R hR).map (Ψ.map (q₁ k l m)))
      (fun k l m =>
        (AlgebraicGeometry.SmallAffineEtale.inclusion B R hR).map (Ψ.map (q₂ k l m))) := by
  obtain ⟨-, -, hOtop', hPle', hPsup'⟩ :=
    preimage_oneHypercover_data qR O P hOaff hPaff hOtop hPsup
  refine (isOneHypercoverOf_etaleObjOfAffineOpen B R hR VR (fun k => qR ⁻¹ᵁ O k)
      (fun k l m => qR ⁻¹ᵁ P k l m) (fun k => (hOaff k).preimage qR)
      (fun k l m => (hPaff k l m).preimage qR) hPle' hOtop' hPsup').of_iso
    (fun k => (imageEtaleIso B hT hR g V₀ E Ψ Fst hsq VR qR hVsq (W k) (O k) (hOaff k)
      (eW k)).symm)
    (fun k l m => (imageEtaleIso B hT hR g V₀ E Ψ Fst hsq VR qR hVsq (Q k l m) (P k l m)
      (hPaff k l m) (eQ k l m)).symm)
    (fun _ => rfl) (fun k l m => ?_) (fun k l m => ?_)
  · exact ((Iso.eq_comp_inv _).2 (map_comp_imageEtaleIso B hT hR g V₀ E Ψ Fst hsq VR qR hVsq
      (q₁ k l m) (O k) (P k l m) (hOaff k) (hPaff k l m) ((hPle k l m).trans inf_le_left)
      (eW k) (eQ k l m) (h₁ k l m))).trans (Category.assoc _ _ _)
  · exact ((Iso.eq_comp_inv _).2 (map_comp_imageEtaleIso B hT hR g V₀ E Ψ Fst hsq VR qR hVsq
      (q₂ k l m) (O l) (P k l m) (hOaff l) (hPaff k l m) ((hPle k l m).trans inf_le_right)
      (eW l) (eQ k l m) (h₂ k l m))).trans (Category.assoc _ _ _)

/-- `isOneHypercoverOf_image` for the images of the objects of an equivalence `E`, with the
identifications the counit of `E` provides. -/
private theorem isOneHypercoverOf_image_of_isEquivalence [E.IsEquivalence] {κ ν : Type u}
    (O : κ → ((AlgebraicGeometry.SmallEtale.toScheme B T hT).obj V₀).Opens)
    (P : κ → κ → ν → ((AlgebraicGeometry.SmallEtale.toScheme B T hT).obj V₀).Opens)
    (hOaff : ∀ k, AlgebraicGeometry.IsAffineOpen (O k))
    (hPaff : ∀ k l m, AlgebraicGeometry.IsAffineOpen (P k l m))
    (hOtop : (⨆ k, O k) = ⊤) (hPsup : ∀ k l, (⨆ m, P k l m) = O k ⊓ O l)
    (hPle : ∀ k l m, P k l m ≤ O k ⊓ O l) :
    IsOneHypercoverOf (AlgebraicGeometry.SmallEtale.topology B R hR) VR
      (fun k => (AlgebraicGeometry.SmallAffineEtale.inclusion B R hR).obj
        (Ψ.obj (E.inv.obj (affObj B hT V₀ (O k) (hOaff k)))))
      (fun k => (imageEtaleIso B hT hR g V₀ E Ψ Fst hsq VR qR hVsq
          (E.inv.obj (affObj B hT V₀ (O k) (hOaff k))) (O k) (hOaff k)
          (E.asEquivalence.counitIso.app _)).hom ≫
        etaleObjToAmbient B R hR VR (qR ⁻¹ᵁ O k) ((hOaff k).preimage qR))
      (fun k l m => (AlgebraicGeometry.SmallAffineEtale.inclusion B R hR).obj
        (Ψ.obj (E.inv.obj (affObj B hT V₀ (P k l m) (hPaff k l m)))))
      (fun k l m => (AlgebraicGeometry.SmallAffineEtale.inclusion B R hR).map
        (Ψ.map (E.inv.map (affObjLe B hT V₀ (P k l m) (O k) (hPaff k l m) (hOaff k)
          ((hPle k l m).trans inf_le_left)))))
      (fun k l m => (AlgebraicGeometry.SmallAffineEtale.inclusion B R hR).map
        (Ψ.map (E.inv.map (affObjLe B hT V₀ (P k l m) (O l) (hPaff k l m) (hOaff l)
          ((hPle k l m).trans inf_le_right))))) :=
  isOneHypercoverOf_image B hT hR g V₀ E Ψ Fst hsq VR qR hVsq O P hOaff hPaff hOtop hPsup hPle
    _ _ _ _ (fun _ => E.asEquivalence.counitIso.app _)
    (fun _ _ _ => E.asEquivalence.counitIso.app _)
    (fun _ _ _ => E.asEquivalence.counitIso.hom.naturality _)
    (fun _ _ _ => E.asEquivalence.counitIso.hom.naturality _)

end Abstract

/-! ### The etale system: the level crossing and the base changes -/

section Geometric

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (D : Iᵒᵖ ⥤ Scheme.{max u v}) (c : Cone D)
  (B : AlgebraicGeometry.BigEtaleSite.{max u v})
  (hD : ∀ i, B.Contains (D.obj i)) (hX : B.Contains c.pt)
  (hc : IsLimit c)
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]

/-- The index of the inverse system of schemes carried by a level of the system of sites. -/
abbrev levelIndex (n : (sys D c B hD hX hc).I) : Iᵒᵖ :=
  (affineEtaleSiteColimit D c B hD hX hc).indexEquiv.functor.obj n

/-- **The crossing from a level of the system of Stacks 0EYL to the small etale site of its
scheme.** The level equivalence followed by the inclusion of Stacks 04HR.

This is the level-side counterpart of
`Stacks.EtaleCohomology.AffineLimitCohomology.limitToSmallEtale`, and the asymmetry between them
is the whole of what the level side of the degree-zero statement needed: at the limit the crossing
is a universe raising followed by 04HR, both of which are restrictions along functors that are
already there, while a level of this system is a category of *representatives* of the small affine
etale site of `X_n`, so the first factor is the level equivalence and its continuity is
`Stacks.EtaleCohomology.affineEtaleSiteColimit_levelToSmallEtale_isContinuous`. -/
def levelToSmallEtale (n : (sys D c B hD hX hc).I) :
    (sys D c B hD hX hc).C n ⥤
      AlgebraicGeometry.SmallEtale B (D.obj (levelIndex D c B hD hX hc n))
        (hD (levelIndex D c B hD hX hc n)) :=
  ((affineEtaleSiteColimit D c B hD hX hc).levelEquiv n).functor ⋙
    AlgebraicGeometry.SmallAffineEtale.inclusion B _ _

/-- The crossing is a morphism of sites. -/
theorem isContinuous_levelToSmallEtale (n : (sys D c B hD hX hc).I) :
    (levelToSmallEtale D c B hD hX hc n).IsContinuous ((sys D c B hD hX hc).J n)
      (AlgebraicGeometry.SmallEtale.topology B (D.obj (levelIndex D c B hD hX hc n))
        (hD (levelIndex D c B hD hX hc n))) :=
  affineEtaleSiteColimit_levelToSmallEtale_isContinuous D c B hD hX hc n

/-- **A sheaf of sets on the small etale site of `X_n`, read on the level `n`.** The level-side
counterpart of `Stacks.EtaleCohomology.AffineLimitCohomology.raisedSheaf`, and what exhibits the
hypotheses `Hs` and `en` of the degree-zero statement below: the sheaf of a level may be taken to
be the restriction of a sheaf on the small etale site of `X_n`, and
`Stacks.EtaleCohomology.affineEtaleSiteColimit_levelToSmallEtale_sheafEquiv` says that this is no
restriction on it -- every sheaf of a level is isomorphic to such a restriction. -/
def levelRaisedSheaf (n : (sys D c B hD hX hc).I)
    (F : Sheaf (AlgebraicGeometry.SmallEtale.topology B (D.obj (levelIndex D c B hD hX hc n))
      (hD (levelIndex D c B hD hX hc n))) (Type (max u v + 1))) :
    Sheaf ((sys D c B hD hX hc).J n) (Type (max u v + 1)) :=
  letI := isContinuous_levelToSmallEtale D c B hD hX hc n
  ((levelToSmallEtale D c B hD hX hc n).sheafPushforwardContinuous (Type (max u v + 1))
    ((sys D c B hD hX hc).J n)
    (AlgebraicGeometry.SmallEtale.topology B (D.obj (levelIndex D c B hD hX hc n))
      (hD (levelIndex D c B hD hX hc n)))).obj F

/-- Reading a sheaf on the small etale site of `X_n` on the level does not change its sections:
the underlying presheaf is restriction along the crossing, on the nose. -/
theorem levelRaisedSheaf_obj (n : (sys D c B hD hX hc).I)
    (F : Sheaf (AlgebraicGeometry.SmallEtale.topology B (D.obj (levelIndex D c B hD hX hc n))
      (hD (levelIndex D c B hD hX hc n))) (Type (max u v + 1))) :
    (levelRaisedSheaf D c B hD hX hc n F).obj =
      (levelToSmallEtale D c B hD hX hc n).op ⋙ F.obj :=
  rfl

/-! #### The base changes of an etale object of a level -/

/-- The transition morphism of schemes between two levels of the system. -/
abbrev transitionScheme {i j : (sys D c B hD hX hc).I} (a : j ⟶ i) :
    D.obj (levelIndex D c B hD hX hc j) ⟶ D.obj (levelIndex D c B hD hX hc i) :=
  D.map ((affineEtaleSiteColimit D c B hD hX hc).indexEquiv.functor.map a)

/-- The transition morphism between two levels, as a morphism of the big etale site. -/
abbrev transitionBigHom {i j : (sys D c B hD hX hc).I} (a : j ⟶ i) :
    B.obj (D.obj (levelIndex D c B hD hX hc j)) (hD _) ⟶
      B.obj (D.obj (levelIndex D c B hD hX hc i)) (hD _) :=
  ObjectProperty.homMk (transitionScheme D c B hD hX hc a)

/-- **The base change of an etale object of a level to a lower level, as data.** For an object
`V₀` of the small etale site of `X_i` and an arrow `a : n ⟶ i`, the object `V_n = V₀ ×_{X_i} X_n`
of the small etale site of `X_n`.

The degree-zero statement of Stacks 09YQ over `V₀` is about the sections of the `F_n` over these
objects, so they are data of the statement and not merely a hypothesis that something fits in a
square. -/
def transitionBaseChangeEtaleObj {i : (sys D c B hD hX hc).I}
    (V₀ : AlgebraicGeometry.SmallEtale B (D.obj (levelIndex D c B hD hX hc i)) (hD _))
    {n : (sys D c B hD hX hc).I} (a : n ⟶ i) :
    AlgebraicGeometry.SmallEtale B (D.obj (levelIndex D c B hD hX hc n)) (hD _) :=
  (AlgebraicGeometry.smallEtaleBaseChange B (transitionBigHom D c B hD hX hc a)).obj V₀

/-- The projection of the base change onto `V₀`. -/
def transitionBaseChangeProj {i : (sys D c B hD hX hc).I}
    (V₀ : AlgebraicGeometry.SmallEtale B (D.obj (levelIndex D c B hD hX hc i)) (hD _))
    {n : (sys D c B hD hX hc).I} (a : n ⟶ i) :
    (AlgebraicGeometry.SmallEtale.toScheme B (D.obj (levelIndex D c B hD hX hc n))
        (hD _)).obj (transitionBaseChangeEtaleObj D c B hD hX hc V₀ a) ⟶
      (AlgebraicGeometry.SmallEtale.toScheme B (D.obj (levelIndex D c B hD hX hc i))
        (hD _)).obj V₀ :=
  B.inclusion.map (pullback.fst V₀.obj.hom (transitionBigHom D c B hD hX hc a))

/-- **The base change of an etale object of a level is a fibre product.** The square that
`imageIsoObjOfPreimageOver` consumes on the level side. -/
theorem transitionBaseChangeEtaleObj_isPullback {i : (sys D c B hD hX hc).I}
    (V₀ : AlgebraicGeometry.SmallEtale B (D.obj (levelIndex D c B hD hX hc i)) (hD _))
    {n : (sys D c B hD hX hc).I} (a : n ⟶ i) :
    IsPullback (transitionBaseChangeProj D c B hD hX hc V₀ a)
      (B.inclusion.map (transitionBaseChangeEtaleObj D c B hD hX hc V₀ a).obj.hom)
      (B.inclusion.map V₀.obj.hom) (transitionScheme D c B hD hX hc a) :=
  AlgebraicGeometry.SmallEtale.isPullback_smallEtaleBaseChange B
    (transitionBigHom D c B hD hX hc a) V₀

/-- The projection of the base change is affine, the transition morphism being affine. -/
instance isAffineHom_transitionBaseChangeProj {i : (sys D c B hD hX hc).I}
    (V₀ : AlgebraicGeometry.SmallEtale B (D.obj (levelIndex D c B hD hX hc i)) (hD _))
    {n : (sys D c B hD hX hc).I} (a : n ⟶ i) :
    IsAffineHom (transitionBaseChangeProj D c B hD hX hc V₀ a) :=
  MorphismProperty.of_isPullback
    (transitionBaseChangeEtaleObj_isPullback D c B hD hX hc V₀ a).flip
    (show IsAffineHom (transitionScheme D c B hD hX hc a) from inferInstance)

/-- The projection of the limit cone to a level, as a morphism of the big etale site. -/
abbrev toLimitBigHom (i : (sys D c B hD hX hc).I) :
    B.obj c.pt hX ⟶ B.obj (D.obj (levelIndex D c B hD hX hc i)) (hD _) :=
  ObjectProperty.homMk (c.π.app (levelIndex D c B hD hX hc i))

/-- **The base change of an etale object of a level to the limit, as data.** The object
`V_X = V₀ ×_{X_{i₀}} X` of the small etale site of `X = lim X_i`, over which the sections of
`𝒢 = colim f_i^{-1}F_i` are computed. -/
def toLimitBaseChangeEtaleObj {i : (sys D c B hD hX hc).I}
    (V₀ : AlgebraicGeometry.SmallEtale B (D.obj (levelIndex D c B hD hX hc i)) (hD _)) :
    AlgebraicGeometry.SmallEtale B c.pt hX :=
  (AlgebraicGeometry.smallEtaleBaseChange B (toLimitBigHom D c B hD hX hc i)).obj V₀

/-- The projection of the base change to the limit onto `V₀`. -/
def toLimitBaseChangeProj {i : (sys D c B hD hX hc).I}
    (V₀ : AlgebraicGeometry.SmallEtale B (D.obj (levelIndex D c B hD hX hc i)) (hD _)) :
    (AlgebraicGeometry.SmallEtale.toScheme B c.pt hX).obj
        (toLimitBaseChangeEtaleObj D c B hD hX hc V₀) ⟶
      (AlgebraicGeometry.SmallEtale.toScheme B (D.obj (levelIndex D c B hD hX hc i))
        (hD _)).obj V₀ :=
  B.inclusion.map (pullback.fst V₀.obj.hom (toLimitBigHom D c B hD hX hc i))

/-- **The base change to the limit is a fibre product.** The square that
`imageIsoObjOfPreimageOver` consumes on the limit side. -/
theorem toLimitBaseChangeEtaleObj_isPullback {i : (sys D c B hD hX hc).I}
    (V₀ : AlgebraicGeometry.SmallEtale B (D.obj (levelIndex D c B hD hX hc i)) (hD _)) :
    IsPullback (toLimitBaseChangeProj D c B hD hX hc V₀)
      (B.inclusion.map (toLimitBaseChangeEtaleObj D c B hD hX hc V₀).obj.hom)
      (B.inclusion.map V₀.obj.hom) (c.π.app (levelIndex D c B hD hX hc i)) :=
  AlgebraicGeometry.SmallEtale.isPullback_smallEtaleBaseChange B
    (toLimitBigHom D c B hD hX hc i) V₀

/-- The projection of the base change to the limit is affine.

Affineness of the projection of the limit cone is an instance BINDER rather than taken from
`Stacks.EtaleCohomology.QcqsLimitCohomology.isAffineHom_limitProjection` inside, for the reason
recorded there: the statements that consume this name the preimage of an open along it, which is
elaborated before any tactic runs, and that theorem takes `hc : IsLimit c`, which typeclass
synthesis cannot infer. Callers discharge the binder with a `have`. -/
instance isAffineHom_toLimitBaseChangeProj {i : (sys D c B hD hX hc).I}
    (V₀ : AlgebraicGeometry.SmallEtale B (D.obj (levelIndex D c B hD hX hc i)) (hD _))
    [IsAffineHom (c.π.app (levelIndex D c B hD hX hc i))] :
    IsAffineHom (toLimitBaseChangeProj D c B hD hX hc V₀) :=
  MorphismProperty.of_isPullback
    (toLimitBaseChangeEtaleObj_isPullback D c B hD hX hc V₀).flip
    (show IsAffineHom (c.π.app (levelIndex D c B hD hX hc i)) from inferInstance)

/-! #### PIECE (a): the transition images and the images at the limit -/

/-- **The transition image of the object of an affine open of `V₀` is the object of the preimage
open in the base change of `V₀`.** The relative counterpart of
`Stacks.EtaleCohomology.QcqsLimitCohomology.transitionImage_isoObjOfPreimage`, whose opens are
opens of the level: the Cech step over an etale object `V₀` of a level has for its datum the
affine opens of `V₀`, so their transition images are the preimages inside the base change `V_n`
of `V₀` and not inside the base change of the level.

`imageIsoObjOfPreimageOver` does the work, at the abstract base change; this feeds it the two
fibre-product squares the system supplies -- `transition_isPullback` for the image of the object
and `transitionBaseChangeEtaleObj_isPullback` for the base change of `V₀` -- and the unit of the
level equivalence carries the result back to the level, exactly as in the absolute case. -/
def transitionImage_isoObjOfPreimageOver {i : (sys D c B hD hX hc).I}
    (V₀ : AlgebraicGeometry.SmallEtale B (D.obj (levelIndex D c B hD hX hc i)) (hD _))
    {n : (sys D c B hD hX hc).I} (a : n ⟶ i) (Y : (sys D c B hD hX hc).C i)
    (O : ((AlgebraicGeometry.SmallEtale.toScheme B (D.obj (levelIndex D c B hD hX hc i))
      (hD _)).obj V₀).Opens)
    (hO : AlgebraicGeometry.IsAffineOpen O)
    (e : ((affineEtaleSiteColimit D c B hD hX hc).levelEquiv i).functor.obj Y ≅
      affObj B (hD _) V₀ O hO) :
    ((sys D c B hD hX hc).u a).obj Y ≅
      ((affineEtaleSiteColimit D c B hD hX hc).levelEquiv n).inverse.obj
        (affObj B (hD _) (transitionBaseChangeEtaleObj D c B hD hX hc V₀ a)
          (transitionBaseChangeProj D c B hD hX hc V₀ a ⁻¹ᵁ O)
          (hO.preimage (transitionBaseChangeProj D c B hD hX hc V₀ a))) :=
  ((affineEtaleSiteColimit D c B hD hX hc).levelEquiv n).unitIso.app _ ≪≫
    (((affineEtaleSiteColimit D c B hD hX hc).levelEquiv n).inverse.mapIso
      (imageIsoObjOfPreimageOver B (hD _) (hD _) (transitionScheme D c B hD hX hc a) V₀
        ((affineEtaleSiteColimit D c B hD hX hc).levelEquiv i).functor
        ((sys D c B hD hX hc).u a ⋙
          ((affineEtaleSiteColimit D c B hD hX hc).levelEquiv n).functor)
        ((affineEtaleSiteColimit D c B hD hX hc).transitionFst a)
        (fun Z => (affineEtaleSiteColimit D c B hD hX hc).transition_isPullback a Z)
        (transitionBaseChangeEtaleObj D c B hD hX hc V₀ a)
        (transitionBaseChangeProj D c B hD hX hc V₀ a)
        (transitionBaseChangeEtaleObj_isPullback D c B hD hX hc V₀ a) Y O hO e))

/-- **The image in the site of `X` of the object of an affine open of `V₀` is the object of the
preimage open in the base change of `V₀` to `X`.** The limit-side counterpart of
`transitionImage_isoObjOfPreimageOver`, by the same construction off the other fibre-product field
of `Stacks.EtaleCohomology.AffineEtaleSiteColimit`; there is no level equivalence to undo, the
functors to the limit landing in the small affine etale site of `X` itself.

Affineness of the projection of the limit cone is an instance BINDER, for the reason recorded on
`Stacks.EtaleCohomology.QcqsLimitCohomology.toLimitImage_isoObjOfPreimage`. -/
def toLimitImage_isoObjOfPreimageOver (i : (sys D c B hD hX hc).I)
    (V₀ : AlgebraicGeometry.SmallEtale B (D.obj (levelIndex D c B hD hX hc i)) (hD _))
    (Y : (sys D c B hD hX hc).C i)
    (O : ((AlgebraicGeometry.SmallEtale.toScheme B (D.obj (levelIndex D c B hD hX hc i))
      (hD _)).obj V₀).Opens)
    (hO : AlgebraicGeometry.IsAffineOpen O)
    (e : ((affineEtaleSiteColimit D c B hD hX hc).levelEquiv i).functor.obj Y ≅
      affObj B (hD _) V₀ O hO)
    [IsAffineHom (c.π.app (levelIndex D c B hD hX hc i))] :
    ((affineEtaleSiteColimit D c B hD hX hc).toLimit i).obj Y ≅
      affObj B hX (toLimitBaseChangeEtaleObj D c B hD hX hc V₀)
        (toLimitBaseChangeProj D c B hD hX hc V₀ ⁻¹ᵁ O)
        (hO.preimage (toLimitBaseChangeProj D c B hD hX hc V₀)) :=
  imageIsoObjOfPreimageOver B (hD _) hX (c.π.app (levelIndex D c B hD hX hc i)) V₀
    ((affineEtaleSiteColimit D c B hD hX hc).levelEquiv i).functor
    ((affineEtaleSiteColimit D c B hD hX hc).toLimit i)
    ((affineEtaleSiteColimit D c B hD hX hc).toLimitFst i)
    (fun Z => (affineEtaleSiteColimit D c B hD hX hc).toLimit_isPullback i Z)
    (toLimitBaseChangeEtaleObj D c B hD hX hc V₀) (toLimitBaseChangeProj D c B hD hX hc V₀)
    (toLimitBaseChangeEtaleObj_isPullback D c B hD hX hc V₀) Y O hO e

/-! #### The datum: one finite family covering `V₀` at every level and at the limit -/

/-- **The limit half of the covering datum, named.** A finite datum of objects of the level `i₀`,
with legs `fV`, whose image in the small etale site of `X` is a one-hypercover of the base change
`V_X` of `V₀` to `X`.

It is named rather than written out for the reason recorded on
`CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites.RestrictionIsColimit`, which applies
here: the degree-zero statement below mentions this condition and the level one together with
everything else, and writing both out exhausts the elaborator's 200000 heartbeats in the
*signature* -- a `(deterministic) timeout at isDefEq` inside the limit half, before any proof
runs. Raising an option is not available in this development. -/
def IsLimitOneHypercoverDatum (i₀ : (sys D c B hD hX hc).I)
    (V₀ : AlgebraicGeometry.SmallEtale B (D.obj (levelIndex D c B hD hX hc i₀)) (hD _))
    {κ' ν' : Type} (W₀ : κ' → (sys D c B hD hX hc).C i₀)
    (P₀ : κ' → κ' → ν' → (sys D c B hD hX hc).C i₀)
    (q₁ : ∀ k l m, P₀ k l m ⟶ W₀ k) (q₂ : ∀ k l m, P₀ k l m ⟶ W₀ l)
    (fV : ∀ k, (limitToSmallEtale D c B hX).obj
      ((toLimitSmall D c B hD hX hc i₀).obj (W₀ k)) ⟶
        toLimitBaseChangeEtaleObj D c B hD hX hc V₀) : Prop :=
  IsOneHypercoverOf (AlgebraicGeometry.SmallEtale.topology B c.pt hX)
    (toLimitBaseChangeEtaleObj D c B hD hX hc V₀)
    (fun k => (limitToSmallEtale D c B hX).obj
      ((toLimitSmall D c B hD hX hc i₀).obj (W₀ k))) fV
    (fun k l m => (limitToSmallEtale D c B hX).obj
      ((toLimitSmall D c B hD hX hc i₀).obj (P₀ k l m)))
    (fun k l m => (limitToSmallEtale D c B hX).map
      ((toLimitSmall D c B hD hX hc i₀).map (q₁ k l m)))
    (fun k l m => (limitToSmallEtale D c B hX).map
      ((toLimitSmall D c B hD hX hc i₀).map (q₂ k l m)))

/-- **The level half of the covering datum, named.** The same datum, with legs `fVn`, whose
transition image at every level `n` below `i₀` is a one-hypercover of the base change `V_n` of
`V₀` there. Named for the same reason as `IsLimitOneHypercoverDatum`. -/
def IsLevelOneHypercoverDatum (i₀ : (sys D c B hD hX hc).I)
    (V₀ : AlgebraicGeometry.SmallEtale B (D.obj (levelIndex D c B hD hX hc i₀)) (hD _))
    {κ' ν' : Type} (W₀ : κ' → (sys D c B hD hX hc).C i₀)
    (P₀ : κ' → κ' → ν' → (sys D c B hD hX hc).C i₀)
    (q₁ : ∀ k l m, P₀ k l m ⟶ W₀ k) (q₂ : ∀ k l m, P₀ k l m ⟶ W₀ l)
    (fVn : ∀ (n : (sys D c B hD hX hc).I) (a : n ⟶ i₀) (k : κ'),
      (levelToSmallEtale D c B hD hX hc n).obj (((sys D c B hD hX hc).u a).obj (W₀ k)) ⟶
        transitionBaseChangeEtaleObj D c B hD hX hc V₀ a) : Prop :=
  ∀ (n : (sys D c B hD hX hc).I) (a : n ⟶ i₀),
    IsOneHypercoverOf (AlgebraicGeometry.SmallEtale.topology B
        (D.obj (levelIndex D c B hD hX hc n)) (hD _))
      (transitionBaseChangeEtaleObj D c B hD hX hc V₀ a)
      (fun k => (levelToSmallEtale D c B hD hX hc n).obj
        (((sys D c B hD hX hc).u a).obj (W₀ k))) (fVn n a)
      (fun k l m => (levelToSmallEtale D c B hD hX hc n).obj
        (((sys D c B hD hX hc).u a).obj (P₀ k l m)))
      (fun k l m => (levelToSmallEtale D c B hD hX hc n).map
        (((sys D c B hD hX hc).u a).map (q₁ k l m)))
      (fun k l m => (levelToSmallEtale D c B hD hX hc n).map
        (((sys D c B hD hX hc).u a).map (q₂ k l m)))

/-- **The covering datum of the degree-zero statement, bundled.** A finite family of objects of
the level `i₀`, with finitely many objects over each pair, legs to the base change of `V₀` at the
limit and at every lower level, and the two one-hypercover conditions.

Bundled because the degree-zero statement cannot afford it unbundled: its eight components
mention `(sys …).I`, `.C i₀` and `.u a` some thirty times and the signature exceeds the
elaborator's heartbeat budget before any proof runs, which is the rule recorded on
`CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites.RestrictionIsColimit`. -/
structure OneHypercoverDatum (i₀ : (sys D c B hD hX hc).I)
    (V₀ : AlgebraicGeometry.SmallEtale B (D.obj (levelIndex D c B hD hX hc i₀)) (hD _)) where
  /-- The index type of the cover of `V₀`. -/
  κ' : Type
  /-- The index type of the covers of the pairwise overlaps. -/
  ν' : Type
  /-- The cover is finite. -/
  finite_κ : Finite κ'
  /-- The covers of the overlaps are finite. -/
  finite_ν : Finite ν'
  /-- The objects of the level `i₀` covering `V₀`. -/
  W₀ : κ' → (sys D c B hD hX hc).C i₀
  /-- The objects over each pair. -/
  P₀ : κ' → κ' → ν' → (sys D c B hD hX hc).C i₀
  /-- The first projection. -/
  q₁ : ∀ k l m, P₀ k l m ⟶ W₀ k
  /-- The second projection. -/
  q₂ : ∀ k l m, P₀ k l m ⟶ W₀ l
  /-- The legs to the base change of `V₀` to the limit. -/
  fV : ∀ k, (limitToSmallEtale D c B hX).obj
    ((toLimitSmall D c B hD hX hc i₀).obj (W₀ k)) ⟶
      toLimitBaseChangeEtaleObj D c B hD hX hc V₀
  /-- The legs to the base change of `V₀` to a lower level. -/
  fVn : ∀ (n : (sys D c B hD hX hc).I) (a : n ⟶ i₀) (k : κ'),
    (levelToSmallEtale D c B hD hX hc n).obj (((sys D c B hD hX hc).u a).obj (W₀ k)) ⟶
      transitionBaseChangeEtaleObj D c B hD hX hc V₀ a
  /-- The image of the datum at the limit is a one-hypercover of the base change there. -/
  isLimitDatum : IsLimitOneHypercoverDatum D c B hD hX hc i₀ V₀ W₀ P₀ q₁ q₂ fV
  /-- The transition image of the datum at every lower level is a one-hypercover of the base
  change there. -/
  isLevelDatum : IsLevelOneHypercoverDatum D c B hD hX hc i₀ V₀ W₀ P₀ q₁ q₂ fVn

include hc in
/-- **The covering datum of Stacks 09YQ in degree zero over a quasi-compact quasi-separated etale
object `V₀` of a level.** There is a finite family of objects of the level `i₀`, with finitely
many objects over each pair, which is simultaneously a one-hypercover of the base change `V_n` of
`V₀` at EVERY level below `i₀`, in its transition images, and a one-hypercover of the base change
`V_X` of `V₀` to `X`, in its image there.

These are the hypotheses `hV` and `hVn` of
`Stacks.WeakSites.ColimitGlobalSections.sectionOver_colimit_of_oneHypercoverOf'`, and they are
produced together because that theorem needs them for ONE family: the consumer fixes `W₀`, `P₀`,
`q₁`, `q₂` and asks for both, so an existential supplying only one of them supplies nothing it can
use. This is the relative counterpart of
`Stacks.EtaleCohomology.QcqsLimitCohomology.exists_hlev_and_hC`, whose datum covers the terminal
sheaf of each site rather than an object of an ambient one.

The family is what a finite affine cover of `V₀` and finite affine covers of its pairwise
intersections give (`Stacks.QcqsOneHypercover.exists_finite_affine_oneHypercover_opens`, for which
quasi-compactness and quasi-separatedness of `V₀` is exactly what is needed), carried to the level
`i₀` by the level equivalence. Both halves are then `isOneHypercoverOf_image` at the two
fibre-product fields of `Stacks.EtaleCohomology.AffineEtaleSiteColimit`, which sit beside each
other for this reason, and the four compatibility equations it asks for are in each case ONE fact:
the naturality of the counit of the level equivalence. -/
theorem exists_oneHypercoverOf_datum (i₀ : (sys D c B hD hX hc).I)
    (V₀ : AlgebraicGeometry.SmallEtale B (D.obj (levelIndex D c B hD hX hc i₀)) (hD _))
    [CompactSpace ((AlgebraicGeometry.SmallEtale.toScheme B
      (D.obj (levelIndex D c B hD hX hc i₀)) (hD _)).obj V₀)]
    [QuasiSeparatedSpace ((AlgebraicGeometry.SmallEtale.toScheme B
      (D.obj (levelIndex D c B hD hX hc i₀)) (hD _)).obj V₀)]
    [IsAffineHom (c.π.app (levelIndex D c B hD hX hc i₀))] :
    Nonempty (OneHypercoverDatum D c B hD hX hc i₀ V₀) := by
  obtain ⟨κ, ν, hκ, hν, O, P, hOaff, hPaff, hOtop, hPle, hPsup⟩ :=
    Stacks.QcqsOneHypercover.exists_finite_affine_oneHypercover_opens
      ((AlgebraicGeometry.SmallEtale.toScheme B (D.obj (levelIndex D c B hD hX hc i₀))
        (hD _)).obj V₀)
  obtain ⟨nκ, ⟨eκ⟩⟩ := Finite.exists_equiv_fin κ
  obtain ⟨nν, ⟨eν⟩⟩ := Finite.exists_equiv_fin ν
  refine ⟨⟨Fin nκ, Fin nν, inferInstance, inferInstance, _, _, _, _, _, _,
    (isOneHypercoverOf_image_of_isEquivalence B (hD _) hX (c.π.app (levelIndex D c B hD hX hc i₀))
      V₀ ((affineEtaleSiteColimit D c B hD hX hc).levelEquiv i₀).functor
      ((affineEtaleSiteColimit D c B hD hX hc).toLimit i₀)
      ((affineEtaleSiteColimit D c B hD hX hc).toLimitFst i₀)
      (fun Z => (affineEtaleSiteColimit D c B hD hX hc).toLimit_isPullback i₀ Z)
      (toLimitBaseChangeEtaleObj D c B hD hX hc V₀)
      (toLimitBaseChangeProj D c B hD hX hc V₀)
      (toLimitBaseChangeEtaleObj_isPullback D c B hD hX hc V₀)
      O P hOaff hPaff hOtop hPsup hPle).reindex eκ.symm eν.symm,
    fun n a => (isOneHypercoverOf_image_of_isEquivalence B (hD _) (hD _)
      (transitionScheme D c B hD hX hc a) V₀
      ((affineEtaleSiteColimit D c B hD hX hc).levelEquiv i₀).functor
      ((sys D c B hD hX hc).u a ⋙
        ((affineEtaleSiteColimit D c B hD hX hc).levelEquiv n).functor)
      ((affineEtaleSiteColimit D c B hD hX hc).transitionFst a)
      (fun Z => (affineEtaleSiteColimit D c B hD hX hc).transition_isPullback a Z)
      (transitionBaseChangeEtaleObj D c B hD hX hc V₀ a)
      (transitionBaseChangeProj D c B hD hX hc V₀ a)
      (transitionBaseChangeEtaleObj_isPullback D c B hD hX hc V₀ a)
      O P hOaff hPaff hOtop hPsup hPle).reindex eκ.symm eν.symm⟩⟩

/-! #### Degree zero -/

/-- **The two object-level inputs of the degree-zero statement, at the etale system.** Every
section of `𝒢` over the image of a level object comes from some level below, and two sections of a
level with the same image there agree at a further level.

These are the hypotheses `hsurjObj` and `hsep` of
`Stacks.WeakSites.ColimitGlobalSections.sectionOver_colimit_of_oneHypercoverOf'`, and they are
`InverseSystemOfFiniteSites.sections_colimit_pullback_of_colimit` -- the case `p = 0` of Stacks
09YN over an object of a level -- read at the five site inputs of Stacks 09YP for the raised site
of the limit: `toLimitSmall_transition`, `toLimitSmall_obj_descends`, `toLimitSmall_hom_descends`,
`toLimitSmall_hom_eventually_eq` and `mem_limitSitePrecoverage_iff`. So the only hypothesis on the
sheaves is a colimit presentation of `𝒢`. -/
theorem objectSections_surjective_and_separated
    (F : InverseSystemOfFiniteSites.SheafSystem.{v, v, max u v + 1} (sys D c B hD hX hc))
    (G : Sheaf (limitSitePrecoverage D c B hX).toGrothendieck (Type (max u v + 1)))
    (ι : ∀ i, (F.obj i).obj ⟶ (toLimitSmall D c B hD hX hc i).op ⋙ G.obj)
    (hpres : F.IsColimitPresentation (toLimitSmall D c B hD hX hc)
      (toLimitSmall_transition D c B hD hX hc) (limitSitePrecoverage D c B hX) G ι) :
    ObjectSectionsSurjective (sys D c B hD hX hc) (toLimitSmall D c B hD hX hc)
        (toLimitSmall_transition D c B hD hX hc) F.obj G ι ∧
      ObjectSectionsSeparated (sys D c B hD hX hc) (toLimitSmall D c B hD hX hc) F.obj F.map
        G ι := by
  obtain ⟨hιc, hG⟩ := hpres
  have main := fun (i : (sys D c B hD hX hc).I) (Y : (sys D c B hD hX hc).C i) =>
    InverseSystemOfFiniteSites.sections_colimit_pullback_of_colimit (sys D c B hD hX hc)
      (toLimitSmall D c B hD hX hc) (toLimitSmall_transition D c B hD hX hc)
      (toLimitSmall_obj_descends D c B hD hX hc) (toLimitSmall_hom_descends D c B hD hX hc)
      (toLimitSmall_hom_eventually_eq D c B hD hX hc) (limitSitePrecoverage D c B hX)
      (mem_limitSitePrecoverage_iff D c B hD hX hc) F.obj F.map F.map_comp G ι hιc hG i Y
      (fun {j} a t => G.obj.map (eqToHom (congrArg op (Functor.congr_obj
          (toLimitSmall_transition D c B hD hX hc a) Y)))
        ((ι j).app (op (((sys D c B hD hX hc).u a).obj Y)) t))
      (fun _ _ => rfl)
  exact ⟨fun i Y z => (main i Y).1 z, fun i Y j a t t' h => (main i Y).2 j a t t' (by rw [h])⟩

/-- **The pinning hypothesis of the degree-zero statement, named at the etale system.** The
restriction map `F_n(V_n) → 𝒢(V_X)` restricted to the objects of the datum is the leg `ι n`;
`Stacks.WeakSites.ColimitGlobalSections.SectionOverMapPinned` with the geometry plugged in.

Named for the reason the module header records: the degree-zero statement below
mentions this condition and its conclusion together with the sheaf data, and elaborating both
applications inside one signature exhausts the heartbeat budget before any proof runs.  A
definition of its own gets its own budget. -/
def SectionsMapPinned (i₀ : (sys D c B hD hX hc).I)
    (V₀ : AlgebraicGeometry.SmallEtale B (D.obj (levelIndex D c B hD hX hc i₀)) (hD _))
    (F : InverseSystemOfFiniteSites.SheafSystem.{v, v, max u v + 1} (sys D c B hD hX hc))
    (G : Sheaf (limitSitePrecoverage D c B hX).toGrothendieck (Type (max u v + 1)))
    (ι : ∀ i, (F.obj i).obj ⟶ (toLimitSmall D c B hD hX hc i).op ⋙ G.obj)
    (G' : Sheaf (AlgebraicGeometry.SmallEtale.topology B c.pt hX) (Type (max u v + 1)))
    (e₀ : (limitToSmallEtale D c B hX).op ⋙ G'.obj ≅ G.obj)
    (Hs : ∀ n, Sheaf (AlgebraicGeometry.SmallEtale.topology B
      (D.obj (levelIndex D c B hD hX hc n)) (hD _)) (Type (max u v + 1)))
    (en : ∀ n, (levelToSmallEtale D c B hD hX hc n).op ⋙ (Hs n).obj ≅ (F.obj n).obj)
    (E : OneHypercoverDatum D c B hD hX hc i₀ V₀)
    (ρ : ∀ (n : (sys D c B hD hX hc).I) (a : n ⟶ i₀),
      (Hs n).obj.obj (op (transitionBaseChangeEtaleObj D c B hD hX hc V₀ a)) →
        G'.obj.obj (op (toLimitBaseChangeEtaleObj D c B hD hX hc V₀))) : Prop :=
  SectionOverMapPinned (sys D c B hD hX hc) (toLimitSmall D c B hD hX hc)
    (toLimitSmall_transition D c B hD hX hc) F.obj G ι i₀ E.W₀ (limitToSmallEtale D c B hX)
    G' e₀ (toLimitBaseChangeEtaleObj D c B hD hX hc V₀) E.fV
    (levelToSmallEtale D c B hD hX hc) Hs en
    (fun _ a => transitionBaseChangeEtaleObj D c B hD hX hc V₀ a) E.fVn ρ

/-- **The conclusion of the degree-zero statement, named at the etale system.** The sections of
`𝒢` over the base change `V_X` of `V₀` to `X` are the filtered colimit, over the arrows `a : n ⟶
i₀`, of the sections of `F_n` over the base change `V_n`;
`Stacks.WeakSites.ColimitGlobalSections.SectionOverIsColimit` with the geometry plugged in.

Named for the same reason as `SectionsMapPinned`. -/
def SectionsIsColimit (i₀ : (sys D c B hD hX hc).I)
    (V₀ : AlgebraicGeometry.SmallEtale B (D.obj (levelIndex D c B hD hX hc i₀)) (hD _))
    (F : InverseSystemOfFiniteSites.SheafSystem.{v, v, max u v + 1} (sys D c B hD hX hc))
    (G' : Sheaf (AlgebraicGeometry.SmallEtale.topology B c.pt hX) (Type (max u v + 1)))
    (Hs : ∀ n, Sheaf (AlgebraicGeometry.SmallEtale.topology B
      (D.obj (levelIndex D c B hD hX hc n)) (hD _)) (Type (max u v + 1)))
    (en : ∀ n, (levelToSmallEtale D c B hD hX hc n).op ⋙ (Hs n).obj ≅ (F.obj n).obj)
    (E : OneHypercoverDatum D c B hD hX hc i₀ V₀)
    (ρ : ∀ (n : (sys D c B hD hX hc).I) (a : n ⟶ i₀),
      (Hs n).obj.obj (op (transitionBaseChangeEtaleObj D c B hD hX hc V₀ a)) →
        G'.obj.obj (op (toLimitBaseChangeEtaleObj D c B hD hX hc V₀))) : Prop :=
  SectionOverIsColimit (sys D c B hD hX hc) (toLimitSmall D c B hD hX hc) F.obj F.map i₀ E.W₀
    G' (toLimitBaseChangeEtaleObj D c B hD hX hc V₀) (levelToSmallEtale D c B hD hX hc) Hs en
    (fun _ a => transitionBaseChangeEtaleObj D c B hD hX hc V₀ a) E.fVn ρ

/-- **Stacks 09YQ in degree zero, over a quasi-compact quasi-separated etale object of a level.**
Let `(X_i)` be an inverse system of schemes over a directed index with affine transition morphisms
and limit `X`, let `F` be a system of sheaves of sets on the small affine etale sites of the `X_i`
and let `𝒢` on the site of `X` be the colimit `colim f_i^{-1}F_i`.  Let `V₀` be an object of the
small etale site of one level `X_{i₀}` whose underlying scheme is quasi-compact and
quasi-separated, let `V_n` be its base change to a lower level and `V_X` its base change to `X`.
Then the sections of `𝒢` over `V_X` are the filtered colimit of the sections of the `F_n` over the
`V_n`: every section over `V_X` is the image of a section of some `F_n` over `V_n`, and two
sections of `F_n` over `V_n` with the same image agree, on the objects of the datum, at a further
level.

This is the Cech step of Stacks 09YQ in degree zero, carried out at the geometry.  The difficulty
it answers is that `V₀` is not an object of the small *affine* etale site of `X_{i₀}` unless it is
affine, and the levels of the system of sites of Stacks 0EYL are categories of representatives of
those affine sites: so neither the levels nor the colimit site contains `V₀`, `V_n` or `V_X`, and
the object-level statement
`Stacks.EtaleCohomology.QcqsLimitCohomology.etaleCohomologyColimit_isColimit` says nothing about
sections over them.  What replaces the missing object is the finite one-hypercover of
`exists_oneHypercoverOf_datum`, which is simultaneously a one-hypercover of every `V_n` and of
`V_X`.

Nothing about sections is assumed.  The statement for an abstract inverse system of sites is
`Stacks.WeakSites.ColimitGlobalSections.sectionOver_colimit_of_oneHypercoverOf'`, and its two
object-level inputs are `objectSections_surjective_and_separated` here, so the hypotheses on the
sheaves are exactly a colimit presentation of `𝒢`.

The two ambient sites are the small etale sites, of `X` and of the `X_n`, and the sheaves `G'` and
`Hs n` there restrict to `𝒢` and to the `F n`.  Neither restriction is an assumption: at the limit
the crossing is `Stacks.EtaleCohomology.AffineLimitCohomology.limitToSmallEtale` and
`Stacks.EtaleCohomology.AffineLimitCohomology.raisedSheaf` exhibits `e₀` as `Iso.refl`; at a level
it is `levelToSmallEtale` and `levelRaisedSheaf` exhibits `en` as `Iso.refl`, and
`Stacks.EtaleCohomology.affineEtaleSiteColimit_levelToSmallEtale_sheafEquiv` says that the level
restriction is an equivalence, so every sheaf of a level is such a restriction.

`exists_oneHypercoverOf_datum` exhibits the datum and both halves of the covering hypothesis, and
`Stacks.WeakSites.ColimitGlobalSections.exists_sectionOver_map_of_oneHypercoverOf` exhibits `ρ`;
so no hypothesis here is vacuous.

Degrees above zero are NOT covered here: what this declaration performs is the degree-zero
descent over the one-hypercover datum. It is not, however, that positive degrees are the same
argument with a spectral sequence over the same datum. This development's route above degree zero
is the Mayer-Vietoris dévissage
`isCohomologyColimit_of_degreeZero_of_affineOpensAcyclic` of the namespace
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology`,
which runs on Mathlib's small étale site of the level — where the level is always a terminal
object (`Stacks.EtaleCohomology.etaleMkIdIsTerminal`, no affineness) and so no descent from
objects arises — and which remains conditional on its own three hypotheses. The whole tag is
carried, unconditionally, by
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.isCohomologyColimit_of_isLimit` in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/SmallEtaleColimitUnconditional.lean`,
which derives those three hypotheses instead of assuming them; this declaration supplies its
degree-zero input. -/
theorem sectionOver_colimit_of_qcqs_etale_object
    (F : InverseSystemOfFiniteSites.SheafSystem.{v, v, max u v + 1} (sys D c B hD hX hc))
    (G : Sheaf (limitSitePrecoverage D c B hX).toGrothendieck (Type (max u v + 1)))
    (ι : ∀ i, (F.obj i).obj ⟶ (toLimitSmall D c B hD hX hc i).op ⋙ G.obj)
    (hpres : F.IsColimitPresentation (toLimitSmall D c B hD hX hc)
      (toLimitSmall_transition D c B hD hX hc) (limitSitePrecoverage D c B hX) G ι)
    (i₀ : (sys D c B hD hX hc).I)
    (V₀ : AlgebraicGeometry.SmallEtale B (D.obj (levelIndex D c B hD hX hc i₀)) (hD _))
    (G' : Sheaf (AlgebraicGeometry.SmallEtale.topology B c.pt hX) (Type (max u v + 1)))
    (e₀ : (limitToSmallEtale D c B hX).op ⋙ G'.obj ≅ G.obj)
    (Hs : ∀ n, Sheaf (AlgebraicGeometry.SmallEtale.topology B
      (D.obj (levelIndex D c B hD hX hc n)) (hD _)) (Type (max u v + 1)))
    (en : ∀ n, (levelToSmallEtale D c B hD hX hc n).op ⋙ (Hs n).obj ≅ (F.obj n).obj)
    (E : OneHypercoverDatum D c B hD hX hc i₀ V₀)
    (ρ : ∀ (n : (sys D c B hD hX hc).I) (a : n ⟶ i₀),
      (Hs n).obj.obj (op (transitionBaseChangeEtaleObj D c B hD hX hc V₀ a)) →
        G'.obj.obj (op (toLimitBaseChangeEtaleObj D c B hD hX hc V₀)))
    (hρ : SectionsMapPinned D c B hD hX hc i₀ V₀ F G ι G' e₀ Hs en E ρ) :
    SectionsIsColimit D c B hD hX hc i₀ V₀ F G' Hs en E ρ := by
  have := E.finite_κ
  have := E.finite_ν
  obtain ⟨hsurjObj, hsep⟩ :=
    objectSections_surjective_and_separated D c B hD hX hc F G ι hpres
  exact sectionOver_colimit_of_oneHypercoverOf' (sys D c B hD hX hc)
    (toLimitSmall D c B hD hX hc) (toLimitSmall_transition D c B hD hX hc) F.obj F.map G ι
    F.map_comp hpres.1 hsurjObj hsep i₀ E.W₀ E.P₀ E.q₁ E.q₂ (limitToSmallEtale D c B hX) G' e₀
    E.isLimitDatum (levelToSmallEtale D c B hD hX hc) Hs en (fun {n} a => E.isLevelDatum n a)
    ρ hρ

end Geometric

end Stacks.EtaleCohomology.QcSeparatedColimit

end
