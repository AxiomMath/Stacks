module

public import StacksFrontier.AlgebraicGeometry.Recovery04IH.LocalizationMorphismsLocallyRinged
public import StacksFrontier.AlgebraicGeometry.Recovery04IH.LocalizedToposStructureMap
public import
  StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedTopoi.CompositionOfLocallyRingedMorphisms
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.RingedToposRelocalizedMorphism

/-!
# The units square of Stacks 04IF's localized morphism of ringed topoi

Let `(f, f♯) : (Sh(C), O) ⟶ (Sh(D), O')` be a morphism of ringed topoi, let `G` be a sheaf of
sets on `D` and put `F = f⁻¹G`.  [Stacks Project, Tag 04IF] localizes `(f, f♯)` to
`(f', (f')♯) : (Sh(C)/F, O_F) ⟶ (Sh(D)/G, O'_G)`, which is
`AlgebraicGeometry.RingedToposHom.localized`.  This file transports the cartesian units square
of Stacks 04HA from `(f, f♯)` to `(f', (f')♯)`.

The transport itself is unconditional and needs no new geometry: `j_F⁻¹` is restriction along
the projection from the site of elements of `F`, so it preserves the cartesian square, and the
units subsheaf of the localized structure sheaf *is* the restriction of the units subsheaf, with
its inclusion the restriction of the inclusion, both on the nose — the observation recorded in
`StacksFrontier/AlgebraicGeometry/Recovery04IH/LocalizationMorphismsLocallyRinged.lean`.
Transporting the resulting square along Stacks 04IF's inverse-image square
`AlgebraicGeometry.RingedToposHom.inverseImageCompLocalizationIso` then produces a square with
the right two columns, and the only thing left to check is that its bottom arrow is the
structure map of `(f')♯`.

That last check is **Stacks 04IF's structure-map identity**, and it is now a theorem:
`AlgebraicGeometry.RingedToposHom.localized_fSharpInverseImage_forget` of
`StacksFrontier/CategoryTheory/Sites/Modules/Localization/RingedToposMorphismLocalization.lean`
says that the
inverse-image form of `(f')♯`, read through 04IF's inverse-image square and on underlying
sheaves of sets, is the restriction `j_F⁻¹(f♯)` of the inverse-image form of `f♯`.  Both
statements below are therefore **unconditional**; they were carried on that equation as a
hypothesis called `hIF` until it was proved.

## Main results

* `AlgebraicGeometry.RingedToposHom.isLocallyRinged_localized`: the localized morphism of ringed
  topoi of Stacks 04IF is a locally ringed morphism as soon as `(f, f♯)` is.
* `AlgebraicGeometry.RingedToposHom.isLocallyRinged_relocalized`: the same for the relocalized
  morphism of [Stacks Project, Tag 04J8], since its second factor — the relocalization morphism
  of [Stacks Project, Tag 04J4] — is locally ringed outright
  (`AlgebraicGeometry.RingedTopos.relocalizationMorphism_isLocallyRinged`) and a composite of
  locally ringed morphisms is locally ringed ([Stacks Project, Tag 04IG]).

Neither statement carries a `@[stacks …]` attribute.  Registering clause (3) of Stacks 04IH at
the level of ringed topoi belongs with that tag's other registrations; clause (3) for a morphism
of ringed *sites* is `AlgebraicGeometry.RingedSite.Hom.localized_isLocallyRinged_sites` of
`StacksFrontier/AlgebraicGeometry/Recovery04IH/LocalizedMorphismLocallyRinged.lean`.

## Implementation notes

The square is produced by `CategoryTheory.IsPullback.of_iso` out of the `j_F⁻¹`-image of the
units square of `f`, with the two left-hand corners moved by the components of
`inverseImageCompLocalizationIso` at the units subsheaf of `Y` and at the underlying sheaf of
sets of `O'`; the comparison of the two left columns is that isomorphism's own naturality at
`AlgebraicGeometry.RingedTopos.unitsι`, and the comparison of the two bottom arrows is
`localized_fSharpInverseImage_forget`.

Two spellings have to be kept apart, and the proof is written in terms rather than in `simp`
for that reason.  `(X.localizationMorphism F).toToposHom.inverseImage.obj (X.forgetRing.obj X.O)`
and `(X.localizedRingedTopos F).forgetRing.obj (X.localizedRingedTopos F).O` are equal by `rfl`
but not syntactically, so `simp only [Category.comp_id]` on a goal mentioning both reports the
goal as not type-correct at `implicit` transparency; `Category.comp_id _` applied as a term
instead goes through, because it is elaborated against the spelling already in the goal.

**How the structure-map identity is proved.**  Both sides are obtained from `f♯` by one
transposition, so the equation is the Beck–Chevalley statement that Stacks 04IF's two squares
are mates: that `AlgebraicGeometry.RingedToposHom.localizationCompPushforwardIso`, the identity
`f'_* j_F⁻¹ ≅ j_G⁻¹ f_*`, is the mate of
`AlgebraicGeometry.RingedToposHom.inverseImageCompLocalizationIso` with respect to the
adjunctions `f⁻¹ ⊣ f_*` and `(f')⁻¹ ⊣ f'_*`.  Both of 04IF's squares are built by transport from
Stacks 04H1's, so the content sits at the *slice* level, and there it is
`MorphismOfTopoi.homEquiv_inverseImageCompToOverIso_inv_app_comp` of
`StacksFrontier/CategoryTheory/Sites/SliceTopos/OverPushforwardBeckChevalley.lean`: both further
edges of both squares are `toOver F` and `toOver G`, whose left adjoints are the two forgetful
functors, and `MorphismOfTopoi.toOverCompPushforwardIso` is a
`CategoryTheory.Adjunction.rightAdjointUniq` of two adjunctions whose *common* left adjoint is
`Over.forget G ⋙ f⁻¹` — so applying that left adjoint's hom-set bijection cancels the universal
property and the adjunct in one step, leaving `CategoryTheory.Functor.Monoidal.μ_fst`, the left
exactness of `f⁻¹` and nothing else.

There is only one universal property to cancel through the lower shriek; in particular
`AlgebraicGeometry.RingedTopos.localizationInverseImageIso` is not a second one: in the transport
(`Stacks.CategoryTheory.homEquiv_beckChevalley_transport`) the identification
`λ_F : j_F⁻¹ ⋙ Φ_F ≅ toOver F` enters the inverse-image square as its inverse and the
direct-image square as itself, so the two cancel against each other by `Iso.inv_hom_id_app`, and
`λ_G` enters only through its naturality.  Nothing has to be known about either identification
beyond that, which is why the argument never looks inside
`AlgebraicGeometry.RingedTopos.localizationEquivalence`, a `Classical.choose`.

## References

* [Stacks Project, Tag 04HA](https://stacks.math.columbia.edu/tag/04HA)
* [Stacks Project, Tag 04IF](https://stacks.math.columbia.edu/tag/04IF)
* [Stacks Project, Tag 04IG](https://stacks.math.columbia.edu/tag/04IG)
* [Stacks Project, Tag 04IH](https://stacks.math.columbia.edu/tag/04IH)
* [Stacks Project, Tag 04J4](https://stacks.math.columbia.edu/tag/04J4)
* [Stacks Project, Tag 04J8](https://stacks.math.columbia.edu/tag/04J8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe v u

namespace AlgebraicGeometry.RingedToposHom

attribute [local instance] AlgebraicGeometry.RingedTopos.isContinuous_elementPostcomp
  AlgebraicGeometry.RingedTopos.isCocontinuous_elementPostcomp
  AlgebraicGeometry.hasSheafCompose_forget_ringCat
  AlgebraicGeometry.hasSheafCompose_forget_commRingCat
  Stacks.hasSheafCompose_forget₂_commRingCat

/-- **The units square of Stacks 04IF's localized morphism of ringed topoi**: the localized
morphism of ringed topoi is locally ringed as soon as `(f, f♯)` is.

The units square of `(f')♯` is the `j_F⁻¹`-image of the units square of `(f, f♯)` with its two
left-hand corners moved by 04IF's inverse-image square: `j_F⁻¹` is restriction along the
projection from the site of elements, so it preserves the cartesian square, and the units
subsheaf of the localized structure sheaf is the restriction of the units subsheaf on the nose.
The bottom arrow is the structure map of `(f')♯` by
`AlgebraicGeometry.RingedToposHom.localized_fSharpInverseImage_forget`, Stacks 04IF's
structure-map identity.

This is stated for ringed topoi in `RingedTopos.{v, u, v}` over essentially small sites, with
every binder in the signature: the clause-(7) registration
`AlgebraicGeometry.RingedToposHom.localized_isLocallyRinged` of
`StacksFrontier/AlgebraicGeometry/Recovery04IH/LocalizedMorphismsLocallyRinged.lean` is the special
case `RingedTopos.{u, u, u}`, which does not reach the small étale ringed topoi
(`RingedTopos.{u, u + 1, u}`) that `AlgebraicGeometry.Space.chartRelocalized` needs.

This carries no attribute: registering clause (3) of [Stacks Project, Tag 04IH] at the level of
ringed topoi belongs with that tag's other registrations.  The clause for a morphism of ringed
*sites* is `AlgebraicGeometry.RingedSite.Hom.localized_isLocallyRinged_sites`. -/
theorem isLocallyRinged_localized {X Y : RingedTopos.{v, u, v}} [EssentiallySmall.{v} X.C]
    [EssentiallySmall.{v} Y.C] (f : RingedToposHom X Y) (G : Y.Topos) (hf : f.IsLocallyRinged) :
    (f.localized G).IsLocallyRinged := by
  have hIF := f.localized_fSharpInverseImage_forget G
  -- `hIF` was the hypothesis this theorem carried until Stacks 04IF's structure-map identity
  -- was proved; the proof below is unchanged.
  obtain ⟨t, ht⟩ := hf
  have hmap := ht.map
    (X.localizationMorphism (f.toToposHom.inverseImage.obj G)).toToposHom.inverseImage
  have hnat := (f.inverseImageCompLocalizationIso G).hom.naturality (RingedTopos.unitsι Y)
  refine ⟨(f.inverseImageCompLocalizationIso G).inv.app (RingedTopos.units Y) ≫
    (X.localizationMorphism (f.toToposHom.inverseImage.obj G)).toToposHom.inverseImage.map t, ?_⟩
  refine hmap.of_iso
    ((f.inverseImageCompLocalizationIso G).app (RingedTopos.units Y))
    (Iso.refl _)
    ((f.inverseImageCompLocalizationIso G).app (Y.forgetRing.obj Y.O))
    (Iso.refl _) ?_ ?_ ?_ ?_
  · exact (Category.comp_id _).trans
      (((f.inverseImageCompLocalizationIso G).app (RingedTopos.units Y)).hom_inv_id_assoc _).symm
  · exact hnat
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · refine Eq.trans (Category.comp_id _) ?_
    refine Eq.trans (congrArg
      (X.localizationMorphism (f.toToposHom.inverseImage.obj G)).toToposHom.inverseImage.map
        (fSharpInverseImage_forget_homEquiv f)).symm ?_
    refine Eq.trans hIF.symm ?_
    exact congrArg (fun z ↦ (f.inverseImageCompLocalizationIso G).hom.app
      (Y.forgetRing.obj Y.O) ≫ z)
        (fSharpInverseImage_forget_homEquiv (f.localized G))

/-- **The units square of Stacks 04J8's relocalized morphism of ringed topoi.**

`AlgebraicGeometry.RingedToposHom.relocalized` is by definition the composite of Stacks 04IF's
localized morphism with the relocalization morphism of [Stacks Project, Tag 04J4], and the
second factor is locally ringed outright
(`AlgebraicGeometry.RingedTopos.relocalizationMorphism_isLocallyRinged`, whose structure map is
the identity on underlying sheaves of sets).  So this is
`AlgebraicGeometry.RingedToposHom.isLocallyRinged_localized` pasted with [Stacks Project,
Tag 04IG].  Its special case `RingedTopos.{u, u, u}` is
`AlgebraicGeometry.RingedToposHom.relocalized_isLocallyRinged`.

This carries no attribute, for the same reason. -/
theorem isLocallyRinged_relocalized {X Y : RingedTopos.{v, u, v}} [EssentiallySmall.{v} X.C]
    [EssentiallySmall.{v} Y.C] (f : RingedToposHom X Y) (G : Y.Topos) {F : X.Topos}
    (s : F ⟶ f.toToposHom.inverseImage.obj G) (hf : f.IsLocallyRinged) :
    (f.relocalized s).IsLocallyRinged :=
  isLocallyRinged_comp (X := X.localizedRingedTopos F)
    (Y := X.localizedRingedTopos (f.toToposHom.inverseImage.obj G))
    (Z := Y.localizedRingedTopos G) (f.localized G) (X.relocalizationMorphism s)
    (f.isLocallyRinged_localized G hf)
    (X.relocalizationMorphism_isLocallyRinged s)

end AlgebraicGeometry.RingedToposHom

end
