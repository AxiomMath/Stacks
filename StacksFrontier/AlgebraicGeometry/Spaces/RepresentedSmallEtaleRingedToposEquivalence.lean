module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedCommRingStructureComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposIsoLocallyRinged
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedTopoi.CompositionOfLocallyRingedMorphisms

/-!
# The small étale ringed topos of a chart does not depend on which big site it is read in

An object `U` of a big fppf site over `S` is at once a chart of the algebraic space
`yoneda.obj U` and a scheme of the big étale site
`AlgebraicGeometry.associatedBigEtaleSite B` carried by the same category of schemes, and the
two readings give two small étale ringed topoi:

* `AlgebraicGeometry.Space.smallEtaleRingedTopos B S hS ⟨yoneda.obj U, _⟩`, cut out of the
  étale charts of the presheaf `yoneda.obj U`;
* `AlgebraicGeometry.RingedSite.toRingedTopos (smallEtaleRingedSite (associatedBigEtaleSite B)
  _ U.left.property)`, cut out of the étale schemes over the underlying scheme of `U`.

Both are `AlgebraicGeometry.RingedTopos.{u, u + 1, u}`, and
`AlgebraicGeometry.Space.representedSmallEtaleEquivalence` identifies their sites, with their
topologies (`representedSmallEtaleEquivalence_topology`) and with their structure sheaves of
commutative rings (`AlgebraicGeometry.Space.representedCommRingStructureIso`, which is the
identity on underlying presheaves).  This file packages that identification as an isomorphism
of ringed topoi and transports the locally ringed condition of Stacks 04HA across it.

## Main definitions

* `AlgebraicGeometry.Space.representedSmallEtaleToposHom`: the identification of the two
  underlying topoi, as a morphism of topoi whose inverse image is restriction along the
  equivalence of sites.
* `AlgebraicGeometry.Space.representedSmallEtaleRingedToposHom`: that morphism of topoi with
  the comparison of structure sheaves as structure map, i.e. the identification as a morphism
  of ringed topoi.
* `AlgebraicGeometry.Space.representedSmallEtaleRingedToposInverse`: the same identification
  read from the scheme side, built out of the inverse of the equivalence of sites rather than
  as a formal inverse of the previous morphism.
* `AlgebraicGeometry.Space.schemeOfRepresentedRingedToposHom`: the conjugate of a morphism of
  the small étale ringed topoi of two representable algebraic spaces, read between the small
  étale ringed topoi of the two schemes.

## Main results

* `AlgebraicGeometry.Space.isLocallyRinged_representedSmallEtaleRingedToposHom` and
  `…_representedSmallEtaleRingedToposInverse`: both directions of the identification are
  morphisms of locally ringed topoi.
* `AlgebraicGeometry.Space.isLocallyRinged_schemeOfRepresentedRingedToposHom`: the conjugate of
  a locally ringed morphism is locally ringed.  This is the transport of
  `AlgebraicGeometry.RingedToposHom.IsLocallyRinged` that the passage between the two big sites
  needs, and it is Stacks 04IG applied twice.

## Implementation notes

The identification is built exactly as the affine-to-big comparison of Stacks 0GZU is
(`AlgebraicGeometry.affineToBigRingedToposHom` of
`StacksFrontier/AlgebraicGeometry/Topologies/BigSites/AffineRingedToposEquivalence.lean`): the
inverse image is `Functor.sheafPushforwardContinuous` along the functor of sites, and the
structure map is the adjunct of `Stacks.Sheaves.ToposPullback.restrictionCommRingIso` pasted
with the comparison of the two structure sheaves.  That definition itself cannot be reused
here, because it takes the sections of the structure sheaf in a universe dominating both sites'
object universes — `Sheaf _ (Type max u₁ v₁ u₂ v₂ w)` — whereas the sites here have objects in
`Type (u + 1)` and sections in `Type u`.  What replaces the size hypothesis is that the functor
of sites is an *equivalence*, so the induced functor on sheaves is an equivalence for any
category of values and with no size condition: that is `CategoryTheory.Equivalence.sheafCongr`,
whose inverse is `Functor.sheafPushforwardContinuous` on the nose.

`AlgebraicGeometry.RingedToposHom.isLocallyRinged_of_isEquivalence_of_isIso_fSharp` is stated
for two ringed topoi with a *common* section universe and with the two
`HasSheafCompose (forget CommRingCat)` instances beyond the four that
`AlgebraicGeometry.RingedToposHom` itself requires, so the variable block below is written in
that shape; both small étale ringed topoi have sections in `Type u`, so nothing is lost.

## References

* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED)
* [Stacks Project, Tag 04HA](https://stacks.math.columbia.edu/tag/04HA)
* [Stacks Project, Tag 04IG](https://stacks.math.columbia.edu/tag/04IG)
* [Stacks Project, Tag 0GZU](https://stacks.math.columbia.edu/tag/0GZU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)

/-- Restriction of sheaves of sets along the equivalence of the two small étale sites of a
chart.  This is the inverse image of the identification of the two topoi. -/
noncomputable abbrev representedSmallEtaleRestriction :
    Sheaf (_root_.AlgebraicGeometry.SmallEtale.topology (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property) (Type u) ⥤
      Sheaf (SmallEtale.topology B S hS (yoneda.obj U)) (Type u) :=
  (representedSmallEtaleEquivalence B S hS U).functor.sheafPushforwardContinuous
    (Type u) (SmallEtale.topology B S hS (yoneda.obj U))
    (_root_.AlgebraicGeometry.SmallEtale.topology (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property)

/-- **Restriction along an equivalence of sites is an equivalence of sheaf topoi**, with no size
hypothesis: it is the inverse half of `CategoryTheory.Equivalence.sheafCongr`.  This is the case
of sheaves valued in `Type u`; the case of sheaves valued in `Type (u + 1)` is
`AlgebraicGeometry.Space.isEquivalence_representedSmallEtaleRestriction`. -/
instance isEquivalence_representedSmallEtaleRestriction_typeU :
    (representedSmallEtaleRestriction B S hS U).IsEquivalence :=
  inferInstanceAs
    (((representedSmallEtaleEquivalence B S hS U).sheafCongr
      (SmallEtale.topology B S hS (yoneda.obj U))
      (_root_.AlgebraicGeometry.SmallEtale.topology (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property) (Type u)).inverse.IsEquivalence)

/-- The identification of the two small étale topoi of a chart, as a morphism of topoi from the
topos of the algebraic space `yoneda.obj U` to the topos of the underlying scheme: its inverse
image is restriction along the equivalence of sites, and its direct image is the quasi-inverse
of that restriction. -/
noncomputable def representedSmallEtaleToposHom :
    MorphismOfTopoi
      (smallEtaleRingedTopos B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).Topos
      (_root_.AlgebraicGeometry.RingedSite.toRingedTopos
        (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property)).Topos where
  inverseImage := representedSmallEtaleRestriction B S hS U
  pushforward := (representedSmallEtaleRestriction B S hS U).asEquivalence.inverse
  adj := (representedSmallEtaleRestriction B S hS U).asEquivalence.toAdjunction
  preservesFiniteLimits := inferInstance

/-- The inverse image of the identification of the two small étale topoi is restriction along
the equivalence of sites. -/
@[simp]
theorem representedSmallEtaleToposHom_inverseImage :
    (representedSmallEtaleToposHom B S hS U).inverseImage =
      representedSmallEtaleRestriction B S hS U :=
  rfl

/-- The direct image of the identification of the two small étale topoi is an equivalence. -/
instance isEquivalence_representedSmallEtaleToposHom_pushforward :
    (representedSmallEtaleToposHom B S hS U).pushforward.IsEquivalence :=
  inferInstanceAs ((representedSmallEtaleRestriction B S hS U).asEquivalence.inverse.IsEquivalence)

/-- The inverse image of the identification of the two small étale topoi is an equivalence. -/
instance isEquivalence_representedSmallEtaleToposHom_inverseImage :
    (representedSmallEtaleToposHom B S hS U).inverseImage.IsEquivalence :=
  inferInstanceAs ((representedSmallEtaleRestriction B S hS U).IsEquivalence)

/-- **The inverse image of the structure sheaf of the small étale site of the underlying scheme
is the structure sheaf of the small étale site of `yoneda.obj U`.**  The inverse image along a
restriction *is* that restriction on sheaves of commutative rings
(`Stacks.Sheaves.ToposPullback.restrictionCommRingIso`), and the restriction of the scheme's
structure sheaf is the space's by
`AlgebraicGeometry.Space.representedCommRingStructureIso`, which is the identity on underlying
presheaves. -/
noncomputable def representedCommRingInverseImageIso :
    (inverseImageCommRingFunctor (representedSmallEtaleToposHom B S hS U)).obj
        (_root_.AlgebraicGeometry.SmallEtale.commRingStructureSheaf (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property) ≅
      structureSheaf B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) :=
  restrictionCommRingIso (SmallEtale.topology B S hS (yoneda.obj U))
      (_root_.AlgebraicGeometry.SmallEtale.topology (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property)
      (representedSmallEtaleEquivalence B S hS U).functor
      (_root_.AlgebraicGeometry.SmallEtale.commRingStructureSheaf (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property) ≪≫
    (representedCommRingStructureIso B S hS U).symm

/-- **The small étale ringed topos of a chart does not depend on which big site the chart is
read in**, as a morphism of ringed topoi: the identification of the two topoi, with the
comparison of the two structure sheaves of commutative rings as structure map. -/
noncomputable def representedSmallEtaleRingedToposHom :
    RingedToposHom
      (smallEtaleRingedTopos B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
      (_root_.AlgebraicGeometry.RingedSite.toRingedTopos
        (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property)) where
  toToposHom := representedSmallEtaleToposHom B S hS U
  fSharp :=
    (commRingImageAdjunction (representedSmallEtaleToposHom B S hS U)).homEquiv _ _
      (representedCommRingInverseImageIso B S hS U).hom

/-- The structure map of the identification, in inverse-image form, is the comparison of the
two structure sheaves of commutative rings. -/
theorem representedSmallEtaleRingedToposHom_fSharpInverseImage :
    (representedSmallEtaleRingedToposHom B S hS U).fSharpInverseImage =
      (representedCommRingInverseImageIso B S hS U).hom :=
  ((commRingImageAdjunction
    (representedSmallEtaleToposHom B S hS U)).homEquiv _ _).symm_apply_apply _

/-- The structure map of the identification, in inverse-image form, is an isomorphism. -/
instance isIso_representedSmallEtaleRingedToposHom_fSharpInverseImage :
    IsIso (representedSmallEtaleRingedToposHom B S hS U).fSharpInverseImage := by
  rw [representedSmallEtaleRingedToposHom_fSharpInverseImage]
  exact (representedCommRingInverseImageIso B S hS U).isIso_hom

/-- **The identification is a morphism of locally ringed topoi.**  Its inverse-image structure
map is an isomorphism, so Stacks 04HA's square of units subsheaves has two invertible
horizontal arrows and is therefore cartesian. -/
theorem isLocallyRinged_representedSmallEtaleRingedToposHom :
    (representedSmallEtaleRingedToposHom B S hS U).IsLocallyRinged :=
  RingedToposHom.isLocallyRinged_of_isIso_fSharpInverseImage
    (representedSmallEtaleRingedToposHom B S hS U)

/-! ### The identification read in the other direction -/

/-- Restriction of sheaves of sets along the *inverse* of the equivalence of the two small étale
sites of a chart. -/
noncomputable abbrev representedSmallEtaleRestrictionInverse :
    Sheaf (SmallEtale.topology B S hS (yoneda.obj U)) (Type u) ⥤
      Sheaf (_root_.AlgebraicGeometry.SmallEtale.topology (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property) (Type u) :=
  (representedSmallEtaleEquivalence B S hS U).inverse.sheafPushforwardContinuous
    (Type u)
    (_root_.AlgebraicGeometry.SmallEtale.topology (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property)
    (SmallEtale.topology B S hS (yoneda.obj U))

/-- Restriction along the inverse equivalence is an equivalence of sheaf topoi: it is the
forward half of `CategoryTheory.Equivalence.sheafCongr`. -/
instance isEquivalence_representedSmallEtaleRestrictionInverse :
    (representedSmallEtaleRestrictionInverse B S hS U).IsEquivalence :=
  inferInstanceAs
    (((representedSmallEtaleEquivalence B S hS U).sheafCongr
      (SmallEtale.topology B S hS (yoneda.obj U))
      (_root_.AlgebraicGeometry.SmallEtale.topology (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property) (Type u)).functor.IsEquivalence)

/-- The identification of the two small étale topoi of a chart, read from the topos of the
underlying scheme to the topos of the algebraic space `yoneda.obj U`. -/
noncomputable def representedSmallEtaleToposInverse :
    MorphismOfTopoi
      (_root_.AlgebraicGeometry.RingedSite.toRingedTopos
        (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property)).Topos
      (smallEtaleRingedTopos B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).Topos where
  inverseImage := representedSmallEtaleRestrictionInverse B S hS U
  pushforward := (representedSmallEtaleRestrictionInverse B S hS U).asEquivalence.inverse
  adj := (representedSmallEtaleRestrictionInverse B S hS U).asEquivalence.toAdjunction
  preservesFiniteLimits := inferInstance

/-- The inverse image of the identification read backwards is restriction along the inverse
equivalence of sites. -/
@[simp]
theorem representedSmallEtaleToposInverse_inverseImage :
    (representedSmallEtaleToposInverse B S hS U).inverseImage =
      representedSmallEtaleRestrictionInverse B S hS U :=
  rfl

/-- The pushforward of the identification read backwards is an equivalence of categories. -/
instance isEquivalence_representedSmallEtaleToposInverse_pushforward :
    (representedSmallEtaleToposInverse B S hS U).pushforward.IsEquivalence :=
  inferInstanceAs
    ((representedSmallEtaleRestrictionInverse B S hS U).asEquivalence.inverse.IsEquivalence)

/-- The inverse image along the inverse equivalence of the structure sheaf of `yoneda.obj U` is
the structure sheaf of the small étale site of the underlying scheme. -/
noncomputable def representedCommRingInverseImageInverseIso :
    (inverseImageCommRingFunctor (representedSmallEtaleToposInverse B S hS U)).obj
        (structureSheaf B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)) ≅
      _root_.AlgebraicGeometry.SmallEtale.commRingStructureSheaf (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property :=
  restrictionCommRingIso
      (_root_.AlgebraicGeometry.SmallEtale.topology (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property)
      (SmallEtale.topology B S hS (yoneda.obj U))
      (representedSmallEtaleEquivalence B S hS U).inverse
      (structureSheaf B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)) ≪≫
    (representedCommRingStructureInverseIso B S hS U).symm

/-- **The identification of the two small étale ringed topoi of a chart, read from the scheme
side.**  This is not built as the inverse of
`AlgebraicGeometry.Space.representedSmallEtaleRingedToposHom` but directly, out of the inverse
of the equivalence of sites and
`AlgebraicGeometry.Space.representedCommRingStructureInverseIso`, which is again the identity on
underlying presheaves. -/
noncomputable def representedSmallEtaleRingedToposInverse :
    RingedToposHom
      (_root_.AlgebraicGeometry.RingedSite.toRingedTopos
        (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property))
      (smallEtaleRingedTopos B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩) where
  toToposHom := representedSmallEtaleToposInverse B S hS U
  fSharp :=
    (commRingImageAdjunction (representedSmallEtaleToposInverse B S hS U)).homEquiv _ _
      (representedCommRingInverseImageInverseIso B S hS U).hom

/-- The structure map of the identification read backwards, in inverse-image form. -/
theorem representedSmallEtaleRingedToposInverse_fSharpInverseImage :
    (representedSmallEtaleRingedToposInverse B S hS U).fSharpInverseImage =
      (representedCommRingInverseImageInverseIso B S hS U).hom :=
  ((commRingImageAdjunction
    (representedSmallEtaleToposInverse B S hS U)).homEquiv _ _).symm_apply_apply _

/-- The structure map of the identification read backwards, in inverse-image form, is an
isomorphism. -/
instance isIso_representedSmallEtaleRingedToposInverse_fSharpInverseImage :
    IsIso (representedSmallEtaleRingedToposInverse B S hS U).fSharpInverseImage := by
  rw [representedSmallEtaleRingedToposInverse_fSharpInverseImage]
  exact (representedCommRingInverseImageInverseIso B S hS U).isIso_hom

/-- **The identification read backwards is a morphism of locally ringed topoi too.** -/
theorem isLocallyRinged_representedSmallEtaleRingedToposInverse :
    (representedSmallEtaleRingedToposInverse B S hS U).IsLocallyRinged :=
  RingedToposHom.isLocallyRinged_of_isIso_fSharpInverseImage
    (representedSmallEtaleRingedToposInverse B S hS U)

/-! ### Conjugating a morphism of the small étale ringed topoi of two charts -/

variable (V : BigFppfOver B S hS)

/-- **A morphism of the small étale ringed topoi of two representable algebraic spaces, read
between the small étale ringed topoi of the two underlying schemes.**  This is the conjugate of
`ψ` by the identification of the two readings of each chart, and it is the form in which the
scheme-level recovery theorems of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/RecoveringMorphisms/` consume a morphism of
ringed topoi produced over a big fppf site. -/
noncomputable def schemeOfRepresentedRingedToposHom
    (ψ : RingedToposHom
      (smallEtaleRingedTopos B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
      (smallEtaleRingedTopos B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩)) :
    RingedToposHom
      (_root_.AlgebraicGeometry.RingedSite.toRingedTopos
        (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property))
      (_root_.AlgebraicGeometry.RingedSite.toRingedTopos
        (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj V) V.left.property)) :=
  RingedToposHom.comp
    (X := _root_.AlgebraicGeometry.RingedSite.toRingedTopos
      (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property))
    (Y := smallEtaleRingedTopos B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩)
    (Z := _root_.AlgebraicGeometry.RingedSite.toRingedTopos
      (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj V) V.left.property))
    (representedSmallEtaleRingedToposHom B S hS V)
    (RingedToposHom.comp
      (X := _root_.AlgebraicGeometry.RingedSite.toRingedTopos
        (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property))
      (Y := smallEtaleRingedTopos B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
      (Z := smallEtaleRingedTopos B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩)
      ψ (representedSmallEtaleRingedToposInverse B S hS U))

/-- **The conjugate of a locally ringed morphism is locally ringed.**  This is Stacks 04IG
applied twice, with the two identifications locally ringed by
`AlgebraicGeometry.Space.isLocallyRinged_representedSmallEtaleRingedToposHom` and
`…_representedSmallEtaleRingedToposInverse`.  It is the transport of
`AlgebraicGeometry.RingedToposHom.IsLocallyRinged` that the passage between the big fppf site
and the big étale site needs. -/
theorem isLocallyRinged_schemeOfRepresentedRingedToposHom
    (ψ : RingedToposHom
      (smallEtaleRingedTopos B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
      (smallEtaleRingedTopos B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩))
    (hψ : ψ.IsLocallyRinged) :
    (schemeOfRepresentedRingedToposHom B S hS U V ψ).IsLocallyRinged :=
  RingedToposHom.isLocallyRinged_comp
    (X := _root_.AlgebraicGeometry.RingedSite.toRingedTopos
      (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property))
    (Y := smallEtaleRingedTopos B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩)
    (Z := _root_.AlgebraicGeometry.RingedSite.toRingedTopos
      (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj V) V.left.property))
    _ _ (isLocallyRinged_representedSmallEtaleRingedToposHom B S hS V)
    (RingedToposHom.isLocallyRinged_comp
      (X := _root_.AlgebraicGeometry.RingedSite.toRingedTopos
        (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property))
      (Y := smallEtaleRingedTopos B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
      (Z := smallEtaleRingedTopos B S hS ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩)
      _ _ hψ (isLocallyRinged_representedSmallEtaleRingedToposInverse B S hS U))

end AlgebraicGeometry.Space

end
