module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.PointTopologyEtaleOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# Closed immersions of algebraic spaces are detected on points

Let `i : Z ⟶ X` be an immersion of algebraic spaces over a scheme `S`. Tag 04CD says that `i`
is a closed immersion exactly when the image of its point set is closed in the point space of
`X`. This file proves that equivalence, and the two halves separately, since each half holds
under a weaker hypothesis than the equivalence needs: the forward implication needs no
immersion hypothesis at all, and the backward implication needs no algebraicity hypothesis.

Both directions run through one computation, carried out in
`AlgebraicGeometry.Space.preimage_range_pointsMap_eq_range_pointsMap_snd`: for a representable
base change of `i` along a section `g` of `X`, the point set of the base change is the preimage
along `|g|` of the point set of `i`. This is Tag 03H4, in the form
`AlgebraicGeometry.Space.preimage_image_pointsMap_of_isPullback`.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.isClosed_range_pointsMap_yoneda_iff`: for a morphism of the big
  fppf site of `S`, the image of the induced map on points is closed for the point topology
  exactly when the image of the underlying map of schemes is closed.
* `AlgebraicGeometry.Space.isClosed_range_pointsMap_of_isClosedImmersion`: the point set of a
  closed immersion into an algebraic space is closed.
* `AlgebraicGeometry.Space.isClosedImmersion_of_isClosed_range_pointsMap`: an immersion with
  closed point set is a closed immersion.
* `AlgebraicGeometry.Space.isClosedImmersion_iff_isClosed_range_pointsMap` is the equivalence
  of Tag 04CD.

## Implementation notes

The point topology `AlgebraicGeometry.Space.pointTopology` is installed as a local instance,
as elsewhere in this directory; it is a `def` and not an instance globally.

The forward implication is the only place where an étale atlas is needed, and it is needed
only to see that the point topology of `X` is the quotient topology of the point topology of
the atlas: the point set of `i` is closed because its preimage in the atlas is the point set of
a base change of `i`, which is a closed immersion of schemes. Surjectivity of the atlas on
points is Tag 03H5, in the form
`AlgebraicGeometry.Space.presheafSurjective_iff_isSurjective_yoneda`, and openness is clause
(3) of Tag 03BX, in the form
`AlgebraicGeometry.Space.isOpenMap_pointsMap_of_presheafEtale`; together they make the atlas a
quotient map on points.

The backward implication needs no atlas: each represented base change of `i` is an immersion
of schemes, hence a preimmersion, whose image is the preimage of the point set of `i` along a
continuous map and therefore closed; an immersion of schemes with closed image is a closed
immersion.

Only the second clause of Tag 04CD is proved here. Its first clause — that `|i|` is a
homeomorphism onto a locally closed subset of `|X|` — is the content of Tag 0ABJ, and is
proved in `StacksFrontier/AlgebraicGeometry/Spaces/ImmersionPointEmbedding.lean`, which imports
this file for the base-change computation below. The tag `04CD` therefore sits on the
equivalence here together with the two conclusions of Tag 0ABJ there.

## References

* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 03H5](https://stacks.math.columbia.edu/tag/03H5)
* [Stacks Project, Tag 04CD](https://stacks.math.columbia.edu/tag/04CD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Closed point sets of represented presheaves -/

/-- For a morphism of the big fppf site of `S`, the image of the induced map on points is
closed for the point topology exactly when the image of the underlying map of schemes is
closed.

This is the closed-range companion of
`AlgebraicGeometry.Space.isClosedMap_pointsMap_yoneda_iff`, obtained from the Tag 03BX
comparison bijection of `AlgebraicGeometry.Space.pointsToScheme`. -/
theorem isClosed_range_pointsMap_yoneda_iff {U V : BigFppfOver B S hS} (h : U ⟶ V) :
    IsClosed (Set.range (pointsMap B S hS (yoneda.obj U) (yoneda.map h))) ↔
      IsClosed (Set.range ⇑((BigFppfOver.toScheme B S hS).map h)) := by
  rw [isClosed_pointTopology_yoneda_iff_isClosed_image, ← Set.image_univ,
    image_pointsToScheme_image_pointsMap, Set.image_univ,
    Set.range_eq_univ.mpr (surjective_pointsToScheme B S hS U), Set.image_univ]

/-! ### The point set of a representable morphism after base change -/

variable {Z X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 03H4, in the form the closed-immersion criterion uses.** For a relatively
representable morphism `i : Z ⟶ X` of presheaves on the big fppf site of `S` and a section `g`
of `X` over an object of the site, the preimage along `|g|` of the point set of `i` is the
point set of the chosen represented base change of `i` along `g`. -/
theorem preimage_range_pointsMap_eq_range_pointsMap_snd {i : Z ⟶ X}
    (hrep : yoneda.relativelyRepresentable i) {A : BigFppfOver B S hS}
    (g : yoneda.obj A ⟶ X) :
    pointsMap B S hS (yoneda.obj A) g ⁻¹' Set.range (pointsMap B S hS Z i) =
      Set.range (pointsMap B S hS (yoneda.obj (hrep.pullback g))
        (yoneda.map (hrep.snd g))) := by
  rw [← Set.image_univ,
    preimage_image_pointsMap_of_isPullback B S hS (hrep.isPullback g) Set.univ,
    Set.preimage_univ, Set.image_univ]

/-- The preimage along `|g|` of the point set of a relatively representable `i` is closed exactly
when the image of the underlying map of schemes of the base change of `i` along `g` is closed. -/
private theorem isClosed_preimage_range_pointsMap_iff {i : Z ⟶ X}
    (hrep : yoneda.relativelyRepresentable i) {A : BigFppfOver B S hS} (g : yoneda.obj A ⟶ X) :
    IsClosed (pointsMap B S hS (yoneda.obj A) g ⁻¹' Set.range (pointsMap B S hS Z i)) ↔
      IsClosed (Set.range ⇑((BigFppfOver.toScheme B S hS).map (hrep.snd g))) := by
  rw [preimage_range_pointsMap_eq_range_pointsMap_snd B S hS hrep g,
    isClosed_range_pointsMap_yoneda_iff B S hS]

/-! ### The criterion -/

/-- **Stacks 04CD, forward implication.** The point set of a closed immersion into an
algebraic space over `S` is closed in the point space of the target.

No immersion hypothesis is needed beyond the closed-immersion hypothesis itself. -/
theorem isClosed_range_pointsMap_of_isClosedImmersion (hX : IsAlgebraicSpace B S hS X)
    (i : Z ⟶ X) (hi : IsClosedImmersion B S hS i) :
    IsClosed (Set.range (pointsMap B S hS Z i)) := by
  obtain ⟨U, a, haSurj, haEtale⟩ := hX.exists_atlas
  have hsurj : Function.Surjective (pointsMap B S hS (yoneda.obj U) a) :=
    (presheafSurjective_iff_isSurjective_yoneda B S hS X hX U a).mp haSurj
  have hq := isQuotientMap_pointsMap_of_presheafEtale B S hS a haEtale hsurj
  rw [← hq.isCoinducing.isClosed_preimage, isClosed_preimage_range_pointsMap_iff B S hS hi.rep a]
  exact (_root_.AlgebraicGeometry.IsClosedImmersion.iff_isPreimmersion.mp (hi.property_snd a)).2

/-- **Stacks 04CD, backward implication.** An immersion of presheaves on the big fppf site of
`S` whose point set is closed in the point space of the target is a closed immersion.

No algebraicity hypothesis is needed. -/
theorem isClosedImmersion_of_isClosed_range_pointsMap (i : Z ⟶ X)
    (hi : IsImmersion B S hS i)
    (hclosed : IsClosed (Set.range (pointsMap B S hS Z i))) :
    IsClosedImmersion B S hS i := by
  have hRI : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  refine MorphismProperty.relative_of_snd hi.rep fun {A} g => ?_
  have himm : _root_.AlgebraicGeometry.IsImmersion
      ((BigFppfOver.toScheme B S hS).map (hi.rep.snd g)) := hi.property_snd g
  have hcl := (isClosed_preimage_range_pointsMap_iff B S hS hi.rep g).mp
    (hclosed.preimage (continuous_pointsMap B S hS g))
  change _root_.AlgebraicGeometry.IsClosedImmersion _
  exact _root_.AlgebraicGeometry.IsClosedImmersion.of_isPreimmersion _ hcl

/-- **Stacks 04CD.** An immersion of algebraic spaces over `S` is a closed immersion exactly
when the image of its point set is a closed subset of the point space of the target. -/
@[stacks 04CD "closed immersion criterion"]
theorem isClosedImmersion_iff_isClosed_range_pointsMap (hX : IsAlgebraicSpace B S hS X)
    (i : Z ⟶ X) (hi : IsImmersion B S hS i) :
    IsClosedImmersion B S hS i ↔ IsClosed (Set.range (pointsMap B S hS Z i)) :=
  ⟨isClosed_range_pointsMap_of_isClosedImmersion B S hS hX i,
    isClosedImmersion_of_isClosed_range_pointsMap B S hS i hi⟩

end AlgebraicGeometry.Space

end
