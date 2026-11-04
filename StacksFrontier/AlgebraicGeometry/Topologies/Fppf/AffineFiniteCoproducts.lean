module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Coproduct
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FiniteCoproducts

/-!
# The big affine fppf category over `S` has finite coproducts

Let `S` be a scheme contained in a big fppf site `B`. The big fppf category over `S` has finite
coproducts (`AlgebraicGeometry.hasFiniteCoproducts_bigFppfOver`), computed on underlying schemes
because `AlgebraicGeometry.BigFppfOver.toScheme` preserves them. This file records that
affineness of an object is stable under those coproducts, so that the full subcategory
`AlgebraicGeometry.BigAffineFppf` of affine objects has finite coproducts too, and the inclusion
preserves them.

The content is the corresponding statement for schemes — a finite disjoint union of affine
schemes is affine — transported along `AlgebraicGeometry.BigFppfOver.toScheme`. The size cutoff
of the site needs no attention: that it is closed under finite coproducts of schemes is
`AlgebraicGeometry.schemeSizeBelow_isClosedUnderFiniteCoproducts`, which is what gives the
coproducts of the big fppf category in the first place.

## Main results

* `AlgebraicGeometry.isAffine_isClosedUnderFiniteCoproducts`: a finite disjoint union of affine
  schemes is affine, as a closure property of the class of affine schemes.
* `AlgebraicGeometry.isAffineOver_isClosedUnderFiniteCoproducts`: affineness of an object of the
  big fppf category over `S` is stable under finite coproducts.
* `AlgebraicGeometry.BigAffineFppf.hasFiniteCoproducts`: **the big affine fppf category over
  `S` has finite coproducts**, and `AlgebraicGeometry.BigAffineFppf.preservesFiniteCoproducts`:
  the inclusion into the big fppf category preserves them.

## Implementation notes

The empty case of the closure for schemes is `AlgebraicGeometry.isAffine_of_isEmpty` read at an
initial scheme, through `AlgebraicGeometry.isInitial_iff_isEmpty`; the binary case is Mathlib's
instance for `X ⨿ Y`. `CategoryTheory.ObjectProperty.IsClosedUnderFiniteCoproducts.mk'`
assembles the two into every finite disjoint union.

The closure for the site is then not proved again: `AlgebraicGeometry.IsAffineOver` is the
inverse image of affineness along `AlgebraicGeometry.BigFppfOver.toScheme`, and
`CategoryTheory.ObjectProperty.IsClosedUnderColimitsOfShape.inverseImage` descends the closure
along a functor preserving the colimits in question.

## References

* [Stacks Project, Tag 021S](https://stacks.math.columbia.edu/tag/021S)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Affineness of a scheme is invariant under isomorphism. -/
public instance isAffine_isClosedUnderIsomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms (fun X : Scheme.{u} ↦ IsAffine X) :=
  ⟨fun e h ↦ have := h; IsAffine.of_isIso e.inv⟩

/-- **A finite disjoint union of affine schemes is affine**, as a closure property of the class
of affine schemes: the empty disjoint union is the empty scheme and a binary one is a
coproduct of two affine schemes. -/
@[ega "II 1.4.9" "more general"]
public instance isAffine_isClosedUnderFiniteCoproducts :
    ObjectProperty.IsClosedUnderFiniteCoproducts (fun X : Scheme.{u} ↦ IsAffine X) := by
  have h0 : ObjectProperty.IsClosedUnderColimitsOfShape
      (fun X : Scheme.{u} ↦ IsAffine X) (Discrete.{0} PEmpty) := by
    apply ObjectProperty.IsClosedUnderColimitsOfShape.mk'
    rintro _ ⟨F, -⟩
    have hT : IsInitial (colimit F : Scheme.{u}) :=
      (IsColimit.equivOfNatIsoOfIso F.uniqueFromEmpty _ _
        (by exact Cocone.ext (Iso.refl _) (by rintro ⟨⟨⟩⟩))).1 (colimit.isColimit F)
    have : IsEmpty (colimit F : Scheme.{u}) := isInitial_iff_isEmpty.1 ⟨hT⟩
    exact isAffine_of_isEmpty
  have h2 : ObjectProperty.IsClosedUnderColimitsOfShape
      (fun X : Scheme.{u} ↦ IsAffine X) (Discrete WalkingPair) := by
    apply ObjectProperty.IsClosedUnderColimitsOfShape.mk'
    rintro _ ⟨F, hF⟩
    have h₁ : IsAffine (F.obj ⟨WalkingPair.left⟩) := hF ⟨WalkingPair.left⟩
    have h₂ : IsAffine (F.obj ⟨WalkingPair.right⟩) := hF ⟨WalkingPair.right⟩
    have : IsAffine (F.obj ⟨WalkingPair.left⟩ ⨿ F.obj ⟨WalkingPair.right⟩) := inferInstance
    exact IsAffine.of_isIso (HasColimit.isoOfNatIso (diagramIsoPair F)).hom
  have : ObjectProperty.IsClosedUnderBinaryCoproducts
      (fun X : Scheme.{u} ↦ IsAffine X) := ⟨h2.colimitsOfShape_le⟩
  exact ObjectProperty.IsClosedUnderFiniteCoproducts.mk'

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Affineness of an object of the big fppf category over `S` is invariant under isomorphism. -/
public instance isAffineOver_isClosedUnderIsomorphisms :
    (IsAffineOver B S hS).IsClosedUnderIsomorphisms :=
  ⟨fun e h ↦ by
    change IsAffine ((BigFppfOver.toScheme B S hS).obj _) at h ⊢
    exact IsAffine.of_isIso ((BigFppfOver.toScheme B S hS).map e.inv)⟩

/-- The functor to schemes from the big fppf category over `S` preserves finite coproducts: it
preserves binary coproducts and the initial object. -/
public instance preservesFiniteCoproducts_bigFppfOverToScheme :
    PreservesFiniteCoproducts (BigFppfOver.toScheme B S hS) where
  preserves n := preservesShape_fin_of_preserves_binary_and_initial _ n

/-- **Affineness of an object of the big fppf category over `S` is stable under finite
coproducts.** The underlying scheme of a finite coproduct is the finite disjoint union of the
underlying schemes, because `AlgebraicGeometry.BigFppfOver.toScheme` preserves finite
coproducts, and a finite disjoint union of affine schemes is affine. -/
@[ega "II 1.4.9" "special case"]
public instance isAffineOver_isClosedUnderFiniteCoproducts :
    (IsAffineOver B S hS).IsClosedUnderFiniteCoproducts where
  isClosedUnderColimitsOfShape J _ :=
    ObjectProperty.IsClosedUnderColimitsOfShape.inverseImage
      (J := Discrete J) (fun X : Scheme.{u} ↦ IsAffine X) (BigFppfOver.toScheme B S hS)

namespace BigAffineFppf

/-- **Stacks 021S, part (2).** The big affine fppf category over `S` has finite coproducts, and
in particular an initial object: the finite disjoint unions formed in the big fppf category over
`S` of affine objects are affine. -/
public instance hasFiniteCoproducts : HasFiniteCoproducts (BigAffineFppf B S hS) :=
  inferInstance

/-- The inclusion of the big affine fppf category over `S` into the big fppf category over `S`
preserves finite coproducts, affineness being stable under them. -/
public instance preservesFiniteCoproducts :
    PreservesFiniteCoproducts (BigAffineFppf.inclusion B S hS) where
  preserves n := preservesShape_fin_of_preserves_binary_and_initial _ n

end BigAffineFppf

end AlgebraicGeometry

end
