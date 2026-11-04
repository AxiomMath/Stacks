module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.RelativeSpecCriterion

/-!
# Transporting the relative-spectrum presentation of an affine morphism along an isomorphism

`AlgebraicGeometry.relativeSpecPushforwardAlgebraIso` presents the source of an affine morphism
`f : X ⟶ S` as the relative spectrum, over `S`, of the pushforward `f_* 𝒪_X` of its structure
sheaf. In practice the algebra one wants to name is not `f_* 𝒪_X` itself but some other
quasi-coherent sheaf of `𝒪_S`-algebras `A` that has been identified with it. This file makes that
substitution: an isomorphism `f_* 𝒪_X ≅ A` of algebra sheaves turns the presentation into one
naming `A`.

## Main definitions

* `AlgebraicGeometry.affineOverIsoOfAlgebraIso`: the identification, in the category of schemes
  affine over `S`, of the source of an affine morphism with the relative spectrum of an algebra
  sheaf isomorphic to the pushforward of its structure sheaf.
* `AlgebraicGeometry.relativeSpecIsoOfAlgebraIso`: **the same identification read in the category
  of schemes over `S`.**

## Main results

* `AlgebraicGeometry.relativeSpecIsoOfAlgebraIso_hom_left_comp`: the identification lies over `S`.
* `AlgebraicGeometry.relativeSpecIsoOfAlgebraIso_hom` and
  `AlgebraicGeometry.relativeSpecIsoOfAlgebraIso_inv`: the two morphisms of the identification
  are the glued comparison morphisms of `AlgebraicGeometry.toRelativeSpecOfAlgebraIso` and
  `AlgebraicGeometry.fromRelativeSpecOfAlgebraIso`.

## Implementation notes

The construction is `AlgebraicGeometry.relativeSpecOverIsoOfAlgebraIso`, read in the full
subcategory of the schemes affine over `S`: both morphisms of the identification are glued from
the maps of affine schemes that the algebra isomorphism gives on sections over the affine opens
of `S`, so the identification names its own maps rather than extracting them from fullness of
the pushforward functor, which would define them by `Classical.choice`.
`Stacks.AffineAlgebraEquivalence.pushforwardAlgebraIso` identifies the pushforward algebra of
the structure morphism of a relative spectrum with the algebra one started from.

## References

* [Stacks Project, Tag 01S8](https://stacks.math.columbia.edu/tag/01S8)
* [Stacks Project, Tag 01LX](https://stacks.math.columbia.edu/tag/01LX)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open Stacks.AffineAlgebraEquivalence
open Stacks.RelativeSpec (AlgebraSheaf)

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S) [IsAffineHom f] (A : AlgebraSheaf S)
  [AlgebraSheaf.IsQuasicoherent A] (e : pushforwardAlgebra f ≅ A)

/-- The source of an affine morphism `f`, as a scheme affine over `S`, is the relative spectrum
of any quasi-coherent algebra sheaf isomorphic to `f_* 𝒪_X`. -/
def affineOverIsoOfAlgebraIso :
    affineOverOfIsAffineHom f ≅ relativeSpecAffineOver A :=
  ObjectProperty.isoMk (IsAffineHomOver S) (relativeSpecOverIsoOfAlgebraIso f A e)

/-- **The source of an affine morphism `f : X ⟶ S` is, over `S`, the relative spectrum of any
quasi-coherent sheaf of `𝒪_S`-algebras isomorphic to `f_* 𝒪_X`.** -/
def relativeSpecIsoOfAlgebraIso :
    Over.mk f ≅ Over.mk (relativeSpecToBase A) :=
  (IsAffineHomOver S).ι.mapIso (affineOverIsoOfAlgebraIso f A e)

/-- The identification of the source of an affine morphism with a relative spectrum is an
identification over `S`. -/
theorem relativeSpecIsoOfAlgebraIso_hom_left_comp :
    (relativeSpecIsoOfAlgebraIso f A e).hom.left ≫ relativeSpecToBase A = f :=
  Over.w (relativeSpecIsoOfAlgebraIso f A e).hom

/-- The identification naming `A` is the glued comparison morphism of
`AlgebraicGeometry.toRelativeSpecOfAlgebraIso`: its forward map is exhibited, not merely shown
to exist. -/
theorem relativeSpecIsoOfAlgebraIso_hom :
    (relativeSpecIsoOfAlgebraIso f A e).hom = toRelativeSpecOfAlgebraIso f A e :=
  rfl

/-- The inverse of the identification naming `A` is the glued comparison morphism in the other
direction. -/
theorem relativeSpecIsoOfAlgebraIso_inv :
    (relativeSpecIsoOfAlgebraIso f A e).inv = fromRelativeSpecOfAlgebraIso f A e :=
  rfl

end AlgebraicGeometry

end
