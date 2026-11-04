module

public import StacksFrontier.AlgebraicGeometry.AlgebraImageSurjective.Transport
public import StacksFrontier.AlgebraicGeometry.FiniteTypeSubalgebraJoin.CommRingImages
public import StacksFrontier.AlgebraicGeometry.FiniteTypeSubalgebraJoin.FunctorImages

/-!
# The corestriction to the image of a morphism of (pre)sheaves of commutative rings is surjective

`Stacks.CommRingImages.hasImages` builds the image of a morphism of commutative rings as its
range, so the corestriction to the explicit image is `RingHom.rangeRestrict`, which is surjective
by construction.  This file carries that surjectivity through the two layers that stand between
it and the image of a morphism of presheaves of commutative rings: the choice of image in
`CommRingCat`, which is only isomorphic to the range, and the pointwise image of a natural
transformation, which is `Stacks.FunctorImages.hasImages`.

The conclusion is that the corestriction to the image of a morphism of presheaves of commutative
rings is surjective *on sections over every object*, and therefore locally surjective for any
Grothendieck topology.  Objectwise surjectivity is strictly stronger than local surjectivity and
is what the sheaf-level statement in
`StacksFrontier/AlgebraicGeometry/AlgebraImageSurjective/Sheaf.lean` needs, since the image of a
morphism of sheaves is the *sheafification* of the presheaf image and only the presheaf-level
map is surjective on the nose.

## Main results

* `Stacks.AlgebraImageSurjective.surjective_factorThruImage_commRingCat`: the corestriction to
  the image of a morphism of commutative rings is surjective.
* `Stacks.AlgebraImageSurjective.surjective_app_factorThruImage`: the corestriction to the
  pointwise image of a morphism of functors into commutative rings is surjective at every object.
* `Stacks.AlgebraImageSurjective.presheaf_isLocallySurjective_factorThruImage`: it is therefore
  locally surjective for any Grothendieck topology.

## Implementation notes

The functor-level step takes the identity
`Stacks.FunctorImages.monoFactorisation f |>.e ≫ isoExt.hom = factorThruImage f` and reads it at
an object with `CategoryTheory.NatTrans.congr_app`.  The left-hand side is stated directly as
`factorThruImage (f.app j) ≫ _`: the component of `Stacks.FunctorImages.imageProjection` at `j`
*is* `CategoryTheory.Limits.factorThruImage (f.app j)`, and the two structure projections
involved are unfolded by term elaboration at default transparency.  Stating the component form
as a rewrite of the natural-transformation form instead does not work, for the reason recorded
in `StacksFrontier/AlgebraicGeometry/AlgebraImageSurjective/Transport.lean`.

The surjectivity of the comparison isomorphism at `j` is supplied by hand, against a stated
expected type, rather than left to the `[IsIso a]` instance argument of a transport lemma: that
instance argument is exactly the one shown in `Transport.lean` to fail at this spelling even
though the instance is synthesizable when asked for directly.

Nothing here asks for `CommRingCat` to be abelian, and nothing here is an epimorphism statement:
an epimorphism of commutative rings need not be surjective (`ℤ → ℚ`), so the surjectivity has to
come from the explicit range factorisation and cannot be read off a categorical property of the
corestriction.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace Stacks.AlgebraImageSurjective

/-- **The corestriction to the image of a morphism of commutative rings is surjective.**  The
explicit image is the range and the corestriction to it is `RingHom.rangeRestrict`; the chosen
image differs from it by an isomorphism. -/
theorem surjective_factorThruImage_commRingCat {R S : CommRingCat.{w}} (f : R ⟶ S) :
    Function.Surjective (factorThruImage f) :=
  surjective_factorThruImage (Stacks.CommRingImages.isImage f) f.hom.rangeRestrict_surjective

/-- **The corestriction to the image of a morphism of functors into commutative rings is
surjective at every object.**  The image is computed pointwise by
`Stacks.FunctorImages.hasImages`, so this is the previous statement at each object, transported
along the comparison isomorphism with the chosen image. -/
theorem surjective_app_factorThruImage {D : Type u} [Category.{v} D] {F G : D ⥤ CommRingCat.{w}}
    (f : F ⟶ G) (j : D) : Function.Surjective ((factorThruImage f).app j) :=
  have h : (Stacks.FunctorImages.monoFactorisation f).e
      ≫ (IsImage.isoExt (Stacks.FunctorImages.isImage f) (Image.isImage f)).hom
      = factorThruImage f := IsImage.e_isoExt_hom _ _
  have hj : factorThruImage (f.app j)
      ≫ (IsImage.isoExt (Stacks.FunctorImages.isImage f) (Image.isImage f)).hom.app j
      = (factorThruImage f).app j := NatTrans.congr_app h j
  have ha : Function.Surjective
      ((IsImage.isoExt (Stacks.FunctorImages.isImage f) (Image.isImage f)).hom.app j) :=
    (ConcreteCategory.bijective_of_isIso _).2
  surjective_of_fac hj (surjective_factorThruImage_commRingCat (f.app j)) ha

/-- **The corestriction to the image of a morphism of presheaves of commutative rings is locally
surjective**, for any Grothendieck topology on the site.  It is in fact surjective on sections
over every object, by `surjective_app_factorThruImage`. -/
theorem presheaf_isLocallySurjective_factorThruImage {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) {F G : Cᵒᵖ ⥤ CommRingCat.{w}} (f : F ⟶ G) :
    Presheaf.IsLocallySurjective J (factorThruImage f) :=
  Presheaf.isLocallySurjective_of_surjective J _ fun U => surjective_app_factorThruImage f U

end Stacks.AlgebraImageSurjective
