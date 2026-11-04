module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts

/-!
# Affineness of a base-changed object of a big fppf category

An object of the big fppf category over `S` has a base change along a morphism
`g : S' → S` of the site, namely `CategoryTheory.Over.pullback g`, and the fibre product is
taken in the site's own category of schemes. This module records when the result has affine
underlying scheme: when the object did and `g` is an affine morphism.

The statement is needed wherever a glueing triple is assembled out of site objects, because the
middle component of such a triple is a base change and its affineness is what lets the affine
equivalence of Stacks 0F9Q be applied. It is a property of the square being glued along rather
than of the object, which is why it is isolated here: at the canonical square of a glueing pair
all four corners are spectra of rings, so the hypothesis on `g` holds there for free.

## Main results

* `AlgebraicGeometry.BigFppfOver.isAffine_toScheme_obj_pullback`: the base change of an object
  with affine underlying scheme along an affine morphism of the site again has affine underlying
  scheme.

## Implementation notes

The fibre product defining the base change is formed in `B.Schemes`, not in `Scheme`, so the
proof goes through `CategoryTheory.Functor.map_isPullback` for the site's inclusion — which
preserves cospan limits — to land the square in schemes, base-changes affineness of `g` along
it, and then reads off affineness of the source from
`AlgebraicGeometry.isAffine_of_isAffineHom`. Instance search supplies the preservation of cospan
limits: the size cutoff is closed under fibre products (Stacks 021U), so the inclusion of the
full subcategory creates them, by
`CategoryTheory.Limits.createsLimitsOfShapeFullSubcategoryInclusion`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.BigFppfOver

/-- **The base change of an affine object of a big fppf category along an affine morphism is
affine.** The fibre product is the one formed in the site's category of schemes; its underlying
scheme is the fibre product of schemes because the site's inclusion preserves cospan limits, and
there the first projection is affine as a base change of `g`, so its source is affine. -/
@[ega "II 1.5.5" "special case"]
theorem isAffine_toScheme_obj_pullback (B : BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S') (g : B.obj hS' ⟶ B.obj hS)
    (hg : IsAffineHom (B.inclusion.map g)) (A : BigFppfOver B S hS)
    (hA : IsAffine ((BigFppfOver.toScheme B S hS).obj A)) :
    IsAffine ((BigFppfOver.toScheme B S' hS').obj ((Over.pullback g).obj A)) := by
  have hpb : IsPullback (B.inclusion.map (pullback.fst A.hom g))
      (B.inclusion.map (pullback.snd A.hom g))
      (B.inclusion.map A.hom) (B.inclusion.map g) :=
    Functor.map_isPullback B.inclusion (IsPullback.of_hasPullback A.hom g)
  let : IsAffineHom (B.inclusion.map g) := hg
  have hfst : IsAffineHom (B.inclusion.map (pullback.fst A.hom g)) :=
    MorphismProperty.of_isPullback hpb.flip
      (show IsAffineHom (B.inclusion.map g) from inferInstance)
  let : IsAffineHom (B.inclusion.map (pullback.fst A.hom g)) := hfst
  let : IsAffine (B.inclusion.obj A.left) := hA
  change IsAffine (B.inclusion.obj (pullback A.hom g))
  exact AlgebraicGeometry.isAffine_of_isAffineHom (B.inclusion.map (pullback.fst A.hom g))

end AlgebraicGeometry.BigFppfOver

end
