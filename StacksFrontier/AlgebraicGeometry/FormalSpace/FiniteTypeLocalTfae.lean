module

public import Mathlib.Data.List.TFAE
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteTypeLocalOnSourceAndTargetRefined

/-!
# Being locally of finite type is local on the source and the target: the equivalence

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` be a morphism of
formal algebraic spaces over `S`. This file proves Stacks 0ANL: the five conditions

1. `f` is locally of finite type;
2. `f` is locally of finite type on some square of representable étale charts with surjective
   source chart (`AlgebraicGeometry.FormalSpace.IsLocallyOfFiniteTypeOnSomeSquare`);
3. `f` is locally of finite type on every square of representable étale charts
   (`AlgebraicGeometry.FormalSpace.IsLocallyOfFiniteTypeOnEverySquare`);
4. `f` is locally of finite type after a covering of the target and coverings of the fibre
   products (`AlgebraicGeometry.FormalSpace.IsLocallyOfFiniteTypeAfterTargetCover`);
5. `f` is locally of finite type on a covering of the source factored through affine
   representable étale charts of the target
   (`AlgebraicGeometry.FormalSpace.IsLocallyOfFiniteTypeOnFactoredAtlas`)

are equivalent.

## Main results

* `AlgebraicGeometry.FormalSpace.isLocallyOfFiniteType_tfae`: Stacks 0ANL.

## Implementation notes

The implications are those of the source's proof:

* (1) ⟹ (2) is `isLocallyOfFiniteTypeOnSomeSquare_of_isLocallyOfFiniteType` (the identity
  square), and (2) ⟹ (1) is `isLocallyOfFiniteType_of_onSomeSquare` (descent along the
  surjective representable étale source chart, Stacks 040Y on represented base changes);
* (1) ⟹ (3) is `isLocallyOfFiniteTypeOnEverySquare_of_isLocallyOfFiniteType` (composition,
  Stacks 046G, and cancellation through the locally of finite type diagonal of Stacks 0AN2),
  and (3) ⟹ (1) is `isLocallyOfFiniteType_of_onEverySquare`;
* (3) ⟹ (4) is `isLocallyOfFiniteTypeAfterTargetCover_of_onEverySquare'`, the fibre products
  `Vⱼ ×_Y X` being formal algebraic spaces by Stacks 0AJ3;
* (4) ⟹ (5) is `isLocallyOfFiniteTypeOnFactoredAtlas_of_afterTargetCover'`, the composite of
  the coverings being a covering as in Definition 0AIM;
* (5) ⟹ (1) is `isLocallyOfFiniteType_of_onFactoredAtlas`, descent along the jointly
  surjective family of the covering.

Surjectivity of the source chart in condition (2), and of the coverings in conditions (4) and
(5), is surjectivity of morphisms of sheaves, which is how Definition 0AIM records it. The
sixth item of the source's list is the placeholder "add more here" and states nothing.

## References

* [Stacks Project, Tag 0ANL](https://stacks.math.columbia.edu/tag/0ANL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Being locally of finite type is local on the source and the target.** For a morphism
`f : X ⟶ Y` of formal algebraic spaces over `S`, the following are equivalent:

1. `f` is locally of finite type;
2. there is a commutative square `p ≫ f = t ≫ q` with `U`, `V` formal algebraic spaces, `p`
   and `q` representable étale, `p` surjective and `t` locally of finite type;
3. for every commutative square `p ≫ f = t ≫ q` with `U`, `V` formal algebraic spaces and
   `p`, `q` representable étale, the map `t` is locally of finite type;
4. there is a covering `{Vⱼ ⟶ Y}` as in Definition 0AIM and for each `j` a covering
   `{Uⱼᵢ ⟶ Vⱼ ×_Y X}` as in Definition 0AIM with each `Uⱼᵢ ⟶ Vⱼ` locally of finite type;
5. there is a covering `{Uᵢ ⟶ X}` as in Definition 0AIM and for each `i` a factorization
   `Uᵢ ⟶ Vᵢ ⟶ Y` with `Vᵢ` an affine formal algebraic space, `Vᵢ ⟶ Y` representable étale and
   `Uᵢ ⟶ Vᵢ` locally of finite type. -/
@[stacks 0ANL "the equivalence of conditions (1) to (5); surjectivity in conditions (2), (4) \
and (5) is surjectivity of morphisms of sheaves, as in Definition 0AIM, and item (6) of the \
source is the placeholder \"add more here\", which states nothing"]
theorem isLocallyOfFiniteType_tfae {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsFormalAlgebraicSpace B S hS X) (hY : IsFormalAlgebraicSpace B S hS Y) :
    List.TFAE [IsLocallyOfFiniteType B S hS f,
      IsLocallyOfFiniteTypeOnSomeSquare B S hS f,
      IsLocallyOfFiniteTypeOnEverySquare B S hS f,
      IsLocallyOfFiniteTypeAfterTargetCover B S hS f,
      IsLocallyOfFiniteTypeOnFactoredAtlas B S hS f] := by
  tfae_have 1 → 2 := isLocallyOfFiniteTypeOnSomeSquare_of_isLocallyOfFiniteType B S hS f hX hY
  tfae_have 2 → 1 := isLocallyOfFiniteType_of_onSomeSquare B S hS f
  tfae_have 1 → 3 := isLocallyOfFiniteTypeOnEverySquare_of_isLocallyOfFiniteType B S hS f
  tfae_have 3 → 4 := isLocallyOfFiniteTypeAfterTargetCover_of_onEverySquare' B S hS f hX hY
  tfae_have 4 → 5 := isLocallyOfFiniteTypeOnFactoredAtlas_of_afterTargetCover' B S hS f
  tfae_have 5 → 1 := isLocallyOfFiniteType_of_onFactoredAtlas B S hS f hX hY
  tfae_finish

end AlgebraicGeometry.FormalSpace

end
