module

public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteObjectOfFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemePullbackTwoFibreProduct

/-!
# The fibre product of the underlying schemes as an object of the site

Let `a : U ⟶ W` and `b : V ⟶ W` be morphisms of the big fppf category of `S`. The fibre product
of the underlying schemes is again small enough to belong to the site
(`AlgebraicGeometry.Scheme.size_pullback_lt`), so it is an object of the big fppf category over
`S`, with the two projections as morphisms to `U` and `V`; and the resulting square is a fibre
product *in the site*, because the structure functor to schemes is faithful and reflects fibre
products.

Composing with `AlgebraicGeometry.Stack.isTwoFibreProduct_schemeStackSquare` this presents the
scheme-level fibre product as a 2-fibre product of the represented algebraic stacks, with the
points of Stacks 04XL of its apex *equal* to the topological space of the scheme-level fibre
product — not merely homeomorphic to it — since
`AlgebraicGeometry.BigFppfOver.siteObjectOver` is built on the given scheme on the nose.

## Main definitions

* `AlgebraicGeometry.Stack.sitePullbackObj`: the fibre product of the underlying schemes, as an
  object of the big fppf category over `S`.
* `AlgebraicGeometry.Stack.sitePullbackFst`, `AlgebraicGeometry.Stack.sitePullbackSnd`: its two
  projections.

## Main results

* `AlgebraicGeometry.Stack.isPullback_sitePullback`: the square is a fibre product in the site.
* `AlgebraicGeometry.Stack.isTwoFibreProduct_sitePullbackStackSquare`: the square of represented
  algebraic stacks over it is a 2-fibre product.
* `AlgebraicGeometry.Stack.toScheme_obj_sitePullbackObj`,
  `AlgebraicGeometry.Stack.toScheme_map_sitePullbackFst` and
  `AlgebraicGeometry.Stack.toScheme_map_sitePullbackSnd`: the underlying scheme and the two
  underlying morphisms are the fibre product of schemes and its projections, by `rfl`.

## Implementation notes

The object is built over `U` rather than over `W`, so that its first projection is the morphism
`AlgebraicGeometry.BigFppfOver.siteMapOver` already supplies and only the second projection has
to be written down. The compatibility that second projection needs is the defining equation of
the fibre product of schemes read against the two structure morphisms, which is why
`CategoryTheory.Limits.pullback.condition` appears in its proof and nowhere else.

That the square is a fibre product in the site is `CategoryTheory.IsPullback.of_map_of_faithful`
at the structure functor: it is faithful, and it reflects fibre products because it is the
forgetful functor of a slice followed by the inclusion of a full subcategory. Both instances are
found by unification, so the hypothesis of that lemma is the scheme-level statement
`CategoryTheory.IsPullback.of_hasPullback` and nothing else.

## References

* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 021S](https://stacks.math.columbia.edu/tag/021S)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {U V W : BigFppfOver B S hS} (a : U ⟶ W) (b : V ⟶ W)

/-- The fibre product of the underlying schemes of `a : U ⟶ W` and `b : V ⟶ W`, as an object of
the big fppf category over `S`, presented over `U` by the first projection. -/
noncomputable def sitePullbackObj : BigFppfOver B S hS :=
  BigFppfOver.siteObjectOver B S hS U
    (Scheme.size_pullback_lt ((BigFppfOver.toScheme B S hS).map a)
      ((BigFppfOver.toScheme B S hS).map b) U.left.property V.left.property)
    (pullback.fst ((BigFppfOver.toScheme B S hS).map a) ((BigFppfOver.toScheme B S hS).map b))

/-- The underlying scheme of `AlgebraicGeometry.Stack.sitePullbackObj` is the fibre product of
the underlying schemes. -/
theorem toScheme_obj_sitePullbackObj :
    (BigFppfOver.toScheme B S hS).obj (sitePullbackObj B S hS a b) =
      pullback ((BigFppfOver.toScheme B S hS).map a)
        ((BigFppfOver.toScheme B S hS).map b) := rfl

/-- The first projection of `AlgebraicGeometry.Stack.sitePullbackObj`. -/
noncomputable def sitePullbackFst : sitePullbackObj B S hS a b ⟶ U :=
  BigFppfOver.siteMapOver B S hS U _ _

/-- The underlying morphism of the first projection is the first projection of the fibre product
of schemes. -/
theorem toScheme_map_sitePullbackFst :
    (BigFppfOver.toScheme B S hS).map (sitePullbackFst B S hS a b) =
      pullback.fst ((BigFppfOver.toScheme B S hS).map a)
        ((BigFppfOver.toScheme B S hS).map b) := rfl

/-- The second projection of `AlgebraicGeometry.Stack.sitePullbackObj`. -/
noncomputable def sitePullbackSnd : sitePullbackObj B S hS a b ⟶ V :=
  Over.homMk
    (⟨pullback.snd ((BigFppfOver.toScheme B S hS).map a)
      ((BigFppfOver.toScheme B S hS).map b)⟩ :
      (sitePullbackObj B S hS a b).left ⟶ V.left)
    (by
      refine B.inclusion.map_injective ?_
      rw [B.inclusion.map_comp]
      have ha : (BigFppfOver.toScheme B S hS).map a ≫ B.inclusion.map W.hom =
          B.inclusion.map U.hom :=
        (B.inclusion.map_comp a.left W.hom).symm.trans (congrArg B.inclusion.map (Over.w a))
      have hb : (BigFppfOver.toScheme B S hS).map b ≫ B.inclusion.map W.hom =
          B.inclusion.map V.hom :=
        (B.inclusion.map_comp b.left W.hom).symm.trans (congrArg B.inclusion.map (Over.w b))
      change pullback.snd _ _ ≫ B.inclusion.map V.hom =
        pullback.fst _ _ ≫ B.inclusion.map U.hom
      rw [← ha, ← hb, ← Category.assoc, ← Category.assoc, pullback.condition])

/-- The underlying morphism of the second projection is the second projection of the fibre
product of schemes. -/
theorem toScheme_map_sitePullbackSnd :
    (BigFppfOver.toScheme B S hS).map (sitePullbackSnd B S hS a b) =
      pullback.snd ((BigFppfOver.toScheme B S hS).map a)
        ((BigFppfOver.toScheme B S hS).map b) := rfl

/-- **The fibre product of the underlying schemes is a fibre product in the site.** The structure
functor to schemes is faithful and reflects fibre products, so the scheme-level statement
suffices. -/
theorem isPullback_sitePullback :
    IsPullback (sitePullbackFst B S hS a b) (sitePullbackSnd B S hS a b) a b :=
  IsPullback.of_map_of_faithful (BigFppfOver.toScheme B S hS)
    (by
      rw [toScheme_map_sitePullbackFst, toScheme_map_sitePullbackSnd]
      exact IsPullback.of_hasPullback _ _)

/-- **The square of represented algebraic stacks over the scheme-level fibre product is a
2-fibre product.** -/
noncomputable def isTwoFibreProduct_sitePullbackStackSquare :
    Bicategory.IsTwoFibreProduct
      (schemeStackSquare.{u, w} B S hS (isPullback_sitePullback B S hS a b).w) :=
  isTwoFibreProduct_schemeStackSquare.{u, w} B S hS (isPullback_sitePullback B S hS a b)

end AlgebraicGeometry.Stack

end
