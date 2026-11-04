module

public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingBaseChangeProjection
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverFibresProjections
public import StacksFrontier.CategoryTheory.TwoFibreProduct.SquareComparisonProjections

/-!
# The square of Stacks 02XI at a fibre, in the spelling of Stacks 0CMR

The fibre of a base change is the 2-fibre product of the fibres: **Stacks 02XI** says that

`(𝒳 ×_𝒴 𝒵)_V ⥤ 𝒳_V ×_{𝒴_V} 𝒵_V`

is an equivalence. This file reads that statement as the 2-cartesianness of a square of fibre
categories in the universes the squares of Stacks 0CMR live in: the apex is `(𝒳 ×_𝒴 𝒵)_V`, the
upper leg is the fibre of the first projection, the left leg the fibre of the base change `p'`,
and the cospan the fibres of `p` and `q`.

That is the right-hand square of the first pasting of **Stacks 0CMT**: pasting it onto the square
of Stacks 0CMR for `p'` replaces `(𝒳 ×_𝒴 𝒵)_V` by `𝒳_V` in the cospan, and so turns the
2-cartesianness of `p'`'s square into that of a rectangle whose cospan is `p_V` and
`colim 𝒵_{Uᵢ} ⟶ 𝒴_V`.

The two projections of the 02XI comparison are the fibres of the two projections of the base
change (`CategoryTheory.TwoFibreProductOver.asSmallFiberPullback_comp_π₁` and `…_π₂`), so
`CategoryTheory.Limits.CategoricalPullback.isEquivalence_squareComparison_projOfEq` applies with
both identifications definitional: the only difference between the two spellings is which proof
of one and the same equality of functors is named.

## Main definitions

* `AlgebraicGeometry.Stack.baseChangeFiberFiller`: the filler of the square.

## Main results

* `AlgebraicGeometry.Stack.isEquivalence_squareComparison_baseChangeFiber`: the square is
  2-cartesian.

## References

* [Stacks Project, Tag 0CMT](https://stacks.math.columbia.edu/tag/0CMT)
* [Stacks Project, Tag 02XI](https://stacks.math.columbia.edu/tag/02XI)
* [Stacks Project, Tag 0CMR](https://stacks.math.columbia.edu/tag/0CMR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{u, max u v, u + 1, max (u + 1) v w}
    (BigFppfOver B S hS))
  (p : 𝒳 ⟶ 𝒴) (q : 𝒵 ⟶ 𝒴)

/-- **The comparison of Stacks 02XI for a base change, in the spelling of Stacks 0CMR.** It is
`CategoryTheory.TwoFibreProductOver.asSmallFiberPullback`, with its source read as the fibre of
`𝒳 ×_𝒴 𝒵` and its target as the 2-fibre product of the cospan
`CategoryTheory.Functor.fiberFunctorOfCompEq` of `p` and `q`. Both readings are definitional, and
naming them is what makes the identities of this file usable. -/
noncomputable def baseChangeFiberPullback (V : BigFppfOver B S hS) :
    AsSmall.{max (u + 1) v w}
        ((BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p.Fiber V) ⥤
      CategoricalPullback
        (AsSmall.down.{max u v, max (u + 1) v w, max (u + 1) v w} ⋙
          Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p p) V ⋙
          AsSmall.up.{max u v, max (u + 1) v w, max (u + 1) v w})
        (AsSmall.down.{max u v, max (u + 1) v w, max (u + 1) v w} ⋙
          Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p q) V ⋙
          AsSmall.up.{max u v, max (u + 1) v w, max (u + 1) v w}) :=
  TwoFibreProductOver.asSmallFiberPullback.{max (u + 1) v w} 𝒳.val.p 𝒵.val.p 𝒴.val.p
    (CatFiberedInGroupoids.homFunctor p) (CatFiberedInGroupoids.homFunctor q)
    (CatFiberedInGroupoids.homFunctor_comp_p p) (CatFiberedInGroupoids.homFunctor_comp_p q) V

/-- The first projection of the comparison of Stacks 02XI is the fibre of the first projection of
the base change. The two sides differ only in which proof of
`CategoryTheory.TwoFibreProductOver.fst ⋙ 𝒳.val.p = (𝒳 ×_𝒴 𝒵).val.p` they name. -/
lemma baseChangeFiberPullback_comp_π₁ (V : BigFppfOver B S hS) :
    baseChangeFiberPullback.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q V ⋙
        CategoricalPullback.π₁ _ _ =
      AsSmall.down.{max u v, max (u + 1) v w, max (u + 1) v w} ⋙
        Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p
          (BigFppfOver.twoFibreProductFst.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q)) V ⋙
        AsSmall.up.{max u v, max (u + 1) v w, max (u + 1) v w} := rfl

/-- The second projection of the comparison of Stacks 02XI is the fibre of the base change `p`'
itself. -/
lemma baseChangeFiberPullback_comp_π₂ (V : BigFppfOver B S hS) :
    baseChangeFiberPullback.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q V ⋙
        CategoricalPullback.π₂ _ _ =
      AsSmall.down.{max u v, max (u + 1) v w, max (u + 1) v w} ⋙
        Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p
          (BigFppfOver.twoFibreProductSnd.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q)) V ⋙
        AsSmall.up.{max u v, max (u + 1) v w, max (u + 1) v w} := rfl

/-- **The filler of the square of Stacks 02XI at a fibre.** -/
noncomputable def baseChangeFiberFiller (V : BigFppfOver B S hS) :
    (AsSmall.down.{max u v, max (u + 1) v w, max (u + 1) v w} ⋙
          Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p
            (BigFppfOver.twoFibreProductFst.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q)) V ⋙
          AsSmall.up.{max u v, max (u + 1) v w, max (u + 1) v w}) ⋙
        (AsSmall.down.{max u v, max (u + 1) v w, max (u + 1) v w} ⋙
          Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p p) V ⋙
          AsSmall.up.{max u v, max (u + 1) v w, max (u + 1) v w}) ≅
      (AsSmall.down.{max u v, max (u + 1) v w, max (u + 1) v w} ⋙
          Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p
            (BigFppfOver.twoFibreProductSnd.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q)) V ⋙
          AsSmall.up.{max u v, max (u + 1) v w, max (u + 1) v w}) ⋙
        (AsSmall.down.{max u v, max (u + 1) v w, max (u + 1) v w} ⋙
          Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p q) V ⋙
          AsSmall.up.{max u v, max (u + 1) v w, max (u + 1) v w}) :=
  CategoricalPullback.projFillerOfEq _ _ _ _
    (baseChangeFiberPullback.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q V)
    (baseChangeFiberPullback_comp_π₁.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q V)
    (baseChangeFiberPullback_comp_π₂.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q V)

/-- **Stacks 02XI as a 2-cartesian square, at the universes of Stacks 0CMR.** The fibre of the
base change, with the fibres of the two projections for its legs over the fibres of `p` and `q`,
is a 2-fibre product: the comparison functor of the square is the comparison of Stacks 02XI, which
is an equivalence.

This is the right-hand square of the first pasting of Stacks 0CMT. -/
lemma isEquivalence_squareComparison_baseChangeFiber (V : BigFppfOver B S hS) :
    (CategoricalPullback.squareComparison
      (AsSmall.down.{max u v, max (u + 1) v w, max (u + 1) v w} ⋙
        Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p
          (BigFppfOver.twoFibreProductFst.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q)) V ⋙
        AsSmall.up.{max u v, max (u + 1) v w, max (u + 1) v w})
      (AsSmall.down.{max u v, max (u + 1) v w, max (u + 1) v w} ⋙
        Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p
          (BigFppfOver.twoFibreProductSnd.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q)) V ⋙
        AsSmall.up.{max u v, max (u + 1) v w, max (u + 1) v w})
      (AsSmall.down.{max u v, max (u + 1) v w, max (u + 1) v w} ⋙
        Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p p) V ⋙
        AsSmall.up.{max u v, max (u + 1) v w, max (u + 1) v w})
      (AsSmall.down.{max u v, max (u + 1) v w, max (u + 1) v w} ⋙
        Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p q) V ⋙
        AsSmall.up.{max u v, max (u + 1) v w, max (u + 1) v w})
      (baseChangeFiberFiller.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q V)).IsEquivalence :=
  let : (baseChangeFiberPullback.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q V).IsEquivalence :=
    TwoFibreProductOver.isEquivalence_asSmallFiberPullback.{max (u + 1) v w} 𝒳.val.p 𝒵.val.p
      𝒴.val.p (CatFiberedInGroupoids.homFunctor p) (CatFiberedInGroupoids.homFunctor q)
      (CatFiberedInGroupoids.homFunctor_comp_p p) (CatFiberedInGroupoids.homFunctor_comp_p q) V
  CategoricalPullback.isEquivalence_squareComparison_projOfEq _ _ _ _ _ _ _

end AlgebraicGeometry.Stack

end
