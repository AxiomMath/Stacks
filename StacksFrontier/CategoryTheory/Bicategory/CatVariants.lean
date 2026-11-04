module

import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Tactic.NormNum.Parity
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.Data.NNRat.Floor
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Sheaves.Init
public import Mathlib.CategoryTheory.Groupoid.Grpd.Basic

public import StacksFrontier.CategoryTheory.Bicategory.Cat
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoCategory
public import StacksFrontier.CategoryTheory.Sites.Stack.TwoCategory

/-!
# Variants of the `(2,1)`-category `Cat`

Stacks 003M records that the construction of Stacks 003K — turn a `2`-category into a
`(2,1)`-category by keeping only the *isomorphisms* of `2`-morphisms — applies just as well to the
`2`-category of groupoids, to the `2`-category of categories fibred in groupoids over a fixed
category, and to the `2`-category of stacks.

The construction itself is Mathlib's `CategoryTheory.Bicategory.Pith`, and that it turns a
`2`-category into a `(2,1)`-category is `CategoryTheory.Bicategory.isTwoOneCategory_pith`
(Stacks 003K, `StacksFrontier.CategoryTheory.Bicategory.Cat`). So each variant below is that
lemma applied to the `2`-category in question; the content of the tag is that these three
`2`-categories are available and strict, so that the construction applies to them.

## Main definitions

* `CategoryTheory.CatGroupoids`: the `2`-category of groupoids, i.e. the full sub-`2`-category of
  the `2`-category `Cat` of categories (Stacks 003J) spanned by the groupoids.

## Main results

* `CategoryTheory.isTwoOneCategory_pith_catGroupoids`, Stacks 003M for groupoids;
* `CategoryTheory.isTwoOneCategory_pith_catFiberedInGroupoids`, Stacks 003M for the categories
  fibred in groupoids over a fixed category (Stacks 02XS);
* `CategoryTheory.isTwoOneCategory_pith_basedStack`, Stacks 003M for the stacks over a site
  (Stacks 02ZG).

## Implementation notes

The `2`-category of groupoids is built the way the other full sub-`2`-categories of this
development are — `CategoryTheory.CatFiberedInGroupoids` (Stacks 02XS),
`CategoryTheory.StackInGroupoids` (Stacks 02ZK) — namely with Mathlib's
`CategoryTheory.Bicategory.InducedBicategory`, here applied to the inclusion
`CategoryTheory.Grpd.forgetToCat` of groupoids into categories. Its `1`-morphisms are therefore all
functors and its `2`-morphisms all morphisms of functors, as in the source, and it is strict
because `Cat` is.
-/

@[expose] public section

namespace CategoryTheory

open _root_.CategoryTheory.Bicategory

universe v₁ v₂ u₁ u₂

set_option linter.checkUnivs false in
/-- The `2`-category of groupoids: the full sub-`2`-category of the `2`-category `Cat` of
categories (Stacks 003J) spanned by the groupoids. Its objects are the groupoids, its
`1`-morphisms all functors between them, and its `2`-morphisms all morphisms of functors. -/
abbrev CatGroupoids :=
  Bicategory.InducedBicategory Cat.{v₁, u₁} (fun 𝒢 : Grpd.{v₁, u₁} ↦ Grpd.forgetToCat.obj 𝒢)

/-- **Stacks 003M**, the variant for groupoids: the `2`-category of groupoids becomes a
`(2,1)`-category once only the isomorphisms of functors are allowed as `2`-morphisms. -/
@[stacks 003M "the 2-category of groupoids"]
lemma isTwoOneCategory_pith_catGroupoids :
    IsTwoOneCategory (Pith CatGroupoids.{v₁, u₁}) :=
  isTwoOneCategory_pith _

/-- **Stacks 003M**, the variant for categories fibred in groupoids over a fixed category: the
`2`-category of categories fibred in groupoids over `𝒞` (Stacks 02XS) becomes a `(2,1)`-category
once only the isomorphisms of `2`-morphisms are kept. -/
@[stacks 003M "the 2-category of categories fibred in groupoids over a fixed category"]
lemma isTwoOneCategory_pith_catFiberedInGroupoids (𝒞 : Type u₁) [Category.{v₁} 𝒞] :
    IsTwoOneCategory (Pith (CatFiberedInGroupoids.{v₁, v₂, u₁, u₂} 𝒞)) :=
  isTwoOneCategory_pith _

/-- **Stacks 003M**, the variant for stacks: the `2`-category of stacks over a site (Stacks 02ZG)
becomes a `(2,1)`-category once only the isomorphisms of `2`-morphisms are kept. -/
@[stacks 003M "the 2-category of stacks"]
lemma isTwoOneCategory_pith_basedStack (𝒞 : Type u₁) [Category.{v₁} 𝒞]
    (J : GrothendieckTopology 𝒞) :
    IsTwoOneCategory (Pith (BasedStack.{v₁, v₂, u₁, u₂} 𝒞 J)) :=
  isTwoOneCategory_pith _

end CategoryTheory
