module

public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationEquivalenceInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.CechTermAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothSchemeChartDescent

/-!
# Transporting smoothness of a base change along an equivalence over the site

`AlgebraicGeometry.Stack.isAlgebraicStack_twoFibreProduct_of_costructuredArrow` reads a base
change `(Sch/U) ×_𝒴 𝒳` of a 1-morphism along a point of `𝒴` through any category over the site
equivalent to it, and transports *algebraicity* back. Algebraicity is a property of the apex
alone, so an equivalence over the site is all it needs.

Smoothness of the base change is a property of the 1-morphism `(Sch/U) ×_𝒴 𝒳 ⟶ (Sch/U)`, so an
equivalence over the site transports it only when the equivalence is compatible with the
projection to `Sch/U` as well. This file supplies that transport, in the three shapes a consumer
meets it in:

* the compatibility given as a 2-isomorphism `q ≅ e ≫ r` of 1-morphisms to the common target;
* the compatibility given as a pre-morphism of 2-commutative squares over the cospan, whose
  first comparison 2-cell *is* the compatibility with the projection;
* no compatibility data at all, when both squares are 2-fibre products of the one cospan: the
  comparison pre-morphism and its 2-cells come from terminality, so smoothness of the first leg
  depends only on the cospan.

The third shape is what the smoothness half of **Stacks 0DQ0** needs. Its hypothesis `hbase` of
`StacksFrontier.AlgebraicGeometry.Quot.PolarizedCurvesToCurvesSmoothReduction` is smoothness of the
first leg of the *canonical* base-change square, and the moduli description of that base change —
for Stacks 0DQ0, the relatively ample locus of a Picard stack — presents it as the apex of some
*other* 2-fibre product square of the same cospan. `isSmooth_fst_of_isTwoFibreProduct_pair` is
the step from the second to the first.

Everything rests on the two cancellation laws already in the library:
`AlgebraicGeometry.Stack.AlgebraicStacks.isSmooth_of_isEquivalence_comp`, which cancels an
equivalence on the left, and `AlgebraicGeometry.Stack.AlgebraicStacks.isSmooth_of_twoIso`, which
is invariance of smoothness under 2-isomorphism. Nothing here is a new mathematical input: it is
**Stacks 075U** read along the comparison of two 2-fibre products, which is
`AlgebraicGeometry.Stack.isEquivalence_of_isTwoFibreProduct_algebraicStacks`.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isSmooth_of_isEquivalence_of_twoIso`: smoothness
  transports along an equivalence over the site compatible, up to 2-isomorphism, with the
  projections to a common target.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isSmooth_fst_of_preHom`: the same with the
  compatibility read off a pre-morphism of 2-commutative squares.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isSmooth_fst_of_isTwoFibreProduct_pair` and
  `AlgebraicGeometry.Stack.AlgebraicStacks.isSmooth_fst_iff_of_isTwoFibreProduct_pair`:
  smoothness of the first leg of a 2-fibre product square depends only on the cospan.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isSmooth_fst_twoFibreProductSquare_of_isTwoFibreProduct`
  : the same with the target square the canonical one.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isSmooth_fst_twoFibreProductSquare_of_equivalenceOver`:
  the smoothness analogue of
  `AlgebraicGeometry.Stack.isAlgebraicStack_twoFibreProduct_of_costructuredArrow`, with the base
  change read through an algebraic stack equivalent to it over the site.

## References

* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 003Z](https://stacks.math.columbia.edu/tag/003Z)
* [Stacks Project, Tag 04T2](https://stacks.math.columbia.edu/tag/04T2)
* [Stacks Project, Tag 075U](https://stacks.math.columbia.edu/tag/075U)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Smoothness transports along an equivalence over the site compatible with the projections.**
Let `e : 𝒟 ⟶ 𝒬` be a 1-morphism of algebraic stacks over `S` whose underlying functor is an
equivalence, and let `q : 𝒟 ⟶ 𝒰` and `r : 𝒬 ⟶ 𝒰` be 1-morphisms to a common target with
`q ≅ e ≫ r`. If `q` is smooth then so is `r`.

Taking `𝒰` to be the stack of a scheme `U` of the site, this is the statement that smoothness of
a 1-morphism to `Sch/U` is invariant under an equivalence over the site that is compatible with
the projection to `Sch/U`; the compatibility is `hqr`, and it is exactly what an equivalence
transporting *algebraicity* (`AlgebraicGeometry.Stack.isAlgebraicStack_of_equivalenceOver`) does
not have to carry. -/
theorem isSmooth_of_isEquivalence_of_twoIso {𝒟 𝒬 𝒰 : Stack.AlgebraicStacks.{u, w} B S hS}
    (e : 𝒟 ⟶ 𝒬) (he : Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor e.hom))
    (q : 𝒟 ⟶ 𝒰) (r : 𝒬 ⟶ 𝒰) (hqr : q ≅ e ≫ r) (hq : IsSmooth B S hS q) :
    IsSmooth B S hS r :=
  isSmooth_of_isEquivalence_comp B S hS e r he (isSmooth_of_twoIso B S hS hqr hq)

/-- **Smoothness of the first leg transports along a pre-morphism of 2-commutative squares whose
underlying 1-morphism is an equivalence.** For squares `P`, `Q` over a cospan `(f, g)` of
algebraic stacks over `S` and a pre-morphism `a : P ⟶ Q` whose underlying functor is an
equivalence, smoothness of `P.fst` gives smoothness of `Q.fst`.

The compatibility with the projection is the comparison 2-cell `a.isoFst : P.fst ≅ a.hom ≫ Q.fst`
that a pre-morphism of squares carries by definition (**Stacks 003O**). -/
theorem isSmooth_fst_of_preHom {𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS} {f : 𝒳 ⟶ 𝒵}
    {g : 𝒴 ⟶ 𝒵} {P Q : Bicategory.TwoCommSq f g} (a : Bicategory.TwoCommSq.PreHom P Q)
    (ha : Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor a.hom.hom))
    (hP : IsSmooth B S hS P.fst) : IsSmooth B S hS Q.fst :=
  isSmooth_of_isEquivalence_of_twoIso B S hS a.hom ha P.fst Q.fst a.isoFst hP

/-- **Smoothness of the first leg of a 2-fibre product square depends only on the cospan.** If
`P` and `Q` are both 2-fibre products of a cospan `(f, g)` of algebraic stacks over `S`
(**Stacks 003Q**) and `P.fst` is smooth, then `Q.fst` is smooth.

Terminality of `Q` supplies a pre-morphism `P ⟶ Q`, whose underlying functor is an equivalence by
`AlgebraicGeometry.Stack.isEquivalence_of_isTwoFibreProduct_algebraicStacks` (**Stacks 003Z**)
and whose first comparison 2-cell is the compatibility with the projection. -/
theorem isSmooth_fst_of_isTwoFibreProduct_pair {𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS}
    {f : 𝒳 ⟶ 𝒵} {g : 𝒴 ⟶ 𝒵} {P Q : Bicategory.TwoCommSq f g}
    (hP : Bicategory.IsTwoFibreProduct P) (hQ : Bicategory.IsTwoFibreProduct Q)
    (h : IsSmooth B S hS P.fst) : IsSmooth B S hS Q.fst :=
  isSmooth_fst_of_preHom B S hS (Bicategory.twoFibreProductPreHom hQ P)
    (Stack.isEquivalence_of_isTwoFibreProduct_algebraicStacks B S hS hP hQ
      (Bicategory.twoFibreProductPreHom hQ P)) h

/-- **Smoothness of the first leg of a 2-fibre product square is a property of the cospan.** Both
directions of `AlgebraicGeometry.Stack.AlgebraicStacks.isSmooth_fst_of_isTwoFibreProduct_pair`. -/
theorem isSmooth_fst_iff_of_isTwoFibreProduct_pair {𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS}
    {f : 𝒳 ⟶ 𝒵} {g : 𝒴 ⟶ 𝒵} {P Q : Bicategory.TwoCommSq f g}
    (hP : Bicategory.IsTwoFibreProduct P) (hQ : Bicategory.IsTwoFibreProduct Q) :
    IsSmooth B S hS P.fst ↔ IsSmooth B S hS Q.fst :=
  ⟨isSmooth_fst_of_isTwoFibreProduct_pair B S hS hP hQ,
    isSmooth_fst_of_isTwoFibreProduct_pair B S hS hQ hP⟩

/-- **Smoothness of the canonical base change from smoothness of the first leg of any 2-fibre
product square of the same cospan.** For `g : 𝒴 ⟶ 𝒵` and `f : 𝒳 ⟶ 𝒵`, if some 2-fibre product
square `P` of the cospan `(g, f)` has smooth first leg, then so does
`AlgebraicGeometry.Stack.twoFibreProductSquareAlgebraicStacks`, the canonical one (**Stacks
04T2**).

This is the form in which a moduli description of a base change discharges a smoothness
hypothesis stated about the canonical base change, such as the hypothesis `hbase` of
`AlgebraicGeometry.isSmooth_polarizedCurvesToCurvesAlgebraicOfPolarized_of_schemeChartBaseChange`.
-/
theorem isSmooth_fst_twoFibreProductSquare_of_isTwoFibreProduct
    {𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS} (g : 𝒴 ⟶ 𝒵) (f : 𝒳 ⟶ 𝒵)
    {P : Bicategory.TwoCommSq g f} (hP : Bicategory.IsTwoFibreProduct P)
    (h : IsSmooth B S hS P.fst) :
    IsSmooth B S hS (Stack.twoFibreProductSquareAlgebraicStacks B S hS g f).fst :=
  isSmooth_fst_of_isTwoFibreProduct_pair B S hS hP
    (Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS g f) h

/-- **The smoothness analogue of
`AlgebraicGeometry.Stack.isAlgebraicStack_twoFibreProduct_of_costructuredArrow`.** Let
`f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S` and `g : (Sch/U) ⟶ 𝒴` a point of `𝒴`
with values in a scheme `U` of the site. The base change `(Sch/U) ×_𝒴 𝒳 ⟶ (Sch/U)` of `f` along
`g` is smooth as soon as some algebraic stack `𝒟` carrying a smooth 1-morphism `q : 𝒟 ⟶ (Sch/U)`
is equivalent to the base change over the site through an equivalence `e` with `q ≅ e ≫ fst`.

Compared with the algebraicity statement, the extra input is exactly `hq`: an equivalence over
the site transports algebraicity of the apex unconditionally, but it transports smoothness of the
projection only when it is compatible with that projection. -/
theorem isSmooth_fst_twoFibreProductSquare_of_equivalenceOver
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (U : BigFppfOver B S hS)
    (g : Stack.schemeStack.{u, w} B S hS U ⟶ 𝒴) (f : 𝒳 ⟶ 𝒴)
    (𝒟 : Stack.AlgebraicStacks.{u, w} B S hS)
    (e : 𝒟 ⟶ (Stack.twoFibreProductSquareAlgebraicStacks B S hS g f).pt)
    (he : Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor e.hom))
    (q : 𝒟 ⟶ Stack.schemeStack.{u, w} B S hS U)
    (hq : q ≅ e ≫ (Stack.twoFibreProductSquareAlgebraicStacks B S hS g f).fst)
    (hqsm : IsSmooth B S hS q) :
    IsSmooth B S hS (Stack.twoFibreProductSquareAlgebraicStacks B S hS g f).fst :=
  isSmooth_of_isEquivalence_of_twoIso B S hS e he q
    (Stack.twoFibreProductSquareAlgebraicStacks B S hS g f).fst hq hqsm

end AlgebraicGeometry.Stack.AlgebraicStacks

end
