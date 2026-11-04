module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.Functoriality
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackSquares.TwoFibreProduct
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoFibreProduct
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.EquivalenceOverMorSheafTarget
public import StacksFrontier.CategoryTheory.Sites.Stack.TwoFibreProductMorSheafIndependentBase

/-!
# The 2-fibre product of a quotient stack with an object-space stack

Let `φ : (U, R, s, t, c) ⟶ (U', R', s', t', c')` be a morphism of groupoids in algebraic spaces
over an algebraic space `B` over a scheme `S` of a big fppf site. Stacks 046Q gives the induced
1-morphism `[φ] : [U/R] ⟶ [U'/R']` of quotient stacks and Stacks 044R the projection
`π' : 𝒮_{U'} ⟶ [U'/R']`. This file assembles the cospan

    [U/R] --[φ]--> [U'/R'] <--π'-- 𝒮_{U'}

and the 2-fibre product `[U/R] ×_{[U'/R']} 𝒮_{U'}` of Stacks 0040 over it, and proves that, as a
category over the big fppf site, this 2-fibre product is fibred in groupoids (Stacks 0041), is a
fibred category (Stacks 02XQ) and has sheaves as morphism presheaves (condition (2) of
Stacks 026F). Those are exactly the hypotheses of
`CategoryTheory.Functor.isEquivalenceOver_of_locallyEssSurjOnFibers`, so a 1-morphism from a
stack into this 2-fibre product is an equivalence over the site as soon as it is fully faithful
and locally essentially surjective on fibres.

## Implementation notes

*Universes.* The object-space side is the **enlarged** fibred category
`AlgebraicGeometry.Stack.liftedFibredCategory`, whose morphisms live one universe above the
site's, as the two quotient stacks' do. The enlargement is what lets the three categories of the
cospan share a hom universe, which is what condition (2) of Stacks 026F needs: the cospan of
morphism presheaves it compares is a cospan of presheaves of types in one universe. See the module
docstring of
`StacksFrontier/CategoryTheory/Sites/Stack/TwoFibreProductMorSheafIndependentBase.lean`.

## Main definitions

* `AlgebraicGeometry.Stack.functorialityTwoFibreProduct`: the 2-fibre product
  `[U/R] ×_{[φ], [U'/R'], π'} 𝒮_{U'}`, as a category over the big fppf site.

## Main results

* `AlgebraicGeometry.Stack.isFibredOneMorphism_quotientStackMap`: the induced 1-morphism of
  Stacks 046Q is a 1-morphism of fibred categories over the site.
* `AlgebraicGeometry.Stack.isFibredOneMorphism_liftedQuotientStackProjection`: so is the
  enlarged projection of Stacks 044R.
* `AlgebraicGeometry.Stack.isFiberedInGroupoids_functorialityTwoFibreProduct`,
  `AlgebraicGeometry.Stack.isFibered_functorialityTwoFibreProduct` and
  `AlgebraicGeometry.Stack.isMorSheaf_functorialityTwoFibreProduct`: Stacks 0041, Stacks 02XQ and
  condition (2) of Stacks 026F for it.
* `AlgebraicGeometry.Stack.isEquivalenceOver_functorialityTwoFibreProduct`: a fully faithful,
  locally essentially surjective 1-morphism from a stack into it is an equivalence over the site.

## References

* [Stacks Project, Tag 0040](https://stacks.math.columbia.edu/tag/0040)
* [Stacks Project, Tag 0041](https://stacks.math.columbia.edu/tag/0041)
* [Stacks Project, Tag 026F](https://stacks.math.columbia.edu/tag/026F)
* [Stacks Project, Tag 02XQ](https://stacks.math.columbia.edu/tag/02XQ)
* [Stacks Project, Tag 044R](https://stacks.math.columbia.edu/tag/044R)
* [Stacks Project, Tag 046N](https://stacks.math.columbia.edu/tag/046N)
* [Stacks Project, Tag 046Q](https://stacks.math.columbia.edu/tag/046Q)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS} {G G' : GroupoidInAlgebraicSpaces C S hS B}

/-! ### The two legs of the cospan -/

/-- **The induced 1-morphism of quotient stacks is a 1-morphism of fibred categories.** It is
strictly over the site by Stacks 046Q, and preservation of strongly cartesian morphisms is free
because the target is fibred in groupoids
(`CategoryTheory.Functor.IsFiberedInGroupoids.isFibredOneMorphism`). -/
theorem isFibredOneMorphism_quotientStackMap (φ : GroupoidInAlgebraicSpaces.Hom G G') :
    Functor.IsFibredOneMorphism (quotientStack G).p (quotientStack G').p
      (quotientStackMap φ).toFunctor :=
  (isFiberedInGroupoids_quotientStack G').isFibredOneMorphism (quotientStackMap φ).w

/-- **The enlarged projection of Stacks 044R is a 1-morphism of fibred categories.** As for
`AlgebraicGeometry.Stack.isFibredOneMorphism_quotientStackMap`, preservation of strongly cartesian
morphisms comes for free from the quotient stack being fibred in groupoids. -/
theorem isFibredOneMorphism_liftedQuotientStackProjection
    (G' : GroupoidInAlgebraicSpaces C S hS B) :
    Functor.IsFibredOneMorphism (liftedFibredCategory G'.objects).p (quotientStack G').p
      (liftedQuotientStackProjection G').toFunctor :=
  (isFiberedInGroupoids_quotientStack G').isFibredOneMorphism
    (liftedQuotientStackProjection G').w

/-! ### The 2-fibre product -/

/-- **The 2-fibre product `[U/R] ×_{[φ], [U'/R'], π'} 𝒮_{U'}`** of Stacks 0040, as a category over
the big fppf site: the 2-fibre product of the induced 1-morphism of Stacks 046Q and the enlarged
projection of Stacks 044R. -/
noncomputable abbrev functorialityTwoFibreProductObj
    (φ : GroupoidInAlgebraicSpaces.Hom G G') : Type (u + 1) :=
  TwoFibreProductOver (quotientStack G).p (liftedFibredCategory G'.objects).p
    (quotientStack G').p (quotientStackMap φ).toFunctor
    (liftedQuotientStackProjection G').toFunctor

/-- The structure functor of the 2-fibre product `[U/R] ×_{[U'/R']} 𝒮_{U'}`. -/
noncomputable abbrev functorialityTwoFibreProduct
    (φ : GroupoidInAlgebraicSpaces.Hom G G') :
    functorialityTwoFibreProductObj φ ⥤ BigFppfOver C S hS :=
  TwoFibreProductOver.structureFunctor _ _ _ _ _

/-- **Stacks 0041** for the 2-fibre product `[U/R] ×_{[U'/R']} 𝒮_{U'}`: it is fibred in
groupoids, because the two quotient stacks and the enlarged object-space stack are and the two
legs are strictly over the site. -/
theorem isFiberedInGroupoids_functorialityTwoFibreProduct
    (φ : GroupoidInAlgebraicSpaces.Hom G G') :
    (functorialityTwoFibreProduct φ).IsFiberedInGroupoids :=
  TwoFibreProductOver.isFiberedInGroupoids _ _ _ _ _
    (isFiberedInGroupoids_quotientStack G)
    (isFiberedInGroupoids_uliftHom _ (fibredCategory C S hS G'.objects.obj).property)
    (isFiberedInGroupoids_quotientStack G')
    (quotientStackMap φ).w (liftedQuotientStackProjection G').w

/-- **Stacks 02XQ** for the 2-fibre product `[U/R] ×_{[U'/R']} 𝒮_{U'}`: it is a fibred category
over the big fppf site. -/
theorem isFibered_functorialityTwoFibreProduct
    (φ : GroupoidInAlgebraicSpaces.Hom G G') :
    (functorialityTwoFibreProduct φ).IsFibered := by
  have : (quotientStack G).p.IsFibered := (isStack_quotientStack G).isFibered
  have : (quotientStack G').p.IsFibered := (isStack_quotientStack G').isFibered
  have : (liftedFibredCategory G'.objects).p.IsFibered :=
    (liftedFibredCategory_isStack G'.objects).isFibered
  exact TwoFibreProductOver.isFibered_structureFunctor _ _ _ _ _
    (isFibredOneMorphism_quotientStackMap φ)
    (isFibredOneMorphism_liftedQuotientStackProjection G')

/-- **Condition (2) of Stacks 026F for the 2-fibre product `[U/R] ×_{[U'/R']} 𝒮_{U'}`**: its
morphism presheaves are sheaves on the big fppf site.

The two quotient stacks and the enlarged object-space stack are stacks, so their morphism
presheaves are sheaves, and
`CategoryTheory.TwoFibreProductOver.isMorSheaf_structureFunctor` transports that
to the 2-fibre product. The `IndependentBase` form is the one that applies: the hom universe of
the site is `u` and that of the three categories of the cospan is `u + 1`. -/
theorem isMorSheaf_functorialityTwoFibreProduct
    (φ : GroupoidInAlgebraicSpaces.Hom G G') (T : BigFppfOver C S hS)
    (x y : have := isFibered_functorialityTwoFibreProduct φ
      (functorialityTwoFibreProduct φ).Fiber T) :
    have := isFibered_functorialityTwoFibreProduct φ
    Functor.IsMorSheaf (functorialityTwoFibreProduct φ) (BigFppfOver.topology C S hS) T x y := by
  have : (quotientStack G).p.IsFibered := (isStack_quotientStack G).isFibered
  have : (quotientStack G').p.IsFibered := (isStack_quotientStack G').isFibered
  have : (liftedFibredCategory G'.objects).p.IsFibered :=
    (liftedFibredCategory_isStack G'.objects).isFibered
  have := isFibered_functorialityTwoFibreProduct φ
  exact TwoFibreProductOver.isMorSheaf_structureFunctor
    (isFibredOneMorphism_quotientStackMap φ)
    (isFibredOneMorphism_liftedQuotientStackProjection G') _
    (fun V a b => (isStack_quotientStack G).isMorSheaf V a b)
    (fun V a b => (liftedFibredCategory_isStack G'.objects).isMorSheaf V a b)
    (fun V a b => (isStack_quotientStack G').isMorSheaf V a b) T x y

/-! ### The equivalence criterion -/

/-- **A fully faithful 1-morphism into the 2-fibre product `[U/R] ×_{[U'/R']} 𝒮_{U'}` which is
locally essentially surjective on fibres is an equivalence over the big fppf site**, provided
descent is effective in its source.

This uses only condition (1)
(`AlgebraicGeometry.Stack.isFibered_functorialityTwoFibreProduct`) and condition (2)
(`AlgebraicGeometry.Stack.isMorSheaf_functorialityTwoFibreProduct`) of Stacks 026F, which are all
that `CategoryTheory.Functor.isEquivalenceOver_of_locallyEssSurjOnFibers` asks of its target.
The full `CategoryTheory.Functor.IsStack` is also available, through
`CategoryTheory.TwoFibreProductOver.isStack_structureFunctor`, so Stacks 046N in
its packaged form may be used here as well. -/
theorem isEquivalenceOver_functorialityTwoFibreProduct
    (φ : GroupoidInAlgebraicSpaces.Hom G G')
    {𝒳 : Type (u + 1)} [Category.{u + 1} 𝒳] {p : 𝒳 ⥤ BigFppfOver C S hS} [p.IsFibered]
    (hdesc : Functor.HasEffectiveDescent p (BigFppfOver.topology C S hS))
    {F : 𝒳 ⥤ functorialityTwoFibreProductObj φ}
    (hF : Functor.IsFibredOneMorphism p (functorialityTwoFibreProduct φ) F)
    [F.Full] [F.Faithful]
    (hloc : have := isFibered_functorialityTwoFibreProduct φ
      Functor.LocallyEssSurjOnFibers (isFibered_functorialityTwoFibreProduct φ) hF.comp_eq
        (BigFppfOver.topology C S hS)) :
    Nonempty (Functor.IsEquivalenceOver p (functorialityTwoFibreProduct φ) F) := by
  have := isFibered_functorialityTwoFibreProduct φ
  exact Functor.isEquivalenceOver_of_locallyEssSurjOnFibers hdesc
    (isMorSheaf_functorialityTwoFibreProduct φ) hF hloc

end AlgebraicGeometry.Stack

end
