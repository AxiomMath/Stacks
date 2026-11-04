module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackSquares.FunctorialityComparison
public import StacksFrontier.CategoryTheory.Sites.Stack.TwoFibreProductDescentIndependentBase
public import StacksFrontier.CategoryTheory.TwoFibreProduct.IsTwoFibreProductOfEquivalence

/-!
# Reducing Stacks 04ZN to the comparison 1-morphism

Let `φ : (U, R, s, t, c) ⟶ (U', R', s', t', c')` be a morphism of groupoids in algebraic spaces
over an algebraic space `B` over a scheme `S` of a big fppf site. The square of Stacks 04ZN,

```
𝒮_U ----π----> [U/R]
 |              |
𝒮_f            [φ]
 v              v
𝒮_{U'} --π'--> [U'/R']
```

is `AlgebraicGeometry.Stack.functorialitySquare`, and
`AlgebraicGeometry.Stack.functorialityComparison` is the comparison 1-morphism
`c : 𝒮_U ⟶ [U/R] ×_{[U'/R']} 𝒮_{U'}` it determines into the 2-fibre product of the cospan.
This file proves that **the square is a 2-fibre product as soon as `c` is full and locally
essentially surjective on fibres**, which is the whole of Stacks 04ZN apart from those two
statements: `c` is faithful for free, and the cartesian source square that Stacks 04ZN assumes is
not used here at all — it is what the two halves use.

## Main results

* `AlgebraicGeometry.Stack.isStack_functorialityTwoFibreProduct` and
  `AlgebraicGeometry.Stack.isStackInGroupoids_functorialityTwoFibreProduct`: **Stacks 026G** and
  **Stacks 02ZI** for the 2-fibre product of the cospan, at the universes at hand.
* `AlgebraicGeometry.Stack.isTwoFibreProduct_functorialitySquare`: the reduction — the square of
  Stacks 04ZN is a 2-fibre product (**Stacks 003Q**) once `c` is full and locally essentially
  surjective on fibres.

## Implementation notes

The route is the one of Stacks 04M9 as this library carries it
(`AlgebraicGeometry.Stack.quotientStack_twoFibreProduct`): the 2-fibre product property is
*terminality* in the category of 2-commutative squares over the cospan (Stacks 003O), the explicit
2-fibre product of Stacks 0040 is terminal there by
`AlgebraicGeometry.Stack.relativeProductIsTerminal`, and terminality transports along a
pre-morphism of squares whose underlying 1-morphism is an equivalence of the underlying
categories, by `CategoryTheory.Bicategory.isTwoFibreProduct_of_section`.

The hypothesis `AlgebraicGeometry.Stack.relativeProductIsTerminal` needs is that the structure
functor of the explicit 2-fibre product is a stack in groupoids with the hom universe of the site
left free. That is Stacks 026G in the form
`CategoryTheory.TwoFibreProductOver.isStack_structureFunctor`, whose two hom
universes are independent — here the site's is `u` and the three categories of the cospan have
`u + 1` — followed by `CategoryTheory.Functor.IsStack.isStackInGroupoids`.

That `c` is an equivalence of the underlying categories is
`AlgebraicGeometry.Stack.isEquivalenceOver_functorialityTwoFibreProduct` applied to the two
hypotheses, the effective descent of the enlarged object-space stack and the faithfulness that
comes for free; the quasi-inverse *over the site* and the two vertical 2-cells that the transport
consumes are then supplied by Stacks 003Z (2),
`CategoryTheory.Functor.IsFiberedInGroupoids.isEquivalence_over`. The mediating pre-morphism is
`AlgebraicGeometry.Stack.relativeProductPreHom` applied to the square, whose underlying functor is
`AlgebraicGeometry.Stack.functorialityComparison` on the nose.

## References

* [Stacks Project, Tag 003O](https://stacks.math.columbia.edu/tag/003O)
* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 003Z](https://stacks.math.columbia.edu/tag/003Z)
* [Stacks Project, Tag 0040](https://stacks.math.columbia.edu/tag/0040)
* [Stacks Project, Tag 026G](https://stacks.math.columbia.edu/tag/026G)
* [Stacks Project, Tag 02ZI](https://stacks.math.columbia.edu/tag/02ZI)
* [Stacks Project, Tag 04M9](https://stacks.math.columbia.edu/tag/04M9)
* [Stacks Project, Tag 04ZN](https://stacks.math.columbia.edu/tag/04ZN)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u

open AlgebraicGeometry.GroupoidInAlgebraicSpaces

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS} {G G' : GroupoidInAlgebraicSpaces C S hS B}

/-! ### The 2-fibre product of the cospan is a stack -/

/-- **Stacks 026G for the 2-fibre product `[U/R] ×_{[U'/R']} 𝒮_{U'}`**: it is a stack over the big
fppf site. The three categories of the cospan are stacks, the two legs are 1-morphisms of fibred
categories, and the universe-independent form of Stacks 026G applies — the hom universe of the
site is `u` and that of the three categories is `u + 1`. -/
theorem isStack_functorialityTwoFibreProduct (φ : Hom G G') :
    Functor.IsStack (functorialityTwoFibreProduct φ) (BigFppfOver.topology C S hS) :=
  TwoFibreProductOver.isStack_structureFunctor _ _ _ _ _
    (BigFppfOver.topology C S hS) (isStack_quotientStack G)
    (liftedFibredCategory_isStack G'.objects) (isStack_quotientStack G')
    (isFibredOneMorphism_quotientStackMap φ)
    (isFibredOneMorphism_liftedQuotientStackProjection G')

/-- **Stacks 02ZI for the 2-fibre product `[U/R] ×_{[U'/R']} 𝒮_{U'}`**: it is a stack in
groupoids over the big fppf site, being a stack (Stacks 026G) that is fibred in groupoids
(Stacks 0041). -/
theorem isStackInGroupoids_functorialityTwoFibreProduct (φ : Hom G G') :
    (functorialityTwoFibreProduct φ).IsStackInGroupoids (BigFppfOver.topology C S hS) :=
  (isStack_functorialityTwoFibreProduct φ).isStackInGroupoids
    (isFiberedInGroupoids_functorialityTwoFibreProduct φ)

/-! ### The two objects of the cospan -/

/-- The quotient stack of a groupoid in algebraic spaces, as an object of the 2-category of
stacks in groupoids over the big fppf site. -/
noncomputable abbrev quotientStackInGroupoids (G : GroupoidInAlgebraicSpaces C S hS B) :
    StackInGroupoids (BigFppfOver C S hS) (BigFppfOver.topology C S hS) :=
  ⟨quotientStack G, isStackInGroupoids_quotientStack G⟩

/-- The universe-enlarged fibred category of an algebraic space, as an object of the 2-category of
stacks in groupoids over the big fppf site. -/
noncomputable abbrev liftedFibredCategoryInGroupoids (X : AlgebraicSpaces C S hS) :
    StackInGroupoids (BigFppfOver C S hS) (BigFppfOver.topology C S hS) :=
  ⟨liftedFibredCategory X, isStackInGroupoids_liftedFibredCategory X⟩

/-! ### The reduction -/

/-- **The square of Stacks 04ZN is a 2-fibre product once its comparison 1-morphism is full and
locally essentially surjective on fibres.**

Faithfulness of the comparison 1-morphism is free
(`AlgebraicGeometry.Stack.functorialityComparison_faithful`), so the two hypotheses here are
exactly the two halves of Stacks 04ZN, and the cartesian source square that Stacks 04ZN assumes
is used only inside them: nothing in this proof consumes it, which is why this declaration does
**not** carry the tag of Stacks 04ZN.

The comparison 1-morphism is an equivalence over the site by
`AlgebraicGeometry.Stack.isEquivalenceOver_functorialityTwoFibreProduct`, and terminality in the
category of 2-commutative squares over the cospan transports along it, exactly as for
Stacks 04M9. -/
noncomputable def isTwoFibreProduct_functorialitySquare (φ : Hom G G')
    (hfull : (functorialityComparison φ).Full)
    (hloc : Functor.LocallyEssSurjOnFibers (isFibered_functorialityTwoFibreProduct φ)
      (isFibredOneMorphism_functorialityComparison φ).comp_eq (BigFppfOver.topology C S hS)) :
    Bicategory.IsTwoFibreProduct (functorialitySquare φ) := by
  refine Nonempty.some ?_
  let h₀ : quotientStackInGroupoids G ⟶ quotientStackInGroupoids G' :=
    Bicategory.InducedBicategory.mkHom (quotientStackMap φ)
  let s₀ : liftedFibredCategoryInGroupoids G'.objects ⟶ quotientStackInGroupoids G' :=
    Bicategory.InducedBicategory.mkHom (liftedQuotientStackProjection G')
  let hprod := isStackInGroupoids_functorialityTwoFibreProduct φ
  let P := relativeProductSquare h₀ s₀ hprod
  let hP := relativeProductIsTerminal h₀ s₀ hprod
  let k := relativeProductPreHom h₀ s₀ hprod (functorialitySquare φ)
  have := hfull
  have := functorialityComparison_faithful φ
  have : (liftedFibredCategory G.objects).p.IsFibered :=
    (liftedFibredCategory_isStack G.objects).isFibered
  obtain ⟨hequiv⟩ := isEquivalenceOver_functorialityTwoFibreProduct φ
    (liftedFibredCategory_isStack G.objects).hasEffectiveDescent
    (isFibredOneMorphism_functorialityComparison φ) hloc
  have hce : (functorialityComparison φ).IsEquivalence :=
    (CategoryTheory.Equivalence.mk (functorialityComparison φ) hequiv.inv
      hequiv.unitIso.symm hequiv.counitIso).isEquivalence_functor
  obtain ⟨K, hK, η, ε, hη, hε⟩ := Functor.IsFiberedInGroupoids.isEquivalence_over
    (liftedFibredCategory G.objects).p (functorialityTwoFibreProduct φ)
    (isFiberedInGroupoids_uliftHom _ (fibredCategory C S hS G.objects.obj).property)
    (isFiberedInGroupoids_functorialityTwoFibreProduct φ)
    (functorialityComparison φ) (functorialityComparison_comp φ) hce
  exact ⟨Bicategory.isTwoFibreProduct_of_section hP
    (k.ofSection (Bicategory.InducedBicategory.mkHom ⟨K, hK⟩)
      (Bicategory.InducedBicategory.isoMk (BasedNatIso.mkNatIso ε hε)))
    k.hom (Bicategory.InducedBicategory.isoMk (BasedNatIso.mkNatIso η hη))⟩

end AlgebraicGeometry.Stack

end
