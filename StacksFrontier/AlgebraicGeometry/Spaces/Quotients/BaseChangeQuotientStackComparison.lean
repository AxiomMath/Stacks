module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackSquares.FunctorialitySquareTerminality
public import StacksFrontier.AlgebraicGeometry.Spaces.Quotients.BaseChangeQuotientStackTwoFibreProduct
public import StacksFrontier.CategoryTheory.TwoFibreProduct.IsTwoFibreProductOfEquivalence

/-!
# Reducing Stacks 0DTG to its comparison 1-morphism

Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces over an algebraic space `B` over a
scheme `S` of a big fppf site, let `φ : U ⟶ X` be an `R`-invariant morphism of algebraic spaces
over `B`, let `g : X' ⟶ X` be a morphism of algebraic spaces over `B` and let
`(U', R', s', t', c')` be the base change of Stacks 048G. The square of Stacks 0DTG,

```
[U'/R'] ---> [U/R]
  |            |
  v            v
 𝒮_{X'} ---> 𝒮_X
```

is `AlgebraicGeometry.Stack.baseChangeQuotientStackSquare`, and
`AlgebraicGeometry.Stack.baseChangeQuotientStackComparison` is the comparison 1-morphism
`c : [U'/R'] ⟶ [U/R] ×_{𝒮_X} 𝒮_{X'}` it determines into the 2-fibre product of the cospan. This
file proves that **the square is a 2-fibre product as soon as `c` is fully faithful and locally
essentially surjective on fibres**.

## Main definitions

* `AlgebraicGeometry.Stack.baseChangeQuotientStackComparison`: the comparison 1-morphism `c`.

## Main results

* `AlgebraicGeometry.Stack.baseChangeQuotientStackComparison_comp` and
  `AlgebraicGeometry.Stack.isFibredOneMorphism_baseChangeQuotientStackComparison`: `c` is
  strictly over the site, hence a 1-morphism of fibred categories.
* `AlgebraicGeometry.Stack.isEquivalenceOver_baseChangeTwoFibreProduct`: a fully faithful,
  locally essentially surjective 1-morphism from a category with effective descent into the
  2-fibre product is an equivalence over the site.
* `AlgebraicGeometry.Stack.isTwoFibreProduct_baseChangeQuotientStackSquare`: the reduction — the
  square of Stacks 0DTG is a 2-fibre product (**Stacks 003Q**) once `c` is full, faithful and
  locally essentially surjective on fibres.

## Implementation notes

The route is the one of Stacks 04M9 and Stacks 04ZN as this library carries them: the 2-fibre
product property is *terminality* in the category of 2-commutative squares over the cospan
(Stacks 003O), the explicit 2-fibre product of Stacks 0040 is terminal there by
`AlgebraicGeometry.Stack.relativeProductIsTerminal`, and terminality transports along a
pre-morphism of squares whose underlying 1-morphism is an equivalence of the underlying
categories, by `CategoryTheory.Bicategory.isTwoFibreProduct_of_section`.

The comparison 1-morphism is taken to be the one that
`AlgebraicGeometry.Stack.relativeProductPreHom` produces from the square, rather than a second,
separately built mediating 1-morphism: that keeps the transport of terminality free of any
comparison between two mediating 1-morphisms. Unfolded, it is
`CategoryTheory.TwoFibreProductOver.lift` of the two arrows out of `[U'/R']` and the filler of
the square, so on an object it is the triple consisting of its image in `[U/R]`, its image in
`𝒮_{X'}` and the component of the filler.

## References

* [Stacks Project, Tag 003O](https://stacks.math.columbia.edu/tag/003O)
* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 003Z](https://stacks.math.columbia.edu/tag/003Z)
* [Stacks Project, Tag 0040](https://stacks.math.columbia.edu/tag/0040)
* [Stacks Project, Tag 026F](https://stacks.math.columbia.edu/tag/026F)
* [Stacks Project, Tag 04M9](https://stacks.math.columbia.edu/tag/04M9)
* [Stacks Project, Tag 04ZN](https://stacks.math.columbia.edu/tag/04ZN)
* [Stacks Project, Tag 0DTG](https://stacks.math.columbia.edu/tag/0DTG)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-! ### The equivalence criterion -/

section Criterion

variable (G : GroupoidInAlgebraicSpaces C S hS B) {X X' : AlgebraicSpaces C S hS}
  (XtoB : X ⟶ B) (g : X' ⟶ X)
  (φ : G.objects ⟶ X) (hφB : φ ≫ XtoB = G.objectsToBase)
  (hφ : Space.IsInvariant (Space.groupoidPreRelation G) φ.hom)

/-- **A fully faithful 1-morphism into the 2-fibre product `[U/R] ×_{𝒮_X} 𝒮_{X'}` which is
locally essentially surjective on fibres is an equivalence over the big fppf site**, provided
descent is effective in its source.

This uses only condition (1)
(`AlgebraicGeometry.Stack.isFibered_baseChangeTwoFibreProduct`) and condition (2)
(`AlgebraicGeometry.Stack.isMorSheaf_baseChangeTwoFibreProduct`) of Stacks 026F, which are all
that `CategoryTheory.Functor.isEquivalenceOver_of_locallyEssSurjOnFibers` asks of its target. -/
theorem isEquivalenceOver_baseChangeTwoFibreProduct
    {𝒳 : Type (u + 1)} [Category.{u + 1} 𝒳] {p : 𝒳 ⥤ BigFppfOver C S hS} [p.IsFibered]
    (hdesc : Functor.HasEffectiveDescent p (BigFppfOver.topology C S hS))
    {F : 𝒳 ⥤ baseChangeTwoFibreProductObj G XtoB g φ hφB hφ}
    (hF : Functor.IsFibredOneMorphism p (baseChangeTwoFibreProduct G XtoB g φ hφB hφ) F)
    [F.Full] [F.Faithful]
    (hloc : have := isFibered_baseChangeTwoFibreProduct G XtoB g φ hφB hφ
      Functor.LocallyEssSurjOnFibers (isFibered_baseChangeTwoFibreProduct G XtoB g φ hφB hφ)
        hF.comp_eq (BigFppfOver.topology C S hS)) :
    Nonempty (Functor.IsEquivalenceOver p (baseChangeTwoFibreProduct G XtoB g φ hφB hφ) F) := by
  have := isFibered_baseChangeTwoFibreProduct G XtoB g φ hφB hφ
  exact Functor.isEquivalenceOver_of_locallyEssSurjOnFibers hdesc
    (isMorSheaf_baseChangeTwoFibreProduct G XtoB g φ hφB hφ) hF hloc

end Criterion

/-! ### The comparison 1-morphism and the reduction -/

section BaseChange

variable (G : GroupoidInAlgebraicSpaces C S hS B) {X X' : AlgebraicSpaces C S hS}
  (XtoB : X ⟶ B) (X'toB : X' ⟶ B) (g : X' ⟶ X) (hg : g ≫ XtoB = X'toB)
  (φ : G.objects ⟶ X) (hφB : φ ≫ XtoB = G.objectsToBase)
  (hφ : Space.IsInvariant (Space.groupoidPreRelation G) φ.hom)

/-- The cospan of the Stacks 0DTG square: the structure arrow `[U/R] ⟶ 𝒮_X` of Stacks 044R. -/
noncomputable abbrev baseChangeCospanFst :
    quotientStackInGroupoids (invariantTargetGroupoid G XtoB φ hφB hφ) ⟶
      liftedFibredCategoryInGroupoids X :=
  Bicategory.InducedBicategory.mkHom
    (liftedQuotientStackToBase (invariantTargetGroupoid G XtoB φ hφB hφ))

/-- The cospan of the Stacks 0DTG square: the 1-morphism `𝒮_{X'} ⟶ 𝒮_X` of Stacks 0458. -/
noncomputable abbrev baseChangeCospanSnd :
    liftedFibredCategoryInGroupoids X' ⟶ liftedFibredCategoryInGroupoids X :=
  Bicategory.InducedBicategory.mkHom (liftedAssociatedMap g)

/-- **The comparison 1-morphism `c : [U'/R'] ⟶ [U/R] ×_{𝒮_X} 𝒮_{X'}` of Stacks 0DTG**: the
mediating 1-morphism of Stacks 0040 for the square
`AlgebraicGeometry.Stack.baseChangeQuotientStackSquare`. On an object `w` of `[U'/R']` over a
test object `T` it is the triple consisting of the image of `w` in `[U/R]`, the point of `X'`
that `w` determines and the component of the filler of the square at `w`.

Stacks 0DTG is the assertion that `c` is an equivalence over the site, which by
`AlgebraicGeometry.Stack.isEquivalenceOver_baseChangeTwoFibreProduct` follows from `c` being
fully faithful and locally essentially surjective on fibres. -/
noncomputable def baseChangeQuotientStackComparison :
    (quotientStack (invariantBaseChangeGroupoid G XtoB g φ hφB hφ)).obj ⥤
      baseChangeTwoFibreProductObj G XtoB g φ hφB hφ :=
  (relativeProductPreHom.{u, w} (baseChangeCospanFst.{u, w} G XtoB φ hφB hφ)
    (baseChangeCospanSnd.{u, w} g)
    (isStackInGroupoids_baseChangeTwoFibreProduct G XtoB g φ hφB hφ)
    (baseChangeQuotientStackSquare.{u, w} G XtoB X'toB g hg φ hφB hφ)).hom.hom.toFunctor

/-- **The comparison 1-morphism is strictly over the big fppf site.** -/
theorem baseChangeQuotientStackComparison_comp :
    baseChangeQuotientStackComparison.{u, w} G XtoB X'toB g hg φ hφB hφ ⋙
        baseChangeTwoFibreProduct G XtoB g φ hφB hφ =
      (quotientStack (invariantBaseChangeGroupoid G XtoB g φ hφB hφ)).p :=
  (relativeProductPreHom.{u, w} (baseChangeCospanFst.{u, w} G XtoB φ hφB hφ)
    (baseChangeCospanSnd.{u, w} g)
    (isStackInGroupoids_baseChangeTwoFibreProduct G XtoB g φ hφB hφ)
    (baseChangeQuotientStackSquare.{u, w} G XtoB X'toB g hg φ hφB hφ)).hom.hom.w

/-- **The comparison 1-morphism is a 1-morphism of fibred categories over the big fppf site.**
It is strictly over the site, and preservation of strongly cartesian morphisms is free because
the target is fibred in groupoids (Stacks 0041 for the 2-fibre product). -/
theorem isFibredOneMorphism_baseChangeQuotientStackComparison :
    Functor.IsFibredOneMorphism
      (quotientStack (invariantBaseChangeGroupoid G XtoB g φ hφB hφ)).p
      (baseChangeTwoFibreProduct G XtoB g φ hφB hφ)
      (baseChangeQuotientStackComparison.{u, w} G XtoB X'toB g hg φ hφB hφ) :=
  (isFiberedInGroupoids_baseChangeTwoFibreProduct G XtoB g φ hφB hφ).isFibredOneMorphism
    (baseChangeQuotientStackComparison_comp.{u, w} G XtoB X'toB g hg φ hφB hφ)

/-- **The square of Stacks 0DTG is a 2-fibre product once its comparison 1-morphism is full,
faithful and locally essentially surjective on fibres.**

The comparison 1-morphism is an equivalence over the site by
`AlgebraicGeometry.Stack.isEquivalenceOver_baseChangeTwoFibreProduct`, and terminality in the
category of 2-commutative squares over the cospan transports along it, exactly as for
Stacks 04M9 and Stacks 04ZN. -/
noncomputable def isTwoFibreProduct_baseChangeQuotientStackSquare
    (hfull : (baseChangeQuotientStackComparison.{u, w} G XtoB X'toB g hg φ hφB hφ).Full)
    (hfaithful : (baseChangeQuotientStackComparison.{u, w} G XtoB X'toB g hg φ hφB hφ).Faithful)
    (hloc : have := isFibered_baseChangeTwoFibreProduct G XtoB g φ hφB hφ
      Functor.LocallyEssSurjOnFibers (isFibered_baseChangeTwoFibreProduct G XtoB g φ hφB hφ)
        (isFibredOneMorphism_baseChangeQuotientStackComparison.{u, w}
          G XtoB X'toB g hg φ hφB hφ).comp_eq (BigFppfOver.topology C S hS)) :
    Bicategory.IsTwoFibreProduct
      (baseChangeQuotientStackSquare.{u, w} G XtoB X'toB g hg φ hφB hφ) := by
  refine Nonempty.some ?_
  have := hfull
  have := hfaithful
  have hprod := isStackInGroupoids_baseChangeTwoFibreProduct G XtoB g φ hφB hφ
  let hP := relativeProductIsTerminal.{u, w} (baseChangeCospanFst.{u, w} G XtoB φ hφB hφ)
    (baseChangeCospanSnd.{u, w} g) hprod
  let k := relativeProductPreHom.{u, w} (baseChangeCospanFst.{u, w} G XtoB φ hφB hφ)
    (baseChangeCospanSnd.{u, w} g) hprod
    (baseChangeQuotientStackSquare.{u, w} G XtoB X'toB g hg φ hφB hφ)
  have : (quotientStack (invariantBaseChangeGroupoid G XtoB g φ hφB hφ)).p.IsFibered :=
    (isStack_quotientStack (invariantBaseChangeGroupoid G XtoB g φ hφB hφ)).isFibered
  obtain ⟨hequiv⟩ := isEquivalenceOver_baseChangeTwoFibreProduct G XtoB g φ hφB hφ
    (isStack_quotientStack (invariantBaseChangeGroupoid G XtoB g φ hφB hφ)).hasEffectiveDescent
    (isFibredOneMorphism_baseChangeQuotientStackComparison.{u, w} G XtoB X'toB g hg φ hφB hφ) hloc
  have hce : (baseChangeQuotientStackComparison.{u, w} G XtoB X'toB g hg φ hφB hφ).IsEquivalence :=
    (CategoryTheory.Equivalence.mk
      (baseChangeQuotientStackComparison.{u, w} G XtoB X'toB g hg φ hφB hφ) hequiv.inv
      hequiv.unitIso.symm hequiv.counitIso).isEquivalence_functor
  obtain ⟨K, hK, η, ε, hη, hε⟩ := Functor.IsFiberedInGroupoids.isEquivalence_over
    (quotientStack (invariantBaseChangeGroupoid G XtoB g φ hφB hφ)).p
    (baseChangeTwoFibreProduct G XtoB g φ hφB hφ)
    (isFiberedInGroupoids_quotientStack (invariantBaseChangeGroupoid G XtoB g φ hφB hφ))
    (isFiberedInGroupoids_baseChangeTwoFibreProduct G XtoB g φ hφB hφ)
    (baseChangeQuotientStackComparison.{u, w} G XtoB X'toB g hg φ hφB hφ)
    (baseChangeQuotientStackComparison_comp.{u, w} G XtoB X'toB g hg φ hφB hφ) hce
  exact ⟨Bicategory.isTwoFibreProduct_of_section hP
    (k.ofSection (Bicategory.InducedBicategory.mkHom ⟨K, hK⟩)
      (Bicategory.InducedBicategory.isoMk (BasedNatIso.mkNatIso ε hε)))
    k.hom (Bicategory.InducedBicategory.isoMk (BasedNatIso.mkNatIso η hη))⟩

end BaseChange

end AlgebraicGeometry.Stack

end
