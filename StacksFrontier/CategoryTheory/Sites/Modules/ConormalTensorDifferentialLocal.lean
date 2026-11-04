module

public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalClassLocal
public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalKernelComparison
public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalPolynomialModel

/-!
# From the polynomial model to the sheaf, in the degree `0` term

This file compares the degree `0` terms of the two conormal sequences of a presentation by a
free algebra sheaf in one direction: a polynomial whose universal differential vanishes in the
degree `0` term of the polynomial model has `1 ⊗ d` of its image in `A[E]` vanishing in the
degree `0` term of the conormal sequence.

## Main results

* `Stacks.Sites.FreeAlgebra.tensorDifferential_unit_eq_zero`: a polynomial whose universal
  differential vanishes in the degree `0` term of the *polynomial* model has
  `1 ⊗ d` of its image in `A[E]` vanishing in the degree `0` term of the conormal sequence.

## References

* [Stacks Project, Tag 08TS](https://stacks.math.columbia.edu/tag/08TS), the conormal sequence.
* [Stacks Project, Tag 08TY](https://stacks.math.columbia.edu/tag/08TY), the independence of the
  naive cotangent complex from the presentation.
-/

@[expose] public section

open CategoryTheory Opposite

universe v u w z

namespace Stacks.Sites.FreeAlgebra

open Stacks.Sites.Conormal

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

local instance [EssentiallySmall.{z} C] : HasSheafify J AddCommGrpCat.{z} :=
  AlgebraicGeometry.SheafOfModules.siteHasSheafify (J := J)

local instance [EssentiallySmall.{z} C] : J.WEqualsLocallyBijective AddCommGrpCat.{z} :=
  AlgebraicGeometry.SheafOfModules.siteWEqualsLocallyBijective (J := J)

variable [HasWeakSheafify J CommRingCat.{w}] [J.WEqualsLocallyBijective CommRingCat.{w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (A B : Sheaf J CommRingCat.{w}) (E : Functor Cᵒᵖ (Type w)) (a : A ⟶ B)
  (e : E ⟶ underlyingPresheaf J B)
  [Presheaf.IsLocallySurjective J (freeAlgebraSheafDesc J A B E a e).hom]

omit [J.WEqualsLocallyBijective CommRingCat.{w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Presheaf.IsLocallySurjective J (freeAlgebraSheafDesc J A B E a e).hom] in
/-- The universal differential of a polynomial, carried along the sheafification unit: if
`1 ⊗ d p` vanishes in the degree `0` term of the polynomial model then `1 ⊗ d` of the image of
`p` in `A[E]` vanishes in the degree `0` term of the conormal sequence. -/
theorem one_tmul_d_unit_eq_zero (X : Cᵒᵖ) (p : (polynomialPresheaf J A E).obj X)
    (h : (1 : (polynomialPresheaf J A E).obj X ⧸
          kernelIdeal (polynomialEvaluation J A B E a e) X)
        ⊗ₜ[(polynomialPresheaf J A E).obj X]
        CommRingCat.KaehlerDifferential.d
          (f := (polynomialCoefficientMap J A E).app X) p = 0) :
    (1 : (freeAlgebraSheaf J A E).obj.obj X ⧸
          kernelIdeal (freeAlgebraSheafDesc J A B E a e).hom X)
        ⊗ₜ[(freeAlgebraSheaf J A E).obj.obj X]
        CommRingCat.KaehlerDifferential.d
          (f := (freeAlgebraSheafCoefficientMap J A E).hom.app X)
          ((polynomialUnit J A E).app X p) = 0 :=
  (tensorMapOfFacₛₗ_one_tmul_d (polynomialEvaluation J A B E a e)
    (freeAlgebraSheafDesc J A B E a e).hom (polynomialUnit J A E)
    (polynomialUnit_comp_desc J A B E a e) (polynomialCoefficientMap J A E)
    (freeAlgebraSheafCoefficientMap J A E).hom
    (coefficientMap_comp_polynomialUnit J A E) X p).symm.trans
    ((congrArg _ h).trans (map_zero _))

omit [J.WEqualsLocallyBijective CommRingCat.{w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **A polynomial whose universal differential vanishes on the polynomial model has
`tensorDifferential` of its image vanishing on the sheaf.** -/
theorem tensorDifferential_unit_eq_zero (X : Cᵒᵖ)
    (p : (polynomialPresheaf J A E).obj X)
    (h : (1 : (polynomialPresheaf J A E).obj X ⧸
          kernelIdeal (polynomialEvaluation J A B E a e) X)
        ⊗ₜ[(polynomialPresheaf J A E).obj X]
        CommRingCat.KaehlerDifferential.d
          (f := (polynomialCoefficientMap J A E).app X) p = 0) :
    tensorDifferential.{v, u, w, z} J A (freeAlgebraSheaf J A E) B
        (freeAlgebraSheafCoefficientMap J A E) (freeAlgebraSheafDesc J A B E a e) X
        ((polynomialUnit J A E).app X p) = 0 :=
  (congrArg (toAssociatedModule.{v, u, w, z} J (freeAlgebraSheaf J A E) B
    (freeAlgebraSheafDesc J A B E a e)
    (tensorPresheaf (freeAlgebraSheafDesc J A B E a e).hom
      (freeAlgebraSheafCoefficientMap J A E).hom) X)
    (one_tmul_d_unit_eq_zero J A B E a e X p h)).trans
    (map_zero (((PresheafOfModules.sheafificationAdjunction.{max w u v z}
      (quotientToRingSheaf J (freeAlgebraSheaf J A E) B
        (freeAlgebraSheafDesc J A B E a e))).unit.app
      ((liftModules.{v, u, w, z} _).obj
        (tensorPresheaf (freeAlgebraSheafDesc J A B E a e).hom
          (freeAlgebraSheafCoefficientMap J A E).hom))).app X).hom)

end Stacks.Sites.FreeAlgebra

end
