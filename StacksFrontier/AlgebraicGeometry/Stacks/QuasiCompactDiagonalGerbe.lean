module

public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackEquivalence
public import StacksFrontier.AlgebraicGeometry.Stacks.CancelTwoFibreProductAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitePresentationBaseChangeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.Gerbe
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeSurjective
public import StacksFrontier.AlgebraicGeometry.Stacks.JointlySurjectiveFlatFppfLocalSections
public import StacksFrontier.AlgebraicGeometry.Stacks.ObjectMorphismFactor
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactFiniteCoverDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactMorphismPermanence
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactPointRepresentative
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalSquare
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationEquivalenceInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversallyInjectiveDiagonal
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CospanReindex
public import StacksFrontier.CategoryTheory.TwoFibreProduct.InducedBicategory
public import StacksFrontier.CategoryTheory.TwoFibreProduct.IsTwoFibreProductOfEquivalence
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverIso
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Pasting
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Swap
public import StacksFrontier.CategoryTheory.TwoYoneda.OverBase
public import StacksFrontier.CategoryTheory.TwoYoneda.RepresentedPoint

/-!
# The absolute diagonal of an algebraic stack, and the diagonal of a gerbe

This file provides, for algebraic stacks over `S`:

* the *absolute diagonal* `Δ_𝒳 : 𝒳 ⟶ 𝒳 × 𝒳`, into the product
  `AlgebraicGeometry.Stack.AlgebraicStacks.product` of **Stacks 04TE**, and the product
  `f₁ × f₂` of two 1-morphisms;
* the factorisation of `Δ_𝒳` through the relative diagonal of a 1-morphism `f : 𝒳 ⟶ 𝒴`, and the
  2-cartesianness of the resulting square;
* surjectivity of the relative diagonal `Δ_f : 𝒳 ⟶ 𝒳 ×_𝒴 𝒳` when `f` makes `𝒳` a gerbe
  over `𝒴`;
* surjectivity, flatness and local finite presentation of `𝟙_𝒵 × f`, by exhibiting it as a base
  change of `f`;
* the 1-morphism out of the algebraic stack of an object of the site named by an object of a
  fibre, and the two comparisons that make it functorial;
* if `𝒳` is a gerbe over `𝒴` and the diagonal of `𝒳` is quasi-compact, then so is the diagonal
  of `𝒴`.

## The diagonal of a 1-morphism

For a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks the absolute diagonal of `𝒳` factors through
the relative diagonal of `f`:

```text
            Δ_f              c
    𝒳  ----------> 𝒳 ×_𝒴 𝒳 ----> 𝒳 × 𝒳
                      |              |
                      |              | f × f
                      v              v
                      𝒴  ---Δ_𝒴---> 𝒴 × 𝒴
```

The comparison `c` forgets the identification of the two images in `𝒴` and keeps the one forced
over the base site; the composite of the top row is `Δ_𝒳` on the nose, and the square is a
2-fibre product of the cospan `(f × f, Δ_𝒴)`, the over-the-site form of **Stacks 02XE** read in
the 2-category of algebraic stacks (**Stacks 03YP**).

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.diagonal`: the absolute diagonal `Δ_𝒳 : 𝒳 ⟶ 𝒳 × 𝒳`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.productMap`: the product `f₁ × f₂` of two
  1-morphisms of algebraic stacks over `S`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.diagonalComparison`: the comparison
  `c : 𝒳 ×_𝒴 𝒳 ⟶ 𝒳 × 𝒳`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.diagonalComparisonSquare`: the square displayed
  above.
* `AlgebraicGeometry.Stack.AlgebraicStacks.productMapIdLeftSquare`: the square exhibiting
  `𝟙_𝒵 × f` as a base change of `f` along the second projection of `𝒵 × 𝒴`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.stackMapFibreObject`: the object of the fibre of `𝒴`
  over `A` that a 1-morphism out of the algebraic stack of `A` evaluates to.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.relativeDiagonal_comp_diagonalComparison`: the
  relative diagonal of `f` followed by the comparison is the absolute diagonal of `𝒳`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isTwoFibreProduct_diagonalComparisonSquare`:
  `𝒳 ×_𝒴 𝒳` is a 2-fibre product of `f × f` and `Δ_𝒴` in the 2-category of algebraic stacks.
* `…isSurjective_relativeDiagonal_twoFibreProduct_of_isGerbeOver`: the relative diagonal of a
  gerbe 1-morphism is surjective.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isTwoFibreProduct_productMapIdLeftSquare`,
  `…isSurjective_productMap_id_left`, `…isFlat_productMap_id_left` and
  `…isLocallyOfFinitePresentation_productMap_id_left`: `𝟙_𝒵 × f` is a base change of `f`, hence
  surjective, flat and locally of finite presentation as soon as `f` is.
* `AlgebraicGeometry.Stack.AlgebraicStacks.fibreObjectStackMapEvaluationIso`: a 1-morphism out of
  the algebraic stack of `A` is the one named by the object of the fibre it evaluates to.
* `AlgebraicGeometry.Stack.AlgebraicStacks.fibreObjectStackMapFactorIso`: a morphism of `𝒴` from
  the `f`-image of an object over `V` to an object over `A`, lying over `v : V ⟶ A`, factors the
  1-morphism named by the first through `v` and the one named by the second.
* `AlgebraicGeometry.Stack.AlgebraicStacks.pairProductMapIso`: a 1-morphism to a product is the
  pair of its two components.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiCompactMorphism_diagonal_of_isGerbeOver`: if
  `𝒳` is a gerbe over `𝒴` and the diagonal of `𝒳` is quasi-compact, then so is the diagonal of `𝒴`.

## References

* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 004B](https://stacks.math.columbia.edu/tag/004B)
* [Stacks Project, Tag 02XD](https://stacks.math.columbia.edu/tag/02XD)
* [Stacks Project, Tag 02XE](https://stacks.math.columbia.edu/tag/02XE)
* [Stacks Project, Tag 03YP](https://stacks.math.columbia.edu/tag/03YP)
* [Stacks Project, Tag 04TE](https://stacks.math.columbia.edu/tag/04TE)
* [Stacks Project, Tag 04ZU](https://stacks.math.columbia.edu/tag/04ZU)
* [Stacks Project, Tag 050U](https://stacks.math.columbia.edu/tag/050U)
* [Stacks Project, Tag 050X](https://stacks.math.columbia.edu/tag/050X)
* [Stacks Project, Tag 06P1](https://stacks.math.columbia.edu/tag/06P1)
* [Stacks Project, Tag 06QC](https://stacks.math.columbia.edu/tag/06QC)
* [Stacks Project, Tag 06QG](https://stacks.math.columbia.edu/tag/06QG)
* [Stacks Project, Tag 06QH](https://stacks.math.columbia.edu/tag/06QH)
* [Stacks Project, Tag 0CPR](https://stacks.math.columbia.edu/tag/0CPR)
* [Stacks Project, Tag 0CPS](https://stacks.math.columbia.edu/tag/0CPS)
* [Stacks Project, Tag 0DQL](https://stacks.math.columbia.edu/tag/0DQL)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w v₁ v₂ v₃ u₁ u₂ u₃

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The absolute diagonal and the product of two 1-morphisms -/

/-- The absolute diagonal `Δ_𝒳 : 𝒳 ⟶ 𝒳 × 𝒳` of an algebraic stack over `S`, into the product
`AlgebraicGeometry.Stack.AlgebraicStacks.product`: it sends an object `x` to the pair `(x, x)`
with the identity identification of the two images. -/
def diagonal (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS) : 𝒳 ⟶ product B S hS 𝒳 𝒳 :=
  Bicategory.InducedBicategory.mkHom (Stack.diagonal.{u, u, u + 1} B S hS 𝒳.val)

/-- The product `f₁ × f₂ : 𝒳₁ × 𝒳₂ ⟶ 𝒴₁ × 𝒴₂` of two 1-morphisms of algebraic stacks over `S`:
on an object `(x₁, x₂)` it is `(f₁ x₁, f₂ x₂)`. -/
def productMap {𝒳₁ 𝒳₂ 𝒴₁ 𝒴₂ : Stack.AlgebraicStacks.{u, w} B S hS}
    (f₁ : 𝒳₁ ⟶ 𝒴₁) (f₂ : 𝒳₂ ⟶ 𝒴₂) :
    product B S hS 𝒳₁ 𝒳₂ ⟶ product B S hS 𝒴₁ 𝒴₂ :=
  Bicategory.InducedBicategory.mkHom (CatFiberedInGroupoids.productMap f₁.hom f₂.hom)

variable {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS}

/-- The comparison `c : 𝒳 ×_𝒴 𝒳 ⟶ 𝒳 × 𝒳` from the 2-fibre product of `f : 𝒳 ⟶ 𝒴` with itself to
the product: it forgets the identification of the two images in `𝒴` and keeps the one forced over
the base site. -/
noncomputable def diagonalComparison (f : 𝒳 ⟶ 𝒴) :
    twoFibreProduct B S hS f f ⟶ product B S hS 𝒳 𝒳 :=
  Bicategory.InducedBicategory.mkHom
    (Stack.relativeDiagonalSquare.{u, u, u} B S hS 𝒳.val 𝒳.val 𝒴.val f.hom f.hom).fst

/-- The relative diagonal of `f` followed by the comparison is the absolute diagonal of `𝒳`. -/
theorem relativeDiagonal_comp_diagonalComparison (f : 𝒳 ⟶ 𝒴) :
    relativeDiagonal B S hS f ≫ diagonalComparison B S hS f = diagonal B S hS 𝒳 :=
  rfl

/-- The 2-commutative square whose apex is `𝒳 ×_𝒴 𝒳`, whose legs are the comparison
`c : 𝒳 ×_𝒴 𝒳 ⟶ 𝒳 × 𝒳` and the second projection followed by `f`, over the cospan
`(f × f, Δ_𝒴)`. -/
noncomputable def diagonalComparisonSquare (f : 𝒳 ⟶ 𝒴) :
    Bicategory.TwoCommSq (productMap B S hS f f) (diagonal B S hS 𝒴) where
  pt := twoFibreProduct B S hS f f
  fst := diagonalComparison B S hS f
  snd := Bicategory.InducedBicategory.mkHom
    (Stack.relativeDiagonalSquare.{u, u, u} B S hS 𝒳.val 𝒳.val 𝒴.val f.hom f.hom).snd
  iso := Bicategory.InducedBicategory.isoMk
    (Stack.relativeDiagonalSquare.{u, u, u} B S hS 𝒳.val 𝒳.val 𝒴.val f.hom f.hom).iso

/-- `𝒳 ×_𝒴 𝒳` is a 2-fibre product of `f × f` and `Δ_𝒴` in the 2-category of algebraic stacks,
by the square `AlgebraicGeometry.Stack.AlgebraicStacks.diagonalComparisonSquare`. -/
noncomputable def isTwoFibreProduct_diagonalComparisonSquare (f : 𝒳 ⟶ 𝒴) :
    Bicategory.IsTwoFibreProduct (diagonalComparisonSquare B S hS f) :=
  Bicategory.isTwoFibreProduct_of_underlying
    (Stack.isTwoFibreProduct_relativeDiagonalSquare.{u, u, u} B S hS 𝒳.val 𝒳.val 𝒴.val
      f.hom f.hom)

/-! ### Surjectivity of the relative diagonal of a gerbe -/

/-- A morphism of the 2-fibre product `𝒳 ×_𝒮 𝒳` out of the image of the diagonal, from two
morphisms of `𝒳` lying over one morphism of the base whose images in `𝒮` are compatible with the
comparison isomorphism of the target. -/
private def diagonalHomMk {C : Type u₁} [Category.{v₁} C] {X : Type u₂} [Category.{v₂} X]
    {Y : Type u₃} [Category.{v₃} Y] {pX : X ⥤ C} {pY : Y ⥤ C} {F : X ⥤ Y}
    (hF : F ⋙ pY = pX)
    {Q : TwoFibreProductOver pX pX pY F F} {x₁ x₂ : X} {R T : C} (g : R ⟶ T)
    (ξ : x₁ ⟶ Q.x) (ξ' : x₂ ⟶ Q.y) (a : x₁ ⟶ x₂)
    (hξ : pX.IsHomLift g ξ) (hb : pX.IsHomLift g (a ≫ ξ'))
    (hsq : F.map a ≫ F.map ξ' = F.map ξ ≫ Q.iso.hom) :
    (TwoFibreProductOver.diagonal hF).obj x₁ ⟶ Q := by
  have := hξ
  have := hb
  refine TwoFibreProductOver.Hom.mk' ξ (a ≫ ξ') ?_ ?_
  · change eqToHom rfl ≫ pX.map (a ≫ ξ') ≫ eqToHom Q.hy
      = eqToHom rfl ≫ pX.map ξ ≫ eqToHom Q.hx
    rw [IsHomLift.fac' pX g ξ, IsHomLift.fac' pX g (a ≫ ξ')]
    simp
  · change F.map ξ ≫ Q.iso.hom = (Iso.refl (F.obj x₁)).hom ≫ F.map (a ≫ ξ')
    simpa using hsq.symm

/-- The morphism of `AlgebraicGeometry.Stack.AlgebraicStacks.diagonalHomMk` lies over the given
morphism of the base. -/
private theorem isHomLift_diagonalHomMk {C : Type u₁} [Category.{v₁} C] {X : Type u₂}
    [Category.{v₂} X] {Y : Type u₃} [Category.{v₃} Y] {pX : X ⥤ C} {pY : Y ⥤ C} {F : X ⥤ Y}
    (hF : F ⋙ pY = pX)
    {Q : TwoFibreProductOver pX pX pY F F} {x₁ x₂ : X} {R T : C} (g : R ⟶ T)
    (ξ : x₁ ⟶ Q.x) (ξ' : x₂ ⟶ Q.y) (a : x₁ ⟶ x₂)
    (hξ : pX.IsHomLift g ξ) (hb : pX.IsHomLift g (a ≫ ξ'))
    (hsq : F.map a ≫ F.map ξ' = F.map ξ ≫ Q.iso.hom) :
    (TwoFibreProductOver.structureFunctor pX pX pY F F).IsHomLift g
      (diagonalHomMk hF g ξ ξ' a hξ hb hsq) :=
  TwoFibreProductOver.structureFunctor_isHomLift _ g hξ

/-- The relative diagonal of a gerbe 1-morphism of algebraic stacks over `S` is surjective, at
the canonical `AlgebraicGeometry.Stack.AlgebraicStacks.twoFibreProduct` model. The same
statement at the `twoFibreProductAlgebraicStack` model is Stacks 0CPR part (2),
`AlgebraicGeometry.Stack.AlgebraicStacks.isSurjective_relativeDiagonal_of_isGerbeOver`. -/
theorem isSurjective_relativeDiagonal_twoFibreProduct_of_isGerbeOver (f : 𝒳 ⟶ 𝒴)
    (hf : IsGerbeOver B S hS f) :
    Stack.IsSurjective B S hS (relativeDiagonal B S hS f) := by
  refine Stack.pointsMap_surjective_of_isSurjectiveOnObjects B S hS
    (relativeDiagonal B S hS f) ?_
  intro U hU Q hQ
  have hQb : Q.base = U := hQ
  have hvert : 𝒴.val.val.p.IsHomLift (𝟙 U) Q.iso.hom := hQb ▸ Q.vertical
  obtain ⟨R, hR, hcov⟩ := hf.locally_full (U := U) Q.iso.hom hvert
  obtain ⟨V, g, hV, hgR⟩ := Stack.exists_isFieldObject_arrow_of_mem_topology B S hS hU hR
  obtain ⟨x₁, x₂, ξ, ξ', a, hξ, hξ', ha, hsq⟩ := hcov g hgR
  rw [CatFiberedInGroupoids.homFunctor_comp_p f.hom] at hξ hξ' ha
  have hbp : 𝒳.val.val.p.IsHomLift g (a ≫ ξ') := by
    simpa using IsHomLift.comp 𝒳.val.val.p (𝟙 V) g a ξ'
  exact ⟨V, hV, g, x₁, IsHomLift.domain_eq 𝒳.val.val.p g ξ,
    diagonalHomMk f.hom.hom.w g ξ ξ' a hξ hbp hsq,
    isHomLift_diagonalHomMk f.hom.hom.w g ξ ξ' a hξ hbp hsq⟩

/-! ### The 1-morphisms named by objects of the fibres -/

/-- The object of the fibre of `𝒴` over an object `A` of the big fppf site of `S` that a
1-morphism out of the algebraic stack of `A` evaluates to under the 2-Yoneda lemma
(**Stacks 004B**). -/
noncomputable def stackMapFibreObject (A : BigFppfOver B S hS)
    (g : Stack.schemeStack.{u, w} B S hS A ⟶ 𝒴) :
    𝒴.val.val.p.Fiber A :=
  (Functor.twoYonedaEvaluation 𝒴.val.val.p A).obj g.hom.hom

/-- A 1-morphism out of the algebraic stack of an object `A` of the site is 2-isomorphic to the
1-morphism named by the object of the fibre it evaluates to. -/
noncomputable def fibreObjectStackMapEvaluationIso (A : BigFppfOver B S hS)
    (g : Stack.schemeStack.{u, w} B S hS A ⟶ 𝒴) :
    Stack.fibreObjectStackMap B S hS 𝒴 A (stackMapFibreObject B S hS A g) ≅ g := by
  have hfull := Functor.twoYonedaEvaluation_full 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids A
  have hfaith := Functor.twoYonedaEvaluation_faithful 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids A
  exact Bicategory.InducedBicategory.isoMk (Bicategory.InducedBicategory.isoMk
    ((Functor.FullyFaithful.ofFullyFaithful
        (Functor.twoYonedaEvaluation 𝒴.val.val.p A)).preimageIso
      (Functor.TwoYoneda.liftBasedEvaluationIso 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids A
        (stackMapFibreObject B S hS A g))))

/-- A morphism of `𝒴` from the `f`-image of an object of `𝒳` over `V` to an object over `A`,
lying over `v : V ⟶ A`, factors the 1-morphism named by the first through `v` and the 1-morphism
named by the second. -/
noncomputable def fibreObjectStackMapFactorIso (f : 𝒳 ⟶ 𝒴) {A V : BigFppfOver B S hS}
    (v : V ⟶ A) (x : 𝒳.val.val.p.Fiber V) (y : 𝒴.val.val.p.Fiber A)
    (ψ : (CatFiberedInGroupoids.homFunctor f.hom).obj x.1 ⟶ y.1)
    (hψ : 𝒴.val.val.p.IsHomLift v ψ) :
    Stack.fibreObjectStackMap B S hS 𝒳 V x ≫ f ≅
      Stack.schemeStackMap B S hS v ≫ Stack.fibreObjectStackMap B S hS 𝒴 A y := by
  have hw : CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p = 𝒳.val.val.p := f.hom.hom.w
  let ex := Functor.TwoYoneda.liftBasedEvaluationIso 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids V x
  let ey := Functor.TwoYoneda.liftBasedEvaluationIso 𝒴.val.val.p
    𝒴.val.isFiberedInGroupoids A y
  have i1 : 𝒴.val.val.p.IsHomLift (𝟙 V)
      ((CatFiberedInGroupoids.homFunctor f.hom).map
        (Functor.Fiber.fiberInclusion.map ex.hom)) :=
    PresheafOfCategories.isHomLift_map_of_comp hw (𝟙 V) _ inferInstance
  have i0 : 𝒴.val.val.p.IsHomLift (𝟙 A) (Functor.Fiber.fiberInclusion.map ey.inv) :=
    ey.inv.2
  have i2 : 𝒴.val.val.p.IsHomLift v (ψ ≫ Functor.Fiber.fiberInclusion.map ey.inv) :=
    @IsHomLift.comp_lift_id_right' _ _ _ _ 𝒴.val.val.p _ _ _ _ _ v ψ hψ A
      (Functor.Fiber.fiberInclusion.map ey.inv) i0
  have hm : 𝒴.val.val.p.IsHomLift v
      ((CatFiberedInGroupoids.homFunctor f.hom).map
          (Functor.Fiber.fiberInclusion.map ex.hom) ≫
        ψ ≫ Functor.Fiber.fiberInclusion.map ey.inv) :=
    @IsHomLift.comp_lift_id_left' _ _ _ _ 𝒴.val.val.p _ _ _ V
      ((CatFiberedInGroupoids.homFunctor f.hom).map
        (Functor.Fiber.fiberInclusion.map ex.hom)) i1 _ _ v
      (ψ ≫ Functor.Fiber.fiberInclusion.map ey.inv) i2
  have hfull := Functor.twoYonedaEvaluation_full 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids V
  have hfaith := Functor.twoYonedaEvaluation_faithful 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids V
  let mm := Functor.TwoYoneda.unitHomOverBase 𝒴.val.val.p v 𝒴.val.isFiberedInGroupoids
    (G := (Stack.fibreObjectStackMap B S hS 𝒳 V x ≫ f).hom.hom)
    (H := Functor.TwoYoneda.liftBased 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids A y)
    ((CatFiberedInGroupoids.homFunctor f.hom).map
        (Functor.Fiber.fiberInclusion.map ex.hom) ≫
      ψ ≫ Functor.Fiber.fiberInclusion.map ey.inv) hm
  have hmm : 𝒴.val.val.p.IsHomLift (𝟙 V) mm :=
    Functor.TwoYoneda.isHomLift_unitHomOverBase 𝒴.val.val.p v
      𝒴.val.isFiberedInGroupoids _ hm
  let e : (Functor.twoYonedaEvaluation 𝒴.val.val.p V).obj
        (Stack.fibreObjectStackMap B S hS 𝒳 V x ≫ f).hom.hom ≅
      (Functor.twoYonedaEvaluation 𝒴.val.val.p V).obj
        (Stack.schemeStackMap B S hS v ≫
          Stack.fibreObjectStackMap B S hS 𝒴 A y).hom.hom :=
    Stack.fiberIsoOfHomLift B S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids V mm hmm
  exact Bicategory.InducedBicategory.isoMk (Bicategory.InducedBicategory.isoMk
    ((Functor.FullyFaithful.ofFullyFaithful
      (Functor.twoYonedaEvaluation 𝒴.val.val.p V)).preimageIso e))

/-- A 1-morphism to a product is the pair of its two components: if `ℓ₁ ≫ f` and `ℓ₂ ≫ f`
are 2-isomorphic to the two projections of `g : 𝒲 ⟶ 𝒴 × 𝒴`, then `(ℓ₁, ℓ₂)` followed by `f × f`
is 2-isomorphic to `g`. -/
noncomputable def pairProductMapIso {𝒲 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (ℓ₁ ℓ₂ : 𝒲 ⟶ 𝒳) (g : 𝒲 ⟶ product B S hS 𝒴 𝒴)
    (θ₁ : ℓ₁ ≫ f ≅ g ≫ (productSquare B S hS 𝒴 𝒴).fst)
    (θ₂ : ℓ₂ ≫ f ≅ g ≫ (productSquare B S hS 𝒴 𝒴).snd) :
    (diagonal B S hS 𝒲 ≫ productMap B S hS ℓ₁ ℓ₂) ≫ productMap B S hS f f ≅ g :=
  Bicategory.InducedBicategory.isoMk (Bicategory.InducedBicategory.isoMk
    (CatFiberedInGroupoids.productNatIso _ _
      (CatFiberedInGroupoids.underlyingIso (Bicategory.InducedBicategory.isoHom θ₁))
      (CatFiberedInGroupoids.underlyingIso (Bicategory.InducedBicategory.isoHom θ₂))
      (fun x => (Bicategory.InducedBicategory.isoHom θ₁).hom.hom.isHomLift' x)
      (fun x => (Bicategory.InducedBicategory.isoHom θ₂).hom.hom.isHomLift' x)))

/-- A lift `ψ` over `v : V ⟶ A` of the object of the fibre named by `u ≫ π`, from the `f`-image of
an object `x` of `𝒳`, yields an object of the fibre over `V` whose named 1-morphism followed by `f`
is 2-isomorphic to `(schemeStackMap v ≫ u) ≫ π`. -/
private theorem exists_fibreObjectStackMap_comp_iso {𝒲 : Stack.AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) {A V : BigFppfOver B S hS} (v : V ⟶ A)
    (u : Stack.schemeStack.{u, w} B S hS A ⟶ 𝒲) (π : 𝒲 ⟶ 𝒴) {x}
    (ψ : (CatFiberedInGroupoids.homFunctor f.hom).obj x ⟶
      (stackMapFibreObject B S hS A (u ≫ π)).1)
    (hψ : 𝒴.val.val.p.IsHomLift v ψ) :
    ∃ y : 𝒳.val.val.p.Fiber V, Nonempty (Stack.fibreObjectStackMap B S hS 𝒳 V y ≫ f ≅
      (Stack.schemeStackMap B S hS v ≫ u) ≫ π) :=
  ⟨⟨x, (BasedFunctor.w_obj f.hom.hom x).symm.trans (IsHomLift.domain_eq 𝒴.val.val.p v ψ)⟩,
    ⟨fibreObjectStackMapFactorIso B S hS f v _ _ ψ hψ ≪≫
      Bicategory.whiskerLeftIso (Stack.schemeStackMap B S hS v)
        (fibreObjectStackMapEvaluationIso B S hS A (u ≫ π)) ≪≫
      (Bicategory.associator _ _ _).symm⟩⟩

/-! ### `𝟙 × f` is a base change of `f` -/

variable (𝒵 : Stack.AlgebraicStacks.{u, w} B S hS)

/-- The 2-isomorphism identifying `f` followed by the structure 1-morphism of `𝒴` to the final
object of the 2-category with the structure 1-morphism of `𝒳`: the identification of the two
structure functors that `f` carries, which is vertical because it is an `eqToHom` of the base. -/
noncomputable def toTerminalStackCompIso (f : 𝒳 ⟶ 𝒴) :
    f ≫ toTerminalStack B S hS 𝒴 ≅ toTerminalStack B S hS 𝒳 :=
  Bicategory.InducedBicategory.isoMk (Bicategory.InducedBicategory.isoMk
    (BasedNatIso.mkNatIso (eqToIso f.hom.hom.w) (Stack.isHomLift_eqToIso_hom_app B S hS f.hom)))

/-- The square exhibiting `𝟙_𝒵 × f : 𝒵 × 𝒳 ⟶ 𝒵 × 𝒴` over the cospan given by the second
projection of `𝒵 × 𝒴` and by `f`: its second leg is the second projection of `𝒵 × 𝒳`, and its
filler is the identity because the product of 1-morphisms commutes with the second projection on
the nose. -/
noncomputable def productMapIdLeftSquare (f : 𝒳 ⟶ 𝒴) :
    Bicategory.TwoCommSq (productSquare B S hS 𝒵 𝒴).snd f where
  pt := product B S hS 𝒵 𝒳
  fst := productMap B S hS (𝟙 𝒵) f
  snd := (productSquare B S hS 𝒵 𝒳).snd
  iso := Iso.refl _

/-- Stacks 02XD at the final object of the 2-category: the iterated 2-fibre product
`(𝒵 × 𝒴) ×_{pr₂, 𝒴, f} 𝒳`, read as a square over the cospan of structure 1-morphisms of `𝒵` and
`𝒳` to the final object. -/
noncomputable def productCancelSquare (f : 𝒳 ⟶ 𝒴) :
    Bicategory.TwoCommSq (toTerminalStack B S hS 𝒵) (toTerminalStack B S hS 𝒳) :=
  Stack.cancelSndSquareAlgebraicStacks B S hS (toTerminalStack B S hS 𝒵)
    (toTerminalStack B S hS 𝒴) f (toTerminalStack B S hS 𝒳)
    (toTerminalStackCompIso B S hS f)

/-- The comparison of `AlgebraicGeometry.Stack.AlgebraicStacks.productCancelSquare` with the
canonical 2-fibre product square of the same cospan, whose apex is `𝒵 × 𝒳`. -/
noncomputable def productCancelPreHom (f : 𝒳 ⟶ 𝒴) :
    Bicategory.TwoCommSq.PreHom (productCancelSquare B S hS 𝒵 f)
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS (toTerminalStack B S hS 𝒵)
        (toTerminalStack B S hS 𝒳)) :=
  Stack.canonicalPreHomAlgebraicStacks B S hS _ _ (productCancelSquare B S hS 𝒵 f)

/-- The comparison of `AlgebraicGeometry.Stack.AlgebraicStacks.productCancelPreHom` is an
equivalence of the underlying categories, both squares being 2-fibre products of one cospan. -/
theorem isEquivalence_productCancelPreHom (f : 𝒳 ⟶ 𝒴) :
    (productCancelPreHom B S hS 𝒵 f).hom.hom.hom.toFunctor.IsEquivalence :=
  Stack.isEquivalence_of_isTwoFibreProduct_algebraicStacks B S hS
    (Stack.isTwoFibreProduct_cancelSndSquareAlgebraicStacks B S hS _ _ f _
      (toTerminalStackCompIso B S hS f))
    (Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS _ _)
    (productCancelPreHom B S hS 𝒵 f)

/-- The first comparison 2-cell of
`AlgebraicGeometry.Stack.AlgebraicStacks.productMapIdLeftPreHom`: the projection of the iterated
2-fibre product to `𝒵 × 𝒴` agrees with the comparison followed by `𝟙_𝒵 × f` on the first
projection on the nose, and on the second projection through the filler of the canonical
square. -/
noncomputable def productMapIdLeftIsoFst (f : 𝒳 ⟶ 𝒴) :
    (Stack.twoFibreProductSquareAlgebraicStacks B S hS
        (productSquare B S hS 𝒵 𝒴).snd f).fst ≅
      (productCancelPreHom B S hS 𝒵 f).hom ≫ (productMapIdLeftSquare B S hS 𝒵 f).fst :=
  Bicategory.InducedBicategory.isoMk (Bicategory.InducedBicategory.isoMk
    (CatFiberedInGroupoids.productNatIso (𝒳 := 𝒵.val) (𝒴 := 𝒴.val)
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS
        (productSquare B S hS 𝒵 𝒴).snd f).fst.hom.hom
      ((productCancelPreHom B S hS 𝒵 f).hom ≫
        (productMapIdLeftSquare B S hS 𝒵 f).fst).hom.hom
      (Iso.refl _)
      (CatFiberedInGroupoids.underlyingIso (Bicategory.InducedBicategory.isoHom
        (Stack.twoFibreProductSquareAlgebraicStacks B S hS
          (productSquare B S hS 𝒵 𝒴).snd f).iso))
      (fun x => IsHomLift.id (BasedFunctor.w_obj
        (BasedFunctor.comp (Stack.twoFibreProductSquareAlgebraicStacks B S hS
            (productSquare B S hS 𝒵 𝒴).snd f).fst.hom.hom
          ⟨TwoFibreProductOver.fst 𝒵.val.val.p 𝒴.val.val.p
            (𝟭 (BigFppfOver B S hS)) 𝒵.val.val.p 𝒴.val.val.p,
            TwoFibreProductOver.fst_comp_eq⟩) x))
      (fun x => (Bicategory.InducedBicategory.isoHom
        (Stack.twoFibreProductSquareAlgebraicStacks B S hS
          (productSquare B S hS 𝒵 𝒴).snd f).iso).hom.hom.isHomLift' x)))

/-- The comparison of the canonical 2-fibre product square of the cospan `(pr₂, f)` with
`AlgebraicGeometry.Stack.AlgebraicStacks.productMapIdLeftSquare`. -/
noncomputable def productMapIdLeftPreHom (f : 𝒳 ⟶ 𝒴) :
    Bicategory.TwoCommSq.PreHom
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS
        (productSquare B S hS 𝒵 𝒴).snd f)
      (productMapIdLeftSquare B S hS 𝒵 f) where
  hom := (productCancelPreHom B S hS 𝒵 f).hom
  isoFst := productMapIdLeftIsoFst B S hS 𝒵 f
  isoSnd := Iso.refl _
  compat := by
    apply Bicategory.InducedBicategory.hom₂_ext
    apply Bicategory.InducedBicategory.hom₂_ext
    apply BasedNatTrans.ext
    apply NatTrans.ext
    funext x
    change (Stack.twoFibreProductSquareAlgebraicStacks B S hS
          (productSquare B S hS 𝒵 𝒴).snd f).iso.hom.hom.hom.app x ≫
        f.hom.hom.toFunctor.map (𝟙 _) ≫ 𝟙 _ =
      ((productMapIdLeftIsoFst B S hS 𝒵 f).hom.hom.hom.app x).b ≫ 𝟙 _ ≫ 𝟙 _
    rw [f.hom.hom.toFunctor.map_id]
    rfl

/-- `𝟙_𝒵 × f` is a base change of `f`: the square
`AlgebraicGeometry.Stack.AlgebraicStacks.productMapIdLeftSquare` is a 2-fibre product of the
cospan given by the second projection of `𝒵 × 𝒴` and by `f`. -/
noncomputable def isTwoFibreProduct_productMapIdLeftSquare (f : 𝒳 ⟶ 𝒴) :
    Bicategory.IsTwoFibreProduct (productMapIdLeftSquare B S hS 𝒵 f) :=
  Bicategory.isTwoFibreProduct_of_underlying
    (Bicategory.isTwoFibreProduct_of_isEquivalence_from
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
        (productSquare B S hS 𝒵 𝒴).snd.hom f.hom)
      (Bicategory.TwoCommSq.PreHom.underlying (productMapIdLeftPreHom B S hS 𝒵 f))
      (isEquivalence_productCancelPreHom B S hS 𝒵 f))

/-- The product of an identity with a surjective 1-morphism is surjective. -/
theorem isSurjective_productMap_id_left (f : 𝒳 ⟶ 𝒴) (hf : Stack.IsSurjective B S hS f) :
    Stack.IsSurjective B S hS (productMap B S hS (𝟙 𝒵) f) :=
  Stack.isSurjective_of_isTwoFibreProduct B S hS (productMapIdLeftSquare B S hS 𝒵 f).swap
    (Bicategory.isTwoFibreProduct_swap (isTwoFibreProduct_productMapIdLeftSquare B S hS 𝒵 f)) hf

/-- The product of an identity with a flat 1-morphism is flat. -/
theorem isFlat_productMap_id_left (f : 𝒳 ⟶ 𝒴) (hf : IsFlat B S hS f) :
    IsFlat B S hS (productMap B S hS (𝟙 𝒵) f) :=
  isFlat_baseChange B S hS f _ (productMapIdLeftSquare B S hS 𝒵 f)
    (isTwoFibreProduct_productMapIdLeftSquare B S hS 𝒵 f) hf

/-- The product of an identity with a locally finitely presented 1-morphism is locally of finite
presentation. -/
theorem isLocallyOfFinitePresentation_productMap_id_left (f : 𝒳 ⟶ 𝒴)
    (hf : IsLocallyOfFinitePresentation B S hS f) :
    IsLocallyOfFinitePresentation B S hS (productMap B S hS (𝟙 𝒵) f) :=
  isLocallyOfFinitePresentation_baseChange B S hS f _ (productMapIdLeftSquare B S hS 𝒵 f)
    (isTwoFibreProduct_productMapIdLeftSquare B S hS 𝒵 f) hf

/-! ### The diagonal of a stack having a gerbe over it -/

/-- Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S` which makes `𝒳` a gerbe over
`𝒴`. If the diagonal of `𝒳` is quasi-compact, then so is the diagonal of `𝒴`. -/
@[stacks 0DQL]
theorem isQuasiCompactMorphism_diagonal_of_isGerbeOver (f : 𝒳 ⟶ 𝒴)
    (hf : IsGerbeOver B S hS f)
    (hΔ : Stack.IsQuasiCompactMorphism B S hS (diagonal B S hS 𝒳)) :
    Stack.IsQuasiCompactMorphism B S hS (diagonal B S hS 𝒴) := by
  classical
  have hc : Stack.IsQuasiCompactMorphism B S hS (diagonalComparison B S hS f) :=
    Stack.isQuasiCompactMorphism_of_comp_of_isSurjective B S hS
      (relativeDiagonal B S hS f) (diagonal B S hS 𝒳) (diagonalComparison B S hS f)
      (eqToIso (relativeDiagonal_comp_diagonalComparison B S hS f))
      (isSurjective_relativeDiagonal_twoFibreProduct_of_isGerbeOver B S hS f hf) hΔ
  intro 𝒯 q h𝒯
  obtain ⟨A, α, hAaff, hαsurj⟩ :=
    Stack.exists_affine_isSurjective_of_isQuasiCompactStack B S hS 𝒯 h𝒯
  refine Stack.isQuasiCompactStack_twoFibreProduct_of_finite_cover B S hS q
    (diagonal B S hS 𝒴) (𝒱 := fun _ : Unit => Stack.schemeStack.{u, w} B S hS A)
    (fun _ => α) (fun z => ⟨(), hαsurj z⟩) ?_
  intro _
  set u := α ≫ q with hu
  obtain ⟨R₁, hR₁, hcov₁⟩ := hf.locally_essSurj
    (stackMapFibreObject B S hS A (u ≫ (productSquare B S hS 𝒴 𝒴).fst)).1
    (stackMapFibreObject B S hS A (u ≫ (productSquare B S hS 𝒴 𝒴).fst)).2
  obtain ⟨R₂, hR₂, hcov₂⟩ := hf.locally_essSurj
    (stackMapFibreObject B S hS A (u ≫ (productSquare B S hS 𝒴 𝒴).snd)).1
    (stackMapFibreObject B S hS A (u ≫ (productSquare B S hS 𝒴 𝒴).snd)).2
  obtain ⟨I, hI, V, v, hVaff, hVR, hVcov⟩ :=
    Stack.exists_finite_affine_family_of_mem_topology B S hS hAaff
      ((BigFppfOver.topology B S hS).intersection_covering hR₁ hR₂)
  refine Stack.isQuasiCompactStack_twoFibreProduct_of_finite_cover B S hS u
    (diagonal B S hS 𝒴) (𝒱 := fun i => Stack.schemeStack.{u, w} B S hS (V i))
    (fun i => Stack.schemeStackMap.{u, w} B S hS (v i))
    (Stack.exists_mem_range_pointsMap_schemeStackMap.{u, w, u} B S hS V v hVcov) ?_
  intro i
  obtain ⟨x₁, ψ₁, hψ₁⟩ := hcov₁ (v i) (hVR i).1
  obtain ⟨x₂, ψ₂, hψ₂⟩ := hcov₂ (v i) (hVR i).2
  obtain ⟨y₁, ⟨θ₁⟩⟩ := exists_fibreObjectStackMap_comp_iso B S hS f (v i) u
    (productSquare B S hS 𝒴 𝒴).fst ψ₁ hψ₁
  obtain ⟨y₂, ⟨θ₂⟩⟩ := exists_fibreObjectStackMap_comp_iso B S hS f (v i) u
    (productSquare B S hS 𝒴 𝒴).snd ψ₂ hψ₂
  have ι := pairProductMapIso B S hS f (Stack.fibreObjectStackMap B S hS 𝒳 (V i) y₁)
    (Stack.fibreObjectStackMap B S hS 𝒳 (V i) y₂)
    (Stack.schemeStackMap B S hS (v i) ≫ u) θ₁ θ₂
  have h𝒱 : Stack.IsQuasiCompactStack.{u, w} B S hS
      (Stack.schemeStack.{u, w} B S hS (V i)).val
      (Stack.schemeStack.{u, w} B S hS (V i)).property :=
    Stack.isQuasiCompactStack_schemeStack_of_isAffine.{u, w} B S hS (V i) (hVaff i)
  set ℓ := diagonal B S hS (Stack.schemeStack.{u, w} B S hS (V i)) ≫
    productMap B S hS (Stack.fibreObjectStackMap B S hS 𝒳 (V i) y₁)
      (Stack.fibreObjectStackMap B S hS 𝒳 (V i) y₂)
  have hqc1 := Stack.isQuasiCompactStack_of_isTwoFibreProduct B S hS
    (Bicategory.isTwoFibreProduct_swap
      (Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS ℓ
        (diagonalComparison B S hS f)))
    (Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS
      (diagonalComparison B S hS f) ℓ) (hc _ ℓ h𝒱)
  exact Stack.isQuasiCompactStack_of_isTwoFibreProduct B S hS
    (Bicategory.isTwoFibreProduct_swap
      (Bicategory.isTwoFibreProduct_reindexSnd ι
        (Bicategory.isTwoFibreProduct_paste
          (Bicategory.isTwoFibreProduct_swap
            (isTwoFibreProduct_diagonalComparisonSquare B S hS f))
          (Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS
            (diagonalComparison B S hS f) ℓ))))
    (Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS
      (Stack.schemeStackMap B S hS (v i) ≫ u) (diagonal B S hS 𝒴)) hqc1

end AlgebraicGeometry.Stack.AlgebraicStacks

end
