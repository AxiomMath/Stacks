module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.ObjectMorphismFactor
public import StacksFrontier.CategoryTheory.FiberedCategory.PresheafElementsEquivalence
public import StacksFrontier.CategoryTheory.TwoYoneda.OverBase
public import StacksFrontier.CategoryTheory.TwoYoneda.RepresentedPoint

/-!
# The 1-morphism named by an object of a fibre, and the 2-Yoneda comparisons

Let `𝒴` be a category fibred in groupoids over the big fppf site of a scheme `S` in `B`. The
2-Yoneda lemma (**Stacks 004B**) identifies the objects of the fibre of `𝒴` over an object `U` of
the site with the 1-morphisms `(Sch/U)_{fppf} ⟶ 𝒴`. This file records that identification as a
pair of mutually inverse constructions on 1-morphisms of the 2-category
`CategoryTheory.CatFiberedInGroupoids` of **Stacks 02XS**, together with the two comparisons that
make it functorial:

* the 1-morphism named by an object of a fibre, and the object a 1-morphism out of a represented
  category evaluates to;
* the 2-isomorphism exhibiting a 1-morphism out of a represented category as the one named by the
  object it evaluates to, which is essential surjectivity of 2-Yoneda evaluation;
* the factorisation, across a 1-morphism `f : 𝒳 ⟶ 𝒴` and over an arrow `v : V ⟶ A` of the site,
  of the 1-morphism named by an object of `𝒳` over `V` through `v` and the 1-morphism named by an
  object of `𝒴` over `A`.

## Main definitions

* `AlgebraicGeometry.Stack.fibreObjectFibredMap`: the 1-morphism named by an object of a fibre.
* `AlgebraicGeometry.Stack.stackMapFibreObject`: the object of the fibre of `𝒴` over `A` that a
  1-morphism out of the represented category of `A` evaluates to.

## Main results

* `AlgebraicGeometry.Stack.fibreObjectStackMapEvaluationIso`: a 1-morphism out of the represented
  category of `A` is the 1-morphism named by the object of the fibre it evaluates to.
* `AlgebraicGeometry.Stack.fibreObjectStackMapFactorIso`: a morphism of `𝒴` from the `f`-image of
  an object over `V` to an object over `A`, lying over `v : V ⟶ A`, factors the 1-morphism named
  by the first through `v` and the 1-morphism named by the second.

## Implementation notes

Nothing here asks the source or the target to be an algebraic stack: the 2-Yoneda lemma needs
only that the structure functor is fibred in groupoids, which is clause (1) of **Stacks 02XS**.
That is what lets these four declarations be applied to a category fibred in groupoids whose
algebraicity is what is being proved, as in the proof of **Stacks 06DC**, where the charts of a
family are glued into a scheme-valued point of the target before the target is known to be an
algebraic stack.

A 1-morphism of `CategoryTheory.CatFiberedInGroupoids` is a
`CategoryTheory.BasedFunctor` wrapped by `CategoryTheory.Bicategory.InducedBicategory.mkHom`, and
a 2-isomorphism is a `CategoryTheory.BasedNatIso` wrapped by
`CategoryTheory.Bicategory.InducedBicategory.isoMk`; since `CategoryTheory.CatFiberedInGroupoids`
is a *full* sub-2-category of `CategoryTheory.BasedCategory`, no condition has to be checked in
either direction. Read in the 2-category `AlgebraicGeometry.Stack.AlgebraicStacks` of
**Stacks 03YP**, which is in turn a full sub-2-category of this one, each of these declarations
acquires one further `mkHom` or `isoMk`.

## References

* [Stacks Project, Tag 004B](https://stacks.math.columbia.edu/tag/004B)
* [Stacks Project, Tag 02XS](https://stacks.math.columbia.edu/tag/02XS)
* [Stacks Project, Tag 03YP](https://stacks.math.columbia.edu/tag/03YP)
* [Stacks Project, Tag 06DC](https://stacks.math.columbia.edu/tag/06DC)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The 1-morphism named by an object of a fibre.** An object `y` of the fibre of a category
`𝒴` fibred in groupoids over the big fppf site of `S`, over an object `U` of that site, is by the
2-Yoneda lemma (**Stacks 004B**) the same thing as a 1-morphism from the represented category of
`U` to `𝒴`; this is that 1-morphism. -/
noncomputable def fibreObjectFibredMap
    (𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (U : BigFppfOver B S hS) (y : 𝒴.val.p.Fiber U) :
    schemeFibredCategory B S hS U ⟶ 𝒴 :=
  Bicategory.InducedBicategory.mkHom
    (Functor.TwoYoneda.liftBased 𝒴.val.p 𝒴.isFiberedInGroupoids U y)

variable {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}

/-- The object of the fibre of `𝒴` over an object `A` of the big fppf site of `S` that a
1-morphism out of the represented category of `A` evaluates to under the 2-Yoneda lemma
(**Stacks 004B**). -/
noncomputable def stackMapFibreObject (A : BigFppfOver B S hS)
    (g : schemeFibredCategory B S hS A ⟶ 𝒴) :
    𝒴.val.p.Fiber A :=
  (Functor.twoYonedaEvaluation 𝒴.val.p A).obj g.hom

/-- **A 1-morphism out of the represented category of an object `A` of the site is the 1-morphism
named by the object of the fibre it evaluates to.** This is essential surjectivity of the
2-Yoneda evaluation functor, read as a 2-isomorphism of 1-morphisms of categories fibred in
groupoids. -/
noncomputable def fibreObjectStackMapEvaluationIso (A : BigFppfOver B S hS)
    (g : schemeFibredCategory B S hS A ⟶ 𝒴) :
    fibreObjectFibredMap B S hS 𝒴 A (stackMapFibreObject B S hS A g) ≅ g := by
  have hfull := Functor.twoYonedaEvaluation_full 𝒴.val.p 𝒴.isFiberedInGroupoids A
  have hfaith := Functor.twoYonedaEvaluation_faithful 𝒴.val.p 𝒴.isFiberedInGroupoids A
  exact Bicategory.InducedBicategory.isoMk
    ((Functor.FullyFaithful.ofFullyFaithful
        (Functor.twoYonedaEvaluation 𝒴.val.p A)).preimageIso
      (Functor.TwoYoneda.liftBasedEvaluationIso 𝒴.val.p 𝒴.isFiberedInGroupoids A
        (stackMapFibreObject B S hS A g)))

/-- **A morphism of `𝒴` from the `f`-image of an object of `𝒳` over `V` to an object over `A`,
lying over `v : V ⟶ A`, factors the 1-morphism named by the first through `v` and the 1-morphism
named by the second.** This is 2-Yoneda over a morphism of the base, across `f`. -/
noncomputable def fibreObjectStackMapFactorIso (f : 𝒳 ⟶ 𝒴) {A V : BigFppfOver B S hS}
    (v : V ⟶ A) (x : 𝒳.val.p.Fiber V) (y : 𝒴.val.p.Fiber A)
    (ψ : (CatFiberedInGroupoids.homFunctor f).obj x.1 ⟶ y.1)
    (hψ : 𝒴.val.p.IsHomLift v ψ) :
    fibreObjectFibredMap B S hS 𝒳 V x ≫ f ≅
      schemeFibredCategoryMap B S hS v ≫ fibreObjectFibredMap B S hS 𝒴 A y := by
  have hw : CatFiberedInGroupoids.homFunctor f ⋙ 𝒴.val.p = 𝒳.val.p := f.hom.w
  let ex := Functor.TwoYoneda.liftBasedEvaluationIso 𝒳.val.p 𝒳.isFiberedInGroupoids V x
  let ey := Functor.TwoYoneda.liftBasedEvaluationIso 𝒴.val.p 𝒴.isFiberedInGroupoids A y
  have i1 : 𝒴.val.p.IsHomLift (𝟙 V)
      ((CatFiberedInGroupoids.homFunctor f).map
        (Functor.Fiber.fiberInclusion.map ex.hom)) :=
    PresheafOfCategories.isHomLift_map_of_comp hw (𝟙 V) _ inferInstance
  have i2 : 𝒴.val.p.IsHomLift v (ψ ≫ Functor.Fiber.fiberInclusion.map ey.inv) :=
    @IsHomLift.comp_lift_id_right' _ _ _ _ 𝒴.val.p _ _ _ _ _ v ψ hψ A
      (Functor.Fiber.fiberInclusion.map ey.inv) ey.inv.2
  have hm : 𝒴.val.p.IsHomLift v
      ((CatFiberedInGroupoids.homFunctor f).map
          (Functor.Fiber.fiberInclusion.map ex.hom) ≫
        ψ ≫ Functor.Fiber.fiberInclusion.map ey.inv) :=
    @IsHomLift.comp_lift_id_left' _ _ _ _ 𝒴.val.p _ _ _ V
      ((CatFiberedInGroupoids.homFunctor f).map
        (Functor.Fiber.fiberInclusion.map ex.hom)) i1 _ _ v
      (ψ ≫ Functor.Fiber.fiberInclusion.map ey.inv) i2
  have hfull := Functor.twoYonedaEvaluation_full 𝒴.val.p 𝒴.isFiberedInGroupoids V
  have hfaith := Functor.twoYonedaEvaluation_faithful 𝒴.val.p 𝒴.isFiberedInGroupoids V
  let mm := Functor.TwoYoneda.unitHomOverBase 𝒴.val.p v 𝒴.isFiberedInGroupoids
    (G := (fibreObjectFibredMap B S hS 𝒳 V x ≫ f).hom)
    (H := Functor.TwoYoneda.liftBased 𝒴.val.p 𝒴.isFiberedInGroupoids A y)
    ((CatFiberedInGroupoids.homFunctor f).map
        (Functor.Fiber.fiberInclusion.map ex.hom) ≫
      ψ ≫ Functor.Fiber.fiberInclusion.map ey.inv) hm
  have hmm : 𝒴.val.p.IsHomLift (𝟙 V) mm :=
    Functor.TwoYoneda.isHomLift_unitHomOverBase 𝒴.val.p v 𝒴.isFiberedInGroupoids _ hm
  let e : (Functor.twoYonedaEvaluation 𝒴.val.p V).obj
        (fibreObjectFibredMap B S hS 𝒳 V x ≫ f).hom ≅
      (Functor.twoYonedaEvaluation 𝒴.val.p V).obj
        (schemeFibredCategoryMap B S hS v ≫
          fibreObjectFibredMap B S hS 𝒴 A y).hom :=
    Stack.fiberIsoOfHomLift B S hS 𝒴.val.p 𝒴.isFiberedInGroupoids V mm hmm
  exact Bicategory.InducedBicategory.isoMk
    ((Functor.FullyFaithful.ofFullyFaithful
      (Functor.twoYonedaEvaluation 𝒴.val.p V)).preimageIso e)

end AlgebraicGeometry.Stack

end
