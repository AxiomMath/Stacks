module

public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackEquivalenceUniverses
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoFibreProductCostructured
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverFunctoriality

/-!
# Base changes along points read as categories of arrows to the point

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of categories fibred in groupoids over the big fppf site of a
scheme `S`, and let `y : (Sch/U) ⟶ 𝒴` be a point of `𝒴` with values in a scheme `U` over `S`, as
in Stacks 06CF. The base change `(Sch/U) ×_{y, 𝒴, f} 𝒳` is equivalent over the site to the
category of arrows `f(x) ⟶ y(U/U)`
(`CategoryTheory.TwoFibreProductOver.TerminalArrow.ofCostructuredArrowFunctor`), so it is an
algebraic stack as soon as some algebraic stack is equivalent to that category of arrows through
an equivalence lying over the site. This is how algebraicity of a 1-morphism is checked against a
moduli description of its fibres, such as the one of Stacks 0D41.

## Main results

* `AlgebraicGeometry.Stack.isAlgebraicStack_twoFibreProduct_of_costructuredArrow`: the base change
  is an algebraic stack if a category over the site equivalent to the arrows to the point is.

## References

* [Stacks Project, Tag 06CF](https://stacks.math.columbia.edu/tag/06CF)
* [Stacks Project, Tag 03YQ](https://stacks.math.columbia.edu/tag/03YQ)
* [Stacks Project, Tag 0041](https://stacks.math.columbia.edu/tag/0041)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w vX uX vY uY vD uD

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The base change of a 1-morphism along a point is an algebraic stack if the arrows to the
point form one.** Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of categories fibred in groupoids over the big
fppf site of `S` and `y : (Sch/U) ⟶ 𝒴` a point lying over `Sch/U ⟶ Sch/S`. If a category `𝒟`
over the site is an algebraic stack and is equivalent to the category of arrows
`f(x) ⟶ y(U/U)` through an equivalence lying over the site, then the 2-fibre product
`(Sch/U) ×_{y, 𝒴, f} 𝒳` is an algebraic stack: it is equivalent over the site to the arrows to
`y(U/U)`, and algebraicity transports along equivalences over the site (Stacks 03YQ). -/
theorem isAlgebraicStack_twoFibreProduct_of_costructuredArrow
    {𝒳 : BasedCategory.{vX, uX} (BigFppfOver B S hS)}
    {𝒴 : BasedCategory.{vY, uY} (BigFppfOver B S hS)}
    (h𝒳 : 𝒳.p.IsFiberedInGroupoids) (h𝒴 : 𝒴.p.IsFiberedInGroupoids) (f : 𝒳 ⥤ᵇ 𝒴)
    (U : BigFppfOver B S hS) (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.obj)
    (hy : y ⋙ 𝒴.p = Over.map U.hom) {𝒟 : Type uD} [Category.{vD} 𝒟]
    (p𝒟 : 𝒟 ⥤ BigFppfOver B S hS)
    (E : 𝒟 ⥤ CostructuredArrow f.toFunctor (y.obj (Over.mk (𝟙 _)))) (hE : E.IsEquivalence)
    (hEp : E ⋙ CostructuredArrow.proj f.toFunctor (y.obj (Over.mk (𝟙 _))) ⋙ 𝒳.p = p𝒟)
    (h : IsAlgebraicStack.{u, w} B S hS (BasedCategory.ofFunctor p𝒟)) :
    IsAlgebraicStack.{u, w} B S hS (BasedCategory.ofFunctor
      (TwoFibreProductOver.structureFunctor (Over.map U.hom) 𝒳.p 𝒴.p y f.toFunctor)) := by
  let K := TwoFibreProductOver.TerminalArrow.ofCostructuredArrowFunctor (𝒞 := B.Schemes) f.w hy h𝒴
  have : K.IsEquivalence :=
    TwoFibreProductOver.TerminalArrow.isEquivalence_ofCostructuredArrowFunctor f.w hy h𝒴 h𝒳
  have hT := TwoFibreProductOver.isFiberedInGroupoids (Over.map U.hom) 𝒳.p 𝒴.p y f.toFunctor
    (Functor.IsFiberedInGroupoids.over_map U.hom) h𝒳 h𝒴 hy f.w
  have hcomp : (E ⋙ K) ⋙ TwoFibreProductOver.structureFunctor (Over.map U.hom) 𝒳.p 𝒴.p y
      f.toFunctor = p𝒟 := by
    rw [Functor.assoc, TwoFibreProductOver.TerminalArrow.ofCostructuredArrowFunctor_comp, hEp]
  obtain ⟨e⟩ := StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence h.1 hT (E ⋙ K)
    hcomp (Functor.isEquivalence_trans E K)
  exact isAlgebraicStack_of_equivalenceOver B S hS e h

end AlgebraicGeometry.Stack

end
