module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackEquivalence
public import StacksFrontier.AlgebraicGeometry.Stacks.SecondDiagonalInertia
public import StacksFrontier.CategoryTheory.FiberedCategory.InertiaSquare
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.SecondDiagonal
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverCompare

/-!
# The inertia stacks are algebraic

Let `S` be a scheme contained in a big fppf site `B`. The inertia `I_𝒳` of an algebraic stack `𝒳`
over `S` is an algebraic stack over `S`, and so is the relative inertia `I_{𝒳/𝒴}` of a 1-morphism
`f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S`.

## Main results

* `AlgebraicGeometry.Stack.isAlgebraicStack_inertia`: the inertia of an algebraic stack is an
  algebraic stack.
* `AlgebraicGeometry.Stack.isAlgebraicStack_relativeInertia`: the relative inertia of a
  1-morphism of algebraic stacks is an algebraic stack.
* `AlgebraicGeometry.Stack.isFiberedInGroupoids_relativeInertia` and
  `AlgebraicGeometry.Stack.relativeInertia`: the relative inertia as an object of the 2-category of
  categories fibred in groupoids over the site.

## Implementation notes

The inertia and the relative inertia are the canonical constructions
`AlgebraicGeometry.Stack.inertia` and `CategoryTheory.RelativeInertia.basedCategory`. The total
categories have morphism universe `u` and object universe `u + 1`, the universes of the
2-category of algebraic stacks `AlgebraicGeometry.Stack.AlgebraicStacks`.

## References

* [Stacks Project, Tag 050Q](https://stacks.math.columbia.edu/tag/050Q)
* [Stacks Project, Tag 034H](https://stacks.math.columbia.edu/tag/034H)
* [Stacks Project, Tag 04Z6](https://stacks.math.columbia.edu/tag/04Z6)
* [Stacks Project, Tag 04TF](https://stacks.math.columbia.edu/tag/04TF)
* [Stacks Project, Tag 03YQ](https://stacks.math.columbia.edu/tag/03YQ)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The inertia `I_𝒳` of an algebraic stack `𝒳` over `S` is an algebraic stack over `S`. -/
@[stacks 050Q "absolute inertia is algebraic"]
theorem isAlgebraicStack_inertia
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val) :
    IsAlgebraicStack.{u, w} B S hS (inertia B S hS 𝒳).val := by
  have hG : 𝒳.val.p ⋙ 𝟭 (BigFppfOver B S hS) = 𝒳.val.p := Functor.comp_id 𝒳.val.p
  obtain ⟨_, hPst, hPdiag, _⟩ :=
    isAlgebraicStack_product.{u, w} B S hS 𝒳 𝒳 h𝒳 h𝒳
  set P := twoFibreProduct B S hS (CatFiberedInGroupoids.product 𝒳 𝒳) 𝒳 𝒳
    (diagonalBasedFunctor B S hS 𝒳) (diagonalBasedFunctor B S hS 𝒳)
  have htf : IsAlgebraicStack.{u, w} B S hS P.val :=
    isAlgebraicStack_twoFibreProduct.{u, w} B S hS 𝒳.val 𝒳.val
      (CatFiberedInGroupoids.product 𝒳 𝒳).val
      (diagonalBasedFunctor B S hS 𝒳) (diagonalBasedFunctor B S hS 𝒳) hPst hPdiag h𝒳 h𝒳
  have hequiv : Functor.IsEquivalence (TwoFibreProductOver.ofRelativeInertia hG) :=
    (CategoryTheory.Equivalence.mk (TwoFibreProductOver.ofRelativeInertia hG)
      (TwoFibreProductOver.toRelativeInertia hG)
      (eqToIso (TwoFibreProductOver.ofRelativeInertia_comp_toRelativeInertia hG).symm)
      (TwoFibreProductOver.unitIso hG).symm).isEquivalence_functor
  exact (isAlgebraicStack_iff_of_isEquivalence.{u, u, u + 1, w} B S hS
    (𝒳 := (inertia B S hS 𝒳).val) (𝒴 := P.val)
    ⟨TwoFibreProductOver.ofRelativeInertia hG,
      TwoFibreProductOver.ofRelativeInertia_comp_structureFunctor hG⟩
    (inertia B S hS 𝒳).isFiberedInGroupoids P.isFiberedInGroupoids hequiv).2 htf

/-- The comparison functor from the relative inertia to the fibre product is an equivalence over
the base. -/
private theorem nonempty_isEquivalenceOver_toFibreProduct
    (𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (f : 𝒳 ⟶ 𝒴) :
    Nonempty (IsEquivalenceOver (RelativeInertia.π f.hom.toFunctor ⋙ 𝒳.val.p)
      (RelativeInertia.FibreProduct.structureFunctor 𝒳.val.p 𝒴.val.p f.hom.toFunctor f.hom.w)
      (RelativeInertia.toFibreProduct 𝒳.val.p 𝒴.val.p f.hom.toFunctor f.hom.w)) :=
  have := 𝒳.isFiberedInGroupoids.isFibered
  have := 𝒴.isFiberedInGroupoids.isFibered
  RelativeInertia.isEquivalenceOver_toFibreProduct 𝒳.val.p 𝒴.val.p f.hom.toFunctor f.hom.w
    (Functor.IsFiberedInGroupoids.isFibredOneMorphism 𝒴.isFiberedInGroupoids f.hom.w)

/-- The relative inertia of a 1-morphism of categories fibred in groupoids over the big fppf
site of `S` is again fibred in groupoids. -/
lemma isFiberedInGroupoids_relativeInertia
    (𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (f : 𝒳 ⟶ 𝒴) :
    (RelativeInertia.basedCategory f.hom).p.IsFiberedInGroupoids := by
  obtain ⟨E⟩ := nonempty_isEquivalenceOver_toFibreProduct B S hS 𝒳 𝒴 f
  exact StacksRepresentableCFG.isFiberedInGroupoids_of_equivalenceOver
    (StacksRepresentableCFG.EquivalenceOver.ofIsEquivalenceOver E)
    (twoFibreProduct B S hS (inertia B S hS 𝒴) 𝒴 (inertia B S hS 𝒳)
      (inertiaNeutralSection B S hS 𝒴)
      ⟨RelativeInertia.functoriality 𝒳.val.p 𝒴.val.p f.hom.toFunctor f.hom.w,
        RelativeInertia.functoriality_comp_toBase 𝒳.val.p 𝒴.val.p f.hom.toFunctor
          f.hom.w⟩).isFiberedInGroupoids

/-- The relative inertia `I_{𝒳/𝒴}` of a 1-morphism of categories fibred in groupoids over the big
fppf site of `S`, as an object of the 2-category of categories fibred in groupoids over that site.
Its objects are the pairs `(x, α)` with `x` an object of `𝒳` and `α` an automorphism of `x` which
`f` sends to an identity. -/
abbrev relativeInertia
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (f : 𝒳 ⟶ 𝒴) : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS) :=
  CatFiberedInGroupoids.mk (RelativeInertia.basedCategory f.hom)
    (isFiberedInGroupoids_relativeInertia B S hS 𝒳 𝒴 f)

/-- The relative inertia `I_{𝒳/𝒴}` of a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` is
an algebraic stack over `S`. -/
@[stacks 050Q "relative inertia is algebraic"]
theorem isAlgebraicStack_relativeInertia
    (𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (f : 𝒳 ⟶ 𝒴)
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
    (h𝒴 : IsAlgebraicStack.{u, w} B S hS 𝒴.val) :
    IsAlgebraicStack.{u, w} B S hS (RelativeInertia.basedCategory f.hom) := by
  have hI𝒳 : IsAlgebraicStack.{u, w} B S hS (inertia B S hS 𝒳).val :=
    isAlgebraicStack_inertia.{u, w} B S hS 𝒳 h𝒳
  obtain ⟨_, hIYst, hIYdiag, _⟩ :=
    isAlgebraicStack_inertia.{u, w} B S hS 𝒴 h𝒴
  set gFun : (inertia B S hS 𝒳).val ⥤ᵇ (inertia B S hS 𝒴).val :=
    ⟨RelativeInertia.functoriality 𝒳.val.p 𝒴.val.p f.hom.toFunctor f.hom.w,
      RelativeInertia.functoriality_comp_toBase 𝒳.val.p 𝒴.val.p f.hom.toFunctor f.hom.w⟩
  set FP := twoFibreProduct B S hS (inertia B S hS 𝒴) 𝒴 (inertia B S hS 𝒳)
    (inertiaNeutralSection B S hS 𝒴) gFun
  have htf : IsAlgebraicStack.{u, w} B S hS FP.val :=
    isAlgebraicStack_twoFibreProduct.{u, w} B S hS 𝒴.val (inertia B S hS 𝒳).val
      (inertia B S hS 𝒴).val (inertiaNeutralSection B S hS 𝒴) gFun hIYst hIYdiag h𝒴 hI𝒳
  obtain ⟨E⟩ := nonempty_isEquivalenceOver_toFibreProduct B S hS 𝒳 𝒴 f
  exact (isAlgebraicStack_iff_of_isEquivalence.{u, u, u + 1, w} B S hS
    (𝒳 := RelativeInertia.basedCategory f.hom) (𝒴 := FP.val)
    ⟨RelativeInertia.toFibreProduct 𝒳.val.p 𝒴.val.p f.hom.toFunctor f.hom.w,
      RelativeInertia.toFibreProduct_comp_structureFunctor 𝒳.val.p 𝒴.val.p
        f.hom.toFunctor f.hom.w⟩
    (isFiberedInGroupoids_relativeInertia B S hS 𝒳 𝒴 f) FP.isFiberedInGroupoids
    E.isEquivalence).2 htf

end AlgebraicGeometry.Stack

end
