module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.Unconditional
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteriaAlgebraicSpaceSources
public import StacksFrontier.AlgebraicGeometry.Stacks.FaithfulRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableStackInSetoids
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SecondDiagonalRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.StackInSetoidsRepresentableBySpace
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductAlgebraicStack
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.TwoFibreProductSetoid

/-!
# A faithful 1-morphism of algebraic stacks is representable by algebraic spaces

Let `S` be a scheme contained in a big fppf site and let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of
algebraic stacks over `S`. **Stacks 04Y5** says that `f` is representable by algebraic spaces
exactly when it is faithful. The implication (3) ⟹ (2) is
`AlgebraicGeometry.Stack.AlgebraicStacks.faithful_homFunctor_of_isRepresentableByAlgebraicSpaces`.
This file proves the implication (2) ⟹ (3).

The proof is the source's. For a scheme `V` over `S` and a 1-morphism
`y : (Sch/V)_{fppf} ⟶ 𝒴`, the 2-fibre product `𝒳 ×_{f, 𝒴, y} (Sch/V)_{fppf}` is an algebraic
stack (Stacks 04TF), and it is a stack in setoids because `f` is faithful and the fibres of
`(Sch/V)_{fppf}` are discrete (the content of Stacks 05UI). An algebraic stack in setoids is
representable by an algebraic space (Stacks 04SZ, (1) ⟹ (3)), and the pointwise criterion of
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_of_forall_twoFibreProduct` turns this
into representability of `f` by algebraic spaces.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isRepresentableByAlgebraicSpaces_of_faithful`:
  the implication (2) ⟹ (3) of **Stacks 04Y5**.
* `AlgebraicGeometry.Stack.AlgebraicStacks.faithful_homFunctor_tfae`: **Stacks 04Y5**, the three
  conditions are equivalent.
* `isRepresentableByAlgebraicSpaces_of_isEquivalence_secondRelativeDiagonal` (same namespace):
  **Stacks 04YY**, the implication (2) ⟹ (1): a 1-morphism of algebraic stacks whose second
  diagonal is an isomorphism is representable by algebraic spaces.

## References

* [Stacks Project, Tag 04SZ](https://stacks.math.columbia.edu/tag/04SZ)
* [Stacks Project, Tag 04TF](https://stacks.math.columbia.edu/tag/04TF)
* [Stacks Project, Tag 04Y5](https://stacks.math.columbia.edu/tag/04Y5)
* [Stacks Project, Tag 04YY](https://stacks.math.columbia.edu/tag/04YY)
* [Stacks Project, Tag 05UI](https://stacks.math.columbia.edu/tag/05UI)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

namespace AlgebraicStacks

variable {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS}

/-- **The implication (2) ⟹ (3) of Stacks 04Y5.** A 1-morphism of algebraic stacks over `S`
whose underlying functor is faithful is representable by algebraic spaces.

For a scheme `V` over `S` and a 1-morphism `y : (Sch/V)_{fppf} ⟶ 𝒴`, the 2-fibre product
`𝒳 ×_{f, 𝒴, y} (Sch/V)_{fppf}` is an algebraic stack by Stacks 04TF and a stack in setoids
because `f` is faithful and the fibres of `(Sch/V)_{fppf}` are discrete; it is therefore
representable by an algebraic space by Stacks 04SZ, the implication (1) ⟹ (3). -/
theorem isRepresentableByAlgebraicSpaces_of_faithful (f : 𝒳 ⟶ 𝒴)
    (hf : (CatFiberedInGroupoids.homFunctor f.hom).Faithful) :
    IsRepresentableByAlgebraicSpaces B S hS f.hom.hom := by
  obtain ⟨_, h𝒴stack, h𝒴diag, _⟩ := 𝒴.property
  refine isRepresentableByAlgebraicSpaces_of_forall_twoFibreProduct B S hS 𝒴.val 𝒳.val
    f.hom.hom fun V y => ?_
  rw [isRepresentableByAlgebraicSpace_twoFibreProduct_swap_iff]
  let W := Stack.twoFibreProduct B S hS 𝒴.val 𝒳.val (schemeFibredCategory B S hS V) f.hom.hom y
  have halg : IsAlgebraicStack.{u, w} B S hS W.val :=
    isAlgebraicStack_twoFibreProduct B S hS 𝒳.val.val (schemeFibredCategory B S hS V).val
      𝒴.val.val f.hom.hom y h𝒴stack h𝒴diag 𝒳.property
      (isAlgebraicStack_schemeFibredCategory B S hS V)
  have : f.hom.hom.toFunctor.Faithful := hf
  have hset : W.val.p.IsStackInSetoids (BigFppfOver.topology B S hS) :=
    Functor.isStackInSetoids_structureFunctor (BigFppfOver.topology B S hS)
      𝒳.val.isFiberedInGroupoids
      (isStackInSetoids_of_isRepresentableByAlgebraicSpace B S hS _
        (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS V))
      halg.2.1.1
  exact isRepresentableByAlgebraicSpace_of_isStackInSetoids B S hS W halg hset

/-- **Stacks 04YY, the implication (2) ⟹ (1).** A 1-morphism of algebraic stacks over `S` whose
second diagonal `Δ_{f, 2}` is an isomorphism is representable by algebraic spaces: the second
diagonal is an isomorphism exactly when `f` is faithful (Stacks 04Z7), and a faithful 1-morphism
of algebraic stacks is representable by algebraic spaces (Stacks 04Y5). -/
@[stacks 04YY "the implication (2) ⟹ (1)"]
theorem isRepresentableByAlgebraicSpaces_of_isEquivalence_secondRelativeDiagonal (f : 𝒳 ⟶ 𝒴)
    (hf : Functor.IsEquivalence (secondRelativeDiagonal B S hS f.hom).hom.toFunctor) :
    IsRepresentableByAlgebraicSpaces B S hS f.hom.hom :=
  isRepresentableByAlgebraicSpaces_of_faithful B S hS f
    ((isEquivalence_secondRelativeDiagonal_iff_faithful B S hS f.hom).mp hf)

/-- **Stacks 04Y5.** For a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` the following are
equivalent:

1. for every object `U` of the big fppf site of `S` the functor `f_U : 𝒳_U ⥤ 𝒴_U` on fibres is
   faithful;
2. the functor `f` is faithful;
3. `f` is representable by algebraic spaces.

The equivalence (1) ⟺ (2) is Stacks 003Z (1),
`CategoryTheory.Functor.IsFiberedInGroupoids.faithful_iff_forall_fiber`; the implication
(3) ⟹ (2) is
`AlgebraicGeometry.Stack.AlgebraicStacks.faithful_homFunctor_of_isRepresentableByAlgebraicSpaces`
and the implication (2) ⟹ (3) is
`AlgebraicGeometry.Stack.AlgebraicStacks.isRepresentableByAlgebraicSpaces_of_faithful`. -/
@[stacks 04Y5]
theorem faithful_homFunctor_tfae {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) :
    List.TFAE
      [∀ U : BigFppfOver B S hS, (Functor.Fiber.mapOfComp 𝒳.val.val.p 𝒴.val.val.p
          (CatFiberedInGroupoids.homFunctor f.hom)
          (CatFiberedInGroupoids.homFunctor_comp_p f.hom) U).Faithful,
        (CatFiberedInGroupoids.homFunctor f.hom).Faithful,
        IsRepresentableByAlgebraicSpaces B S hS f.hom.hom] := by
  have : 𝒴.val.val.p.IsFibered := 𝒴.val.isFiberedInGroupoids.isFibered
  tfae_have 1 ↔ 2 := (Functor.IsFiberedInGroupoids.faithful_iff_forall_fiber 𝒳.val.val.p
    𝒴.val.val.p 𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
    (CatFiberedInGroupoids.homFunctor f.hom) (CatFiberedInGroupoids.homFunctor_comp_p f.hom)).symm
  tfae_have 2 → 3 := isRepresentableByAlgebraicSpaces_of_faithful B S hS f
  tfae_have 3 → 2 := faithful_homFunctor_of_isRepresentableByAlgebraicSpaces B S hS f
  tfae_finish

end AlgebraicStacks

end AlgebraicGeometry.Stack

end
