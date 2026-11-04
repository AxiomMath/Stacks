module

public import StacksFrontier.AlgebraicGeometry.Stacks.MonomorphismFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionStackBaseChange
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Diagonal
public import StacksFrontier.CategoryTheory.TwoFibreProduct.IdentityCospan
public import StacksFrontier.CategoryTheory.TwoFibreProduct.IsTwoFibreProductOfEquivalence
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Pasting

/-!
# Postcomposing with a monomorphism does not change the relative dimension

Let `𝒯 --g--> 𝒵 --i--> 𝒳` be 1-morphisms of locally Noetherian algebraic stacks over `S` with
`g` and `g ≫ i` locally of finite type, and let `i` be a **monomorphism** in the sense of
**Stacks 04ZW**. Then for every `t ∈ |𝒯|` the relative dimensions of Stacks 0DRL agree:

`dim_t(𝒯_{i(g(t))}) = dim_t(𝒯_{g(t)})`.

## Main definitions

* `AlgebraicGeometry.Stack.selfCospanSquare`: the 2-commutative square over the cospan `(i, i)`
  whose apex is the source of `i` and both of whose legs are the identity.

## Main results

* `AlgebraicGeometry.Stack.isTwoFibreProduct_selfCospanSquare`: that square is 2-cartesian when
  `i` is a monomorphism, i.e. `𝒵 = 𝒵 ×_𝒳 𝒵`. This is the implication (1) ⟹ (3) of
  **Stacks 04ZZ** read as a statement about 2-fibre product squares.
* `AlgebraicGeometry.Stack.relativeStackDimensionAt_comp_of_isMonomorphism`: the invariance of
  the relative dimension of **Stacks 0DRL** under postcomposition with a monomorphism.

## References

* [Stacks Project, Tag 003O](https://stacks.math.columbia.edu/tag/003O)
* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 04T2](https://stacks.math.columbia.edu/tag/04T2)
* [Stacks Project, Tag 04Z7](https://stacks.math.columbia.edu/tag/04Z7)
* [Stacks Project, Tag 04ZW](https://stacks.math.columbia.edu/tag/04ZW)
* [Stacks Project, Tag 04ZZ](https://stacks.math.columbia.edu/tag/04ZZ)
* [Stacks Project, Tag 0504](https://stacks.math.columbia.edu/tag/0504)
* [Stacks Project, Tag 05UK](https://stacks.math.columbia.edu/tag/05UK)
* [Stacks Project, Tag 0DRL](https://stacks.math.columbia.edu/tag/0DRL)
* [Stacks Project, Tag 0DRN](https://stacks.math.columbia.edu/tag/0DRN)
-/


@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The square of a 1-morphism against itself.** For `i : 𝒵 ⟶ 𝒳` the 2-commutative square

```text
        𝟙 𝒵
  𝒵 ---------> 𝒵
  |            |
𝟙 |            | i
  v      i     v
  𝒵 ---------> 𝒳
```

over the cospan `(i, i)`, with apex `𝒵` and both legs the identity. It is a 2-fibre product
exactly when `i` is a monomorphism, which is the implication (1) ⟹ (3) of Stacks 04ZZ; the
definition itself assumes nothing. -/
@[reducible]
def selfCospanSquare {𝒵 𝒳 : AlgebraicStacks.{u, w} B S hS} (i : 𝒵 ⟶ 𝒳) :
    Bicategory.TwoCommSq i i where
  pt := 𝒵
  fst := 𝟙 𝒵
  snd := 𝟙 𝒵
  iso := Iso.refl _

/-- **Stacks 04ZZ, the implication (1) ⟹ (3), as a 2-fibre product square: `𝒵 = 𝒵 ×_𝒳 𝒵` for a
monomorphism `i : 𝒵 ⟶ 𝒳`.** The square `AlgebraicGeometry.Stack.selfCospanSquare` of the cospan
`(i, i)` is 2-cartesian. -/
noncomputable def isTwoFibreProduct_selfCospanSquare
    {𝒵 𝒳 : AlgebraicStacks.{u, w} B S hS} (i : 𝒵 ⟶ 𝒳)
    (hi : AlgebraicStacks.IsMonomorphism B S hS i) :
    Bicategory.IsTwoFibreProduct (selfCospanSquare B S hS i) := by
  refine Bicategory.isTwoFibreProduct_of_underlying
    (Bicategory.isTwoFibreProduct_of_isEquivalence_to
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
        i.hom i.hom)
      (CatFiberedInGroupoids.preHomTwoFibreProductSquare.{u, u, u + 1, u + 1} i.hom i.hom
        (selfCospanSquare B S hS i).underlying) ?_)
  exact (TwoFibreProductOver.full_and_faithful_iff_isEquivalence_diagonal
    𝒵.val.property 𝒳.val.property i.hom.hom.w).1
    (AlgebraicStacks.full_and_faithful_homFunctor_of_isMonomorphism B S hS i hi)

/-- **The graph square of `g` along `i`**, obtained by pasting
`AlgebraicGeometry.Stack.selfCospanSquare` of the cospan `(i, i)` onto the degenerate 2-fibre
product of the cospan `(𝟙 𝒵, g)`. Its apex is `𝒯`, its second leg is `𝟙 𝒯` and its first leg is
`g ≫ 𝟙 𝒵`, pasting being what composes the legs. -/
@[reducible]
private noncomputable def pastedGraphSquare {𝒯 𝒵 𝒳 : AlgebraicStacks.{u, w} B S hS}
    (g : 𝒯 ⟶ 𝒵) (i : 𝒵 ⟶ 𝒳) : Bicategory.TwoCommSq i (g ≫ i) :=
  (selfCospanSquare B S hS i).pasteSnd (Bicategory.TwoCommSq.idCospan g)

/-- The graph square `AlgebraicGeometry.Stack.pastedGraphSquare` of `g` along a monomorphism `i`
is 2-cartesian. -/
private noncomputable def isTwoFibreProduct_pastedGraphSquare
    {𝒯 𝒵 𝒳 : AlgebraicStacks.{u, w} B S hS} (g : 𝒯 ⟶ 𝒵) (i : 𝒵 ⟶ 𝒳)
    (hi : AlgebraicStacks.IsMonomorphism B S hS i) :
    Bicategory.IsTwoFibreProduct (pastedGraphSquare B S hS g i) :=
  Bicategory.isTwoFibreProduct_pasteSnd _ (isTwoFibreProduct_selfCospanSquare B S hS i hi) _
    (Bicategory.isTwoFibreProduct_idCospan g)

/-- The map on points of the identity 1-morphism of an algebraic stack fixes every point, the
fibred-in-groupoids witness of the source being `𝒯.val.property` rather than a choice extracted
from algebraicity. -/
private theorem pointsMap_snd_id {𝒯 : AlgebraicStacks.{u, w} B S hS}
    (t : points B S hS 𝒯.val.val 𝒯.val.property) :
    pointsMap B S hS 𝒯.val.val 𝒯.val.property 𝒯.val.property (𝟙 𝒯 : 𝒯 ⟶ 𝒯).hom.hom t = t := by
  induction t using Quotient.inductionOn with
  | h p => cases p; rfl

/-- The relative dimension of Stacks 0DRL depends on the 1-morphism only through its name: equal
1-morphisms have equal relative dimensions, the two locally-of-finite-type witnesses being
propositions. -/
private theorem relativeStackDimensionAt_congr_hom {𝒯 𝒳 : AlgebraicStacks.{u, w} B S hS}
    {f f' : 𝒯 ⟶ 𝒳} (hff : f = f')
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (hf' : AlgebraicStacks.IsLocallyOfFiniteType B S hS f')
    (h𝒯 : IsLocallyNoetherianStack.{u, w} B S hS 𝒯)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (t : points B S hS 𝒯.val.val 𝒯.val.property) :
    relativeStackDimensionAt.{u, w} B S hS f hf h𝒯 h𝒳 t =
      relativeStackDimensionAt.{u, w} B S hS f' hf' h𝒯 h𝒳 t := by
  subst hff
  rfl

/-- **Postcomposing with a monomorphism does not change the relative dimension of Stacks 0DRL.**
Let `g : 𝒯 ⟶ 𝒵` and `i : 𝒵 ⟶ 𝒳` be 1-morphisms of locally Noetherian algebraic stacks over `S`
with `i` a monomorphism (Stacks 04ZW) and with `g` and `g ≫ i` locally of finite type. Then for
every `t ∈ |𝒯|` the relative dimension of `g ≫ i` at `t` equals that of `g` at `t`. -/
theorem relativeStackDimensionAt_comp_of_isMonomorphism
    {𝒯 𝒵 𝒳 : AlgebraicStacks.{u, w} B S hS} (g : 𝒯 ⟶ 𝒵) (i : 𝒵 ⟶ 𝒳)
    (hi : AlgebraicStacks.IsMonomorphism B S hS i)
    (hg : AlgebraicStacks.IsLocallyOfFiniteType B S hS g)
    (hgi : AlgebraicStacks.IsLocallyOfFiniteType B S hS (g ≫ i))
    (h𝒯 : IsLocallyNoetherianStack.{u, w} B S hS 𝒯)
    (h𝒵 : IsLocallyNoetherianStack.{u, w} B S hS 𝒵)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (t : points B S hS 𝒯.val.val 𝒯.val.property) :
    relativeStackDimensionAt.{u, w} B S hS (g ≫ i) hgi h𝒯 h𝒳 t =
      relativeStackDimensionAt.{u, w} B S hS g hg h𝒯 h𝒵 t := by
  have hfst : AlgebraicStacks.IsLocallyOfFiniteType B S hS (g ≫ 𝟙 𝒵) := by
    rwa [Category.comp_id]
  have h := relativeStackDimensionAt_fst_eq_relativeStackDimensionAt.{u, w} B S hS i (g ≫ i)
    (pastedGraphSquare B S hS g i) (isTwoFibreProduct_pastedGraphSquare B S hS g i hi) hgi hfst
    h𝒯 h𝒯 h𝒵 h𝒳 t
  rw [pointsMap_snd_id B S hS t] at h
  rw [← h]
  exact relativeStackDimensionAt_congr_hom B S hS (Category.comp_id g).symm hg hfst h𝒯 h𝒵 t

end AlgebraicGeometry.Stack

end
