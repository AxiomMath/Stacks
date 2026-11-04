module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenSubmersiveComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsEquivalenceHomeomorph
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverBased
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverCompositeSnd

/-!
# Composition of universally open and of universally submersive 1-morphisms (Stacks 06U4, 0CHZ)

**Stacks 06U4** asserts that the composite of two universally open 1-morphisms of algebraic
stacks over `S` is universally open, and **Stacks 0CHZ** the same for universally submersive
ones. The source proves neither (both read "Omitted.").

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.iteratedBaseChangeComparison`: the comparison
  1-morphism over the site.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.iteratedBaseChangeComparison`: the comparison
  1-morphism over the site from the base change of `f ≫ g` along `k` to the iterated base change.
* `AlgebraicGeometry.Stack.AlgebraicStacks.universallyOpen_comp`: **Stacks 06U4**, the universal
  half.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isUniversallySubmersive_comp`: **Stacks 0CHZ**, the
  universal half.

## Implementation notes

For `k : 𝒯 ⟶ 𝒵` the base change of `f ≫ g` along `k` is identified with the iterated base change
`(𝒯 ×_𝒵 𝒴) ×_𝒴 𝒳 ⟶ 𝒯 ×_𝒵 𝒴 ⟶ 𝒯`, whose two legs are a base change of `f` and a base change of
`g` and so are open (resp. submersive) by hypothesis; the non-universal halves
`AlgebraicGeometry.Stack.AlgebraicStacks.isOpen_comp` and `...isSubmersive_comp` then compose
them.

The identification is **not** constructed here. Composition of 1-morphisms of algebraic stacks is
composition of the underlying based functors on the nose, so the apex of the canonical square of
`(k, f ≫ g)` is literally the source of `CategoryTheory.TwoFibreProductOver.splitSnd` and the apex
of the iterated square is literally its target; that comparison is an equivalence of categories by
`CategoryTheory.TwoFibreProductOver.isEquivalence_splitSnd`, is a 1-morphism over the site by
`...splitSnd_comp_structureFunctor`, and is strictly over `𝒯` by `...splitSnd_comp_fst_comp_fst` —
all three of which hold by `rfl` at these arguments. Stacks 003Z (2) upgrades it to an equivalence
in the 2-category of categories over the site, and
`AlgebraicGeometry.Stack.isOpenMap_pointsMap_of_comp_isEquivalence` and
`...isQuotientMap_pointsMap_of_comp_isEquivalence` transport the point-topological property
across it.

So no 2-fibre-product pasting lemma and no transport of a square is used: the comparison the
argument needs is a definitional identity of two concrete 2-fibre products over the site, and the
library already proves it is an equivalence.

## References

* [Stacks Project, Tag 003Z](https://stacks.math.columbia.edu/tag/003Z)
* [Stacks Project, Tag 0040](https://stacks.math.columbia.edu/tag/0040)
* [Stacks Project, Tag 04T2](https://stacks.math.columbia.edu/tag/04T2)
* [Stacks Project, Tag 04XL](https://stacks.math.columbia.edu/tag/04XL)
* [Stacks Project, Tag 06U2](https://stacks.math.columbia.edu/tag/06U2)
* [Stacks Project, Tag 06U4](https://stacks.math.columbia.edu/tag/06U4)
* [Stacks Project, Tag 06U6](https://stacks.math.columbia.edu/tag/06U6)
* [Stacks Project, Tag 0CHZ](https://stacks.math.columbia.edu/tag/0CHZ)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The comparison 1-morphism over the site from the base change of `f ≫ g` along `k` to the
iterated base change — first base change `g` along `k`, then base change `f` along the second
projection. It is `CategoryTheory.TwoFibreProductOver.splitSnd`, which applies here because
composition of 1-morphisms of algebraic stacks is composition of the underlying functors on the
nose, so the apex of the one square is literally the source of `splitSnd` and the apex of the
other is literally its target. -/
def iteratedBaseChangeComparison {𝒯 𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS}
    (k : 𝒯 ⟶ 𝒵) (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵) :
    (Stack.twoFibreProductSquareAlgebraicStacks B S hS k (f ≫ g)).pt.val.val ⥤ᵇ
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS
        (Stack.twoFibreProductSquareAlgebraicStacks B S hS k g).snd f).pt.val.val where
  toFunctor := TwoFibreProductOver.splitSnd 𝒯.val.val.p 𝒳.val.val.p 𝒴.val.val.p 𝒵.val.val.p
    k.hom.hom.toFunctor f.hom.hom.toFunctor g.hom.hom.toFunctor f.hom.hom.w
  w := TwoFibreProductOver.splitSnd_comp_structureFunctor _ _ _ _ _ _ _ f.hom.hom.w

/-- The comparison is an equivalence of the underlying categories:
`CategoryTheory.TwoFibreProductOver.isEquivalence_splitSnd`. -/
theorem isEquivalence_iteratedBaseChangeComparison
    {𝒯 𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS}
    (k : 𝒯 ⟶ 𝒵) (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵) :
    (iteratedBaseChangeComparison B S hS k f g).toFunctor.IsEquivalence :=
  TwoFibreProductOver.isEquivalence_splitSnd _ _ _ _ _ _ _ f.hom.hom.w g.hom.hom.w

/-- The comparison is strictly over the target of `k`: composed with the two first projections of
the iterated square it is the first projection of the direct one. -/
theorem iteratedBaseChangeComparison_comp_fst
    {𝒯 𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS}
    (k : 𝒯 ⟶ 𝒵) (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵) :
    (iteratedBaseChangeComparison B S hS k f g).comp
        ((Stack.twoFibreProductSquareAlgebraicStacks B S hS
          (Stack.twoFibreProductSquareAlgebraicStacks B S hS k g).snd f).fst ≫
          (Stack.twoFibreProductSquareAlgebraicStacks B S hS k g).fst).hom.hom =
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS k (f ≫ g)).fst.hom.hom :=
  BasedCategory.BasedFunctor.ext'
    (TwoFibreProductOver.splitSnd_comp_fst_comp_fst _ _ _ _ _ _ _ f.hom.hom.w)

/-- **Stacks 06U4.** The composite of two universally open 1-morphisms of algebraic stacks over
`S` is universally open. -/
@[stacks 06U4 "composition_universally_open"]
theorem universallyOpen_comp {𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)
    (hf : UniversallyOpen B S hS f) (hg : UniversallyOpen B S hS g) :
    UniversallyOpen B S hS (f ≫ g) := fun 𝒯 k =>
  Stack.isOpenMap_pointsMap_of_comp_isEquivalence B S hS _ _ _
    (iteratedBaseChangeComparison B S hS k f g)
    (isEquivalence_iteratedBaseChangeComparison B S hS k f g) _ _
    (iteratedBaseChangeComparison_comp_fst B S hS k f g)
    (isOpen_comp B S hS
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS
        (Stack.twoFibreProductSquareAlgebraicStacks B S hS k g).snd f).fst
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS k g).fst
      (hf _ (Stack.twoFibreProductSquareAlgebraicStacks B S hS k g).snd) (hg 𝒯 k))

/-- **Stacks 0CHZ.** The composite of two universally submersive 1-morphisms of algebraic stacks
over `S` is universally submersive. -/
@[stacks 0CHZ "composition_universally_submersive"]
theorem isUniversallySubmersive_comp {𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)
    (hf : IsUniversallySubmersive B S hS f) (hg : IsUniversallySubmersive B S hS g) :
    IsUniversallySubmersive B S hS (f ≫ g) := fun 𝒯 k =>
  Stack.isQuotientMap_pointsMap_of_comp_isEquivalence B S hS _ _ _
    (iteratedBaseChangeComparison B S hS k f g)
    (isEquivalence_iteratedBaseChangeComparison B S hS k f g) _ _
    (iteratedBaseChangeComparison_comp_fst B S hS k f g)
    (isSubmersive_comp B S hS
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS
        (Stack.twoFibreProductSquareAlgebraicStacks B S hS k g).snd f).fst
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS k g).fst
      (hf _ (Stack.twoFibreProductSquareAlgebraicStacks B S hS k g).snd) (hg 𝒯 k))

end AlgebraicGeometry.Stack.AlgebraicStacks

end
