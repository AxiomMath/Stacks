module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.WellNighAffineFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.WellNighAffineModuliTopology

/-!
# The moduli space of a well-nigh affine algebraic stack

This file states and proves Stacks 0DUP: a well-nigh affine algebraic stack `𝒳` has a uniform
categorical moduli space `f : 𝒳 ⟶ M` in the category of affine schemes, and `f` is separated,
quasi-compact and a universal homeomorphism.

## Main results

* `AlgebraicGeometry.Stack.exists_isUniformCategoricalModuliSpaceIn_of_isWellNighAffine`:
  Stacks 0DUP.

## Implementation notes

A well-nigh affine `𝒳` has a chart `x : U ⟶ 𝒳` from an affine scheme with affine finite locally
free relation `s, t : R ⟶ U` (`AlgebraicGeometry.Stack.nonempty_wellNighAffineChart`, from the
groupoid presentation of Stacks 0DUM). The moduli space is `M = Spec C`, `C` the ring of
`R`-invariant functions on `U`, and `f` is the descent of the invariant map `U ⟶ M`
(`AlgebraicGeometry.Stack.WellNighAffineChart.moduliMap`). The clauses are:

* uniformity:
  `AlgebraicGeometry.Stack.WellNighAffineChart.isUniformCategoricalModuliSpaceIn_moduliMap`;
* separatedness: `AlgebraicGeometry.Stack.WellNighAffineChart.isSeparated_moduliMap`;
* quasi-compactness:
  `AlgebraicGeometry.Stack.WellNighAffineChart.isQuasiCompactMorphism_moduliMap`;
* universal homeomorphism:
  `AlgebraicGeometry.Stack.WellNighAffineChart.universalHomeomorphism_moduliMap`.

The category of affine schemes is read as the full subcategory of algebraic spaces over `S`
which are affine, `fun W => Space.IsAffineSpace B S hS W.obj`, the reading of Stacks 0DUG.

## References

* [Stacks Project, Tag 0DUP](https://stacks.math.columbia.edu/tag/0DUP)
* [Stacks Project, Tag 0DUG](https://stacks.math.columbia.edu/tag/0DUG)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0DUP.** Let the algebraic stack `𝒳` be well-nigh affine. There exists a uniform
categorical moduli space `f : 𝒳 ⟶ M` in the category of affine schemes. Moreover `f` is
separated, quasi-compact, and a universal homeomorphism. -/
@[stacks 0DUP]
theorem exists_isUniformCategoricalModuliSpaceIn_of_isWellNighAffine
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (h𝒳 : IsWellNighAffine.{u, w} B S hS 𝒳) :
    ∃ (M : AlgebraicSpaces B S hS)
      (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS M.obj M.property),
      IsUniformCategoricalModuliSpaceIn B S hS (fun W => Space.IsAffineSpace B S hS W.obj) M
          f.hom ∧
        AlgebraicStacks.IsSeparated B S hS f ∧ IsQuasiCompactMorphism.{u, w} B S hS f ∧
          UniversalHomeomorphism B S hS f := by
  obtain ⟨K⟩ := nonempty_wellNighAffineChart B S hS 𝒳 h𝒳
  exact ⟨K.moduliSpace, K.moduliMap, K.isUniformCategoricalModuliSpaceIn_moduliMap,
    K.isSeparated_moduliMap h𝒳, K.isQuasiCompactMorphism_moduliMap,
    K.universalHomeomorphism_moduliMap⟩

end AlgebraicGeometry.Stack

end
