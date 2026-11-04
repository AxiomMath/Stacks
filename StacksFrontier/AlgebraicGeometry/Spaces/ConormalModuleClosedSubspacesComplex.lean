module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleFactorizationVanishing

/-!
# The conormal sequence of a pair of closed subspaces is a complex

Let `Z ⊆ Y ⊆ X` be closed subspaces of an algebraic space `X` over a scheme `S` contained in a
big fppf site `B`, the inclusion of `Z` in `Y` being given by a morphism `f : Z ⟶ Y` of algebraic
spaces with `f` followed by the inclusion of `Y` the inclusion of `Z`.  [Stacks Project,
Tag 06BD] asserts that

```
  i^*𝒞_{Y/X} ⟶ 𝒞_{Z/X} ⟶ 𝒞_{Z/Y} ⟶ 0
```

is exact, `i : Z ⟶ Y` being the inclusion.  Two of the three clauses are available for algebraic
spaces: the right-hand map is an epimorphism
(`AlgebraicGeometry.Space.epi_conormalMap_closedSubspaces` of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleBaseChangeEpi.lean`), and this file proves
that the composite of the two maps is zero, so that the sequence is a complex.

## Where the sequence lives

As in `StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleBaseChangeEpi.lean`, the copy of `Z`
inside `Y` is taken as the inverse image `j⁻¹(Z)` of `Z ⊆ X` along the inclusion `j : Y ⟶ X`,
this development having no composition of closed subspaces; the sequence is read on that inverse
image, along its projection `π` to `Z`.  The right-hand map is then the map of [Stacks Project,
Tag 04CP] of the fibre product square of `j`, and the left-hand map is `π^*` of the map of that
tag for the square of `Z ⊆ X` over `Y ⊆ X` with the identity of `X` as its morphism of ambient
spaces.

## Main results

* `AlgebraicGeometry.Space.closedSubspacesConormal_square`: the square of closed subspaces
  `Z ⊆ X` over `Y ⊆ X` whose conormal map is the left-hand map of the sequence.
* `AlgebraicGeometry.Space.conormalMap_comp_conormalMap_closedSubspaces_eq_zero`: **the
  composite-is-zero clause of [Stacks Project, Tag 06BD]**.

## Implementation notes

**The containment `Z ⊆ Y` enters as a morphism and an equation.**  The hypothesis `hf` below
says that `f : Z ⟶ Y` followed by the inclusion of `Y` is the inclusion of `Z`, which is what it
means for `Z` to be contained in `Y` as a closed subspace; the inequality `Z.1 ≤ Y.1` that
`AlgebraicGeometry.Space.epi_conormalMap_closedSubspaces` carries is its shadow, and is not
enough on its own, because the left-hand map of the sequence is attached to the morphism `f` and
not to the inequality.

**The vanishing needs no scheme-level input.**  The ambient morphism of the outer rectangle of
the two stacked squares is `Y ⟶ X ⟶ X`, that is the inclusion `j` itself, which factors through
`Y` trivially; so
`AlgebraicGeometry.Space.comp_conormalMap_eq_zero_of_factors` applies, and the whole content is
that the defining ideal sheaf of `Y` is killed by the comorphism of `j`.  Exactness in the middle
is a different matter and is not proved; see the "What is not proved" section of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleBaseChangeEpi.lean`.

## References

* [Stacks Project, Tag 06BD](https://stacks.math.columbia.edu/tag/06BD)
* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 04CQ](https://stacks.math.columbia.edu/tag/04CQ)
* [Stacks Project, Tag 04G2](https://stacks.math.columbia.edu/tag/04G2), part (3)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : AlgebraicSpaces B S hS} (Y Z : ClosedSubspaces B S hS X.1)
    (f : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨Y.1.toFunctor, Y.2.1⟩ : AlgebraicSpaces B S hS))

/-- The square of closed subspaces whose conormal map is the left-hand map of the conormal
sequence of the pair `Z ⊆ Y ⊆ X`: it has `Z ⊆ X` upstairs, `Y ⊆ X` downstairs, the identity of
`X` as its morphism of ambient spaces and `f : Z ⟶ Y` as its morphism of subspaces. -/
theorem closedSubspacesConormal_square
    (hf : f ≫ subspaceInclusion B S hS X Y = subspaceInclusion B S hS X Z) :
    subspaceInclusion B S hS X Z ≫ (𝟙 X : X ⟶ X) =
      f ≫ subspaceInclusion B S hS X Y :=
  (Category.comp_id (subspaceInclusion B S hS X Z)).trans hf.symm

/-- **The composite-is-zero clause of [Stacks Project, Tag 06BD].**  Let `Y` and `Z` be closed
subspaces of an algebraic space `X` with `Z` contained in `Y` through `f : Z ⟶ Y`.  The composite
of the two maps `i^*𝒞_{Y/X} ⟶ 𝒞_{Z/X} ⟶ 𝒞_{Z/Y}` of the conormal sequence of the pair is zero,
so that the sequence is a complex; together with
`AlgebraicGeometry.Space.epi_conormalMap_closedSubspaces` this makes it a complex, exact at its
right term.

Both maps are maps of [Stacks Project, Tag 04CP], the left one at the square of
`AlgebraicGeometry.Space.closedSubspacesConormal_square` and the right one at the fibre product
square of the inclusion `j : Y ⟶ X`.  By part (3) of [Stacks Project, Tag 04G2] their composite
is the conormal map of the outer rectangle, whose morphism of ambient spaces is `j ≫ 𝟙 X = j`;
that factors through the inclusion of `Y`, so
`AlgebraicGeometry.Space.comp_conormalMap_eq_zero_of_factors` applies.

Exactness in the middle is not proved; see the "What is not proved" section of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleBaseChangeEpi.lean`. -/
@[stacks 06BD "the sequence is a complex: the composite of i^*𝒞_{Y/X} ⟶ 𝒞_{Z/X} and \
𝒞_{Z/X} ⟶ 𝒞_{Z/Y} is zero"]
theorem conormalMap_comp_conormalMap_closedSubspaces_eq_zero
    (hf : f ≫ subspaceInclusion B S hS X Y = subspaceInclusion B S hS X Z) :
    (modulePullback B S hS
          (preimageProjection B S hS (subspaceInclusion B S hS X Y) Z)).map
        (conormalMap B S hS Z Y (𝟙 X : X ⟶ X) f
          (closedSubspacesConormal_square B S hS Y Z f hf)) ≫
      conormalMap B S hS
        (preimageSubspace B S hS (subspaceInclusion B S hS X Y) Z) Z
        (subspaceInclusion B S hS X Y)
        (preimageProjection B S hS (subspaceInclusion B S hS X Y) Z)
        (conormalEtaleRestrictionSquare B S hS (subspaceInclusion B S hS X Y) Z) = 0 := by
  have key := comp_conormalMap_eq_zero_of_factors B S hS
    (subspaceInclusion B S hS X Y) (𝟙 X : X ⟶ X)
    (preimageSubspace B S hS (subspaceInclusion B S hS X Y) Z) Z Y
    (preimageProjection B S hS (subspaceInclusion B S hS X Y) Z) f
    (conormalEtaleRestrictionSquare B S hS (subspaceInclusion B S hS X Y) Z)
    (closedSubspacesConormal_square B S hS Y Z f hf)
    (𝟙 (⟨Y.1.toFunctor, Y.2.1⟩ : AlgebraicSpaces B S hS))
    ((Category.comp_id (subspaceInclusion B S hS X Y)).trans
      (Category.id_comp (subspaceInclusion B S hS X Y)).symm)
  rw [key]

end AlgebraicGeometry.Space

end
