module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.ChangeOfBaseScheme
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStackPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.ChowNoetherianReduction
public import StacksFrontier.AlgebraicGeometry.Stacks.IntegralQuasiSeparatedStack
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedSchemeStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationAbsolute
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationAbsoluteQuasiSeparated
public import StacksFrontier.CategoryTheory.FiberedCategory.RelocalizeAsElements

/-!
# Quasi-separatedness inputs of Chow's lemma for algebraic stacks

Two quasi-separatedness statements that the proof of Chow's lemma for algebraic stacks
(Stacks 0CQ8) uses without comment.

## Main results

* `...isQuasiCompactMorphism_inertiaProjectionAlgebraicStacks_of_isQuasiSeparated`, in the same
  namespace: if `f : 𝒳 ⟶ Y` is a quasi-separated 1-morphism to a quasi-separated algebraic space,
  then the inertia projection `I_𝒳 ⟶ 𝒳` is quasi-compact.

## Implementation notes

For the first statement, the view of the stack of `Y` over `Spec ℤ` has the same objects as the
category of elements of `Y`, with structure functor composed with the relocalization along
`S ⟶ Spec ℤ`; `CategoryTheory.PresheafOfCategories.relocalizeElementsEquivalenceOver` identifies it
with the category of elements of the lower-shriek extension of `Y`, which is the algebraic space
whose quasi-separatedness over `Spec ℤ` is the hypothesis. The structure morphism of the view is
then represented by the unique morphism from that space to the terminal presheaf, and Stacks 04YT
and Stacks 04YZ part (2) reduce quasi-separatedness of the structure morphism to
quasi-separatedness of that morphism of algebraic spaces, which is Stacks 04ZI part (6).

The second statement is Stacks 050L part (8) applied to `f`, followed by the quasi-compactness of
the absolute diagonal of an absolutely quasi-separated algebraic stack and the identification of
the inertia projection with a base change of that diagonal.

## References

* [Stacks Project, Tag 03BS](https://stacks.math.columbia.edu/tag/03BS)
* [Stacks Project, Tag 04YT](https://stacks.math.columbia.edu/tag/04YT)
* [Stacks Project, Tag 04YZ](https://stacks.math.columbia.edu/tag/04YZ)
* [Stacks Project, Tag 050D](https://stacks.math.columbia.edu/tag/050D)
* [Stacks Project, Tag 050L](https://stacks.math.columbia.edu/tag/050L)
* [Stacks Project, Tag 0CQ8](https://stacks.math.columbia.edu/tag/0CQ8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The inertia projection of an algebraic stack quasi-separated over a quasi-separated
algebraic space is quasi-compact.** Let `Y` be an algebraic space over `S` which is
quasi-separated in the sense of Stacks 03BS, part (3), and `f : 𝒳 ⟶ Y` a quasi-separated
1-morphism (Stacks 04YW). Then the inertia projection `I_𝒳 ⟶ 𝒳` is quasi-compact in the sense of
Stacks 050U.

`Y` is quasi-separated as an algebraic stack
(`AlgebraicGeometry.Stack.AlgebraicStacks.isAbsolutelyQuasiSeparated_algebraicSpaceStack`), so `𝒳`
is quasi-separated by Stacks 050L, part (8); its absolute diagonal is therefore quasi-compact, and
the inertia projection is a base change of that diagonal. -/
theorem isQuasiCompactMorphism_inertiaProjectionAlgebraicStacks_of_isQuasiSeparated
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (hYqs : Space.IsAbsolutelyQuasiSeparated B S hS (BigFppfSite.contains_terminal B) Y)
    {𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)
    (hf : IsQuasiSeparated B S hS f) :
    IsQuasiCompactMorphism.{u, w} B S hS (inertiaProjectionAlgebraicStacks B S hS 𝒳) :=
  isQuasiCompactMorphism_inertiaProjectionAlgebraicStacks.{u, w} B S hS 𝒳
    (isQuasiCompact_diagonal_of_isAbsolutelyQuasiSeparated.{u, w} B S hS
      (BigFppfSite.contains_terminal B) 𝒳
      (isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS (BigFppfSite.contains_terminal B) f
        (isAbsolutelyQuasiSeparated_algebraicSpaceStack B S hS (BigFppfSite.contains_terminal B) hY
          hYqs) hf))

end AlgebraicGeometry.Stack.AlgebraicStacks

end
