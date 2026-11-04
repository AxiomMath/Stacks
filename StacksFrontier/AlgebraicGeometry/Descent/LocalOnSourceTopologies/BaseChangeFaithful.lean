module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
public import StacksCore.Tactic.StacksAttribute

/-!
# Base change along a surjective flat morphism is faithful

For a surjective flat morphism `h : S' ⟶ S` of schemes the base change functor
`Over S ⥤ Over S'` is faithful. Two morphisms of `S`-schemes that agree after base change to
`S'` are equal.

## Main results

* `AlgebraicGeometry.Flat.faithful_overPullback_of_surjective`: **Stacks 02VX**.

## Implementation notes

The base change functor is Mathlib's `CategoryTheory.Over.pullback`, which sends an `S`-scheme
`A` to `A ×_S S' ⟶ S'`. Faithfulness is immediate from the fact that a surjective flat morphism
of schemes is an epimorphism (Tag 02VW, Mathlib's
`AlgebraicGeometry.Flat.epi_of_flat_of_surjective`): the first projection
`A ×_S S' ⟶ A` is a base change of `h`, hence again surjective and flat, hence an epimorphism,
and it is the morphism along which the two base-changed maps are compared.

Mathlib already has this faithfulness under two strictly stronger hypotheses — `h` surjective,
flat and quasi-compact, and `h` surjective, flat and locally of finite presentation, both in
`Mathlib/AlgebraicGeometry/Morphisms/FlatDescent.lean`, both obtained from descent of
isomorphisms. The statement here needs neither extra hypothesis, because epimorphy of a
surjective flat morphism needs neither, so it subsumes both.

## References

* [Stacks Project, Tag 02VW](https://stacks.math.columbia.edu/tag/02VW)
* [Stacks Project, Tag 02VX](https://stacks.math.columbia.edu/tag/02VX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 02VX.** Base change along a surjective flat morphism of schemes is a
faithful functor on the category of schemes over the base. -/
@[stacks 02VX]
instance Flat.faithful_overPullback_of_surjective {S' S : Scheme.{u}} (h : S' ⟶ S)
    [Flat h] [Surjective h] : (Over.pullback h).Faithful where
  map_injective {A B} a b hab := by
    have hfst : Epi (pullback.fst A.hom h) := Flat.epi_of_flat_of_surjective _
    have h₁ := congrArg (fun k ↦ k.left ≫ pullback.fst B.hom h) hab
    simp only [Over.pullback_map_left, pullback.lift_fst] at h₁
    exact Over.OverMorphism.ext ((cancel_epi (pullback.fst A.hom h)).mp h₁)

end AlgebraicGeometry

end
