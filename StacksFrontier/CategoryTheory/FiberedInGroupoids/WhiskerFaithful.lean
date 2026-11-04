module

public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoCategory

/-!
# Right whiskering by a faithful 1-morphism of categories fibred in groupoids

In the 2-category of categories fibred in groupoids over a category `𝒞` (Stacks 02XS), a
2-morphism is a morphism of the underlying functors (clause (3) of the source), and right
whiskering by a 1-morphism `h` applies the functor underlying `h` to each component. So if that
functor is faithful, right whiskering by `h` is injective on 2-morphisms: a 2-morphism into the
source of `h` is determined by its image after `h`.

## Main results

* `CategoryTheory.CatFiberedInGroupoids.hom₂_ext_of_whiskerRight_faithful`: two 2-morphisms that
  agree after right whiskering by a 1-morphism with faithful underlying functor are equal.

## Implementation notes

The hypothesis is faithfulness of the underlying *functor*, not of the 1-morphism in any
2-categorical sense; that is the form in which the library's suppliers of faithfulness state it
(for instance Stacks 04Y5, the implication (3) ⟹ (2),
`AlgebraicGeometry.Stack.AlgebraicStacks.faithful_homFunctor_of_isRepresentableByAlgebraicSpaces`),
and it is also exactly what the componentwise argument consumes.

## References

* [Stacks Project, Tag 02XS](https://stacks.math.columbia.edu/tag/02XS)
-/

@[expose] public section

open CategoryTheory.Bicategory

namespace CategoryTheory.CatFiberedInGroupoids

universe v₁ v₂ u₁ u₂

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞]

/-- **Right whiskering by a 1-morphism with faithful underlying functor is injective on
2-morphisms.** A 2-morphism of categories fibred in groupoids is a morphism of the underlying
functors, and right whiskering by `h` applies the functor underlying `h` to each of its
components; faithfulness of that functor therefore recovers each component, and two 2-morphisms
agreeing in every component are equal. -/
theorem hom₂_ext_of_whiskerRight_faithful
    {𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{v₁, v₂, u₁, u₂} 𝒞} {u v : 𝒳 ⟶ 𝒴} (h : 𝒴 ⟶ 𝒵)
    [(homFunctor h).Faithful] {η θ : u ⟶ v} (e : η ▷ h = θ ▷ h) : η = θ := by
  refine Bicategory.InducedBicategory.hom₂_ext (BasedNatTrans.ext _ _ (NatTrans.ext ?_))
  funext z
  exact (homFunctor h).map_injective (congrArg (fun t => t.hom.toNatTrans.app z) e)

end CategoryTheory.CatFiberedInGroupoids

end
