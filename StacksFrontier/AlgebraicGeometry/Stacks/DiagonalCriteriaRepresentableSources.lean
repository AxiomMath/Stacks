module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteriaSchemePoints
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentabilityTransport
public import StacksFrontier.CategoryTheory.FiberedCategory.UliftBasedCategory

/-!
# The criteria for a representable diagonal: conditions (4) and (5) (Stacks 045G)

Let `S` be a scheme contained in a big fppf site `B` and let `𝒳` be a category fibred in groupoids
over the big fppf site of `S`. Condition (3) of Stacks 045G is that every 1-morphism to `𝒳` from
the category represented by a *scheme* over `S` is representable by algebraic spaces, and condition
(5) is the same with "scheme" replaced by "representable category fibred in groupoids". The source
says these are equivalent by Stacks 0457 — representability by algebraic spaces is invariant under
an equivalence of the source — and so they are: a representable category fibred in groupoids is by
definition equivalent over the site to a slice, and a slice is the category represented by a
scheme.

Condition (4), the one about 2-fibre products, is then equivalent to (5) through the equivalence of
(3) and (4) proved in
`StacksFrontier/AlgebraicGeometry/Stacks/DiagonalCriteriaSchemePoints.lean`.

## Main results

* `isRepresentableFromSchemes_iff_isRepresentableFromRepresentableCategories`, in the namespace
  `AlgebraicGeometry.Stack`: the equivalence of conditions (3) and (5).
* `hasAlgebraicSpaceSchemePointProducts_iff_isRepresentableFromRepresentableCategories`, in the
  same namespace: **Stacks 045G**, the equivalence of conditions (4) and (5).

## Implementation notes

The direction (3) to (5) is Stacks 0457 as it stands: a representable category fibred in groupoids
`𝒯` comes with a quasi-inverse `G : 𝒞/X ⥤ 𝒯` of the representing equivalence, strictly over the
site, and `G` composed with the given 1-morphism is a 1-morphism out of the category represented by
the scheme `X`, to which condition (3) applies. Stacks 0457 then transports representability back
along `G`.

The direction (5) to (3) is the same transport in the other direction, but it needs a *universe
lift*: condition (5) quantifies over categories fibred in groupoids at the universes
`(max u v₁, max (u+1) w₁)`, and the slice of the site over a scheme lives at `(u, u+1)`. The
lifted slice `CategoryTheory.CatFiberedInGroupoids.ulift` is a category fibred in groupoids at the
right universes, is representable — it is equivalent over the site to the slice, and
`Stacks.RepresentableMorphism.isRepresentableCFG_of_isRepresentable` converts that into the
source's notion — and the 1-morphism out of it is the given one precomposed with
`CategoryTheory.BasedCategory.uliftDown`.

`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_iff_of_equivalence_source` takes the
hypothesis that the comparison 1-morphism is an equivalence as an *instance* argument, which
instance search cannot discharge here: the categories involved are the total categories of
`CategoryTheory.BasedCategory`s built with `CategoryTheory.BasedCategory.ofFunctor`, whose
`Category` instance is not the one instance search finds for the same type. The wrapper
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_iff_of_equivalence_source'` takes it
explicitly, which is all that is needed, since inside the wrapper the comparison is a variable.

## References

* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
* [Stacks Project, Tag 0457](https://stacks.math.columbia.edu/tag/0457)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u v w v₁ w₁ t₁ t₂ t₃ s₁ s₂ s₃

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0457 for a precomposition.** Precomposing a 1-morphism with an equivalence of the
source over the site does not change representability by algebraic spaces.

This is `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_iff_of_equivalence_source` with
the comparison 2-cell taken to be the identity and with the hypothesis that the comparison
1-morphism is an equivalence supplied *explicitly*: instance search cannot find it, because the
total categories involved are those of `CategoryTheory.BasedCategory`s built with
`CategoryTheory.BasedCategory.ofFunctor`, whose `Category` instance is not the one instance search
finds for the same type. The three categories fibred in groupoids are explicit arguments so that
the 1-morphism may be given as an anonymous constructor. -/
theorem isRepresentableByAlgebraicSpaces_comp_iff
    (𝒳' : CatFiberedInGroupoids.{u, t₁, u + 1, s₁} (BigFppfOver B S hS))
    (𝒳 : CatFiberedInGroupoids.{u, t₂, u + 1, s₂} (BigFppfOver B S hS))
    (𝒴 : CatFiberedInGroupoids.{u, t₃, u + 1, s₃} (BigFppfOver B S hS))
    (f : 𝒳.val ⥤ᵇ 𝒴.val) (a : 𝒳'.val ⥤ᵇ 𝒳.val) (hae : Functor.IsEquivalence a.toFunctor) :
    IsRepresentableByAlgebraicSpaces B S hS f ↔
      IsRepresentableByAlgebraicSpaces B S hS (BasedFunctor.comp a f) := by
  have _ := hae
  exact isRepresentableByAlgebraicSpaces_iff_of_equivalence_source B S hS f
    (BasedFunctor.comp a f) a (Iso.refl _)

variable (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS))

/-- **Stacks 045G, the equivalence of conditions (3) and (5).** Every 1-morphism to `𝒳` from the
category represented by a scheme over `S` is representable by algebraic spaces if and only if every
1-morphism to `𝒳` from a representable category fibred in groupoids is. -/
theorem isRepresentableFromSchemes_iff_isRepresentableFromRepresentableCategories :
    IsRepresentableFromSchemes B S hS 𝒳 ↔
      IsRepresentableFromRepresentableCategories.{u, v, w, v₁, w₁} B S hS 𝒳 := by
  constructor
  · rintro h₃ 𝒯 ⟨X, E, hE⟩ x
    obtain ⟨G, hG, ⟨η, -⟩, ⟨ε, -⟩⟩ := hE.exists_inverse
    exact (isRepresentableByAlgebraicSpaces_comp_iff B S hS (schemeFibredCategory B S hS X) 𝒯 𝒳
      x ⟨G, hG.comm⟩ (CategoryTheory.Equivalence.mk G E η.symm ε).isEquivalence_functor).2
      (h₃ X (BasedFunctor.comp ⟨G, hG.comm⟩ x))
  · intro h₅ U x
    refine (isRepresentableByAlgebraicSpaces_comp_iff B S hS
      (CatFiberedInGroupoids.ulift.{u, u + 1, u, u + 1, v₁, w₁}
        (schemeFibredCategory B S hS U))
      (schemeFibredCategory B S hS U) 𝒳 x
      ⟨BasedCategory.uliftDown (schemeFibredCategory B S hS U).val,
        BasedCategory.uliftDown_comp (schemeFibredCategory B S hS U).val⟩
      ((BasedCategory.uliftEquivalenceOver
        (schemeFibredCategory B S hS U).val).isEquivalence_hom_functor)).2 ?_
    refine h₅ (CatFiberedInGroupoids.ulift.{u, u + 1, u, u + 1, v₁, w₁}
      (schemeFibredCategory B S hS U)) ?_ _
    exact Stacks.RepresentableMorphism.isRepresentableCFG_of_isRepresentable _
      ⟨U, ⟨BasedCategory.uliftEquivalenceOver (schemeFibredCategory B S hS U).val⟩⟩

/-- **Stacks 045G, the equivalence of conditions (4) and (5).** The 2-fibre product over `𝒳` of
any two scheme-valued points of `𝒳` is representable by an algebraic space if and only if every
1-morphism to `𝒳` from a representable category fibred in groupoids is representable by algebraic
spaces. -/
@[stacks 045G "parts (4) and (5)"]
theorem hasAlgebraicSpaceSchemePointProducts_iff_isRepresentableFromRepresentableCategories :
    HasAlgebraicSpaceSchemePointProducts B S hS 𝒳 ↔
      IsRepresentableFromRepresentableCategories.{u, v, w, v₁, w₁} B S hS 𝒳 :=
  (isRepresentableFromSchemes_iff_hasAlgebraicSpaceSchemePointProducts B S hS 𝒳).symm.trans
    (isRepresentableFromSchemes_iff_isRepresentableFromRepresentableCategories B S hS 𝒳)

end AlgebraicGeometry.Stack

end
