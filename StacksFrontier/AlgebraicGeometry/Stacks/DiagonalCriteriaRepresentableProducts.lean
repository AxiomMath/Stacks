module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteriaRepresentableSources

/-!
# The criteria for a representable diagonal: conditions (5) and (6) (Stacks 045G)

Let `S` be a scheme contained in a big fppf site `B` and let `𝒳` be a category fibred in groupoids
over the big fppf site of `S`. Condition (5) of Stacks 045G says that every 1-morphism to `𝒳` from
a representable category fibred in groupoids is representable by algebraic spaces, and condition
(6) says that the 2-fibre product over `𝒳` of any two such 1-morphisms is representable by an
algebraic space. The source calls this equivalence "formal": both conditions are about the same
2-fibre products, and a representable source may be replaced by the slice it is equivalent to.

The equivalence is obtained by comparing both conditions with condition (4), the one for 2-fibre
products of *scheme-valued* points. Condition (4) is equivalent to (5) in
`StacksFrontier/AlgebraicGeometry/Stacks/DiagonalCriteriaRepresentableSources.lean`, and it is
equivalent to (6) here, by replacing each factor of the 2-fibre product by an equivalent one:
downwards, each representable factor by the slice it represents; upwards, each slice by its
universe lift, which is what makes it an admissible argument of the quantifier of condition (6).

## Main results

* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_twoFibreProduct_precompose_iff`: the
  2-fibre product over `𝒳` of two 1-morphisms is representable by an algebraic space exactly when
  the one obtained by precomposing both with equivalences over the site is.
* `hasAlgebraicSpaceSchemePointProducts_iff_hasAlgebraicSpaceRepresentableProducts`, in the
  namespace `AlgebraicGeometry.Stack`: the equivalence of conditions (4) and (6).
* `representableFromCategories_iff_algebraicSpaceProducts`, in the same namespace:
  **Stacks 045G**, the equivalence of conditions (5) and (6).

## Implementation notes

The comparison of 2-fibre products is the composite of
`CategoryTheory.TwoFibreProductOver.precomposeSnd`, which replaces the second factor, and
`CategoryTheory.TwoFibreProductOver.precomposeFst`, which replaces the first; both commute with
the structure functor on the nose, so the composite is a 1-morphism *strictly* over the site and
`StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence` turns it into an equivalence in
the 2-category of categories over the site, which is what
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_iff_of_equivalenceOver` consumes.

Both directions of the equivalence of (4) and (6) are instances of the one comparison, with
different equivalences: `CategoryTheory.BasedCategory.uliftDown` going up, and the quasi-inverse
of a representing equivalence going down. The latter is extracted from
`Stacks.RepresentableMorphism.IsRepresentableCFG` exactly as in the equivalence of conditions (3)
and (5).

## References

* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
* [Stacks Project, Tag 02XA](https://stacks.math.columbia.edu/tag/02XA)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u v w v₁ w₁ v₂ w₂ a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS))

/-- **The 2-fibre product over `𝒳` does not see an equivalence of either factor.** If `t` and `s`
are 1-morphisms over the site whose underlying functors are equivalences, then the 2-fibre product
of `x` and `y` over `𝒳` is representable by an algebraic space exactly when the 2-fibre product of
`t ⋙ x` and `s ⋙ y` is.

The hypotheses that `t` and `s` are equivalences are explicit, not instance arguments: the total
categories are those of `CategoryTheory.BasedCategory`s, whose `Category` instance is not the one
instance search finds for the same type. -/
theorem isRepresentableByAlgebraicSpace_twoFibreProduct_precompose_iff
    (𝒯₁ : CatFiberedInGroupoids.{u, a₁, u + 1, b₁} (BigFppfOver B S hS))
    (𝒯₁' : CatFiberedInGroupoids.{u, a₂, u + 1, b₂} (BigFppfOver B S hS))
    (𝒯₂ : CatFiberedInGroupoids.{u, a₃, u + 1, b₃} (BigFppfOver B S hS))
    (𝒯₂' : CatFiberedInGroupoids.{u, a₄, u + 1, b₄} (BigFppfOver B S hS))
    (x : 𝒯₁.val ⥤ᵇ 𝒳.val) (y : 𝒯₂.val ⥤ᵇ 𝒳.val)
    (t : 𝒯₁'.val ⥤ᵇ 𝒯₁.val) (s : 𝒯₂'.val ⥤ᵇ 𝒯₂.val)
    (hte : Functor.IsEquivalence t.toFunctor) (hse : Functor.IsEquivalence s.toFunctor) :
    IsRepresentableByAlgebraicSpace B S hS (twoFibreProduct B S hS 𝒳 𝒯₁ 𝒯₂ x y) ↔
      IsRepresentableByAlgebraicSpace B S hS (twoFibreProduct B S hS 𝒳 𝒯₁' 𝒯₂'
        (BasedFunctor.comp t x) (BasedFunctor.comp s y)) := by
  have hsnd := TwoFibreProductOver.isEquivalence_precomposeSnd'
    (pT' := 𝒯₂'.val.p) (pT := 𝒯₂.val.p) (p𝒜 := 𝒯₁'.val.p) (pℬ := 𝒳.val.p)
    (Gl := y.toFunctor) (Fl := t.toFunctor ⋙ x.toFunctor) (t := s.toFunctor) (ht := s.w)
    𝒯₂'.isFiberedInGroupoids 𝒯₂.isFiberedInGroupoids 𝒯₁'.isFiberedInGroupoids hse y.w
  have hfst := TwoFibreProductOver.isEquivalence_precomposeFst
    𝒯₁'.val.p 𝒯₁.val.p 𝒯₂.val.p 𝒳.val.p x.toFunctor y.toFunctor t.toFunctor t.w
    𝒯₂.isFiberedInGroupoids 𝒯₁'.isFiberedInGroupoids 𝒯₁.isFiberedInGroupoids hte x.w
  obtain ⟨k⟩ := StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence
    (TwoFibreProductOver.isFiberedInGroupoids 𝒯₁'.val.p 𝒯₂'.val.p 𝒳.val.p
      (t.toFunctor ⋙ x.toFunctor) (s.toFunctor ⋙ y.toFunctor)
      𝒯₁'.isFiberedInGroupoids 𝒯₂'.isFiberedInGroupoids 𝒳.isFiberedInGroupoids
      (BasedFunctor.comp t x).w (BasedFunctor.comp s y).w)
    (TwoFibreProductOver.isFiberedInGroupoids 𝒯₁.val.p 𝒯₂.val.p 𝒳.val.p
      x.toFunctor y.toFunctor 𝒯₁.isFiberedInGroupoids 𝒯₂.isFiberedInGroupoids
      𝒳.isFiberedInGroupoids x.w y.w)
    (TwoFibreProductOver.precomposeSnd (pT := 𝒯₁'.val.p) (pℬ := 𝒳.val.p)
      (t.toFunctor ⋙ x.toFunctor) y.toFunctor s.toFunctor s.w ⋙
      TwoFibreProductOver.precomposeFst 𝒯₁'.val.p 𝒯₁.val.p 𝒯₂.val.p 𝒳.val.p
        x.toFunctor y.toFunctor t.toFunctor t.w) rfl inferInstance
  exact isRepresentableByAlgebraicSpace_iff_of_equivalenceOver k

/-- **Stacks 045G, the equivalence of conditions (4) and (6).** The 2-fibre product over `𝒳` of
two scheme-valued points of `𝒳` is representable by an algebraic space if and only if the 2-fibre
product over `𝒳` of any two representable categories fibred in groupoids is. -/
theorem hasAlgebraicSpaceSchemePointProducts_iff_hasAlgebraicSpaceRepresentableProducts :
    HasAlgebraicSpaceSchemePointProducts B S hS 𝒳 ↔
      HasAlgebraicSpaceRepresentableProducts.{u, v, w, v₁, w₁, v₂, w₂} B S hS 𝒳 := by
  refine ⟨fun h₄ 𝒯₁ 𝒯₂ ⟨X₁, E₁, hE₁⟩ ⟨X₂, E₂, hE₂⟩ x y => ?_, fun h₆ U V x y => ?_⟩
  · obtain ⟨G₁, hG₁, ⟨η₁, -⟩, ⟨ε₁, -⟩⟩ := hE₁.exists_inverse
    obtain ⟨G₂, hG₂, ⟨η₂, -⟩, ⟨ε₂, -⟩⟩ := hE₂.exists_inverse
    exact (isRepresentableByAlgebraicSpace_twoFibreProduct_precompose_iff B S hS 𝒳 𝒯₁
      (schemeFibredCategory B S hS X₁) 𝒯₂ (schemeFibredCategory B S hS X₂) x y
      ⟨G₁, hG₁.comm⟩ ⟨G₂, hG₂.comm⟩
      (CategoryTheory.Equivalence.mk G₁ E₁ η₁.symm ε₁).isEquivalence_functor
      (CategoryTheory.Equivalence.mk G₂ E₂ η₂.symm ε₂).isEquivalence_functor).2
      (h₄ X₁ X₂ (BasedFunctor.comp ⟨G₁, hG₁.comm⟩ x) (BasedFunctor.comp ⟨G₂, hG₂.comm⟩ y))
  · refine (isRepresentableByAlgebraicSpace_twoFibreProduct_precompose_iff B S hS 𝒳
      (schemeFibredCategory B S hS U)
      (CategoryTheory.CatFiberedInGroupoids.ulift.{u, u + 1, u, u + 1, v₁, w₁}
        (schemeFibredCategory B S hS U))
      (schemeFibredCategory B S hS V)
      (CategoryTheory.CatFiberedInGroupoids.ulift.{u, u + 1, u, u + 1, v₂, w₂}
        (schemeFibredCategory B S hS V)) x y
      ⟨BasedCategory.uliftDown (schemeFibredCategory B S hS U).val,
        BasedCategory.uliftDown_comp (schemeFibredCategory B S hS U).val⟩
      ⟨BasedCategory.uliftDown (schemeFibredCategory B S hS V).val,
        BasedCategory.uliftDown_comp (schemeFibredCategory B S hS V).val⟩
      ((BasedCategory.uliftEquivalenceOver
        (schemeFibredCategory B S hS U).val).isEquivalence_hom_functor)
      ((BasedCategory.uliftEquivalenceOver
        (schemeFibredCategory B S hS V).val).isEquivalence_hom_functor)).2 ?_
    refine h₆ _ _ ?_ ?_ _ _ <;>
      exact Stacks.RepresentableMorphism.isRepresentableCFG_of_isRepresentable _
        ⟨_, ⟨BasedCategory.uliftEquivalenceOver (schemeFibredCategory B S hS _).val⟩⟩

/-- **Stacks 045G, the equivalence of conditions (5) and (6).** Every 1-morphism to `𝒳` from a
representable category fibred in groupoids is representable by algebraic spaces if and only if the
2-fibre product over `𝒳` of any two such 1-morphisms is representable by an algebraic space. -/
@[stacks 045G "parts (5) and (6)"]
theorem representableFromCategories_iff_algebraicSpaceProducts :
    IsRepresentableFromRepresentableCategories.{u, v, w, v₁, w₁} B S hS 𝒳 ↔
      HasAlgebraicSpaceRepresentableProducts.{u, v, w, v₁, w₁, v₂, w₂} B S hS 𝒳 :=
  (hasAlgebraicSpaceSchemePointProducts_iff_isRepresentableFromRepresentableCategories
      B S hS 𝒳).symm.trans
    (hasAlgebraicSpaceSchemePointProducts_iff_hasAlgebraicSpaceRepresentableProducts B S hS 𝒳)

end AlgebraicGeometry.Stack

end
