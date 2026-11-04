module

public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentabilityTransport
public import StacksFrontier.AlgebraicGeometry.Stacks.SecondDiagonal
public import StacksFrontier.CategoryTheory.FiberedCategory.IsoOver
public import StacksFrontier.CategoryTheory.FiberedCategory.InertiaBasedCategory
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverCompare

/-!
# The second diagonal and the neutral section of the inertia

Let `S` be a scheme contained in a big fppf site `B` and let `𝒳` be a category fibred in
groupoids over the big fppf site of `S`. The target `𝒳 ×_{Δ, 𝒳 × 𝒳, Δ} 𝒳` of the second diagonal

`Δ_Δ : 𝒳 ⟶ 𝒳 ×_{Δ, 𝒳 × 𝒳, Δ} 𝒳`

is equivalent over the site to the inertia `I_𝒳` of `𝒳`, and under this equivalence `Δ_Δ` is the
neutral section `x ↦ (x, 𝟙 x)` of the inertia. Hence `Δ_Δ` is representable by algebraic spaces
exactly when the neutral section of the inertia is.

## Main definitions

* `AlgebraicGeometry.Stack.inertia`: the inertia `I_𝒳` of `𝒳`, as a category fibred in groupoids
  over the big fppf site of `S`.
* `AlgebraicGeometry.Stack.inertiaNeutralSection`: the neutral section `x ↦ (x, 𝟙 x)` of the
  inertia of `𝒳`.

## Main results

* `AlgebraicGeometry.Stack.isFiberedInGroupoids_relativeInertiaStruct`: the inertia of a category
  fibred in groupoids over the site is again fibred in groupoids.
* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_secondDiagonal_iff_neutralSection`:
  the second diagonal of `𝒳` is representable by algebraic spaces if and only if the neutral
  section of the inertia of `𝒳` is.

## References

* [Stacks Project, Tag 07WG](https://stacks.math.columbia.edu/tag/07WG)
* [Stacks Project, Tag 034H](https://stacks.math.columbia.edu/tag/034H)
* [Stacks Project, Tag 0457](https://stacks.math.columbia.edu/tag/0457)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u v w v' w'

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS))

/-- The second 2-fibre product of the diagonal of `𝒳`, as an object of the 2-category of
categories fibred in groupoids over the big fppf site of `S`. -/
private abbrev secondDiagonalTarget :
    CatFiberedInGroupoids.{u, max u v, u + 1, max (max (u + 1) w) v} (BigFppfOver B S hS) :=
  twoFibreProduct B S hS (CatFiberedInGroupoids.product 𝒳 𝒳) 𝒳 𝒳
    (diagonalBasedFunctor B S hS 𝒳) (diagonalBasedFunctor B S hS 𝒳)

/-- The inertia of a category fibred in groupoids over the big fppf site of `S` is fibred in
groupoids. -/
lemma isFiberedInGroupoids_relativeInertiaStruct :
    (relativeInertiaStruct 𝒳.val.p 𝒳.val.p).IsFiberedInGroupoids := by
  obtain ⟨E⟩ :=
    TwoFibreProductOver.isEquivalenceOver_toRelativeInertia (Functor.comp_id 𝒳.val.p)
  exact Functor.IsFiberedInGroupoids.of_isEquivalenceOver
    (TwoFibreProductOver.toRelativeInertia_comp_relativeInertiaStruct
      (Functor.comp_id 𝒳.val.p))
    (StacksRepresentableCFG.EquivalenceOver.toFunctorIsEquivalenceOver
      (StacksRepresentableCFG.EquivalenceOver.ofIsEquivalenceOver E))
    (secondDiagonalTarget B S hS 𝒳).isFiberedInGroupoids

/-- The inertia `I_𝒳` of `𝒳`, as an object of the 2-category of categories fibred in groupoids
over the big fppf site of `S`. Its objects are the pairs `(x, α)` with `x` an object of `𝒳` and
`α` an automorphism of `x` in the fibre of `𝒳` over `𝒳.p x`. -/
abbrev inertia : CatFiberedInGroupoids.{u, v, u + 1, max w v} (BigFppfOver B S hS) :=
  CatFiberedInGroupoids.mk
    (RelativeInertia.basedCategory
      (𝒴 := BasedCategory.ofFunctor (𝟭 (BigFppfOver B S hS)))
      ⟨𝒳.val.p, Functor.comp_id 𝒳.val.p⟩)
    (isFiberedInGroupoids_relativeInertiaStruct B S hS 𝒳)

/-- The neutral section `x ↦ (x, 𝟙 x)` of the inertia of `𝒳`, as a 1-morphism of categories over
the big fppf site of `S`. -/
abbrev inertiaNeutralSection : 𝒳.val ⥤ᵇ (inertia B S hS 𝒳).val where
  toFunctor := RelativeInertia.neutralSection 𝒳.val.p
  w := rfl

/-- The second diagonal `𝒳 ⟶ 𝒳 ×_{Δ, 𝒳 × 𝒳, Δ} 𝒳` is representable by algebraic spaces if and
only if the neutral section of the inertia of `𝒳` is. -/
theorem isRepresentableByAlgebraicSpaces_secondDiagonal_iff_neutralSection :
    IsRepresentableByAlgebraicSpaces B S hS
        (relativeDiagonalBasedFunctor B S hS 𝒳 (CatFiberedInGroupoids.product 𝒳 𝒳)
          (diagonalBasedFunctor B S hS 𝒳)) ↔
      IsRepresentableByAlgebraicSpaces B S hS (inertiaNeutralSection B S hS 𝒳) := by
  obtain ⟨E⟩ :=
    TwoFibreProductOver.isEquivalenceOver_toRelativeInertia (Functor.comp_id 𝒳.val.p)
  refine (isRepresentableByAlgebraicSpaces_iff_of_equivalenceOver_target B S hS
    (𝒴' := secondDiagonalTarget B S hS 𝒳) (𝒴 := inertia B S hS 𝒳)
    (inertiaNeutralSection B S hS 𝒳)
    (relativeDiagonalBasedFunctor B S hS 𝒳 (CatFiberedInGroupoids.product 𝒳 𝒳)
      (diagonalBasedFunctor B S hS 𝒳))
    (StacksRepresentableCFG.EquivalenceOver.ofIsEquivalenceOver E)
    (eqToIso (BasedCategory.BasedFunctor.ext'
      (TwoFibreProductOver.diagonal_comp_toRelativeInertia
        (Functor.comp_id 𝒳.val.p)).symm))).symm

end AlgebraicGeometry.Stack

end
