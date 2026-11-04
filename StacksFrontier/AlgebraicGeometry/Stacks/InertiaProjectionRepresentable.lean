module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.BaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentabilityTransport
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverCompare
public import StacksFrontier.AlgebraicGeometry.Stacks.SecondDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStack
public import StacksFrontier.CategoryTheory.FiberedCategory.InertiaBasedCategory

/-!
# The projection of the inertia is representable by algebraic spaces

Let `S` be a scheme contained in a big fppf site `B` and let `𝒳` be a category fibred in
groupoids over the big fppf site of `S` whose diagonal `Δ : 𝒳 ⟶ 𝒳 × 𝒳` is representable by
algebraic spaces. Then the forgetful 1-morphism `π : I_𝒳 ⟶ 𝒳` of the inertia of `𝒳` is
representable by algebraic spaces. In particular this holds for every algebraic stack `𝒳`.

## Main results

* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_inertiaProjection`: the projection of
  the absolute inertia is representable by algebraic spaces when the diagonal is.
* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_inertiaProjection_of_isAlgebraicStack`:
  the same for an algebraic stack.

## Implementation notes

The inertia appears as `CategoryTheory.RelativeInertia.basedCategory` of the 1-morphism
`⟨𝒳.p, rfl⟩` from `𝒳` to the final object `CategoryTheory.BasedCategory.ofFunctor (𝟭 _)` of the
categories over the site, the absolute case of the relative inertia.

`𝒳` has morphism universe `max u v` and object universe `max (u + 1) v w` for the site universe
`u`, so that `𝒳 × 𝒳` is an object of the same 2-category as `𝒳`.

## References

* [Stacks Project, Tag 050Q](https://stacks.math.columbia.edu/tag/050Q)
* [Stacks Project, Tag 034H](https://stacks.math.columbia.edu/tag/034H)
* [Stacks Project, Tag 0302](https://stacks.math.columbia.edu/tag/0302)
* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u v w t

/-- If the diagonal of a category fibred in groupoids `𝒳` over the big fppf site of `S` is
representable by algebraic spaces, then so is the forgetful 1-morphism `π : I_𝒳 ⟶ 𝒳` of its
inertia. -/
@[stacks 050Q "representability by algebraic spaces of the absolute inertia projection"]
theorem isRepresentableByAlgebraicSpaces_inertiaProjection
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 : CatFiberedInGroupoids.{u, max u v, u + 1, max (u + 1) v w} (BigFppfOver B S hS))
    (hΔ : IsRepresentableByAlgebraicSpaces B S hS (diagonalBasedFunctor B S hS 𝒳)) :
    IsRepresentableByAlgebraicSpaces B S hS
      (RelativeInertia.basedProjection
        (𝒴 := BasedCategory.ofFunctor (𝟭 (BigFppfOver B S hS)))
        ⟨𝒳.val.p, rfl⟩) := by
  have hG : 𝒳.val.p ⋙ 𝟭 (BigFppfOver B S hS) = 𝒳.val.p := Functor.comp_id 𝒳.val.p
  set P := CatFiberedInGroupoids.twoFibreProductSquare.{u, v, u + 1, w}
    (diagonal B S hS 𝒳) (diagonal B S hS 𝒳)
  have h1 : IsRepresentableByAlgebraicSpaces B S hS P.fst.hom :=
    isRepresentableByAlgebraicSpaces_baseChange.{u, v, w} B S hS 𝒳
      (CatFiberedInGroupoids.product 𝒳 𝒳) 𝒳 (diagonal B S hS 𝒳) (diagonal B S hS 𝒳) P
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, v, u + 1, w}
        (diagonal B S hS 𝒳) (diagonal B S hS 𝒳)) hΔ
  obtain ⟨E⟩ := TwoFibreProductOver.isEquivalenceOver_toRelativeInertia hG
  have e : StacksRepresentableCFG.EquivalenceOver
      (RelativeInertia.basedCategory
        (𝒴 := BasedCategory.ofFunctor (𝟭 (BigFppfOver B S hS))) ⟨𝒳.val.p, rfl⟩).p
      P.pt.val.p :=
    (StacksRepresentableCFG.EquivalenceOver.ofIsEquivalenceOver E).symm
  have hinertia : (RelativeInertia.basedCategory
      (𝒴 := BasedCategory.ofFunctor (𝟭 (BigFppfOver B S hS)))
        ⟨𝒳.val.p, rfl⟩).p.IsFiberedInGroupoids :=
    StacksRepresentableCFG.isFiberedInGroupoids_of_equivalenceOver e P.pt.isFiberedInGroupoids
  let aFun : (RelativeInertia.basedCategory
      (𝒴 := BasedCategory.ofFunctor (𝟭 (BigFppfOver B S hS))) ⟨𝒳.val.p, rfl⟩) ⥤ᵇ P.pt.val :=
    ⟨TwoFibreProductOver.ofRelativeInertia hG,
      TwoFibreProductOver.ofRelativeInertia_comp_structureFunctor hG⟩
  have hequiv : Functor.IsEquivalence aFun.toFunctor :=
    (CategoryTheory.Equivalence.mk (TwoFibreProductOver.ofRelativeInertia hG)
      (TwoFibreProductOver.toRelativeInertia hG)
      (eqToIso (TwoFibreProductOver.ofRelativeInertia_comp_toRelativeInertia hG).symm)
      (TwoFibreProductOver.unitIso hG).symm).isEquivalence_functor
  exact (isRepresentableByAlgebraicSpaces_iff_of_equivalence_source B S hS
    (𝒳' := CatFiberedInGroupoids.mk _ hinertia) (𝒳 := P.pt) (𝒴 := 𝒳)
    P.fst.hom
    (RelativeInertia.basedProjection (𝒴 := BasedCategory.ofFunctor (𝟭 (BigFppfOver B S hS)))
      ⟨𝒳.val.p, rfl⟩)
    aFun (Iso.refl _)).mp h1

/-- The forgetful 1-morphism `π : I_𝒳 ⟶ 𝒳` of the inertia of an algebraic stack `𝒳` is
representable by algebraic spaces. -/
@[stacks 050Q "the inertia projection of an algebraic stack is representable by spaces"]
theorem isRepresentableByAlgebraicSpaces_inertiaProjection_of_isAlgebraicStack
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 : CatFiberedInGroupoids.{u, max u v, u + 1, max (u + 1) v w} (BigFppfOver B S hS))
    (h𝒳 : IsAlgebraicStack.{u, t} B S hS 𝒳.val) :
    IsRepresentableByAlgebraicSpaces B S hS
      (RelativeInertia.basedProjection
        (𝒴 := BasedCategory.ofFunctor (𝟭 (BigFppfOver B S hS)))
        ⟨𝒳.val.p, rfl⟩) :=
  isRepresentableByAlgebraicSpaces_inertiaProjection B S hS 𝒳 h𝒳.2.2.1


end AlgebraicGeometry.Stack

end
