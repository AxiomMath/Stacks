module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianSpaces
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStackMapProperties
public import StacksFrontier.AlgebraicGeometry.Stacks.ProperClosedImmersionAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.ProperCompositionAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.ReducedInducedStructureClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveProperties

/-!
# Reductions in the proof of Chow's lemma for algebraic stacks

Let `f : 𝒳 ⟶ Y` be a 1-morphism from an algebraic stack to an algebraic space. Chow's lemma
(Stacks 0CQ8) produces, when `Y` is quasi-compact and quasi-separated and `f` is separated of
finite type, a proper surjective `X ⟶ 𝒳` from an algebraic space together with an open immersion
`X ⟶ X̄` into an algebraic space proper over `Y`, compatible over `Y`. This file names that
conclusion and proves the reductions of the source's proof which only move the cover around.

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.HasChowCover`: the conclusion of Stacks 0CQ8 for `f`.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.HasChowCover.of_proper`: the conclusion descends
  along a proper morphism of algebraic spaces `Y' ⟶ Y` covered by a proper surjective
  1-morphism `𝒳' ⟶ 𝒳`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.HasChowCover.of_comp`: the conclusion for `a ≫ f`
  gives it for `f` when `a` is proper and surjective.
* `AlgebraicGeometry.Stack.AlgebraicStacks.HasChowCover.of_reduction`: the step "we may replace
  `𝒳` by its reduction" of the proof of Stacks 0CQ8 (Stacks 050C).
* `AlgebraicGeometry.Stack.AlgebraicStacks.HasChowCover.of_forall_isReducedStack`: over a
  Noetherian base, Chow's lemma reduces to reduced algebraic stacks.

## References

* [Stacks Project, Tag 0CQ8](https://stacks.math.columbia.edu/tag/0CQ8)
* [Stacks Project, Tag 050C](https://stacks.math.columbia.edu/tag/050C)
-/

@[expose] public section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The conclusion of Chow's lemma (Stacks 0CQ8)** for a 1-morphism `f : 𝒳 ⟶ Y` from an
algebraic stack to an algebraic space: there are algebraic spaces `X` and `X̄`, a proper
surjective 1-morphism `a : X ⟶ 𝒳`, an open immersion `i : X ⟶ X̄` and a proper morphism
`p : X̄ ⟶ Y` of algebraic spaces with `a ≫ f` 2-isomorphic to `i ≫ p`. -/
def HasChowCover {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    {𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY) :
    Prop :=
  ∃ (X Xbar : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
    (_hXbar : IsAlgebraicSpace B S hS Xbar)
    (a : algebraicSpaceStack.{u, w} B S hS X hX ⟶ 𝒳) (i : X ⟶ Xbar) (p : Xbar ⟶ Y),
    IsProper B S hS a ∧ IsSurjective B S hS a ∧ Space.IsOpenImmersion B S hS i ∧
      Space.IsProper B S hS p ∧
      Nonempty (a ≫ f ≅ algebraicSpaceStackMap.{u, w} B S hS hX hY (i ≫ p))

/-- The algebraic stack map of a composite of morphisms of algebraic spaces is the composite of
the algebraic stack maps. -/
theorem algebraicSpaceStackMap_comp {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (g : X ⟶ Y) (h : Y ⟶ Z) :
    algebraicSpaceStackMap.{u, w} B S hS hX hZ (g ≫ h) =
      algebraicSpaceStackMap.{u, w} B S hS hX hY g ≫
        algebraicSpaceStackMap.{u, w} B S hS hY hZ h := by
  simp only [algebraicSpaceStackMap, associatedMap_comp]
  rfl

/-- **Chow covers descend along proper covers.** Let `f : 𝒳 ⟶ Y` and `f' : 𝒳' ⟶ Y'` be
1-morphisms from algebraic stacks to algebraic spaces, `q : Y' ⟶ Y` a proper morphism of
algebraic spaces and `b : 𝒳' ⟶ 𝒳` a proper surjective 1-morphism with `b ≫ f` 2-isomorphic to
`f' ≫ q`. If the conclusion of Stacks 0CQ8 holds for `f'`, it holds for `f`: compose the cover
with `b` and the compactification with `q`. -/
theorem HasChowCover.of_proper {Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) (hY' : IsAlgebraicSpace B S hS Y')
    {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)
    (f' : 𝒳' ⟶ algebraicSpaceStack.{u, w} B S hS Y' hY')
    (q : Y' ⟶ Y) (hq : Space.IsProper B S hS q) (b : 𝒳' ⟶ 𝒳) (hb : IsProper B S hS b)
    (hbs : IsSurjective B S hS b)
    (e : b ≫ f ≅ f' ≫ algebraicSpaceStackMap.{u, w} B S hS hY' hY q)
    (h' : HasChowCover.{u, w} B S hS hY' f') :
    HasChowCover.{u, w} B S hS hY f := by
  obtain ⟨X, Xbar, hX, hXbar, a, i, p, ha, has, hi, hp, ⟨ea⟩⟩ := h'
  have hcomp := algebraicSpaceStackMap_comp B S hS hX hY' hY (i ≫ p) q
  exact ⟨X, Xbar, hX, hXbar, a ≫ b, i, p ≫ q, isProper_comp B S hS a b ha hb,
    isSurjective_comp B S hS a b has hbs, hi, Space.isProper_comp B S hS hXbar hY' hY p q hp hq,
    ⟨Bicategory.associator _ _ _ ≪≫ Bicategory.whiskerLeftIso a e ≪≫
      (Bicategory.associator _ _ _).symm ≪≫ Bicategory.whiskerRightIso ea _ ≪≫
      eqToIso (by simpa using hcomp.symm)⟩⟩

/-- **Chow covers descend along proper surjective 1-morphisms over the same base.** If
`b : 𝒳' ⟶ 𝒳` is proper and surjective and the conclusion of Stacks 0CQ8 holds for `b ≫ f`, it
holds for `f`. -/
theorem HasChowCover.of_comp {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY) (b : 𝒳' ⟶ 𝒳) (hb : IsProper B S hS b)
    (hbs : IsSurjective B S hS b) (h' : HasChowCover.{u, w} B S hS hY (b ≫ f)) :
    HasChowCover.{u, w} B S hS hY f := by
  obtain ⟨X, Xbar, hX, hXbar, a, i, p, ha, has, hi, hp, ⟨ea⟩⟩ := h'
  exact ⟨X, Xbar, hX, hXbar, a ≫ b, i, p, isProper_comp B S hS a b ha hb,
    isSurjective_comp B S hS a b has hbs, hi, hp,
    ⟨Bicategory.associator _ _ _ ≪≫ ea⟩⟩

/-- **The reduction step of the proof of Stacks 0CQ8.** If the conclusion of Chow's lemma holds
for the composite `𝒳_red ⟶ 𝒳 ⟶ Y` of the inclusion of the reduction (Stacks 050C) with `f`, it
holds for `f`: the inclusion is a closed immersion, hence proper, and surjective. -/
theorem HasChowCover.of_reduction {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)
    (h' : HasChowCover.{u, w} B S hS hY ((stackReduction 𝒳).inclusion ≫ f)) :
    HasChowCover.{u, w} B S hS hY f :=
  HasChowCover.of_comp B S hS hY f _
    (isProper_of_isClosedImmersion B S hS _ (stackReduction 𝒳).isClosedImmersion)
    (stackReduction 𝒳).isSurjective_inclusion h'

/-- The composite of the inclusion of the reduction with a separated 1-morphism of finite type
is separated and of finite type. -/
theorem isSeparated_and_isFiniteType_reduction_comp {𝒴 𝒳 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (hsep : IsSeparated B S hS f) (hft : IsFiniteType B S hS f) :
    IsSeparated B S hS ((stackReduction 𝒳).inclusion ≫ f) ∧
      IsFiniteType B S hS ((stackReduction 𝒳).inclusion ≫ f) := by
  have hP := isProper_of_isClosedImmersion B S hS _ (stackReduction 𝒳).isClosedImmersion
  exact ⟨isSeparated_comp B S hS _ f hP.1 hsep, isFiniteType_comp B S hS _ f hP.2.1 hft⟩

/-- **The reduction step of the proof of Stacks 0CQ8, over a Noetherian base.** If the
conclusion of Chow's lemma holds for every separated 1-morphism of finite type from a *reduced*
algebraic stack to a Noetherian algebraic space, it holds without the reducedness: replace `𝒳` by
its reduction (Stacks 050C). -/
theorem HasChowCover.of_forall_isReducedStack
    (hred : ∀ (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hY : IsAlgebraicSpace B S hS Y),
      Space.IsNoetherian B S hS B.contains_terminal Y →
      ∀ (𝒳 : AlgebraicStacks.{u, w} B S hS) (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY),
        IsReducedStack B S hS 𝒳 → IsSeparated B S hS f → IsFiniteType B S hS f →
          HasChowCover.{u, w} B S hS hY f)
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (hYN : Space.IsNoetherian B S hS B.contains_terminal Y)
    {𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)
    (hsep : IsSeparated B S hS f) (hft : IsFiniteType B S hS f) :
    HasChowCover.{u, w} B S hS hY f := by
  obtain ⟨hsep', hft'⟩ := isSeparated_and_isFiniteType_reduction_comp B S hS f hsep hft
  exact HasChowCover.of_reduction B S hS hY f
    (hred Y hY hYN _ _ (stackReduction 𝒳).isReducedStack hsep' hft')

end AlgebraicGeometry.Stack.AlgebraicStacks

end
