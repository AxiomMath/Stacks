module

public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.PointInfinityFibreIntersectionDifference
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 0B07 part (3) at a presented pair of sections

`Stacks.Chow.PointCycle.IsPointFibreIntersectionDifference` is the shape of part (3) at a pair
`t`, `t'` of points of the affine chart, and
`Stacks.Chow.PointCycle.IsPointInfinityFibreIntersectionDifference` is its shape at the pair
`(t, ∞)`. This file defines the common shape at an arbitrary pair of sections
`s₁ s₂ : X ⟶ X ×_S ℙ¹_S`, and proves part (3) at a pair of distinct sections each of which is
`pointSection p t` for some `t` or `infinitySection p`.

## Main definitions

* `Stacks.Chow.PointCycle.IsSectionPairFibreIntersectionDifference`: a `k`-cycle `β` on `X` is
  `pr_{X,*}(α · X × s₁ - α · X × s₂)` for a `(k + 1)`-cycle `α` on `X ×_S ℙ¹_S` no component of
  which is contained in `s₁` or `s₂`.

## Main results

* `Stacks.Chow.PointCycle.isSectionPairFibreIntersectionDifference_swap`: swapping the two
  sections negates the cycle.
* `isSectionPairFibreIntersectionDifference_of_isPointFibreIntersectionDifference` and
  `isSectionPairFibreIntersectionDifference_of_isPointInfinityFibreIntersectionDifference`
  (in `Stacks.Chow.PointCycle`): the two restricted shapes are instances of the shape at a pair
  of sections.
* `Stacks.Chow.PointCycle.isSectionPairFibreIntersectionDifference_of_mem_rationalEquivalences`:
  every `k`-cycle rationally equivalent to zero has the shape at a pair of distinct sections
  `s₁`, `s₂`, each equal to `pointSection p t` for some `t` or to `infinitySection p`.

## References

* [Stacks Project, Tag 0B07](https://stacks.math.columbia.edu/tag/0B07)
-/

@[expose] public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.TorFormula CategoryTheory CategoryTheory.Limits
  TopologicalSpace

universe u

attribute [local instance 100000] HasDerivedCategory.standard

namespace Stacks.Chow

namespace PointCycle

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]

section PartThreePair

section

variable [AlgebraicGeometry.IsIntegral X] (hY : IsRegular (projectiveLineProduct p)) (k : ℤ)

/-- **The shape of Tag 0B07 part (3) at an arbitrary pair of sections.** A `k`-cycle `β` on `X`
is of the form `pr_{X,*}(α · X × s₁ - α · X × s₂)` for a `(k + 1)`-cycle `α` on `X ×_S ℙ¹_S` no
component of which is contained in the section `s₁` or the section `s₂`. -/
def IsSectionPairFibreIntersectionDifference (s₁ s₂ : X ⟶ projectiveLineProduct p)
    (β : CycleGroup C p k) : Prop :=
  ∃ (α : CycleGroup C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) (k + 1))
    (_ : ∀ x ∈ Function.support α.1,
      ¬ Set.range (integralComponentAt x).subschemeι ⊆ Set.range s₁)
    (_ : ∀ x ∈ Function.support α.1,
      ¬ Set.range (integralComponentAt x).subschemeι ⊆ Set.range s₂)
    (m₁ : haveI : IsLocallyNoetherian (projectiveLineProduct p) :=
            LocallyOfFiniteType.isLocallyNoetherian
              (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
          torFormulaCycleIntersectionProduct C
              (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY k α.1
              (@Function.locallyFinsuppWithin.single (projectiveLineProduct p) _ ℤ
                (Classical.decEq _) _ (s₁ (genericPoint X)) (1 : ℤ)) ∈
            cyclesOfDimension C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) k)
    (m₂ : haveI : IsLocallyNoetherian (projectiveLineProduct p) :=
            LocallyOfFiniteType.isLocallyNoetherian
              (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
          torFormulaCycleIntersectionProduct C
              (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY k α.1
              (@Function.locallyFinsuppWithin.single (projectiveLineProduct p) _ ℤ
                (Classical.decEq _) _ (s₂ (genericPoint X)) (1 : ℤ)) ∈
            cyclesOfDimension C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) k),
    β =
      properPushforward C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) p
          (pullback.fst p (relativeProjectiveLine C.S ↘ C.S)) rfl k ⟨_, m₁⟩ -
        properPushforward C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) p
          (pullback.fst p (relativeProjectiveLine C.S ↘ C.S)) rfl k ⟨_, m₂⟩

/-- The shape at an arbitrary pair is symmetric up to negation: swapping the two sections
negates the cycle. -/
theorem isSectionPairFibreIntersectionDifference_swap
    {s₁ s₂ : X ⟶ projectiveLineProduct p} {β : CycleGroup C p k}
    (h : IsSectionPairFibreIntersectionDifference C p hY k s₁ s₂ β) :
    IsSectionPairFibreIntersectionDifference C p hY k s₂ s₁ (-β) := by
  obtain ⟨α, h₁, h₂, m₁, m₂, rfl⟩ := h
  exact ⟨α, h₂, h₁, m₂, m₁, neg_sub _ _⟩

end

variable (hY : IsRegular (projectiveLineProduct p)) (k : ℤ) (Kf : Type u) [Field Kf]
  (hC : C.S = AlgebraicGeometry.Spec (CommRingCat.of Kf))
  [AlgebraicGeometry.IsVariety Kf (p ≫ eqToHom hC)]

/-- The shape at the pair `(t, t')` of `IsPointFibreIntersectionDifference` is the shape at the
pair of sections `(pointSection p t, pointSection p t')`. -/
theorem isSectionPairFibreIntersectionDifference_of_isPointFibreIntersectionDifference
    (t t' : Γ(C.S, ⊤)) {β : CycleGroup C p k}
    (h : IsPointFibreIntersectionDifference C p Kf hC hY k t t' β) :
    IsSectionPairFibreIntersectionDifference C p hY k (pointSection p t) (pointSection p t') β :=
  by
  obtain ⟨α, hT, hT', rfl⟩ := h
  exact ⟨α, hT, hT',
    torFormulaCycleIntersectionProduct_pointSection_mem_cyclesOfDimension C p Kf hC hY k t α hT,
    torFormulaCycleIntersectionProduct_pointSection_mem_cyclesOfDimension C p Kf hC hY k t' α hT',
    rfl⟩

/-- The shape at the pair `(t, ∞)` of `IsPointInfinityFibreIntersectionDifference` is the shape
at the pair of sections `(pointSection p t, infinitySection p)`. -/
theorem isSectionPairFibreIntersectionDifference_of_isPointInfinityFibreIntersectionDifference
    (t : Γ(C.S, ⊤)) {β : CycleGroup C p k}
    (h : IsPointInfinityFibreIntersectionDifference C p Kf hC hY k t β) :
    IsSectionPairFibreIntersectionDifference C p hY k (pointSection p t) (infinitySection p) β :=
  by
  obtain ⟨α, hT, hInf, rfl⟩ := h
  exact ⟨α, hT, hInf,
    torFormulaCycleIntersectionProduct_pointSection_mem_cyclesOfDimension C p Kf hC hY k t α hT,
    torFormulaCycleIntersectionProduct_infinitySection_mem_cyclesOfDimension C p Kf hC hY k α
      hInf,
    rfl⟩

include hC in
/-- **Stacks 0B07 part (3) at a presented pair of sections.**
Every `k`-cycle rationally equivalent to zero is of the form `pr_{X,*}(α · X × s₁ - α · X × s₂)`
for distinct sections `s₁`, `s₂`, each of which is either `pointSection p t` for some `t` of the
affine chart, or `infinitySection p`. -/
theorem isSectionPairFibreIntersectionDifference_of_mem_rationalEquivalences [IsAlgClosed Kf]
    {s₁ s₂ : X ⟶ projectiveLineProduct p}
    (h₁ : (∃ t : Γ(C.S, ⊤), s₁ = pointSection p t) ∨ s₁ = infinitySection p)
    (h₂ : (∃ t : Γ(C.S, ⊤), s₂ = pointSection p t) ∨ s₂ = infinitySection p)
    (hne : s₁ ≠ s₂) (β : CycleGroup C p k) (hβ : β ∈ rationalEquivalences C p k) :
    IsSectionPairFibreIntersectionDifference C p hY k s₁ s₂ β := by
  rcases h₁ with ⟨t, rfl⟩ | rfl <;> rcases h₂ with ⟨t', rfl⟩ | rfl
  · exact isSectionPairFibreIntersectionDifference_of_isPointFibreIntersectionDifference C p hY
      k Kf hC t t'
      (isPointFibreIntersectionDifference_of_mem_rationalEquivalences C p Kf hC hY k t t'
        (fun h => hne (congrArg (pointSection p) h)) β hβ)
  · exact
      isSectionPairFibreIntersectionDifference_of_isPointInfinityFibreIntersectionDifference C p
        hY k Kf hC t
        (isPointInfinityFibreIntersectionDifference_of_mem_rationalEquivalences C p Kf hC hY k t
          (isUnit_of_ne_zero_of_eq_spec C hC) β hβ)
  · have h := isSectionPairFibreIntersectionDifference_swap C p hY k
      (isSectionPairFibreIntersectionDifference_of_isPointInfinityFibreIntersectionDifference C p
        hY k Kf hC t'
        (isPointInfinityFibreIntersectionDifference_of_mem_rationalEquivalences C p Kf hC hY k t'
          (isUnit_of_ne_zero_of_eq_spec C hC) (-β) (neg_mem hβ)))
    rwa [neg_neg] at h
  · exact absurd rfl hne

end PartThreePair

end PointCycle

end Stacks.Chow

end
