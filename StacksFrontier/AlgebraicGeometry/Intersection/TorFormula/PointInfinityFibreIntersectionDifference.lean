module

public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.FibreCyclePointSectionRationalEquivalenceCycle
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.PointInfinityFamilyFibreDifferenceExistence
import StacksCore.Tactic.StacksAttribute

/-!
# Tag 0B07 part (3) at the pair `(t, ∞)`

`Stacks.Chow.PointCycle.IsPointFibreIntersectionDifference` and its closure induction carry Tag
0B07 part (3) at an arbitrary pair of distinct points `t`, `t'` of the affine chart.
This file carries the same shape at the pair `(t, ∞)`: one point `t` of the affine chart and the
point at infinity.

Every lemma mirrors a `(t, t')` one with the point-`t'` machinery of this file's own
`FibreCyclePointSectionRationalEquivalenceCycle` replaced by the point-at-infinity machinery of
`StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.FibreCycleRationalEquivalenceCycle`
(`Stacks.Chow.torFormulaCycleIntersectionProduct_infinitySection_mem_cyclesOfDimension`,
`Stacks.Chow.properPushforward_eq_infinityFiberCycle_of_coe_eq`), which that file already
imports. The closure induction runs on `Stacks.Chow.pointInfinityFibreDifferences` and Tag 0AZI
at the pair `(t, ∞)`,
`Stacks.Chow.rationalEquivalences_eq_closure_pointInfinityFibreDifferences`, in place of
`Stacks.Chow.pointFibreDifferences` and
`Stacks.Chow.rationalEquivalences_eq_closure_pointFibreDifferences_of_ne`. There is no hypothesis
analogous to `t ≠ t'`: the point at infinity is never a point of the affine chart.

## Main definitions

* `Stacks.Chow.PointCycle.IsPointInfinityFibreIntersectionDifference` — the shape of part (3) at
  the pair `(t, ∞)`.

## Main results

* `Stacks.Chow.PointCycle.isPointInfinityFibreIntersectionDifference_of_mem_rationalEquivalences`
  — **Tag 0B07 part (3) at the pair `(t, ∞)`, for an arbitrary point `t` of the affine chart.**

## References

* [Stacks Project, Tag 0B07](https://stacks.math.columbia.edu/tag/0B07)
* [Stacks Project, Tag 0B08](https://stacks.math.columbia.edu/tag/0B08)
* [Stacks Project, Tag 0AZI](https://stacks.math.columbia.edu/tag/0AZI)
-/

@[expose] public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.TorFormula CategoryTheory CategoryTheory.Limits
  TopologicalSpace

universe u

attribute [local instance 100000] HasDerivedCategory.standard

namespace Stacks.Chow

namespace PointCycle

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]

section PartThreeInfinity

variable (Kf : Type u) [Field Kf]
  (hC : C.S = AlgebraicGeometry.Spec (CommRingCat.of Kf))
  [AlgebraicGeometry.IsVariety Kf (p ≫ eqToHom hC)]
  (hY : IsRegular (projectiveLineProduct p)) (k : ℤ) (t : Γ(C.S, ⊤))

/-- **The shape of Tag 0B07 part (3) at the pair `(t, ∞)`.** A `k`-cycle `β` on `X` is of the
form `pr_{X,*}(α · X × t - α · X × ∞)` for a `(k + 1)`-cycle `α` on `X ×_S ℙ¹_S` no component of
which is contained in either the section at `t` or the section at infinity. -/
def IsPointInfinityFibreIntersectionDifference (β : CycleGroup C p k) : Prop :=
  ∃ (α : CycleGroup C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) (k + 1))
    (hT : ∀ x ∈ Function.support α.1,
      ¬ Set.range (integralComponentAt x).subschemeι ⊆ Set.range (pointSection p t))
    (hInf : ∀ x ∈ Function.support α.1,
      ¬ Set.range (integralComponentAt x).subschemeι ⊆ Set.range (infinitySection p)),
    β =
      properPushforward C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) p
          (pullback.fst p (relativeProjectiveLine C.S ↘ C.S)) rfl k
          ⟨torFormulaCycleIntersectionProduct C
              (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY k α.1
              (@Function.locallyFinsuppWithin.single (projectiveLineProduct p) _ ℤ
                (Classical.decEq _) _ ((pointSection p t) (genericPoint X)) (1 : ℤ)),
            torFormulaCycleIntersectionProduct_pointSection_mem_cyclesOfDimension C p Kf hC hY k
              t α hT⟩ -
        properPushforward C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) p
          (pullback.fst p (relativeProjectiveLine C.S ↘ C.S)) rfl k
          ⟨torFormulaCycleIntersectionProduct C
              (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY k α.1
              (@Function.locallyFinsuppWithin.single (projectiveLineProduct p) _ ℤ
                (Classical.decEq _) _ ((infinitySection p) (genericPoint X)) (1 : ℤ)),
            torFormulaCycleIntersectionProduct_infinitySection_mem_cyclesOfDimension C p Kf hC hY
              k α hInf⟩

/-- The pushforward of the Tor-formula product with a fixed cycle `s` is additive in the first
cycle. -/
private theorem properPushforward_torFormulaCycleIntersectionProduct_add
    [CompactSpace (projectiveLineProduct p)]
    (α₁ α₂ : CycleGroup C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) (k + 1))
    (s : AlgebraicCycle (projectiveLineProduct p) ℤ) (m m₁ m₂) :
    properPushforward C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) p
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S)) rfl k
        ⟨torFormulaCycleIntersectionProduct C
          (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY k (α₁ + α₂).1 s, m⟩ =
      properPushforward C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) p
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S)) rfl k
        ⟨torFormulaCycleIntersectionProduct C
          (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY k α₁.1 s, m₁⟩ +
      properPushforward C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) p
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S)) rfl k
        ⟨torFormulaCycleIntersectionProduct C
          (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY k α₂.1 s, m₂⟩ := by
  rw [← properPushforward_add]
  exact congrArg _ (Subtype.ext (cycleIntersectionProduct_add_left _
    (finite_support_of_compactSpace _) (finite_support_of_compactSpace _)
    (finite_support_of_compactSpace _)))

/-- The pushforward of the Tor-formula product with a fixed cycle `s` commutes with negation of
the first cycle. -/
private theorem properPushforward_torFormulaCycleIntersectionProduct_neg
    [CompactSpace (projectiveLineProduct p)]
    (α : CycleGroup C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) (k + 1))
    (s : AlgebraicCycle (projectiveLineProduct p) ℤ) (m m₁) :
    properPushforward C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) p
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S)) rfl k
        ⟨torFormulaCycleIntersectionProduct C
          (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY k (-α).1 s, m⟩ =
      -properPushforward C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) p
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S)) rfl k
        ⟨torFormulaCycleIntersectionProduct C
          (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY k α.1 s, m₁⟩ := by
  rw [← properPushforward_neg]
  refine congrArg _ (Subtype.ext (eq_neg_of_add_eq_zero_left ?_))
  change cycleIntersectionProduct _ (-α).1 s + cycleIntersectionProduct _ α.1 s = 0
  rw [← cycleIntersectionProduct_add_left _ (finite_support_of_compactSpace _)
    (finite_support_of_compactSpace _) (finite_support_of_compactSpace _)]
  simp

/-- The pushforward of the Tor-formula product of the zero cycle with a cycle `s` is zero. -/
private theorem properPushforward_torFormulaCycleIntersectionProduct_zero
    (s : AlgebraicCycle (projectiveLineProduct p) ℤ) (m) :
    properPushforward C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) p
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S)) rfl k
        ⟨torFormulaCycleIntersectionProduct C
          (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY k
          (0 : CycleGroup C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) (k + 1)).1 s,
          m⟩ = 0 := by
  rw [← properPushforward_zero C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) p
    (pullback.fst p (relativeProjectiveLine C.S ↘ C.S)) rfl k]
  exact congrArg _ (Subtype.ext (cycleIntersectionProduct_zero_left _ _))

/-- The zero cycle is of the shape of part (3) at the pair `(t, ∞)`: take `α = 0`. -/
theorem isPointInfinityFibreIntersectionDifference_zero :
    IsPointInfinityFibreIntersectionDifference C p Kf hC hY k t 0 := by
  refine ⟨0, fun x hx => absurd hx ?_, fun x hx => absurd hx ?_, ?_⟩
  · simp
  · simp
  · rw [properPushforward_torFormulaCycleIntersectionProduct_zero,
      properPushforward_torFormulaCycleIntersectionProduct_zero, sub_zero]

/-- The shape of part (3) at the pair `(t, ∞)` is closed under addition: add the two cycles
`α`. -/
theorem isPointInfinityFibreIntersectionDifference_add {β γ : CycleGroup C p k}
    (hβ : IsPointInfinityFibreIntersectionDifference C p Kf hC hY k t β)
    (hγ : IsPointInfinityFibreIntersectionDifference C p Kf hC hY k t γ) :
    IsPointInfinityFibreIntersectionDifference C p Kf hC hY k t (β + γ) := by
  obtain ⟨α₁, hT₁, hInf₁, rfl⟩ := hβ
  obtain ⟨α₂, hT₂, hInf₂, rfl⟩ := hγ
  have : CompactSpace (projectiveLineProduct p) :=
    compactSpace_projectiveLineProduct Kf C hC p
  have hsupp : ∀ z ∈ Function.support (α₁ + α₂).1,
      z ∈ Function.support α₁.1 ∨ z ∈ Function.support α₂.1 :=
    fun z hz => Function.support_add _ _ hz
  refine ⟨α₁ + α₂, fun z hz => (hsupp z hz).elim (hT₁ z) (hT₂ z),
    fun z hz => (hsupp z hz).elim (hInf₁ z) (hInf₂ z), ?_⟩
  rw [properPushforward_torFormulaCycleIntersectionProduct_add,
    properPushforward_torFormulaCycleIntersectionProduct_add]
  rotate_left
  · exact torFormulaCycleIntersectionProduct_infinitySection_mem_cyclesOfDimension C p Kf hC hY k
      α₁ hInf₁
  · exact torFormulaCycleIntersectionProduct_infinitySection_mem_cyclesOfDimension C p Kf hC hY k
      α₂ hInf₂
  · exact torFormulaCycleIntersectionProduct_pointSection_mem_cyclesOfDimension C p Kf hC hY k t
      α₁ hT₁
  · exact torFormulaCycleIntersectionProduct_pointSection_mem_cyclesOfDimension C p Kf hC hY k t
      α₂ hT₂
  abel

/-- The shape of part (3) at the pair `(t, ∞)` is closed under negation: negate the cycle
`α`. -/
theorem isPointInfinityFibreIntersectionDifference_neg {β : CycleGroup C p k}
    (hβ : IsPointInfinityFibreIntersectionDifference C p Kf hC hY k t β) :
    IsPointInfinityFibreIntersectionDifference C p Kf hC hY k t (-β) := by
  obtain ⟨α, hTα, hInfα, rfl⟩ := hβ
  have : CompactSpace (projectiveLineProduct p) :=
    compactSpace_projectiveLineProduct Kf C hC p
  have hsupp : ∀ z ∈ Function.support (-α).1, z ∈ Function.support α.1 :=
    fun z hz => by simpa using hz
  refine ⟨-α, fun z hz => hTα z (hsupp z hz), fun z hz => hInfα z (hsupp z hz), ?_⟩
  rw [properPushforward_torFormulaCycleIntersectionProduct_neg,
    properPushforward_torFormulaCycleIntersectionProduct_neg]
  rotate_left
  · exact torFormulaCycleIntersectionProduct_infinitySection_mem_cyclesOfDimension C p Kf hC hY k
      α hInfα
  · exact torFormulaCycleIntersectionProduct_pointSection_mem_cyclesOfDimension C p Kf hC hY k t
      α hTα
  abel

/-- A basic rational equivalence at the pair `(t, ∞)` is of the shape of part (3): take
`α = [W]`, the prime cycle of the closed subvariety `W` whose two fibre cycles at `t` and `∞` it
is the difference of. -/
theorem isPointInfinityFibreIntersectionDifference_of_mem_pointInfinityFibreDifferences
    {γ : CycleGroup C p k} (hγ : γ ∈ pointInfinityFibreDifferences C p k t) :
    IsPointInfinityFibreIntersectionDifference C p Kf hC hY k t γ := by
  obtain ⟨W, hWint, hDim, hTW, hInfW, rfl⟩ := hγ
  have := hWint
  have hW : W = integralComponentAt (W.subschemeι (genericPoint W.subscheme)) :=
    (Scheme.IdealSheafData.ker_subschemeι W).symm.trans (ker_eq_integralComponentAt W.subschemeι)
  have hmemgen : genericPoint W.subscheme ∈ genericPoints W.subscheme := by
    rw [genericPoints_eq_singleton]
    exact Set.mem_singleton _
  have hwdim : relativeDimension C.dimensionFunction
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
      (W.subschemeι (genericPoint W.subscheme)) = k + 1 := by
    have h := hDim ⟨genericPoint W.subscheme, hmemgen⟩
    rwa [show familyBase p W = W.subschemeι ≫
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) from rfl,
      relativeDimension_comp_closedImmersion] at h
  have hTw : ¬ Set.range
      (integralComponentAt (W.subschemeι (genericPoint W.subscheme))).subschemeι ⊆
        Set.range (pointSection p t) := by rw [← hW]; exact hTW
  have hInfw : ¬ Set.range
      (integralComponentAt (W.subschemeι (genericPoint W.subscheme))).subschemeι ⊆
        Set.range (infinitySection p) := by rw [← hW]; exact hInfW
  have hmemsingle : (@Function.locallyFinsuppWithin.single (projectiveLineProduct p) _ ℤ
      (Classical.decEq _) _ (W.subschemeι (genericPoint W.subscheme)) (1 : ℤ)) ∈
      cyclesOfDimension C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) (k + 1) := by
    rw [mem_cyclesOfDimension_iff_forall_point]
    intro z hz
    have hzw : z = W.subschemeι (genericPoint W.subscheme) := by
      by_contra hne
      exact hz (by simp [Function.locallyFinsuppWithin.single_apply, hne])
    rw [hzw]
    exact hwdim
  obtain ⟨α, hαdef⟩ : ∃ a : CycleGroup C
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) (k + 1),
      a.1 = @Function.locallyFinsuppWithin.single (projectiveLineProduct p) _ ℤ
        (Classical.decEq _) _ (W.subschemeι (genericPoint W.subscheme)) (1 : ℤ) :=
    ⟨⟨_, hmemsingle⟩, rfl⟩
  have hsupp : ∀ z ∈ Function.support α.1, z = W.subschemeι (genericPoint W.subscheme) := by
    intro z hz
    rw [hαdef] at hz
    by_contra hne
    exact hz (by simp [Function.locallyFinsuppWithin.single_apply, hne])
  have hT'' : ∀ x ∈ Function.support α.1,
      ¬ Set.range (integralComponentAt x).subschemeι ⊆ Set.range (pointSection p t) := by
    intro z hz
    rw [hsupp z hz]
    exact hTw
  have hInf'' : ∀ x ∈ Function.support α.1,
      ¬ Set.range (integralComponentAt x).subschemeι ⊆ Set.range (infinitySection p) := by
    intro z hz
    rw [hsupp z hz]
    exact hInfw
  refine ⟨α, hT'', hInf'', ?_⟩
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_projectiveLineProduct_le Kf C hC p
  have m0 := torFormulaCycleIntersectionProduct_pointSection_mem_cyclesOfDimension C p Kf hC hY k
    t α hT''
  have mi := torFormulaCycleIntersectionProduct_infinitySection_mem_cyclesOfDimension C p Kf hC
    hY k α hInf''
  have hprod : ∀ (y : projectiveLineProduct p),
      cycleIntersectionProduct (torFormulaSubvarietyProductTotal C
            (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY k) α.1
          (@Function.locallyFinsuppWithin.single (projectiveLineProduct p) _ ℤ
            (Classical.decEq _) _ y (1 : ℤ)) =
        torFormulaSubvarietyProductTotal C
          (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY k
          (W.subschemeι (genericPoint W.subscheme)) y := by
    intro y
    rw [hαdef, @cycleIntersectionProduct_single_single (projectiveLineProduct p)
      (Classical.decEq _) (torFormulaSubvarietyProductTotal C
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY k)
      (W.subschemeι (genericPoint W.subscheme)) y 1 1]
    simp
  rw [properPushforward_eq_pointFiberCycle_of_coe_eq C p hY k d t
      (W.subschemeι (genericPoint W.subscheme)) hd hwdim hTw ⟨_, m0⟩ (hprod _),
    properPushforward_eq_infinityFiberCycle_of_coe_eq C p hY k d
      (W.subschemeι (genericPoint W.subscheme)) hd hwdim hInfw ⟨_, mi⟩ (hprod _),
    ← hW]

/-- **Stacks 0B07, part (3), at the pair `(t, ∞)`, for an arbitrary point `t` of the affine
chart.** Every `k`-cycle rationally equivalent to zero is of the form
`pr_{X,*}(α · X × t - α · X × ∞)`. -/
theorem isPointInfinityFibreIntersectionDifference_of_mem_rationalEquivalences [IsAlgClosed Kf]
    (hbase : ∀ c : Γ(C.S, ⊤), c ≠ 0 → IsUnit c) (β : CycleGroup C p k)
    (hβ : β ∈ rationalEquivalences C p k) :
    IsPointInfinityFibreIntersectionDifference C p Kf hC hY k t β := by
  rw [rationalEquivalences_eq_closure_pointInfinityFibreDifferences Kf C hC p k t hbase] at hβ
  exact AddSubgroup.closure_induction
    (fun x hx =>
      isPointInfinityFibreIntersectionDifference_of_mem_pointInfinityFibreDifferences C p Kf hC
        hY k t hx)
    (isPointInfinityFibreIntersectionDifference_zero C p Kf hC hY k t)
    (fun x y _ _ ihx ihy =>
      isPointInfinityFibreIntersectionDifference_add C p Kf hC hY k t ihx ihy)
    (fun x _ ih => isPointInfinityFibreIntersectionDifference_neg C p Kf hC hY k t ih) hβ

end PartThreeInfinity

end PointCycle

end Stacks.Chow

end
