module

public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.SectionPairFibreIntersectionDifference
public import StacksFrontier.AlgebraicGeometry.Chow.FamilyFibreDivisors.ClosedPointSection

/-!
# The clauses of Tag 0B07 at a section of the family presented as a point of `ℙ¹`

`StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.FibreCyclePointSection` and the files
beside it carry the clauses of Tag 0B07 at `Stacks.Chow.pointSection p t`, the section of
`X ×_S ℙ¹_S ⟶ X` at a point of the affine chart, and at `Stacks.Chow.infinitySection p`. This
file reads each of them at a section `s : X ⟶ X ×_S ℙ¹_S` subject only to the hypothesis that it
is *one of those two shapes*, which is what
`Stacks.Chow.exists_closedPointSection_eq_pointSection_or_eq_infinitySection` supplies for the
section at an arbitrary closed point of `ℙ¹_S` over an algebraically closed field. Nothing is
reproved: every statement here is obtained by substituting the shape and applying the
corresponding existing statement, and part (2) for an arbitrary cycle is the sum over the
components of `α` of part (2) for a prime cycle, exactly as at the distinguished pair in
`...FibreCycleRationalEquivalenceCycle`.

## Main results

* `Stacks.Chow.cycleAssociatedToClosedSubscheme_sup_sectionKer_eq_intersectionProductCycle` —
  part (1)(a) at such a section.
* `Stacks.Chow.properPushforward_intersectionProductCycle_eq_sectionFiberCycle` — part (1)(b).
* `Stacks.Chow.sub_properPushforward_intersectionProductCycle_sectionPair_mem_rationalEquivalences`
  — part (2) for a prime cycle, at a pair of such sections.
* `Stacks.Chow.sub_properPushforward_torFormulaCycleProduct_sectionPair_mem_rationalEquivalences`
  — part (2) for an arbitrary `(k + 1)`-cycle, at a pair of such sections.

## References

* [Stacks Project, Tag 0B07](https://stacks.math.columbia.edu/tag/0B07)
-/

@[expose] public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.TorFormula CategoryTheory CategoryTheory.Limits
  TopologicalSpace

universe u

attribute [local instance 100000] HasDerivedCategory.standard

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]
  (Kf : Type u) [Field Kf] [IsAlgClosed Kf]
  (hC : C.S = AlgebraicGeometry.Spec (CommRingCat.of Kf))
  [AlgebraicGeometry.IsVariety Kf (p ≫ eqToHom hC)]
  (hY : IsRegular (projectiveLineProduct p)) (k : ℤ)

/-- The hypothesis carried by every statement of this file: the section is the section at a point
of the affine chart, or the infinity section. -/
abbrev IsPresentedSection (s : X ⟶ projectiveLineProduct p) : Prop :=
  (∃ t : Γ(C.S, ⊤), s = pointSection p t) ∨ s = infinitySection p

/-! ### Part (1)(a) -/

omit [IsAlgClosed Kf] in
include hC in
/-- **Stacks 0B07, part (1)(a), at a section presented as a point of `ℙ¹_S`.** The cycle
`[W_a]_k` of the scheme-theoretic intersection `W ∩ (X × a)` is the Section 43.14 intersection
product `W · (X × a)`. -/
theorem cycleAssociatedToClosedSubscheme_sup_sectionKer_eq_intersectionProductCycle
    {s : X ⟶ projectiveLineProduct p} (hs : IsPresentedSection C p s)
    (W : (projectiveLineProduct p).IdealSheafData) [IsIntegral W.subscheme]
    (hDim : ∀ ξ : genericPoints W.subscheme,
      relativeDimension C.dimensionFunction (familyBase p W) ξ.1 = k + 1)
    (hWD : schemeDeltaDimension C ((W ⊔ s.ker).subschemeι ≫
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)) ≤ (k : EInt)) :
    haveI : IsLocallyNoetherian (projectiveLineProduct p) :=
      LocallyOfFiniteType.isLocallyNoetherian
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
    (cycleAssociatedToClosedSubscheme C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
        (W ⊔ s.ker).subschemeι k).1 =
      intersectionProductCycle C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY
        (subschemeStructureSheaf W) (subschemeStructureSheaf s.ker)
        (isCoherent_subschemeStructureSheaf W)
        (isCoherent_subschemeStructureSheaf s.ker) k
        (schemeDeltaDimension_reducedSupport_torSheaf_le C
          (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY W s.ker k hWD) := by
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_projectiveLineProduct_le Kf C hC p
  rcases hs with ⟨t, rfl⟩ | rfl
  · exact cycleAssociatedToClosedSubscheme_sup_eq_intersectionProductCycle C
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY W (pointSection p t).ker k d hd
      hWD (localConditions_ker_pointSection C p t W hDim hWD)
  · exact cycleAssociatedToClosedSubscheme_sup_eq_intersectionProductCycle C
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY W (infinitySection p).ker k d hd
      hWD (localConditions_ker_infinitySection C p W hDim hWD)

/-! ### Part (1)(b) -/

omit [IsAlgClosed Kf] in
include hC in
/-- **Stacks 0B07, part (1)(b), at a section presented as a point of `ℙ¹_S`.** The cycle
`[W_a]_k` of the fibre of `W` at the point, viewed as a closed subscheme of `X`, is the proper
pushforward along `pr : X ×_S ℙ¹_S ⟶ X` of the Section 43.14 intersection product
`W · (X × a)`. -/
theorem properPushforward_intersectionProductCycle_eq_sectionFiberCycle
    {s : X ⟶ projectiveLineProduct p} (hs : IsPresentedSection C p s)
    (W : (projectiveLineProduct p).IdealSheafData) [IsIntegral W.subscheme]
    (hDim : ∀ ξ : genericPoints W.subscheme,
      relativeDimension C.dimensionFunction (familyBase p W) ξ.1 = k + 1)
    (hWD : schemeDeltaDimension C ((W ⊔ s.ker).subschemeι ≫
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)) ≤ (k : EInt)) :
    haveI : IsLocallyNoetherian (projectiveLineProduct p) :=
      LocallyOfFiniteType.isLocallyNoetherian
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
    properPushforward C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) p
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S)) rfl k
        ⟨intersectionProductCycle C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY
            (subschemeStructureSheaf W) (subschemeStructureSheaf s.ker)
            (isCoherent_subschemeStructureSheaf W)
            (isCoherent_subschemeStructureSheaf s.ker) k
            (schemeDeltaDimension_reducedSupport_torSheaf_le C
              (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY W s.ker k hWD),
          intersectionProductCycle_mem_cyclesOfDimension C
            (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY W s.ker k hWD⟩ =
      cycleAssociatedToClosedSubscheme C p (W.comap s).subschemeι k := by
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_projectiveLineProduct_le Kf C hC p
  rcases hs with ⟨t, rfl⟩ | rfl
  · exact properPushforward_intersectionProductCycle_eq_pointFiberCycle C p t W k d hY hd hDim hWD
  · exact properPushforward_intersectionProductCycle_eq_infinityFiberCycle C p W k d hY hd hDim hWD

/-! ### The fibre cycles at a pair of such sections are rationally equivalent -/

omit [Field Kf] [IsAlgClosed Kf] [IsVariety Kf (p ≫ eqToHom hC)] in
/-- **The two fibre cycles of an integral `W` at a pair of sections presented as points of
`ℙ¹_S` are rationally equivalent.** This is the content of part (2) for a prime cycle, read on
the fibre cycles rather than on the intersection products. -/
theorem sub_cycleAssociatedToClosedSubscheme_comap_mem_rationalEquivalences
    {s₁ s₂ : X ⟶ projectiveLineProduct p} (h₁ : IsPresentedSection C p s₁)
    (h₂ : IsPresentedSection C p s₂)
    (W : (projectiveLineProduct p).IdealSheafData) [IsIntegral W.subscheme]
    (hDim : ∀ ξ : genericPoints W.subscheme,
      relativeDimension C.dimensionFunction (familyBase p W) ξ.1 = k + 1)
    (hT₁ : ¬ Set.range W.subschemeι ⊆ Set.range s₁)
    (hT₂ : ¬ Set.range W.subschemeι ⊆ Set.range s₂) :
    cycleAssociatedToClosedSubscheme C p (W.comap s₁).subschemeι k -
        cycleAssociatedToClosedSubscheme C p (W.comap s₂).subschemeι k ∈
      rationalEquivalences C p k := by
  rcases h₁ with ⟨t, rfl⟩ | rfl <;> rcases h₂ with ⟨t', rfl⟩ | rfl
  · exact pointFiberCycles_rationallyEquivalent C p W t k t' hDim hT₁ hT₂
  · exact pointFiberCycle_rationallyEquivalent_infinityFiberCycle C p W t k hDim hT₁ hT₂
  · rw [← neg_sub]
    exact neg_mem
      (pointFiberCycle_rationallyEquivalent_infinityFiberCycle C p W t' k hDim hT₂ hT₁)
  · rw [sub_self]
    exact zero_mem _

/-! ### Part (2) for a prime cycle -/

omit [IsAlgClosed Kf] in
include hC in
/-- **Stacks 0B07, part (2) for a prime cycle, at a pair of sections presented as points of
`ℙ¹_S`.** `pr_{X,*}(W · X × a - W · X × b)` is rationally equivalent to zero. -/
theorem sub_properPushforward_intersectionProductCycle_sectionPair_mem_rationalEquivalences
    {s₁ s₂ : X ⟶ projectiveLineProduct p} (h₁ : IsPresentedSection C p s₁)
    (h₂ : IsPresentedSection C p s₂)
    (W : (projectiveLineProduct p).IdealSheafData) [IsIntegral W.subscheme]
    (hDim : ∀ ξ : genericPoints W.subscheme,
      relativeDimension C.dimensionFunction (familyBase p W) ξ.1 = k + 1)
    (hT₁ : ¬ Set.range W.subschemeι ⊆ Set.range s₁)
    (hT₂ : ¬ Set.range W.subschemeι ⊆ Set.range s₂)
    (hWD₁ : schemeDeltaDimension C ((W ⊔ s₁.ker).subschemeι ≫
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)) ≤ (k : EInt))
    (hWD₂ : schemeDeltaDimension C ((W ⊔ s₂.ker).subschemeι ≫
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)) ≤ (k : EInt)) :
    haveI : IsLocallyNoetherian (projectiveLineProduct p) :=
      LocallyOfFiniteType.isLocallyNoetherian
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
    properPushforward C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) p
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S)) rfl k
        ⟨intersectionProductCycle C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY
            (subschemeStructureSheaf W) (subschemeStructureSheaf s₁.ker)
            (isCoherent_subschemeStructureSheaf W)
            (isCoherent_subschemeStructureSheaf s₁.ker) k
            (schemeDeltaDimension_reducedSupport_torSheaf_le C
              (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY W s₁.ker k hWD₁),
          intersectionProductCycle_mem_cyclesOfDimension C
            (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY W s₁.ker k hWD₁⟩ -
      properPushforward C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) p
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S)) rfl k
        ⟨intersectionProductCycle C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY
            (subschemeStructureSheaf W) (subschemeStructureSheaf s₂.ker)
            (isCoherent_subschemeStructureSheaf W)
            (isCoherent_subschemeStructureSheaf s₂.ker) k
            (schemeDeltaDimension_reducedSupport_torSheaf_le C
              (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY W s₂.ker k hWD₂),
          intersectionProductCycle_mem_cyclesOfDimension C
            (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY W s₂.ker k hWD₂⟩ ∈
      rationalEquivalences C p k := by
  rw [properPushforward_intersectionProductCycle_eq_sectionFiberCycle C p Kf hC hY k h₁ W hDim
      hWD₁,
    properPushforward_intersectionProductCycle_eq_sectionFiberCycle C p Kf hC hY k h₂ W hDim hWD₂]
  exact sub_cycleAssociatedToClosedSubscheme_comap_mem_rationalEquivalences C p k h₁ h₂ W
    hDim hT₁ hT₂

/-! ### The Tag 0B08 product with the fibre at such a section -/

section Cycle

variable [AlgebraicGeometry.IsIntegral X]

omit [AlgebraicGeometry.IsIntegral X] in
/-- **The Tag 0B08 product `α · (X × a)` as the finite sum of the products of the components of
`α`.** This is the bilinearity of the product and holds at every point of the family. -/
theorem torFormulaCycleIntersectionProduct_point_eq_sum (z : projectiveLineProduct p)
    (α : AlgebraicCycle (projectiveLineProduct p) ℤ) (hα : (Function.support α).Finite) :
    haveI : IsLocallyNoetherian (projectiveLineProduct p) :=
      LocallyOfFiniteType.isLocallyNoetherian
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
    torFormulaCycleIntersectionProduct C
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY k α
        (@Function.locallyFinsuppWithin.single (projectiveLineProduct p) _ ℤ (Classical.decEq _) _
          z (1 : ℤ)) =
      ∑ x ∈ hα.toFinset, α x • torFormulaSubvarietyProductTotal C
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY k x z :=
  have : IsLocallyNoetherian (projectiveLineProduct p) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
  @cycleIntersectionProduct_single_right (projectiveLineProduct p) (Classical.decEq _) _ α hα _

/-- The Tag 0B08 summand `W_x · (X × a)` at one component of `α` is a `k`-cycle. -/
theorem torFormulaSubvarietyProductTotal_section_mem_cyclesOfDimension
    {s : X ⟶ projectiveLineProduct p} (hs : IsPresentedSection C p s)
    (x : projectiveLineProduct p)
    (hx : relativeDimension C.dimensionFunction
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) x = k + 1)
    (hT : ¬ Set.range (integralComponentAt x).subschemeι ⊆ Set.range s) :
    haveI : IsLocallyNoetherian (projectiveLineProduct p) :=
      LocallyOfFiniteType.isLocallyNoetherian
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
    torFormulaSubvarietyProductTotal C
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY k x (s (genericPoint X)) ∈
      cyclesOfDimension C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) k := by
  rcases hs with ⟨t, rfl⟩ | rfl
  · exact PointCycle.torFormulaSubvarietyProductTotal_pointSection_mem_cyclesOfDimension C p hY k t
      x hx hT
  · exact torFormulaSubvarietyProductTotal_infinitySection_mem_cyclesOfDimension C p hY k x hx hT

omit [IsAlgClosed Kf] in
include hC in
/-- **The Tag 0B08 product `α · (X × a)` is a `k`-cycle**: every summand is, by part (1)(a). -/
theorem torFormulaCycleIntersectionProduct_section_mem_cyclesOfDimension
    {s : X ⟶ projectiveLineProduct p} (hs : IsPresentedSection C p s)
    (α : CycleGroup C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) (k + 1))
    (hT : ∀ x ∈ Function.support α.1,
      ¬ Set.range (integralComponentAt x).subschemeι ⊆ Set.range s) :
    haveI : IsLocallyNoetherian (projectiveLineProduct p) :=
      LocallyOfFiniteType.isLocallyNoetherian
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
    torFormulaCycleIntersectionProduct C
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY k α.1
        (@Function.locallyFinsuppWithin.single (projectiveLineProduct p) _ ℤ (Classical.decEq _) _
          (s (genericPoint X)) (1 : ℤ)) ∈
      cyclesOfDimension C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) k := by
  rcases hs with ⟨t, rfl⟩ | rfl
  · exact PointCycle.torFormulaCycleIntersectionProduct_pointSection_mem_cyclesOfDimension C p Kf
      hC hY k t α hT
  · exact torFormulaCycleIntersectionProduct_infinitySection_mem_cyclesOfDimension C p Kf hC hY k
      α hT

/-- **Part (1)(b) at one component of `α`.** A `k`-cycle whose underlying cycle is the Tag 0B08
summand `W_x · (X × a)` pushes forward to the fibre cycle `[W_{x,a}]_k`. -/
theorem properPushforward_eq_sectionFiberCycle_of_coe_eq
    {s : X ⟶ projectiveLineProduct p} (hs : IsPresentedSection C p s) (d : ℕ)
    (x : projectiveLineProduct p)
    (hd : topologicalKrullDim (projectiveLineProduct p) ≤ (d : WithBot ℕ∞))
    (hx : relativeDimension C.dimensionFunction
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) x = k + 1)
    (hT : ¬ Set.range (integralComponentAt x).subschemeι ⊆ Set.range s)
    (A : CycleGroup C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) k)
    (hA :
      haveI : IsLocallyNoetherian (projectiveLineProduct p) :=
        LocallyOfFiniteType.isLocallyNoetherian
          (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
      A.1 = torFormulaSubvarietyProductTotal C
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY k x (s (genericPoint X))) :
    properPushforward C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) p
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S)) rfl k A =
      cycleAssociatedToClosedSubscheme C p ((integralComponentAt x).comap s).subschemeι k := by
  rcases hs with ⟨t, rfl⟩ | rfl
  · exact PointCycle.properPushforward_eq_pointFiberCycle_of_coe_eq C p hY k d t x hd hx hT A hA
  · exact properPushforward_eq_infinityFiberCycle_of_coe_eq C p hY k d x hd hx hT A hA

omit [IsAlgClosed Kf] in
include hC in
/-- **Stacks 0B07, part (2) in full, at a pair of sections presented as points of `ℙ¹_S`.** For
an arbitrary `(k + 1)`-cycle `α` on `X ×_S ℙ¹_S` meeting the two fibres properly,
`pr_{X,*}(α · X × a - α · X × b)` is rationally equivalent to zero. The product is the finite sum
of the products of the components of `α`, and each summand difference is part (2) for a prime
cycle. -/
theorem sub_properPushforward_torFormulaCycleProduct_sectionPair_mem_rationalEquivalences
    {s₁ s₂ : X ⟶ projectiveLineProduct p} (h₁ : IsPresentedSection C p s₁)
    (h₂ : IsPresentedSection C p s₂)
    (α : CycleGroup C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) (k + 1))
    (hT₁ : ∀ x ∈ Function.support α.1,
      ¬ Set.range (integralComponentAt x).subschemeι ⊆ Set.range s₁)
    (hT₂ : ∀ x ∈ Function.support α.1,
      ¬ Set.range (integralComponentAt x).subschemeι ⊆ Set.range s₂) :
    haveI : IsLocallyNoetherian (projectiveLineProduct p) :=
      LocallyOfFiniteType.isLocallyNoetherian
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
    properPushforward C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) p
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S)) rfl k
        ⟨torFormulaCycleIntersectionProduct C
            (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY k α.1
            (@Function.locallyFinsuppWithin.single (projectiveLineProduct p) _ ℤ
              (Classical.decEq _) _ (s₁ (genericPoint X)) (1 : ℤ)),
          torFormulaCycleIntersectionProduct_section_mem_cyclesOfDimension C p Kf hC hY k h₁
            α hT₁⟩ -
      properPushforward C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) p
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S)) rfl k
        ⟨torFormulaCycleIntersectionProduct C
            (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY k α.1
            (@Function.locallyFinsuppWithin.single (projectiveLineProduct p) _ ℤ
              (Classical.decEq _) _ (s₂ (genericPoint X)) (1 : ℤ)),
          torFormulaCycleIntersectionProduct_section_mem_cyclesOfDimension C p Kf hC hY k h₂
            α hT₂⟩ ∈
      rationalEquivalences C p k := by
  have : IsLocallyNoetherian (projectiveLineProduct p) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
  have : CompactSpace (projectiveLineProduct p) :=
    compactSpace_projectiveLineProduct Kf C hC p
  have hα : (Function.support α.1).Finite := finite_support_of_compactSpace α.1
  have hsupp : ∀ x ∈ hα.toFinset, x ∈ Function.support α.1 := fun x hx => hα.mem_toFinset.1 hx
  have hdimpt : ∀ x ∈ hα.toFinset, relativeDimension C.dimensionFunction
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) x = k + 1 := fun x hx =>
    (mem_cyclesOfDimension_iff_forall_point C
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) (k + 1) α.1).1 α.2 x (hsupp x hx)
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_projectiveLineProduct_le Kf C hC p
  have hdec : ∀ (s : X ⟶ projectiveLineProduct p) (h : IsPresentedSection C p s)
      (hT : ∀ x ∈ Function.support α.1,
        ¬ Set.range (integralComponentAt x).subschemeι ⊆ Set.range s),
      (⟨torFormulaCycleIntersectionProduct C
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY k α.1
        (@Function.locallyFinsuppWithin.single (projectiveLineProduct p) _ ℤ
          (Classical.decEq _) _ (s (genericPoint X)) (1 : ℤ)),
      torFormulaCycleIntersectionProduct_section_mem_cyclesOfDimension C p Kf hC hY k h α hT⟩ :
      CycleGroup C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) k) =
      ∑ x ∈ hα.toFinset.attach, α.1 x.1 •
        (⟨torFormulaSubvarietyProductTotal C
            (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY k x.1
            (s (genericPoint X)),
          torFormulaSubvarietyProductTotal_section_mem_cyclesOfDimension C p hY k h x.1
            (hdimpt x.1 x.2) (hT x.1 (hsupp x.1 x.2))⟩ :
          CycleGroup C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) k) := by
    intro s h hT
    refine Subtype.ext ?_
    change torFormulaCycleIntersectionProduct C
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY k α.1
        (@Function.locallyFinsuppWithin.single (projectiveLineProduct p) _ ℤ
          (Classical.decEq _) _ (s (genericPoint X)) (1 : ℤ)) = _
    rw [torFormulaCycleIntersectionProduct_point_eq_sum C p hY k (s (genericPoint X)) α.1 hα,
      ← Finset.sum_attach hα.toFinset (fun x => α.1 x • torFormulaSubvarietyProductTotal C
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY k x (s (genericPoint X)))]
    simp
  rw [hdec s₁ h₁ hT₁, hdec s₂ h₂ hT₂]
  simp only [← properPushforwardHom_apply, map_sum, ← Finset.sum_sub_distrib]
  refine AddSubgroup.sum_mem _ fun x _ => ?_
  rw [map_zsmul, map_zsmul, ← smul_sub, properPushforwardHom_apply, properPushforwardHom_apply,
    properPushforward_eq_sectionFiberCycle_of_coe_eq C p hY k h₁ d x.1 hd (hdimpt x.1 x.2)
      (hT₁ x.1 (hsupp x.1 x.2)) _ rfl,
    properPushforward_eq_sectionFiberCycle_of_coe_eq C p hY k h₂ d x.1 hd (hdimpt x.1 x.2)
      (hT₂ x.1 (hsupp x.1 x.2)) _ rfl]
  have : IsIntegral (integralComponentAt x.1).subscheme := isIntegral_integralComponentAt x.1
  exact AddSubgroup.zsmul_mem _
    (sub_cycleAssociatedToClosedSubscheme_comap_mem_rationalEquivalences C p k h₁ h₂
      (integralComponentAt x.1)
      (relativeDimension_familyBase_integralComponentAt_genericPoints C p x.1 (hdimpt x.1 x.2))
      (hT₁ x.1 (hsupp x.1 x.2)) (hT₂ x.1 (hsupp x.1 x.2))) _

end Cycle

end Stacks.Chow

end
