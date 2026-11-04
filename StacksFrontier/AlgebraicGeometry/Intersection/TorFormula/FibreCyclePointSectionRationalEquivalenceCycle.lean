module

public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.FibreCyclePointSectionPushforward
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.FibreCycleRationalEquivalenceCycle
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.PointFamilyFibreDifferenceExistence
import StacksCore.Tactic.StacksAttribute

/-!
# Tag 0B07 part (3) at an arbitrary pair of points of the affine chart

Part (3) of Tag 0B07 says that every `k`-cycle rationally equivalent to zero is of the form
`pr_{X,*}(α · X × a - α · X × b)` for a `(k + 1)`-cycle `α` on `X ×_S ℙ¹_S` meeting `X × a` and
`X × b` properly. The repository carries it at the traditional pair `a = 0`, `b = ∞`, which is
`Stacks.Chow.isFibreIntersectionDifference_of_mem_rationalEquivalences`. This file carries it at
an arbitrary pair of distinct points of the affine chart, attached to global functions `t`, `t'`
on the base.

Three ingredients are new.

* **The delta-dimension bound at an arbitrary point.** The section at `t` is an effective
  Cartier divisor on `ℙ¹_S` (`Stacks.Chow.isEffectiveCartierDivisor_ker_lineSection`), so the
  divisor it cuts on an integral `W` not contained in it is an effective Cartier divisor on `W`,
  whence `Stacks.Chow.schemeDeltaDimension_sup_ker_pointSection_le`. This is the arbitrary-point
  analogue of `Stacks.Chow.schemeDeltaDimension_sup_ker_zeroSection_le`; unlike the zero-section
  one it needs no reducedness detour, because `Stacks.Chow.pointDivisor` is defined by the
  kernel ideal sheaf of the section rather than by the reduced structure on its image.
* **The Tag 0B08 summand at the section at `t`**, and its identification with the Section 43.14
  product of Tag 0AZR — the arbitrary-point analogue of
  `Stacks.Chow.torFormulaSubvarietyProductTotal_zeroSection_eq` — together with part (1)(b) in
  the form `Stacks.Chow.properPushforward_eq_pointFiberCycle_of_coe_eq`.
* **The generating set at the pair.** The closure induction is run on
  `Stacks.Chow.pointFibreDifferences`, whose generators are the fibre differences at `(t, t')`,
  and the equality of that closure with the group of cycles rationally equivalent to zero is
  `Stacks.Chow.rationalEquivalences_eq_closure_pointFibreDifferences_of_ne` — Tag 0AZI at the
  pair. The hard-coded zero-and-infinity generating set `Stacks.Chow.fibreDifferences` of Tag
  0AZG is never unfolded, and Tag 0B2U, moving an arbitrary pair to `(0, ∞)`, is not invoked.

## Main definitions

* `Stacks.Chow.IsPointFibreIntersectionDifference` — the shape of part (3) at the pair.

## Main results

* `Stacks.Chow.pointDivisor_isEffectiveCartierDivisor` — Tag 02S4 part (1) at an arbitrary
  point.
* `Stacks.Chow.schemeDeltaDimension_sup_ker_pointSection_le` — proper intersection with the
  section at `t`, as a delta-dimension bound.
* `Stacks.Chow.torFormulaSubvarietyProductTotal_pointSection_mem_cyclesOfDimension` and
  `Stacks.Chow.torFormulaCycleIntersectionProduct_pointSection_mem_cyclesOfDimension` —
  `α · X × a` is a `k`-cycle.
* `Stacks.Chow.properPushforward_eq_pointFiberCycle_of_coe_eq` — part (1)(b) at one component
  of `α`.
* `Stacks.Chow.isPointFibreIntersectionDifference_of_mem_rationalEquivalences` — **Tag 0B07 part
  (3) at an arbitrary pair of distinct points of the affine chart.**

## References

* [Stacks Project, Tag 0B07](https://stacks.math.columbia.edu/tag/0B07)
* [Stacks Project, Tag 0B08](https://stacks.math.columbia.edu/tag/0B08)
* [Stacks Project, Tag 0AZI](https://stacks.math.columbia.edu/tag/0AZI)
* [Stacks Project, Tag 02S4](https://stacks.math.columbia.edu/tag/02S4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.TorFormula CategoryTheory CategoryTheory.Limits
  TopologicalSpace

universe u

attribute [local instance 100000] HasDerivedCategory.standard

namespace Stacks.Chow

/-! ### The divisor at an arbitrary point is an effective Cartier divisor -/

section Cartier

variable {X S : Scheme.{u}} (f : X ⟶ S) (t : Γ(S, ⊤))
  (W : (projectiveLineProduct f).IdealSheafData)

/-- The divisor of `W` at `t` is locally principal. No reducedness of `W` is needed: the divisor
is cut out by the kernel ideal sheaf of the section, not by the reduced structure on its
image. -/
theorem isLocallyPrincipal_pointDivisor :
    Stacks.Divisors.IsLocallyPrincipal (pointDivisor f t W) := by
  rw [pointDivisor]
  exact Stacks.Divisors.isLocallyPrincipal_comap _ _ (isLocallyPrincipal_ker_pointSection f t)

/-- **Stacks Project, Tag 02S4, part (1), at an arbitrary point of the affine chart.** If `W` is
integral and is not contained in the image of the section at `t`, then the divisor it cuts is an
effective Cartier divisor on `W`. -/
theorem pointDivisor_isEffectiveCartierDivisor [IsIntegral W.subscheme]
    (h : ¬ Set.range W.subschemeι ⊆ Set.range (pointSection f t)) :
    Stacks.Divisors.IsEffectiveCartierDivisor (pointDivisor f t W) :=
  have : IsReduced W.subscheme := AlgebraicGeometry.isReduced_of_isIntegral W.subscheme
  Stacks.Divisors.isEffectiveCartierDivisor_of_isLocallyPrincipal _
    (pointDivisor_ne_bot f t W h) (isLocallyPrincipal_pointDivisor f t W)

end Cartier

/-! ### Proper intersection with the section at an arbitrary point -/

/-- **Proper intersection with the section at an arbitrary point, as a delta-dimension bound on
the scheme-theoretic intersection.** For an integral closed subscheme `W ⊆ X ×_S ℙ¹_S` of
relative dimension `k + 1` not contained in the image of the section at `t`, the closed
subscheme `W ∩ (X × a)` cut out by `W ⊔ (pointSection p t).ker` has delta-dimension at most `k`.

This is `Stacks.Chow.schemeDeltaDimension_sup_ker_zeroSection_le` at an arbitrary point. Read on
`X ×_S ℙ¹_S` the intersection has the same underlying closed set as the divisor of `W` at `t`,
an effective Cartier divisor on `W` by Tag 02S4 part (1), whose delta-dimension drops by one. -/
theorem schemeDeltaDimension_sup_ker_pointSection_le (C : ChowSituation.{u}) {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] (t : Γ(C.S, ⊤))
    (W : (projectiveLineProduct p).IdealSheafData) [IsIntegral W.subscheme] {k : ℤ}
    (hDim : ∀ ξ : genericPoints W.subscheme,
      relativeDimension C.dimensionFunction (familyBase p W) ξ.1 = k + 1)
    (hT : ¬ Set.range W.subschemeι ⊆ Set.range (pointSection p t)) :
    schemeDeltaDimension C ((W ⊔ (pointSection p t).ker).subschemeι ≫
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)) ≤ (k : EInt) := by
  have hrange : Set.range (W ⊔ (pointSection p t).ker).subschemeι.base =
      Set.range ((pointDivisor p t W).subschemeι ≫ W.subschemeι).base := by
    rw [Scheme.IdealSheafData.range_subschemeι,
      ← ker_pointDivisor_subschemeι_comp_subschemeι p t W, Scheme.Hom.support_ker]
    exact (IsClosedImmersion.isClosedEmbedding
      ((pointDivisor p t W).subschemeι ≫ W.subschemeι)).isClosed_range.closure_eq
  rw [schemeDeltaDimension_eq_of_equal_ranges C
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
      (W ⊔ (pointSection p t).ker).subschemeι
      ((pointDivisor p t W).subschemeι ≫ W.subschemeι) hrange,
    schemeDeltaDimension_congr C (Category.assoc (pointDivisor p t W).subschemeι W.subschemeι
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p))]
  refine (schemeDeltaDimension_isEffectiveCartierDivisor_le C (familyBase p W)
    (pointDivisor p t W) (pointDivisor_isEffectiveCartierDivisor p t W hT)).trans ?_
  rw [schemeDeltaDimension_familyBase C p W hDim, coe_add_neg_one k]

namespace PointCycle

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]

/-- The projective line product over a scheme locally of finite type is locally Noetherian. -/
private theorem isLocallyNoetherian_projectiveLineProduct :
    IsLocallyNoetherian (projectiveLineProduct p) :=
  LocallyOfFiniteType.isLocallyNoetherian
    (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)

/-! ### The image of the section at an arbitrary point as the closure of a point -/

omit [LocallyOfFiniteType p] in
/-- The image of the section at `t` is the reduced closure of the image of the generic point of
`X`: the section is a closed immersion with integral source. -/
theorem ker_pointSection_eq_integralComponentAt [IsIntegral X] (t : Γ(C.S, ⊤)) :
    (pointSection p t).ker = integralComponentAt ((pointSection p t) (genericPoint X)) :=
  ker_eq_integralComponentAt (pointSection p t)

/-! ### The Tag 0B08 product with the fibre at an arbitrary point as a finite sum -/

section Products

variable [IsIntegral X] (hY : IsRegular (projectiveLineProduct p)) (k : ℤ) (t : Γ(C.S, ⊤))

/-- **The Tag 0B08 product `α · (X × a)` as the finite sum of the products of the components.**
-/
theorem torFormulaCycleIntersectionProduct_pointSection_eq_sum
    (α : AlgebraicCycle (projectiveLineProduct p) ℤ) (hα : (Function.support α).Finite) :
    haveI : IsLocallyNoetherian (projectiveLineProduct p) :=
      LocallyOfFiniteType.isLocallyNoetherian
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
    torFormulaCycleIntersectionProduct C
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY k α
        (@Function.locallyFinsuppWithin.single (projectiveLineProduct p) _ ℤ (Classical.decEq _) _
          ((pointSection p t) (genericPoint X)) (1 : ℤ)) =
      ∑ x ∈ hα.toFinset, α x • torFormulaSubvarietyProductTotal C
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY k x
        ((pointSection p t) (genericPoint X)) :=
  have := isLocallyNoetherian_projectiveLineProduct C p
  @cycleIntersectionProduct_single_right (projectiveLineProduct p) (Classical.decEq _) _ α hα _

end Products

/-! ### The summand of the Tag 0B08 product at one component of `α` -/

section Component

variable [IsIntegral X] (hY : IsRegular (projectiveLineProduct p)) (k : ℤ) (d : ℕ)
  (t : Γ(C.S, ⊤)) (x : projectiveLineProduct p)

omit [AlgebraicGeometry.IsIntegral X] in
/-- The scheme-theoretic intersection of the component `W = closure {x}` of `α` with the image
of the section at `t` has delta-dimension at most `k`. -/
theorem schemeDeltaDimension_integralComponentAt_sup_ker_pointSection_le
    (hx : relativeDimension C.dimensionFunction
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) x = k + 1)
    (hT : ¬ Set.range (integralComponentAt x).subschemeι ⊆ Set.range (pointSection p t)) :
    schemeDeltaDimension C ((integralComponentAt x ⊔ (pointSection p t).ker).subschemeι ≫
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)) ≤ (k : EInt) :=
  have : IsIntegral (integralComponentAt x).subscheme := isIntegral_integralComponentAt x
  schemeDeltaDimension_sup_ker_pointSection_le C p t (integralComponentAt x)
    (relativeDimension_familyBase_integralComponentAt_genericPoints C p x hx) hT

/-- The Tor-support bound of Tag 0B08 at the pair consisting of a component of `α` and the
generic point of `X × a`, from proper intersection. -/
theorem torSupportBound_pointSection
    (hx : relativeDimension C.dimensionFunction
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) x = k + 1)
    (hT : ¬ Set.range (integralComponentAt x).subschemeι ⊆ Set.range (pointSection p t)) :
    haveI : IsLocallyNoetherian (projectiveLineProduct p) :=
      LocallyOfFiniteType.isLocallyNoetherian
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
    TorSupportBound C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY k x
      ((pointSection p t) (genericPoint X)) := by
  have := isLocallyNoetherian_projectiveLineProduct C p
  refine schemeDeltaDimension_reducedSupport_torSheaf_le C
    (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY (integralComponentAt x)
    (integralComponentAt ((pointSection p t) (genericPoint X))) k ?_
  rw [← ker_pointSection_eq_integralComponentAt C p t]
  exact schemeDeltaDimension_integralComponentAt_sup_ker_pointSection_le C p k t x hx hT

/-- The Tag 0B08 summand `W_x · (X × a)` is the Section 43.14 product of the structure sheaf of
`W_x = closure {x}` and that of the image of the section at `t`. -/
theorem torFormulaSubvarietyProductTotal_pointSection_eq
    (hx : relativeDimension C.dimensionFunction
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) x = k + 1)
    (hT : ¬ Set.range (integralComponentAt x).subschemeι ⊆ Set.range (pointSection p t)) :
    haveI : IsLocallyNoetherian (projectiveLineProduct p) :=
      LocallyOfFiniteType.isLocallyNoetherian
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
    torFormulaSubvarietyProductTotal C
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY k x
        ((pointSection p t) (genericPoint X)) =
      intersectionProductCycle C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY
        (subschemeStructureSheaf (integralComponentAt x))
        (subschemeStructureSheaf (pointSection p t).ker)
        (isCoherent_subschemeStructureSheaf (integralComponentAt x))
        (isCoherent_subschemeStructureSheaf (pointSection p t).ker) k
        (schemeDeltaDimension_reducedSupport_torSheaf_le C
          (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY (integralComponentAt x)
          (pointSection p t).ker k
          (schemeDeltaDimension_integralComponentAt_sup_ker_pointSection_le C p k t x hx hT)) := by
  have := isLocallyNoetherian_projectiveLineProduct C p
  rw [torFormulaSubvarietyProductTotal_eq_of_bound C
    (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY k
    (torSupportBound_pointSection C p hY k t x hx hT)]
  exact intersectionProductCycle_congr_right C
    (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY _
    (congrArg subschemeStructureSheaf (ker_pointSection_eq_integralComponentAt C p t).symm)
    _ _ _ k _ _

/-- The Tag 0B08 summand `W_x · (X × a)` is a `k`-cycle: by part (1)(a) it is the cycle of the
scheme-theoretic intersection `W_x ∩ (X × a)`, which has delta-dimension at most `k`. -/
theorem torFormulaSubvarietyProductTotal_pointSection_mem_cyclesOfDimension
    (hx : relativeDimension C.dimensionFunction
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) x = k + 1)
    (hT : ¬ Set.range (integralComponentAt x).subschemeι ⊆ Set.range (pointSection p t)) :
    haveI : IsLocallyNoetherian (projectiveLineProduct p) :=
      LocallyOfFiniteType.isLocallyNoetherian
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
    torFormulaSubvarietyProductTotal C
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY k x
        ((pointSection p t) (genericPoint X)) ∈
      cyclesOfDimension C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) k := by
  have := isLocallyNoetherian_projectiveLineProduct C p
  have hWD := schemeDeltaDimension_integralComponentAt_sup_ker_pointSection_le C p k t x hx hT
  rw [torFormulaSubvarietyProductTotal_pointSection_eq C p hY k t x hx hT]
  exact intersectionProductCycle_mem_cyclesOfDimension C
    (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY (integralComponentAt x)
    (pointSection p t).ker k hWD

/-- **Part (1)(b) at one component of `α`, at an arbitrary point.** A `k`-cycle whose underlying
cycle is the Tag 0B08 summand `W_x · (X × a)` pushes forward along `pr : X ×_S ℙ¹_S ⟶ X` to the
fibre cycle `[W_{x,a}]_k`. -/
theorem properPushforward_eq_pointFiberCycle_of_coe_eq
    (hd : topologicalKrullDim (projectiveLineProduct p) ≤ (d : WithBot ℕ∞))
    (hx : relativeDimension C.dimensionFunction
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) x = k + 1)
    (hT : ¬ Set.range (integralComponentAt x).subschemeι ⊆ Set.range (pointSection p t))
    (A : CycleGroup C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) k)
    (hA :
      haveI : IsLocallyNoetherian (projectiveLineProduct p) :=
        LocallyOfFiniteType.isLocallyNoetherian
          (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
      A.1 = torFormulaSubvarietyProductTotal C
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY k x
        ((pointSection p t) (genericPoint X))) :
    properPushforward C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) p
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S)) rfl k A =
      cycleAssociatedToClosedSubscheme C p
        (pointFiber p t (integralComponentAt x)).subschemeι k := by
  have := isLocallyNoetherian_projectiveLineProduct C p
  have : IsIntegral (integralComponentAt x).subscheme := isIntegral_integralComponentAt x
  have hWD := schemeDeltaDimension_integralComponentAt_sup_ker_pointSection_le C p k t x hx hT
  rw [show A = ⟨_, intersectionProductCycle_mem_cyclesOfDimension C
    (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY (integralComponentAt x)
    (pointSection p t).ker k hWD⟩ from
    Subtype.ext (hA.trans (torFormulaSubvarietyProductTotal_pointSection_eq C p hY k t x hx hT))]
  exact properPushforward_intersectionProductCycle_eq_pointFiberCycle C p t
    (integralComponentAt x) k d hY hd
    (relativeDimension_familyBase_integralComponentAt_genericPoints C p x hx) hWD

end Component

/-! ### Part (3) at an arbitrary pair -/

section PartThree

variable (Kf : Type u) [Field Kf]
  (hC : C.S = AlgebraicGeometry.Spec (CommRingCat.of Kf))
  [AlgebraicGeometry.IsVariety Kf (p ≫ eqToHom hC)]
  (hY : IsRegular (projectiveLineProduct p)) (k : ℤ) (t t' : Γ(C.S, ⊤))

/-- **`α · (X × a)` is a `k`-cycle.** Every summand is, by part (1)(a). -/
theorem torFormulaCycleIntersectionProduct_pointSection_mem_cyclesOfDimension
    (α : CycleGroup C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) (k + 1))
    (hT : ∀ x ∈ Function.support α.1,
      ¬ Set.range (integralComponentAt x).subschemeι ⊆ Set.range (pointSection p t)) :
    haveI : IsLocallyNoetherian (projectiveLineProduct p) :=
      LocallyOfFiniteType.isLocallyNoetherian
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
    torFormulaCycleIntersectionProduct C
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY k α.1
        (@Function.locallyFinsuppWithin.single (projectiveLineProduct p) _ ℤ (Classical.decEq _) _
          ((pointSection p t) (genericPoint X)) (1 : ℤ)) ∈
      cyclesOfDimension C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) k := by
  have := isLocallyNoetherian_projectiveLineProduct C p
  have : CompactSpace (projectiveLineProduct p) :=
    compactSpace_projectiveLineProduct Kf C hC p
  have hα : (Function.support α.1).Finite := finite_support_of_compactSpace α.1
  rw [torFormulaCycleIntersectionProduct_pointSection_eq_sum C p hY k t α.1 hα]
  refine AddSubgroup.sum_mem _ fun x hx => AddSubgroup.zsmul_mem _ ?_ _
  have hmem : x ∈ Function.support α.1 := hα.mem_toFinset.1 hx
  exact torFormulaSubvarietyProductTotal_pointSection_mem_cyclesOfDimension C p hY k t x
    ((mem_cyclesOfDimension_iff_forall_point C
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) (k + 1) α.1).1 α.2 x hmem)
    (hT x hmem)

/-- **The shape of Tag 0B07 part (3) at an arbitrary pair.** A `k`-cycle `β` on `X` is of the
form `pr_{X,*}(α · X × a - α · X × b)` for a `(k + 1)`-cycle `α` on `X ×_S ℙ¹_S` no component of
which is contained in either of the two sections. -/
def IsPointFibreIntersectionDifference (β : CycleGroup C p k) : Prop :=
  ∃ (α : CycleGroup C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) (k + 1))
    (hT : ∀ x ∈ Function.support α.1,
      ¬ Set.range (integralComponentAt x).subschemeι ⊆ Set.range (pointSection p t))
    (hT' : ∀ x ∈ Function.support α.1,
      ¬ Set.range (integralComponentAt x).subschemeι ⊆ Set.range (pointSection p t')),
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
                (Classical.decEq _) _ ((pointSection p t') (genericPoint X)) (1 : ℤ)),
            torFormulaCycleIntersectionProduct_pointSection_mem_cyclesOfDimension C p Kf hC hY k
              t' α hT'⟩

/-- The zero cycle is of the shape of part (3) at the pair: take `α = 0`. -/
theorem isPointFibreIntersectionDifference_zero :
    IsPointFibreIntersectionDifference C p Kf hC hY k t t' 0 := by
  refine ⟨0, fun x hx => absurd hx ?_, fun x hx => absurd hx ?_, ?_⟩
  · simp
  · simp
  · rw [show (⟨torFormulaCycleIntersectionProduct C
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY k
        (0 : CycleGroup C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) (k + 1)).1
        (@Function.locallyFinsuppWithin.single (projectiveLineProduct p) _ ℤ
          (Classical.decEq _) _ ((pointSection p t) (genericPoint X)) (1 : ℤ)), _⟩ :
          CycleGroup C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) k) = 0 from
      Subtype.ext (cycleIntersectionProduct_zero_left _ _),
      show (⟨torFormulaCycleIntersectionProduct C
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY k
        (0 : CycleGroup C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) (k + 1)).1
        (@Function.locallyFinsuppWithin.single (projectiveLineProduct p) _ ℤ
          (Classical.decEq _) _ ((pointSection p t') (genericPoint X)) (1 : ℤ)), _⟩ :
          CycleGroup C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) k) = 0 from
      Subtype.ext (cycleIntersectionProduct_zero_left _ _)]
    simp

/-- The shape of part (3) at the pair is closed under addition: add the two cycles `α`. -/
theorem isPointFibreIntersectionDifference_add {β γ : CycleGroup C p k}
    (hβ : IsPointFibreIntersectionDifference C p Kf hC hY k t t' β)
    (hγ : IsPointFibreIntersectionDifference C p Kf hC hY k t t' γ) :
    IsPointFibreIntersectionDifference C p Kf hC hY k t t' (β + γ) := by
  obtain ⟨α₁, hT₁, hT'₁, rfl⟩ := hβ
  obtain ⟨α₂, hT₂, hT'₂, rfl⟩ := hγ
  have : CompactSpace (projectiveLineProduct p) :=
    compactSpace_projectiveLineProduct Kf C hC p
  have hf1 : (Function.support α₁.1).Finite := finite_support_of_compactSpace α₁.1
  have hf2 : (Function.support α₂.1).Finite := finite_support_of_compactSpace α₂.1
  have hsupp : ∀ z ∈ Function.support (α₁ + α₂).1,
      z ∈ Function.support α₁.1 ∨ z ∈ Function.support α₂.1 := by
    intro z hz
    by_contra hcon
    simp only [not_or, Function.mem_support, not_not] at hcon
    exact hz (by simp [hcon.1, hcon.2])
  have hTs : ∀ s : Γ(C.S, ⊤), (∀ x ∈ Function.support α₁.1,
        ¬ Set.range (integralComponentAt x).subschemeι ⊆ Set.range (pointSection p s)) →
      (∀ x ∈ Function.support α₂.1,
        ¬ Set.range (integralComponentAt x).subschemeι ⊆ Set.range (pointSection p s)) →
      ∀ x ∈ Function.support (α₁ + α₂).1,
        ¬ Set.range (integralComponentAt x).subschemeι ⊆ Set.range (pointSection p s) :=
    fun _ h₁ h₂ z hz => (hsupp z hz).elim (h₁ z) (h₂ z)
  have hT' := hTs t hT₁ hT₂
  have hT'' := hTs t' hT'₁ hT'₂
  refine ⟨α₁ + α₂, hT', hT'', ?_⟩
  have m0 := torFormulaCycleIntersectionProduct_pointSection_mem_cyclesOfDimension C p Kf hC hY k
    t (α₁ + α₂) hT'
  have m01 := torFormulaCycleIntersectionProduct_pointSection_mem_cyclesOfDimension C p Kf hC hY k
    t α₁ hT₁
  have m02 := torFormulaCycleIntersectionProduct_pointSection_mem_cyclesOfDimension C p Kf hC hY k
    t α₂ hT₂
  have mi := torFormulaCycleIntersectionProduct_pointSection_mem_cyclesOfDimension C p Kf hC hY k
    t' (α₁ + α₂) hT''
  have mi1 := torFormulaCycleIntersectionProduct_pointSection_mem_cyclesOfDimension C p Kf hC hY k
    t' α₁ hT'₁
  have mi2 := torFormulaCycleIntersectionProduct_pointSection_mem_cyclesOfDimension C p Kf hC hY k
    t' α₂ hT'₂
  rw [show (⟨_, m0⟩ :
        CycleGroup C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) k) =
        ⟨_, m01⟩ + ⟨_, m02⟩ from
      Subtype.ext (cycleIntersectionProduct_add_left _ hf1 hf2
        (finite_support_of_compactSpace _)),
    show (⟨_, mi⟩ :
        CycleGroup C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) k) =
        ⟨_, mi1⟩ + ⟨_, mi2⟩ from
      Subtype.ext (cycleIntersectionProduct_add_left _ hf1 hf2
        (finite_support_of_compactSpace _)),
    properPushforward_add, properPushforward_add]
  abel

/-- The shape of part (3) at the pair is closed under negation: negate the cycle `α`. -/
theorem isPointFibreIntersectionDifference_neg {β : CycleGroup C p k}
    (hβ : IsPointFibreIntersectionDifference C p Kf hC hY k t t' β) :
    IsPointFibreIntersectionDifference C p Kf hC hY k t t' (-β) := by
  obtain ⟨α, hTα, hT'α, rfl⟩ := hβ
  have : CompactSpace (projectiveLineProduct p) :=
    compactSpace_projectiveLineProduct Kf C hC p
  have hfα : (Function.support α.1).Finite := finite_support_of_compactSpace α.1
  have hfn : (Function.support (-α).1).Finite := finite_support_of_compactSpace (-α).1
  have hsupp : ∀ z ∈ Function.support (-α).1, z ∈ Function.support α.1 := by
    intro z hz
    simp only [Function.mem_support] at hz ⊢
    intro hcon
    exact hz (by simp [hcon])
  have hT' : ∀ x ∈ Function.support (-α).1,
      ¬ Set.range (integralComponentAt x).subschemeι ⊆ Set.range (pointSection p t) :=
    fun z hz => hTα z (hsupp z hz)
  have hT'' : ∀ x ∈ Function.support (-α).1,
      ¬ Set.range (integralComponentAt x).subschemeι ⊆ Set.range (pointSection p t') :=
    fun z hz => hT'α z (hsupp z hz)
  refine ⟨-α, hT', hT'', ?_⟩
  have m0 := torFormulaCycleIntersectionProduct_pointSection_mem_cyclesOfDimension C p Kf hC hY k
    t (-α) hT'
  have m0α := torFormulaCycleIntersectionProduct_pointSection_mem_cyclesOfDimension C p Kf hC hY k
    t α hTα
  have mi := torFormulaCycleIntersectionProduct_pointSection_mem_cyclesOfDimension C p Kf hC hY k
    t' (-α) hT''
  have miα := torFormulaCycleIntersectionProduct_pointSection_mem_cyclesOfDimension C p Kf hC hY k
    t' α hT'α
  have hneg : ∀ (y : projectiveLineProduct p),
      cycleIntersectionProduct (torFormulaSubvarietyProductTotal C
            (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY k) (-α).1
          (@Function.locallyFinsuppWithin.single (projectiveLineProduct p) _ ℤ
            (Classical.decEq _) _ y (1 : ℤ)) =
        -cycleIntersectionProduct (torFormulaSubvarietyProductTotal C
            (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY k) α.1
          (@Function.locallyFinsuppWithin.single (projectiveLineProduct p) _ ℤ
            (Classical.decEq _) _ y (1 : ℤ)) := by
    intro y
    have hsum := cycleIntersectionProduct_add_left
      (torFormulaSubvarietyProductTotal C
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY k) hfα hfn
      (finite_support_of_compactSpace
        (@Function.locallyFinsuppWithin.single (projectiveLineProduct p) _ ℤ
          (Classical.decEq _) _ y (1 : ℤ)))
    rw [show α.1 + (-α).1 = 0 from by simp, cycleIntersectionProduct_zero_left] at hsum
    exact eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact hsum.symm)
  rw [show (⟨_, m0⟩ :
        CycleGroup C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) k) =
        -⟨_, m0α⟩ from Subtype.ext (hneg _),
    show (⟨_, mi⟩ :
        CycleGroup C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) k) =
        -⟨_, miα⟩ from Subtype.ext (hneg _),
    properPushforward_neg, properPushforward_neg]
  abel

/-- A basic rational equivalence at the pair is of the shape of part (3): take `α = [W]`, the
prime cycle of the closed subvariety `W` whose two fibre cycles at `a` and `b` it is the
difference of. -/
theorem isPointFibreIntersectionDifference_of_mem_pointFibreDifferences {γ : CycleGroup C p k}
    (hγ : γ ∈ pointFibreDifferences C p k t t') :
    IsPointFibreIntersectionDifference C p Kf hC hY k t t' γ := by
  obtain ⟨W, hWint, hDim, hTW, hT'W, rfl⟩ := hγ
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
  have hT'w : ¬ Set.range
      (integralComponentAt (W.subschemeι (genericPoint W.subscheme))).subschemeι ⊆
        Set.range (pointSection p t') := by rw [← hW]; exact hT'W
  have hsingle : ∀ z ∈ Function.support (@Function.locallyFinsuppWithin.single
      (projectiveLineProduct p) _ ℤ (Classical.decEq _) _
      (W.subschemeι (genericPoint W.subscheme)) (1 : ℤ)),
      z = W.subschemeι (genericPoint W.subscheme) := by
    intro z hz
    by_contra hne
    exact hz (by simp [Function.locallyFinsuppWithin.single_apply, hne])
  have hmemsingle : (@Function.locallyFinsuppWithin.single (projectiveLineProduct p) _ ℤ
      (Classical.decEq _) _ (W.subschemeι (genericPoint W.subscheme)) (1 : ℤ)) ∈
      cyclesOfDimension C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) (k + 1) := by
    rw [mem_cyclesOfDimension_iff_forall_point]
    intro z hz
    rw [hsingle z hz]
    exact hwdim
  obtain ⟨α, hαdef⟩ : ∃ a : CycleGroup C
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) (k + 1),
      a.1 = @Function.locallyFinsuppWithin.single (projectiveLineProduct p) _ ℤ
        (Classical.decEq _) _ (W.subschemeι (genericPoint W.subscheme)) (1 : ℤ) :=
    ⟨⟨_, hmemsingle⟩, rfl⟩
  have hTα : ∀ s : Γ(C.S, ⊤),
      ¬ Set.range (integralComponentAt (W.subschemeι (genericPoint W.subscheme))).subschemeι ⊆
        Set.range (pointSection p s) → ∀ x ∈ Function.support α.1,
      ¬ Set.range (integralComponentAt x).subschemeι ⊆ Set.range (pointSection p s) := by
    intro s h z hz
    rw [hsingle z (hαdef ▸ hz)]
    exact h
  have hT'' := hTα t hTw
  have hT''' := hTα t' hT'w
  refine ⟨α, hT'', hT''', ?_⟩
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_projectiveLineProduct_le Kf C hC p
  have m0 := torFormulaCycleIntersectionProduct_pointSection_mem_cyclesOfDimension C p Kf hC hY k
    t α hT''
  have mi := torFormulaCycleIntersectionProduct_pointSection_mem_cyclesOfDimension C p Kf hC hY k
    t' α hT'''
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
    properPushforward_eq_pointFiberCycle_of_coe_eq C p hY k d t'
      (W.subschemeι (genericPoint W.subscheme)) hd hwdim hT'w ⟨_, mi⟩ (hprod _),
    ← hW]

/-- **Stacks 0B07, part (3), at an arbitrary pair of distinct closed points of the affine
chart.** Every `k`-cycle rationally equivalent to zero is of the form
`pr_{X,*}(α · X × a - α · X × b)`. -/
theorem isPointFibreIntersectionDifference_of_mem_rationalEquivalences [IsAlgClosed Kf]
    (hne : t ≠ t') (β : CycleGroup C p k) (hβ : β ∈ rationalEquivalences C p k) :
    IsPointFibreIntersectionDifference C p Kf hC hY k t t' β := by
  rw [rationalEquivalences_eq_closure_pointFibreDifferences_of_ne Kf C hC p k t t' hne] at hβ
  exact AddSubgroup.closure_induction
    (fun x hx => isPointFibreIntersectionDifference_of_mem_pointFibreDifferences C p Kf hC hY k
      t t' hx)
    (isPointFibreIntersectionDifference_zero C p Kf hC hY k t t')
    (fun x y _ _ ihx ihy => isPointFibreIntersectionDifference_add C p Kf hC hY k t t' ihx ihy)
    (fun x _ ih => isPointFibreIntersectionDifference_neg C p Kf hC hY k t t' ih) hβ

end PartThree

end PointCycle

end Stacks.Chow

end
