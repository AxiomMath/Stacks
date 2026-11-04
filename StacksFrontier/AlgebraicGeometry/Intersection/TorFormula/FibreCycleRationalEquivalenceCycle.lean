module

public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.ProjectiveLineProductDimension
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.CycleIntersectionProduct
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.FibreProperIntersection
import StacksCore.Tactic.StacksAttribute

/-!
# Tag 0B07 parts (2) and (3) for a general cycle

Part (2) of Tag 0B07 says that for a `(k + 1)`-cycle `α` on `X ×_S ℙ¹_S` meeting both `X × a`
and `X × b` properly the `k`-cycle `pr_{X,*}(α · X × a - α · X × b)` is rationally equivalent
to zero, and part (3) is the converse: every `k`-cycle rationally equivalent to zero is of that
form. This file carries both, as the `ℤ`-linear extension of the prime case over the components
of `α` through the bilinear product
`AlgebraicGeometry.TorFormula.torFormulaCycleIntersectionProduct` of Tag 0B08.

## Implementation notes

The hypothesis that `α` meets `X × a` properly is read, component by component, in the form
Section 43.8 and Tag 0AZG use: no component of `α` is contained in the image of the section.
The two delta-dimension bounds the Section 43.14 product of Tag 0AZR needs follow from it, by
`Stacks.Chow.schemeDeltaDimension_sup_ker_zeroSection_le` and
`AlgebraicGeometry.TorFormula.schemeDeltaDimension_reducedSupport_torSheaf_le`.

No bound on the Krull dimension of `X ×_S ℙ¹_S` is assumed: the statements of this file are
over a variety over a field, where one exists by
`Stacks.Chow.exists_topologicalKrullDim_projectiveLineProduct_le`, and the source states none.
What the statements do carry about the ambient family is its regularity `hY`, which over an
arbitrary Chow situation does not follow;
`StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.FibreCycleNonsingularVariety` carries
them for a nonsingular variety over an algebraically closed field with that derived too.

## References

* [Stacks Project, Tag 0B07](https://stacks.math.columbia.edu/tag/0B07)
* [Stacks Project, Tag 0B08](https://stacks.math.columbia.edu/tag/0B08)
* [Stacks Project, Tag 0AZG](https://stacks.math.columbia.edu/tag/0AZG)
* [Stacks Project, Tag 0AZI](https://stacks.math.columbia.edu/tag/0AZI)
-/

@[expose] public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.TorFormula CategoryTheory CategoryTheory.Limits
  TopologicalSpace

universe u

attribute [local instance 100000] HasDerivedCategory.standard

namespace AlgebraicGeometry.TorFormula

/-- The Section 43.14 product depends on its second module only through its value: equal
modules give equal cycles, the coherence witnesses and the delta-dimension bounds being
propositions. -/
theorem intersectionProductCycle_congr_right (C : Stacks.Chow.ChowSituation.{u})
    {Y : Scheme.{u}} (f : Y ⟶ C.S) [LocallyOfFiniteType f] [IsLocallyNoetherian Y]
    (hY : IsRegular Y) (F : Y.Modules) {G G' : Y.Modules} (hG : G = G')
    (cF : SheafOfModules.IsCoherent F) (cG : SheafOfModules.IsCoherent G)
    (cG' : SheafOfModules.IsCoherent G') (k : ℤ)
    (h : ∀ i : ℕ,
      haveI := isCoherent_torSheaf_of_isRegular Y hY F G cF cG i
      Stacks.Chow.schemeDeltaDimension C
        ((Stacks.Chow.reducedSupport (torSheaf Y F G i)).subschemeι ≫ f) ≤ WithBotTop.coe k)
    (h' : ∀ i : ℕ,
      haveI := isCoherent_torSheaf_of_isRegular Y hY F G' cF cG' i
      Stacks.Chow.schemeDeltaDimension C
        ((Stacks.Chow.reducedSupport (torSheaf Y F G' i)).subschemeι ≫ f) ≤ WithBotTop.coe k) :
    intersectionProductCycle C f hY F G cF cG k h =
      intersectionProductCycle C f hY F G' cF cG' k h' := by
  subst hG
  rfl

end AlgebraicGeometry.TorFormula

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]

/-- The Tag 0B08 product `α · y` of a cycle with a point as the finite sum of the products of
the components. -/
private theorem torFormulaCycleIntersectionProduct_single_eq_sum
    (hY : IsRegular (projectiveLineProduct p)) (k : ℤ) (y : projectiveLineProduct p)
    (α : AlgebraicCycle (projectiveLineProduct p) ℤ) (hα : (Function.support α).Finite) :
    haveI : IsLocallyNoetherian (projectiveLineProduct p) :=
      LocallyOfFiniteType.isLocallyNoetherian
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
    torFormulaCycleIntersectionProduct C
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY k α
        (@Function.locallyFinsuppWithin.single (projectiveLineProduct p) _ ℤ (Classical.decEq _) _
          y (1 : ℤ)) =
      ∑ x ∈ hα.toFinset, α x • torFormulaSubvarietyProductTotal C
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY k x y :=
  have : IsLocallyNoetherian (projectiveLineProduct p) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
  @cycleIntersectionProduct_single_right (projectiveLineProduct p) (Classical.decEq _) _ α hα _

/-- The Tor-support bound at a pair of points follows from the delta-dimension bound of the sum
of the ideal sheaves of their reduced closures, `D` being the one of the second. -/
private theorem torSupportBound_of_eq_integralComponentAt
    (hY : IsRegular (projectiveLineProduct p)) (k : ℤ) (x : projectiveLineProduct p)
    {D : (projectiveLineProduct p).IdealSheafData} {y : projectiveLineProduct p}
    (hD : D = integralComponentAt y)
    (hWD : schemeDeltaDimension C ((integralComponentAt x ⊔ D).subschemeι ≫
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)) ≤ (k : EInt)) :
    haveI : IsLocallyNoetherian (projectiveLineProduct p) :=
      LocallyOfFiniteType.isLocallyNoetherian
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
    TorSupportBound C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY k x y := by
  have : IsLocallyNoetherian (projectiveLineProduct p) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
  subst hD
  exact schemeDeltaDimension_reducedSupport_torSheaf_le C
    (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY (integralComponentAt x) _ k hWD

/-- The Tag 0B08 summand `W_x · V` is the Section 43.14 product of the structure sheaves of
`W_x` and of `V = D` when `D` is the reduced closure of the point `y`. -/
private theorem torFormulaSubvarietyProductTotal_eq_of_eq_integralComponentAt
    (hY : IsRegular (projectiveLineProduct p)) (k : ℤ) (x : projectiveLineProduct p)
    {D : (projectiveLineProduct p).IdealSheafData} {y : projectiveLineProduct p}
    (hD : D = integralComponentAt y)
    (hWD : schemeDeltaDimension C ((integralComponentAt x ⊔ D).subschemeι ≫
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)) ≤ (k : EInt)) :
    haveI : IsLocallyNoetherian (projectiveLineProduct p) :=
      LocallyOfFiniteType.isLocallyNoetherian
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
    torFormulaSubvarietyProductTotal C
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY k x y =
      intersectionProductCycle C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY
        (subschemeStructureSheaf (integralComponentAt x)) (subschemeStructureSheaf D)
        (isCoherent_subschemeStructureSheaf (integralComponentAt x))
        (isCoherent_subschemeStructureSheaf D) k
        (schemeDeltaDimension_reducedSupport_torSheaf_le C
          (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY
          (integralComponentAt x) D k hWD) := by
  have : IsLocallyNoetherian (projectiveLineProduct p) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
  rw [torFormulaSubvarietyProductTotal_eq_of_bound C
    (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY k
    (torSupportBound_of_eq_integralComponentAt C p hY k x hD hWD)]
  exact intersectionProductCycle_congr_right C
    (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY _
    (congrArg subschemeStructureSheaf hD.symm) _ _ _ k _ _

/-- The Tag 0B08 summand `W_x · V` is a `k`-cycle when `V = D` is the reduced closure of the
point `y` and `W_x ∩ D` has delta-dimension at most `k`. -/
private theorem torFormulaSubvarietyProductTotal_mem_cyclesOfDimension_of_eq
    (hY : IsRegular (projectiveLineProduct p)) (k : ℤ) (x : projectiveLineProduct p)
    {D : (projectiveLineProduct p).IdealSheafData} {y : projectiveLineProduct p}
    (hD : D = integralComponentAt y)
    (hWD : schemeDeltaDimension C ((integralComponentAt x ⊔ D).subschemeι ≫
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)) ≤ (k : EInt)) :
    haveI : IsLocallyNoetherian (projectiveLineProduct p) :=
      LocallyOfFiniteType.isLocallyNoetherian
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
    torFormulaSubvarietyProductTotal C
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY k x y ∈
      cyclesOfDimension C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) k := by
  have : IsLocallyNoetherian (projectiveLineProduct p) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
  rw [torFormulaSubvarietyProductTotal_eq_of_eq_integralComponentAt C p hY k x hD hWD]
  exact intersectionProductCycle_mem_cyclesOfDimension C
    (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY (integralComponentAt x) D k hWD

/-! ### The image of a distinguished section as the closure of a point -/

omit [LocallyOfFiniteType p] in
/-- The image of the zero section is the reduced closure of the image of the generic point of
`X`: the section is a closed immersion with integral source. -/
theorem ker_zeroSection_eq_integralComponentAt [IsIntegral X] :
    (zeroSection p).ker = integralComponentAt ((zeroSection p) (genericPoint X)) :=
  ker_eq_integralComponentAt (zeroSection p)

omit [LocallyOfFiniteType p] in
/-- The image of the infinity section is the reduced closure of the image of the generic point
of `X`. -/
theorem ker_infinitySection_eq_integralComponentAt [IsIntegral X] :
    (infinitySection p).ker = integralComponentAt ((infinitySection p) (genericPoint X)) :=
  ker_eq_integralComponentAt (infinitySection p)

/-! ### The Tag 0B08 product with a distinguished fibre as a finite sum -/

section Products

variable [IsIntegral X] (hY : IsRegular (projectiveLineProduct p)) (k : ℤ)

/-- **The Tag 0B08 product `α · (X × 0)` as the finite sum of the products of the components.**
-/
theorem torFormulaCycleIntersectionProduct_zeroSection_eq_sum
    (α : AlgebraicCycle (projectiveLineProduct p) ℤ) (hα : (Function.support α).Finite) :
    haveI : IsLocallyNoetherian (projectiveLineProduct p) :=
      LocallyOfFiniteType.isLocallyNoetherian
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
    torFormulaCycleIntersectionProduct C
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY k α
        (@Function.locallyFinsuppWithin.single (projectiveLineProduct p) _ ℤ (Classical.decEq _) _
          ((zeroSection p) (genericPoint X)) (1 : ℤ)) =
      ∑ x ∈ hα.toFinset, α x • torFormulaSubvarietyProductTotal C
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY k x
        ((zeroSection p) (genericPoint X)) :=
  torFormulaCycleIntersectionProduct_single_eq_sum C p hY k _ α hα

/-- **The Tag 0B08 product `α · (X × ∞)` as the finite sum of the products of the components.**
-/
theorem torFormulaCycleIntersectionProduct_infinitySection_eq_sum
    (α : AlgebraicCycle (projectiveLineProduct p) ℤ) (hα : (Function.support α).Finite) :
    haveI : IsLocallyNoetherian (projectiveLineProduct p) :=
      LocallyOfFiniteType.isLocallyNoetherian
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
    torFormulaCycleIntersectionProduct C
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY k α
        (@Function.locallyFinsuppWithin.single (projectiveLineProduct p) _ ℤ (Classical.decEq _) _
          ((infinitySection p) (genericPoint X)) (1 : ℤ)) =
      ∑ x ∈ hα.toFinset, α x • torFormulaSubvarietyProductTotal C
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY k x
        ((infinitySection p) (genericPoint X)) :=
  torFormulaCycleIntersectionProduct_single_eq_sum C p hY k _ α hα

end Products

/-! ### The summand of the Tag 0B08 product at one component of `α` -/

section Component

variable [IsIntegral X] (hY : IsRegular (projectiveLineProduct p)) (k : ℤ) (d : ℕ)
  (x : projectiveLineProduct p)

omit [IsIntegral X] in
/-- The scheme-theoretic intersection of the component `W = closure {x}` of `α` with the image
of the zero section has delta-dimension at most `k`, which is what the Section 43.14 product
needs of the proper-intersection hypothesis. -/
theorem schemeDeltaDimension_integralComponentAt_sup_ker_zeroSection_le
    (hx : relativeDimension C.dimensionFunction
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) x = k + 1)
    (h₀ : ¬ Set.range (integralComponentAt x).subschemeι ⊆ Set.range (zeroSection p)) :
    schemeDeltaDimension C ((integralComponentAt x ⊔ (zeroSection p).ker).subschemeι ≫
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)) ≤ (k : EInt) :=
  have : IsIntegral (integralComponentAt x).subscheme := isIntegral_integralComponentAt x
  schemeDeltaDimension_sup_ker_zeroSection_le C p (integralComponentAt x)
    (relativeDimension_familyBase_integralComponentAt_genericPoints C p x hx) h₀

omit [IsIntegral X] in
/-- The infinity-section twin of
`Stacks.Chow.schemeDeltaDimension_integralComponentAt_sup_ker_zeroSection_le`. -/
theorem schemeDeltaDimension_integralComponentAt_sup_ker_infinitySection_le
    (hx : relativeDimension C.dimensionFunction
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) x = k + 1)
    (hInf : ¬ Set.range (integralComponentAt x).subschemeι ⊆ Set.range (infinitySection p)) :
    schemeDeltaDimension C ((integralComponentAt x ⊔ (infinitySection p).ker).subschemeι ≫
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)) ≤ (k : EInt) :=
  have : IsIntegral (integralComponentAt x).subscheme := isIntegral_integralComponentAt x
  schemeDeltaDimension_sup_ker_infinitySection_le C p (integralComponentAt x)
    (relativeDimension_familyBase_integralComponentAt_genericPoints C p x hx) hInf

/-- The Tor-support bound of Tag 0B08 at the pair consisting of a component of `α` and the
generic point of `X × 0`, from proper intersection. -/
theorem torSupportBound_zeroSection
    (hx : relativeDimension C.dimensionFunction
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) x = k + 1)
    (h₀ : ¬ Set.range (integralComponentAt x).subschemeι ⊆ Set.range (zeroSection p)) :
    haveI : IsLocallyNoetherian (projectiveLineProduct p) :=
      LocallyOfFiniteType.isLocallyNoetherian
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
    TorSupportBound C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY k x
      ((zeroSection p) (genericPoint X)) :=
  torSupportBound_of_eq_integralComponentAt C p hY k x (ker_zeroSection_eq_integralComponentAt C p)
    (schemeDeltaDimension_integralComponentAt_sup_ker_zeroSection_le C p k x hx h₀)

/-- The infinity-section twin of `Stacks.Chow.torSupportBound_zeroSection`. -/
theorem torSupportBound_infinitySection
    (hx : relativeDimension C.dimensionFunction
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) x = k + 1)
    (hInf : ¬ Set.range (integralComponentAt x).subschemeι ⊆ Set.range (infinitySection p)) :
    haveI : IsLocallyNoetherian (projectiveLineProduct p) :=
      LocallyOfFiniteType.isLocallyNoetherian
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
    TorSupportBound C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY k x
      ((infinitySection p) (genericPoint X)) :=
  torSupportBound_of_eq_integralComponentAt C p hY k x
    (ker_infinitySection_eq_integralComponentAt C p)
    (schemeDeltaDimension_integralComponentAt_sup_ker_infinitySection_le C p k x hx hInf)

/-- The Tag 0B08 summand `W_x · (X × 0)` is the Section 43.14 product of the structure sheaf of
`W_x = closure {x}` and that of the image of the zero section. -/
theorem torFormulaSubvarietyProductTotal_zeroSection_eq
    (hx : relativeDimension C.dimensionFunction
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) x = k + 1)
    (h₀ : ¬ Set.range (integralComponentAt x).subschemeι ⊆ Set.range (zeroSection p)) :
    haveI : IsLocallyNoetherian (projectiveLineProduct p) :=
      LocallyOfFiniteType.isLocallyNoetherian
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
    torFormulaSubvarietyProductTotal C
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY k x
        ((zeroSection p) (genericPoint X)) =
      intersectionProductCycle C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY
        (subschemeStructureSheaf (integralComponentAt x))
        (subschemeStructureSheaf (zeroSection p).ker)
        (isCoherent_subschemeStructureSheaf (integralComponentAt x))
        (isCoherent_subschemeStructureSheaf (zeroSection p).ker) k
        (schemeDeltaDimension_reducedSupport_torSheaf_le C
          (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY (integralComponentAt x)
          (zeroSection p).ker k
          (schemeDeltaDimension_integralComponentAt_sup_ker_zeroSection_le C p k x hx h₀)) :=
  torFormulaSubvarietyProductTotal_eq_of_eq_integralComponentAt C p hY k x
    (ker_zeroSection_eq_integralComponentAt C p)
    (schemeDeltaDimension_integralComponentAt_sup_ker_zeroSection_le C p k x hx h₀)

/-- The infinity-section twin of
`Stacks.Chow.torFormulaSubvarietyProductTotal_zeroSection_eq`. -/
theorem torFormulaSubvarietyProductTotal_infinitySection_eq
    (hx : relativeDimension C.dimensionFunction
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) x = k + 1)
    (hInf : ¬ Set.range (integralComponentAt x).subschemeι ⊆ Set.range (infinitySection p)) :
    haveI : IsLocallyNoetherian (projectiveLineProduct p) :=
      LocallyOfFiniteType.isLocallyNoetherian
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
    torFormulaSubvarietyProductTotal C
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY k x
        ((infinitySection p) (genericPoint X)) =
      intersectionProductCycle C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY
        (subschemeStructureSheaf (integralComponentAt x))
        (subschemeStructureSheaf (infinitySection p).ker)
        (isCoherent_subschemeStructureSheaf (integralComponentAt x))
        (isCoherent_subschemeStructureSheaf (infinitySection p).ker) k
        (schemeDeltaDimension_reducedSupport_torSheaf_le C
          (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY (integralComponentAt x)
          (infinitySection p).ker k
          (schemeDeltaDimension_integralComponentAt_sup_ker_infinitySection_le C p k x
            hx hInf)) :=
  torFormulaSubvarietyProductTotal_eq_of_eq_integralComponentAt C p hY k x
    (ker_infinitySection_eq_integralComponentAt C p)
    (schemeDeltaDimension_integralComponentAt_sup_ker_infinitySection_le C p k x hx hInf)

/-- The Tag 0B08 summand `W_x · (X × 0)` is a `k`-cycle: by part (1)(a) it is the cycle of the
scheme-theoretic intersection `W_x ∩ (X × 0)`, which has delta-dimension at most `k`. -/
theorem torFormulaSubvarietyProductTotal_zeroSection_mem_cyclesOfDimension
    (hx : relativeDimension C.dimensionFunction
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) x = k + 1)
    (h₀ : ¬ Set.range (integralComponentAt x).subschemeι ⊆ Set.range (zeroSection p)) :
    haveI : IsLocallyNoetherian (projectiveLineProduct p) :=
      LocallyOfFiniteType.isLocallyNoetherian
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
    torFormulaSubvarietyProductTotal C
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY k x
        ((zeroSection p) (genericPoint X)) ∈
      cyclesOfDimension C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) k :=
  torFormulaSubvarietyProductTotal_mem_cyclesOfDimension_of_eq C p hY k x
    (ker_zeroSection_eq_integralComponentAt C p)
    (schemeDeltaDimension_integralComponentAt_sup_ker_zeroSection_le C p k x hx h₀)

/-- The infinity-section twin of
`Stacks.Chow.torFormulaSubvarietyProductTotal_zeroSection_mem_cyclesOfDimension`. -/
theorem torFormulaSubvarietyProductTotal_infinitySection_mem_cyclesOfDimension
    (hx : relativeDimension C.dimensionFunction
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) x = k + 1)
    (hInf : ¬ Set.range (integralComponentAt x).subschemeι ⊆ Set.range (infinitySection p)) :
    haveI : IsLocallyNoetherian (projectiveLineProduct p) :=
      LocallyOfFiniteType.isLocallyNoetherian
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
    torFormulaSubvarietyProductTotal C
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY k x
        ((infinitySection p) (genericPoint X)) ∈
      cyclesOfDimension C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) k :=
  torFormulaSubvarietyProductTotal_mem_cyclesOfDimension_of_eq C p hY k x
    (ker_infinitySection_eq_integralComponentAt C p)
    (schemeDeltaDimension_integralComponentAt_sup_ker_infinitySection_le C p k x hx hInf)

/-- **Part (1)(b) at one component of `α`.** A `k`-cycle whose underlying cycle is the Tag 0B08
summand `W_x · (X × 0)` pushes forward along `pr : X ×_S ℙ¹_S ⟶ X` to the fibre cycle
`[W_{x,0}]_k`. -/
theorem properPushforward_eq_zeroFiberCycle_of_coe_eq
    (hd : topologicalKrullDim (projectiveLineProduct p) ≤ (d : WithBot ℕ∞))
    (hx : relativeDimension C.dimensionFunction
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) x = k + 1)
    (h₀ : ¬ Set.range (integralComponentAt x).subschemeι ⊆ Set.range (zeroSection p))
    (A : CycleGroup C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) k)
    (hA :
      haveI : IsLocallyNoetherian (projectiveLineProduct p) :=
        LocallyOfFiniteType.isLocallyNoetherian
          (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
      A.1 = torFormulaSubvarietyProductTotal C
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY k x
        ((zeroSection p) (genericPoint X))) :
    properPushforward C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) p
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S)) rfl k A =
      cycleAssociatedToClosedSubscheme C p (zeroFiber p (integralComponentAt x)).subschemeι k := by
  have : IsLocallyNoetherian (projectiveLineProduct p) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
  have hWD₀ := schemeDeltaDimension_integralComponentAt_sup_ker_zeroSection_le C p k x hx h₀
  rw [show A = ⟨_, intersectionProductCycle_mem_cyclesOfDimension C
    (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY (integralComponentAt x)
    (zeroSection p).ker k hWD₀⟩ from
    Subtype.ext (hA.trans (torFormulaSubvarietyProductTotal_zeroSection_eq C p hY k x hx h₀))]
  exact properPushforward_intersectionProductCycle_integralComponentAt_eq_zeroFiberCycle C p x k d
    hY hd hx hWD₀

/-- The infinity-section twin of `Stacks.Chow.properPushforward_eq_zeroFiberCycle_of_coe_eq`. -/
theorem properPushforward_eq_infinityFiberCycle_of_coe_eq
    (hd : topologicalKrullDim (projectiveLineProduct p) ≤ (d : WithBot ℕ∞))
    (hx : relativeDimension C.dimensionFunction
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) x = k + 1)
    (hInf : ¬ Set.range (integralComponentAt x).subschemeι ⊆ Set.range (infinitySection p))
    (A : CycleGroup C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) k)
    (hA :
      haveI : IsLocallyNoetherian (projectiveLineProduct p) :=
        LocallyOfFiniteType.isLocallyNoetherian
          (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
      A.1 = torFormulaSubvarietyProductTotal C
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY k x
        ((infinitySection p) (genericPoint X))) :
    properPushforward C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) p
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S)) rfl k A =
      cycleAssociatedToClosedSubscheme C p
        (infinityFiber p (integralComponentAt x)).subschemeι k := by
  have : IsLocallyNoetherian (projectiveLineProduct p) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
  have hWDinf := schemeDeltaDimension_integralComponentAt_sup_ker_infinitySection_le C p k x hx hInf
  rw [show A = ⟨_, intersectionProductCycle_mem_cyclesOfDimension C
    (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY (integralComponentAt x)
    (infinitySection p).ker k hWDinf⟩ from
    Subtype.ext (hA.trans
      (torFormulaSubvarietyProductTotal_infinitySection_eq C p hY k x hx hInf))]
  exact properPushforward_intersectionProductCycle_integralComponentAt_eq_infinityFiberCycle C p x
    k d hY hd hx hWDinf

end Component

/-! ### Part (2) for a general cycle -/

section PartTwo

variable (Kf : Type u) [Field Kf]
  (hC : C.S = AlgebraicGeometry.Spec (CommRingCat.of Kf))
  [AlgebraicGeometry.IsVariety Kf (p ≫ eqToHom hC)]
  (hY : IsRegular (projectiveLineProduct p)) (k : ℤ)

/-- **`α · y` is a `k`-cycle** once every summand `W_x · y` is. -/
private theorem torFormulaCycleIntersectionProduct_single_mem_cyclesOfDimension
    [CompactSpace (projectiveLineProduct p)] (y : projectiveLineProduct p)
    (α : CycleGroup C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) (k + 1))
    (hy : ∀ x ∈ Function.support α.1,
      relativeDimension C.dimensionFunction
          (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) x = k + 1 →
        haveI : IsLocallyNoetherian (projectiveLineProduct p) :=
          LocallyOfFiniteType.isLocallyNoetherian
            (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
        torFormulaSubvarietyProductTotal C
            (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY k x y ∈
          cyclesOfDimension C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) k) :
    haveI : IsLocallyNoetherian (projectiveLineProduct p) :=
      LocallyOfFiniteType.isLocallyNoetherian
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
    torFormulaCycleIntersectionProduct C
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY k α.1
        (@Function.locallyFinsuppWithin.single (projectiveLineProduct p) _ ℤ (Classical.decEq _) _
          y (1 : ℤ)) ∈
      cyclesOfDimension C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) k := by
  have : IsLocallyNoetherian (projectiveLineProduct p) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
  have hα : (Function.support α.1).Finite := finite_support_of_compactSpace α.1
  rw [torFormulaCycleIntersectionProduct_single_eq_sum C p hY k y α.1 hα]
  refine AddSubgroup.sum_mem _ fun x hx => AddSubgroup.zsmul_mem _ ?_ _
  have hmem : x ∈ Function.support α.1 := hα.mem_toFinset.1 hx
  exact hy x hmem ((mem_cyclesOfDimension_iff_forall_point C
    (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) (k + 1) α.1).1 α.2 x hmem)

/-- **`α · (X × 0)` is a `k`-cycle.** Every summand is, by part (1)(a). -/
theorem torFormulaCycleIntersectionProduct_zeroSection_mem_cyclesOfDimension
    (α : CycleGroup C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) (k + 1))
    (h₀ : ∀ x ∈ Function.support α.1,
      ¬ Set.range (integralComponentAt x).subschemeι ⊆ Set.range (zeroSection p)) :
    haveI : IsLocallyNoetherian (projectiveLineProduct p) :=
      LocallyOfFiniteType.isLocallyNoetherian
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
    torFormulaCycleIntersectionProduct C
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY k α.1
        (@Function.locallyFinsuppWithin.single (projectiveLineProduct p) _ ℤ (Classical.decEq _) _
          ((zeroSection p) (genericPoint X)) (1 : ℤ)) ∈
      cyclesOfDimension C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) k :=
  haveI : CompactSpace (projectiveLineProduct p) :=
    compactSpace_projectiveLineProduct Kf C hC p
  torFormulaCycleIntersectionProduct_single_mem_cyclesOfDimension C p hY k _ α fun x hx hdx =>
    torFormulaSubvarietyProductTotal_zeroSection_mem_cyclesOfDimension C p hY k x hdx (h₀ x hx)

/-- **`α · (X × ∞)` is a `k`-cycle.** -/
theorem torFormulaCycleIntersectionProduct_infinitySection_mem_cyclesOfDimension
    (α : CycleGroup C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) (k + 1))
    (hInf : ∀ x ∈ Function.support α.1,
      ¬ Set.range (integralComponentAt x).subschemeι ⊆ Set.range (infinitySection p)) :
    haveI : IsLocallyNoetherian (projectiveLineProduct p) :=
      LocallyOfFiniteType.isLocallyNoetherian
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
    torFormulaCycleIntersectionProduct C
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY k α.1
        (@Function.locallyFinsuppWithin.single (projectiveLineProduct p) _ ℤ (Classical.decEq _) _
          ((infinitySection p) (genericPoint X)) (1 : ℤ)) ∈
      cyclesOfDimension C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) k :=
  haveI : CompactSpace (projectiveLineProduct p) :=
    compactSpace_projectiveLineProduct Kf C hC p
  torFormulaCycleIntersectionProduct_single_mem_cyclesOfDimension C p hY k _ α fun x hx hdx =>
    torFormulaSubvarietyProductTotal_infinitySection_mem_cyclesOfDimension C p hY k x hdx
      (hInf x hx)

/-- **Stacks 0B07, part (2).** Let `X` be a variety over an algebraically closed field whose
family of projective lines is regular, and let `α` be a `(k + 1)`-cycle on `X ×_S ℙ¹_S` meeting
both `X × 0` and `X × ∞` properly, in the sense that no component of `α` is contained in either
section. Then `pr_{X,*}(α · X × 0 - α · X × ∞)` is rationally equivalent to zero. -/
theorem sub_properPushforward_torFormulaCycleIntersectionProduct_mem_rationalEquivalences
    [IsAlgClosed Kf]
    (α : CycleGroup C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) (k + 1))
    (h₀ : ∀ x ∈ Function.support α.1,
      ¬ Set.range (integralComponentAt x).subschemeι ⊆ Set.range (zeroSection p))
    (hInf : ∀ x ∈ Function.support α.1,
      ¬ Set.range (integralComponentAt x).subschemeι ⊆ Set.range (infinitySection p)) :
    haveI : IsLocallyNoetherian (projectiveLineProduct p) :=
      LocallyOfFiniteType.isLocallyNoetherian
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
    properPushforward C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) p
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S)) rfl k
        ⟨torFormulaCycleIntersectionProduct C
            (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY k α.1
            (@Function.locallyFinsuppWithin.single (projectiveLineProduct p) _ ℤ
              (Classical.decEq _) _ ((zeroSection p) (genericPoint X)) (1 : ℤ)),
          torFormulaCycleIntersectionProduct_zeroSection_mem_cyclesOfDimension C p Kf hC hY k
            α h₀⟩ -
      properPushforward C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) p
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S)) rfl k
        ⟨torFormulaCycleIntersectionProduct C
            (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY k α.1
            (@Function.locallyFinsuppWithin.single (projectiveLineProduct p) _ ℤ
              (Classical.decEq _) _ ((infinitySection p) (genericPoint X)) (1 : ℤ)),
          torFormulaCycleIntersectionProduct_infinitySection_mem_cyclesOfDimension C p Kf hC hY k
            α hInf⟩ ∈
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
  have hdec : ∀ (y : projectiveLineProduct p)
      (hT : ∀ x ∈ hα.toFinset, torFormulaSubvarietyProductTotal C
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY k x y ∈
          cyclesOfDimension C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) k)
      (hm : torFormulaCycleIntersectionProduct C
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY k α.1
        (@Function.locallyFinsuppWithin.single (projectiveLineProduct p) _ ℤ
          (Classical.decEq _) _ y (1 : ℤ)) ∈
          cyclesOfDimension C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) k),
      (⟨_, hm⟩ : CycleGroup C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) k) =
        ∑ x ∈ hα.toFinset.attach, α.1 x.1 •
          (⟨torFormulaSubvarietyProductTotal C
            (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY k x.1 y, hT x.1 x.2⟩ :
            CycleGroup C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) k) := by
    intro y hT hm
    refine Subtype.ext ?_
    change torFormulaCycleIntersectionProduct C
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY k α.1
        (@Function.locallyFinsuppWithin.single (projectiveLineProduct p) _ ℤ
          (Classical.decEq _) _ y (1 : ℤ)) = _
    rw [torFormulaCycleIntersectionProduct_single_eq_sum C p hY k y α.1 hα,
      ← Finset.sum_attach hα.toFinset (fun x => α.1 x • torFormulaSubvarietyProductTotal C
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY k x y)]
    simp
  rw [rationalEquivalences_eq_rationalEquivalencesByFibres Kf C hC p k, hdec _ (fun x hx =>
      torFormulaSubvarietyProductTotal_zeroSection_mem_cyclesOfDimension C p hY k x
        (hdimpt x hx) (h₀ x (hsupp x hx))) _,
    hdec _ (fun x hx =>
      torFormulaSubvarietyProductTotal_infinitySection_mem_cyclesOfDimension C p hY k x
        (hdimpt x hx) (hInf x (hsupp x hx))) _]
  simp only [← properPushforwardHom_apply, map_sum, ← Finset.sum_sub_distrib]
  refine AddSubgroup.sum_mem _ fun x _ => ?_
  rw [map_zsmul, map_zsmul, ← smul_sub, properPushforwardHom_apply, properPushforwardHom_apply,
    properPushforward_eq_zeroFiberCycle_of_coe_eq C p hY k d x.1 hd (hdimpt x.1 x.2)
      (h₀ x.1 (hsupp x.1 x.2)) _ rfl,
    properPushforward_eq_infinityFiberCycle_of_coe_eq C p hY k d x.1 hd (hdimpt x.1 x.2)
      (hInf x.1 (hsupp x.1 x.2)) _ rfl]
  have : IsIntegral (integralComponentAt x.1).subscheme := isIntegral_integralComponentAt x.1
  exact AddSubgroup.zsmul_mem _
    (sub_cycleAssociatedToFibres_mem_rationalEquivalencesByFibres C p k
      (integralComponentAt x.1) inferInstance
      (relativeDimension_familyBase_integralComponentAt_genericPoints C p x.1 (hdimpt x.1 x.2))
      (h₀ x.1 (hsupp x.1 x.2)) (hInf x.1 (hsupp x.1 x.2))) _

end PartTwo

/-! ### Part (3), the converse -/

section PartThree

variable (Kf : Type u) [Field Kf]
  (hC : C.S = AlgebraicGeometry.Spec (CommRingCat.of Kf))
  [AlgebraicGeometry.IsVariety Kf (p ≫ eqToHom hC)]
  (hY : IsRegular (projectiveLineProduct p)) (k : ℤ)

/-- **The shape of Tag 0B07 part (3).** A `k`-cycle `β` on `X` is of the form
`pr_{X,*}(α · X × 0 - α · X × ∞)` for a `(k + 1)`-cycle `α` on `X ×_S ℙ¹_S` no component of
which is contained in either distinguished section. -/
def IsFibreIntersectionDifference (β : CycleGroup C p k) : Prop :=
  ∃ (α : CycleGroup C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) (k + 1))
    (h₀ : ∀ x ∈ Function.support α.1,
      ¬ Set.range (integralComponentAt x).subschemeι ⊆ Set.range (zeroSection p))
    (hInf : ∀ x ∈ Function.support α.1,
      ¬ Set.range (integralComponentAt x).subschemeι ⊆ Set.range (infinitySection p)),
    β =
      properPushforward C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) p
          (pullback.fst p (relativeProjectiveLine C.S ↘ C.S)) rfl k
          ⟨torFormulaCycleIntersectionProduct C
              (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY k α.1
              (@Function.locallyFinsuppWithin.single (projectiveLineProduct p) _ ℤ
                (Classical.decEq _) _ ((zeroSection p) (genericPoint X)) (1 : ℤ)),
            torFormulaCycleIntersectionProduct_zeroSection_mem_cyclesOfDimension C p Kf hC hY k
              α h₀⟩ -
        properPushforward C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) p
          (pullback.fst p (relativeProjectiveLine C.S ↘ C.S)) rfl k
          ⟨torFormulaCycleIntersectionProduct C
              (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY k α.1
              (@Function.locallyFinsuppWithin.single (projectiveLineProduct p) _ ℤ
                (Classical.decEq _) _ ((infinitySection p) (genericPoint X)) (1 : ℤ)),
            torFormulaCycleIntersectionProduct_infinitySection_mem_cyclesOfDimension C p Kf hC hY
              k α hInf⟩

/-- The zero cycle is of the shape of part (3): take `α = 0`. -/
theorem isFibreIntersectionDifference_zero :
    IsFibreIntersectionDifference C p Kf hC hY k 0 := by
  refine ⟨0, fun x hx => absurd hx ?_, fun x hx => absurd hx ?_, ?_⟩
  · simp
  · simp
  · have h0 : ∀ (y : projectiveLineProduct p) (hm : torFormulaCycleIntersectionProduct C
          (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) hY k
          (0 : CycleGroup C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) (k + 1)).1
          (@Function.locallyFinsuppWithin.single (projectiveLineProduct p) _ ℤ
            (Classical.decEq _) _ y (1 : ℤ)) ∈
          cyclesOfDimension C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) k),
        (⟨_, hm⟩ : CycleGroup C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) k) = 0 :=
      fun y _ => Subtype.ext (cycleIntersectionProduct_zero_left _ _)
    rw [h0, h0]
    simp

/-- The shape of part (3) is closed under addition: add the two cycles `α`. -/
theorem isFibreIntersectionDifference_add {β γ : CycleGroup C p k}
    (hβ : IsFibreIntersectionDifference C p Kf hC hY k β)
    (hγ : IsFibreIntersectionDifference C p Kf hC hY k γ) :
    IsFibreIntersectionDifference C p Kf hC hY k (β + γ) := by
  obtain ⟨α₁, h₀₁, hInf₁, rfl⟩ := hβ
  obtain ⟨α₂, h₀₂, hInf₂, rfl⟩ := hγ
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
  have h₀' : ∀ x ∈ Function.support (α₁ + α₂).1,
      ¬ Set.range (integralComponentAt x).subschemeι ⊆ Set.range (zeroSection p) :=
    fun z hz => (hsupp z hz).elim (h₀₁ z) (h₀₂ z)
  have hInf' : ∀ x ∈ Function.support (α₁ + α₂).1,
      ¬ Set.range (integralComponentAt x).subschemeι ⊆ Set.range (infinitySection p) :=
    fun z hz => (hsupp z hz).elim (hInf₁ z) (hInf₂ z)
  refine ⟨α₁ + α₂, h₀', hInf', ?_⟩
  have m0 := torFormulaCycleIntersectionProduct_zeroSection_mem_cyclesOfDimension C p Kf hC hY k
    (α₁ + α₂) h₀'
  have m01 := torFormulaCycleIntersectionProduct_zeroSection_mem_cyclesOfDimension C p Kf hC hY k
    α₁ h₀₁
  have m02 := torFormulaCycleIntersectionProduct_zeroSection_mem_cyclesOfDimension C p Kf hC hY k
    α₂ h₀₂
  have mi := torFormulaCycleIntersectionProduct_infinitySection_mem_cyclesOfDimension C p Kf hC
    hY k (α₁ + α₂) hInf'
  have mi1 := torFormulaCycleIntersectionProduct_infinitySection_mem_cyclesOfDimension C p Kf hC
    hY k α₁ hInf₁
  have mi2 := torFormulaCycleIntersectionProduct_infinitySection_mem_cyclesOfDimension C p Kf hC
    hY k α₂ hInf₂
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

/-- The shape of part (3) is closed under negation: negate the cycle `α`. -/
theorem isFibreIntersectionDifference_neg {β : CycleGroup C p k}
    (hβ : IsFibreIntersectionDifference C p Kf hC hY k β) :
    IsFibreIntersectionDifference C p Kf hC hY k (-β) := by
  obtain ⟨α, h₀α, hInfα, rfl⟩ := hβ
  have : CompactSpace (projectiveLineProduct p) :=
    compactSpace_projectiveLineProduct Kf C hC p
  have hfα : (Function.support α.1).Finite := finite_support_of_compactSpace α.1
  have hfn : (Function.support (-α).1).Finite := finite_support_of_compactSpace (-α).1
  have hsupp : ∀ z ∈ Function.support (-α).1, z ∈ Function.support α.1 := by
    intro z hz
    simp only [Function.mem_support] at hz ⊢
    intro hcon
    exact hz (by simp [hcon])
  have h₀' : ∀ x ∈ Function.support (-α).1,
      ¬ Set.range (integralComponentAt x).subschemeι ⊆ Set.range (zeroSection p) :=
    fun z hz => h₀α z (hsupp z hz)
  have hInf' : ∀ x ∈ Function.support (-α).1,
      ¬ Set.range (integralComponentAt x).subschemeι ⊆ Set.range (infinitySection p) :=
    fun z hz => hInfα z (hsupp z hz)
  refine ⟨-α, h₀', hInf', ?_⟩
  have m0 := torFormulaCycleIntersectionProduct_zeroSection_mem_cyclesOfDimension C p Kf hC hY k
    (-α) h₀'
  have m0α := torFormulaCycleIntersectionProduct_zeroSection_mem_cyclesOfDimension C p Kf hC hY k
    α h₀α
  have mi := torFormulaCycleIntersectionProduct_infinitySection_mem_cyclesOfDimension C p Kf hC
    hY k (-α) hInf'
  have miα := torFormulaCycleIntersectionProduct_infinitySection_mem_cyclesOfDimension C p Kf hC
    hY k α hInfα
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

/-- A basic rational equivalence is of the shape of part (3): take `α = [W]`, the prime cycle
of the closed subvariety `W` whose two distinguished fibres it is the difference of. -/
theorem isFibreIntersectionDifference_of_mem_fibreDifferences {γ : CycleGroup C p k}
    (hγ : γ ∈ fibreDifferences C p k) :
    IsFibreIntersectionDifference C p Kf hC hY k γ := by
  obtain ⟨W, hWint, hDim, h₀W, hInfW, rfl⟩ := hγ
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
  have h₀w : ¬ Set.range
      (integralComponentAt (W.subschemeι (genericPoint W.subscheme))).subschemeι ⊆
        Set.range (zeroSection p) := by rw [← hW]; exact h₀W
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
  have h₀' : ∀ x ∈ Function.support α.1,
      ¬ Set.range (integralComponentAt x).subschemeι ⊆ Set.range (zeroSection p) := by
    intro z hz
    rw [hsupp z hz]
    exact h₀w
  have hInf' : ∀ x ∈ Function.support α.1,
      ¬ Set.range (integralComponentAt x).subschemeι ⊆ Set.range (infinitySection p) := by
    intro z hz
    rw [hsupp z hz]
    exact hInfw
  refine ⟨α, h₀', hInf', ?_⟩
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_projectiveLineProduct_le Kf C hC p
  have m0 := torFormulaCycleIntersectionProduct_zeroSection_mem_cyclesOfDimension C p Kf hC hY k
    α h₀'
  have mi := torFormulaCycleIntersectionProduct_infinitySection_mem_cyclesOfDimension C p Kf hC
    hY k α hInf'
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
  rw [properPushforward_eq_zeroFiberCycle_of_coe_eq C p hY k d
      (W.subschemeι (genericPoint W.subscheme)) hd hwdim h₀w ⟨_, m0⟩ (hprod _),
    properPushforward_eq_infinityFiberCycle_of_coe_eq C p hY k d
      (W.subschemeι (genericPoint W.subscheme)) hd hwdim hInfw ⟨_, mi⟩ (hprod _),
    ← hW]

/-- **Stacks 0B07, part (3).** Conversely, every `k`-cycle rationally equivalent to zero is of
that form. -/
theorem isFibreIntersectionDifference_of_mem_rationalEquivalences [IsAlgClosed Kf]
    (β : CycleGroup C p k) (hβ : β ∈ rationalEquivalences C p k) :
    IsFibreIntersectionDifference C p Kf hC hY k β := by
  rw [rationalEquivalences_eq_rationalEquivalencesByFibres Kf C hC p k,
    rationalEquivalencesByFibres] at hβ
  exact AddSubgroup.closure_induction
    (fun x hx => isFibreIntersectionDifference_of_mem_fibreDifferences C p Kf hC hY k hx)
    (isFibreIntersectionDifference_zero C p Kf hC hY k)
    (fun x y _ _ ihx ihy => isFibreIntersectionDifference_add C p Kf hC hY k ihx ihy)
    (fun x _ ih => isFibreIntersectionDifference_neg C p Kf hC hY k ih) hβ

end PartThree

end Stacks.Chow

end
