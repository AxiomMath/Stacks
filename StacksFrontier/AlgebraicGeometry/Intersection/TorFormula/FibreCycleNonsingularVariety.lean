module

public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.ProductRegular
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.ProjectiveLineProductDimension
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.FibreCycleRationalEquivalenceCycle
import StacksCore.Tactic.StacksAttribute

/-!
# Tag 0B07 for a nonsingular variety, with no hypothesis on the ambient `X × P¹`

Tag 0B07 is a statement about a *nonsingular variety* `X` over an algebraically closed field.
`StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.FibreCycleRationalEquivalence` and
`...FibreCycleRationalEquivalenceCycle` prove its parts over an arbitrary Chow situation, which
is more general in the base but leaves regularity of the ambient family `X ×_S ℙ¹_S` as a
hypothesis `hY`, because over an arbitrary base it does not follow. This file specializes them
to the source's own setting, where it does follow:
`Stacks.Chow.isRegular_projectiveLineProduct` derives it from nonsingularity of `X`, the
projective line being smooth over its base. So the statements here assume about `X` exactly what
the source assumes — that it is a nonsingular variety over an algebraically closed field — and
nothing at all about `X ×_S ℙ¹_S`. The bound on the Krull dimension of the family that makes
the alternating `Tor` sum finite is not assumed either: it is
`Stacks.Chow.exists_topologicalKrullDim_projectiveLineProduct_le`, which holds for the
projective-line family of every variety, and the source states no such bound.

The second hypothesis the Section 43.14 product used to take, the delta-dimension bounds on the
supports of the `Tor` sheaves, is not assumed anywhere either: it is
`AlgebraicGeometry.TorFormula.schemeDeltaDimension_reducedSupport_torSheaf_le`, derived from
proper intersection.

## Main results

* `cycleAssociatedToClosedSubscheme_sup_zeroSection_eq_intersectionProductCycle_of_isRegular` and
  its infinity twin — **Tag 0B07 part (1)(a)** for a nonsingular variety.
* `Stacks.Chow.properPushforward_intersectionProductCycle_eq_zeroFiberCycle_of_isRegular` and its
  infinity twin — **Tag 0B07 part (1)(b)** for a nonsingular variety.
* `sub_properPushforward_intersectionProductCycle_mem_rationalEquivalences_of_isRegular` —
  **Tag 0B07 part (2) for a prime cycle** for a nonsingular variety.
* `sub_properPushforward_torFormulaCycleIntersectionProduct_mem_rationalEquivalences_of_isRegular`
  — **Tag 0B07 part (2) in full** for a nonsingular variety.
* `Stacks.Chow.isFibreIntersectionDifference_of_mem_rationalEquivalences_of_isRegular` —
  **Tag 0B07 part (3)**, the converse, for a nonsingular variety.

## Implementation notes

Each statement is the corresponding statement of the two files above with the regularity
argument supplied by `Stacks.Chow.isRegular_projectiveLineProduct_of_eq` instead of assumed,
and with the Krull-dimension bound on the family obtained from
`Stacks.Chow.exists_topologicalKrullDim_projectiveLineProduct_le` instead of assumed; an
algebraically closed field is perfect, which is what the first derivation needs, and the second
needs only that `X` is a variety over the ground field. Nothing is reproved.

The pair of distinct closed points of the projective line is still `a = 0`, `b = ∞`, the
traditional choice the source itself makes in Section 43.8 and the one
`Stacks.Chow.fibreDifferences` (Tag 0AZG) is built on. Moving an arbitrary pair of distinct
closed points there is the 2-transitivity of Tag 0B2U, which is not invoked, here or in the files
this one specializes.

## References

* [Stacks Project, Tag 0B07](https://stacks.math.columbia.edu/tag/0B07)
* [Stacks Project, Tag 0AZR](https://stacks.math.columbia.edu/tag/0AZR)
* [Stacks Project, Tag 0AZG](https://stacks.math.columbia.edu/tag/0AZG)
* [Stacks Project, Tag 056S](https://stacks.math.columbia.edu/tag/056S)
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
  (hX : IsRegular X) (k : ℤ)

/-! ### Part (1)(a) -/

/-- **Stacks 0B07, part (1)(a), for a nonsingular variety, at the zero section.** The cycle
`[W_a]_k` of the scheme-theoretic intersection `W ∩ (X × a)` is the Section 43.14 intersection
product `W · (X × a)` on `X ×_S ℙ¹_S`. Nothing is assumed about the ambient family: its
regularity comes from nonsingularity of `X`, and the finiteness of the alternating `Tor` sum
from `Stacks.Chow.exists_topologicalKrullDim_projectiveLineProduct_le`. -/
theorem cycleAssociatedToClosedSubscheme_sup_zeroSection_eq_intersectionProductCycle_of_isRegular
    (W : (projectiveLineProduct p).IdealSheafData) [IsIntegral W.subscheme]
    (hDim : ∀ ξ : genericPoints W.subscheme,
      relativeDimension C.dimensionFunction (familyBase p W) ξ.1 = k + 1)
    (hWD : schemeDeltaDimension C ((W ⊔ (zeroSection p).ker).subschemeι ≫
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)) ≤ (k : EInt)) :
    haveI : IsLocallyNoetherian (projectiveLineProduct p) :=
      LocallyOfFiniteType.isLocallyNoetherian
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
    (cycleAssociatedToClosedSubscheme C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
        (W ⊔ (zeroSection p).ker).subschemeι k).1 =
      intersectionProductCycle C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
        (isRegular_projectiveLineProduct_of_eq p hC hX)
        (subschemeStructureSheaf W) (subschemeStructureSheaf (zeroSection p).ker)
        (isCoherent_subschemeStructureSheaf W)
        (isCoherent_subschemeStructureSheaf (zeroSection p).ker) k
        (schemeDeltaDimension_reducedSupport_torSheaf_le C
          (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
          (isRegular_projectiveLineProduct_of_eq p hC hX) W (zeroSection p).ker k hWD) := by
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_projectiveLineProduct_le Kf C hC p
  exact cycleAssociatedToClosedSubscheme_sup_eq_intersectionProductCycle C
    (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
    (isRegular_projectiveLineProduct_of_eq p hC hX) W (zeroSection p).ker k d hd hWD
    (localConditions_ker_zeroSection C p W hDim hWD)

/-- **Stacks 0B07, part (1)(a), for a nonsingular variety, at the infinity section.** The
infinity twin of
`cycleAssociatedToClosedSubscheme_sup_zeroSection_eq_intersectionProductCycle_of_isRegular`. -/
theorem
    cycleAssociatedToClosedSubscheme_sup_infinitySection_eq_intersectionProductCycle_of_isRegular
    (W : (projectiveLineProduct p).IdealSheafData) [IsIntegral W.subscheme]
    (hDim : ∀ ξ : genericPoints W.subscheme,
      relativeDimension C.dimensionFunction (familyBase p W) ξ.1 = k + 1)
    (hWD : schemeDeltaDimension C ((W ⊔ (infinitySection p).ker).subschemeι ≫
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)) ≤ (k : EInt)) :
    haveI : IsLocallyNoetherian (projectiveLineProduct p) :=
      LocallyOfFiniteType.isLocallyNoetherian
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
    (cycleAssociatedToClosedSubscheme C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
        (W ⊔ (infinitySection p).ker).subschemeι k).1 =
      intersectionProductCycle C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
        (isRegular_projectiveLineProduct_of_eq p hC hX)
        (subschemeStructureSheaf W) (subschemeStructureSheaf (infinitySection p).ker)
        (isCoherent_subschemeStructureSheaf W)
        (isCoherent_subschemeStructureSheaf (infinitySection p).ker) k
        (schemeDeltaDimension_reducedSupport_torSheaf_le C
          (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
          (isRegular_projectiveLineProduct_of_eq p hC hX) W (infinitySection p).ker k hWD) := by
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_projectiveLineProduct_le Kf C hC p
  exact cycleAssociatedToClosedSubscheme_sup_eq_intersectionProductCycle C
    (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
    (isRegular_projectiveLineProduct_of_eq p hC hX) W (infinitySection p).ker k d hd hWD
    (localConditions_ker_infinitySection C p W hDim hWD)

/-! ### Part (1)(b) -/

/-- **Stacks 0B07, part (1)(b), for a nonsingular variety, at the zero section.** The cycle
`[W_a]_k` of the fibre of `W` over the section, viewed as a closed subscheme of `X`, is the
proper pushforward along `pr : X ×_S ℙ¹_S ⟶ X` of the Section 43.14 intersection product
`W · (X × a)`. Nothing is assumed about the ambient family. -/
theorem properPushforward_intersectionProductCycle_eq_zeroFiberCycle_of_isRegular
    (W : (projectiveLineProduct p).IdealSheafData) [IsIntegral W.subscheme]
    (hDim : ∀ ξ : genericPoints W.subscheme,
      relativeDimension C.dimensionFunction (familyBase p W) ξ.1 = k + 1)
    (hWD : schemeDeltaDimension C ((W ⊔ (zeroSection p).ker).subschemeι ≫
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)) ≤ (k : EInt)) :
    haveI : IsLocallyNoetherian (projectiveLineProduct p) :=
      LocallyOfFiniteType.isLocallyNoetherian
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
    properPushforward C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) p
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S)) rfl k
        ⟨intersectionProductCycle C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
            (isRegular_projectiveLineProduct_of_eq p hC hX)
            (subschemeStructureSheaf W) (subschemeStructureSheaf (zeroSection p).ker)
            (isCoherent_subschemeStructureSheaf W)
            (isCoherent_subschemeStructureSheaf (zeroSection p).ker) k
            (schemeDeltaDimension_reducedSupport_torSheaf_le C
              (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
              (isRegular_projectiveLineProduct_of_eq p hC hX) W
              (zeroSection p).ker k hWD),
          intersectionProductCycle_mem_cyclesOfDimension C
            (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
            (isRegular_projectiveLineProduct_of_eq p hC hX) W (zeroSection p).ker k hWD⟩ =
      cycleAssociatedToClosedSubscheme C p (zeroFiber p W).subschemeι k := by
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_projectiveLineProduct_le Kf C hC p
  exact properPushforward_intersectionProductCycle_eq_zeroFiberCycle C p W k d
    (isRegular_projectiveLineProduct_of_eq p hC hX) hd hDim hWD

/-- **Stacks 0B07, part (1)(b), for a nonsingular variety, at the infinity section.** The
infinity twin of
`Stacks.Chow.properPushforward_intersectionProductCycle_eq_zeroFiberCycle_of_isRegular`. -/
theorem properPushforward_intersectionProductCycle_eq_infinityFiberCycle_of_isRegular
    (W : (projectiveLineProduct p).IdealSheafData) [IsIntegral W.subscheme]
    (hDim : ∀ ξ : genericPoints W.subscheme,
      relativeDimension C.dimensionFunction (familyBase p W) ξ.1 = k + 1)
    (hWD : schemeDeltaDimension C ((W ⊔ (infinitySection p).ker).subschemeι ≫
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)) ≤ (k : EInt)) :
    haveI : IsLocallyNoetherian (projectiveLineProduct p) :=
      LocallyOfFiniteType.isLocallyNoetherian
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
    properPushforward C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) p
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S)) rfl k
        ⟨intersectionProductCycle C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
            (isRegular_projectiveLineProduct_of_eq p hC hX)
            (subschemeStructureSheaf W) (subschemeStructureSheaf (infinitySection p).ker)
            (isCoherent_subschemeStructureSheaf W)
            (isCoherent_subschemeStructureSheaf (infinitySection p).ker) k
            (schemeDeltaDimension_reducedSupport_torSheaf_le C
              (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
              (isRegular_projectiveLineProduct_of_eq p hC hX) W
              (infinitySection p).ker k hWD),
          intersectionProductCycle_mem_cyclesOfDimension C
            (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
            (isRegular_projectiveLineProduct_of_eq p hC hX) W (infinitySection p).ker k hWD⟩ =
      cycleAssociatedToClosedSubscheme C p (infinityFiber p W).subschemeι k := by
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_projectiveLineProduct_le Kf C hC p
  exact properPushforward_intersectionProductCycle_eq_infinityFiberCycle C p W k d
    (isRegular_projectiveLineProduct_of_eq p hC hX) hd hDim hWD

/-! ### Part (2) -/

/-- **Stacks 0B07, part (2) for a prime cycle, for a nonsingular variety.**
`pr_{X,*}(W · X × 0 - W · X × ∞)` is rationally equivalent to zero, with nothing assumed about
the ambient family. -/
theorem sub_properPushforward_intersectionProductCycle_mem_rationalEquivalences_of_isRegular
    (W : (projectiveLineProduct p).IdealSheafData) [IsIntegral W.subscheme]
    (hDim : ∀ ξ : genericPoints W.subscheme,
      relativeDimension C.dimensionFunction (familyBase p W) ξ.1 = k + 1)
    (h₀ : ¬ Set.range W.subschemeι ⊆ Set.range (zeroSection p))
    (hInf : ¬ Set.range W.subschemeι ⊆ Set.range (infinitySection p))
    (hWD₀ : schemeDeltaDimension C ((W ⊔ (zeroSection p).ker).subschemeι ≫
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)) ≤ (k : EInt))
    (hWDinf : schemeDeltaDimension C ((W ⊔ (infinitySection p).ker).subschemeι ≫
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)) ≤ (k : EInt)) :
    haveI : IsLocallyNoetherian (projectiveLineProduct p) :=
      LocallyOfFiniteType.isLocallyNoetherian
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
    properPushforward C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) p
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S)) rfl k
        ⟨intersectionProductCycle C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
            (isRegular_projectiveLineProduct_of_eq p hC hX)
            (subschemeStructureSheaf W) (subschemeStructureSheaf (zeroSection p).ker)
            (isCoherent_subschemeStructureSheaf W)
            (isCoherent_subschemeStructureSheaf (zeroSection p).ker) k
            (schemeDeltaDimension_reducedSupport_torSheaf_le C
              (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
              (isRegular_projectiveLineProduct_of_eq p hC hX) W
              (zeroSection p).ker k hWD₀),
          intersectionProductCycle_mem_cyclesOfDimension C
            (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
            (isRegular_projectiveLineProduct_of_eq p hC hX) W (zeroSection p).ker k hWD₀⟩ -
      properPushforward C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) p
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S)) rfl k
        ⟨intersectionProductCycle C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
            (isRegular_projectiveLineProduct_of_eq p hC hX)
            (subschemeStructureSheaf W) (subschemeStructureSheaf (infinitySection p).ker)
            (isCoherent_subschemeStructureSheaf W)
            (isCoherent_subschemeStructureSheaf (infinitySection p).ker) k
            (schemeDeltaDimension_reducedSupport_torSheaf_le C
              (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
              (isRegular_projectiveLineProduct_of_eq p hC hX) W
              (infinitySection p).ker k hWDinf),
          intersectionProductCycle_mem_cyclesOfDimension C
            (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
            (isRegular_projectiveLineProduct_of_eq p hC hX) W (infinitySection p).ker
            k hWDinf⟩ ∈
      rationalEquivalences C p k :=
  sub_properPushforward_intersectionProductCycle_mem_rationalEquivalences C p W k Kf hC
    (isRegular_projectiveLineProduct_of_eq p hC hX) hDim h₀ hInf hWD₀ hWDinf

/-- **Stacks 0B07, part (2) in full, for a nonsingular variety.** For an arbitrary
`(k + 1)`-cycle `α` on `X ×_S ℙ¹_S` no component of which is contained in either distinguished
section, `pr_{X,*}(α · X × 0 - α · X × ∞)` is rationally equivalent to zero. -/
theorem
    sub_properPushforward_torFormulaCycleIntersectionProduct_mem_rationalEquivalences_of_isRegular
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
            (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
            (isRegular_projectiveLineProduct_of_eq p hC hX) k α.1
            (@Function.locallyFinsuppWithin.single (projectiveLineProduct p) _ ℤ
              (Classical.decEq _) _ ((zeroSection p) (genericPoint X)) (1 : ℤ)),
          torFormulaCycleIntersectionProduct_zeroSection_mem_cyclesOfDimension C p Kf hC
            (isRegular_projectiveLineProduct_of_eq p hC hX) k α h₀⟩ -
      properPushforward C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) p
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S)) rfl k
        ⟨torFormulaCycleIntersectionProduct C
            (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
            (isRegular_projectiveLineProduct_of_eq p hC hX) k α.1
            (@Function.locallyFinsuppWithin.single (projectiveLineProduct p) _ ℤ
              (Classical.decEq _) _ ((infinitySection p) (genericPoint X)) (1 : ℤ)),
          torFormulaCycleIntersectionProduct_infinitySection_mem_cyclesOfDimension C p Kf hC
            (isRegular_projectiveLineProduct_of_eq p hC hX) k α hInf⟩ ∈
      rationalEquivalences C p k :=
  sub_properPushforward_torFormulaCycleIntersectionProduct_mem_rationalEquivalences C p Kf hC
    (isRegular_projectiveLineProduct_of_eq p hC hX) k α h₀ hInf

/-! ### Part (3), the converse -/

/-- **Stacks 0B07, part (3), for a nonsingular variety.** Every `k`-cycle rationally equivalent
to zero is `pr_{X,*}(α · X × 0 - α · X × ∞)` for a `(k + 1)`-cycle `α` on `X ×_S ℙ¹_S` no
component of which is contained in either distinguished section. -/
theorem isFibreIntersectionDifference_of_mem_rationalEquivalences_of_isRegular
    (β : CycleGroup C p k) (hβ : β ∈ rationalEquivalences C p k) :
    IsFibreIntersectionDifference C p Kf hC
      (isRegular_projectiveLineProduct_of_eq p hC hX) k β :=
  isFibreIntersectionDifference_of_mem_rationalEquivalences C p Kf hC
    (isRegular_projectiveLineProduct_of_eq p hC hX) k β hβ

end Stacks.Chow

end
