module

public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.FibreDifferencePushforward
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.DivisorFibreCycle
import StacksCore.Tactic.StacksAttribute

/-!
# Pushing the fibre cycle of `X ×_S ℙ¹_S` down to `X`

Let `f : X ⟶ S` and let `W ⊆ X ×_S ℙ¹_S` be a closed subscheme. The scheme-theoretic
intersection of `W` with the image of the zero section is cut out by `W ⊔ (zeroSection f).ker`,
and this file shows that its cycle on `X ×_S ℙ¹_S` is carried by the proper pushforward along
the first projection to the cycle of the zero fibre `W₀` on `X`.

## Main results

* `Stacks.Chow.properPushforward_cycleAssociatedToClosedSubscheme_sup_ker_zeroSection` and its
  infinity twin — the pushforward identity.

## References

* [Stacks Project, Tag 0B07](https://stacks.math.columbia.edu/tag/0B07)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

section Ker

variable {X S : Scheme.{u}} (f : X ⟶ S) (W : (projectiveLineProduct f).IdealSheafData)

/-- The scheme-theoretic intersection of `W` with the image of the zero section, presented
through the zero divisor of `W`. -/
theorem ker_zeroDivisor_subschemeι_comp_subschemeι [IsReduced W.subscheme] :
    ((zeroDivisor f W).subschemeι ≫ W.subschemeι).ker = W ⊔ (zeroSection f).ker := by
  rw [← Scheme.IdealSheafData.map_ker, Scheme.IdealSheafData.ker_subschemeι,
    zeroDivisor_eq_comap_ker f W,
    Stacks.IdealSheaf.map_comap_of_isClosedImmersion W.subschemeι (zeroSection f).ker,
    Scheme.IdealSheafData.ker_subschemeι, sup_comm]

/-- The scheme-theoretic intersection of `W` with the image of the infinity section, presented
through the infinity divisor of `W`. -/
theorem ker_infinityDivisor_subschemeι_comp_subschemeι [IsReduced W.subscheme] :
    ((infinityDivisor f W).subschemeι ≫ W.subschemeι).ker = W ⊔ (infinitySection f).ker := by
  rw [← Scheme.IdealSheafData.map_ker, Scheme.IdealSheafData.ker_subschemeι,
    infinityDivisor_eq_comap_ker f W,
    Stacks.IdealSheaf.map_comap_of_isClosedImmersion W.subschemeι (infinitySection f).ker,
    Scheme.IdealSheafData.ker_subschemeι, sup_comm]

end Ker

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]
  (W : (projectiveLineProduct p).IdealSheafData) (k : ℤ)

/-- **Stacks 0B07, the pushforward of part (1)(b), for the zero section.** The cycle on
`X ×_S ℙ¹_S` of the scheme-theoretic intersection of `W` with the image of the zero section is
carried by the proper pushforward along the first projection to the cycle of the zero fibre of
`W` on `X`. -/
theorem properPushforward_cycleAssociatedToClosedSubscheme_sup_ker_zeroSection
    [IsReduced W.subscheme] :
    properPushforward C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) p
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S)) rfl k
        (cycleAssociatedToClosedSubscheme C
          (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
          (W ⊔ (zeroSection p).ker).subschemeι k) =
      cycleAssociatedToClosedSubscheme C p (zeroFiber p W).subschemeι k := by
  have hci : IsClosedImmersion
      (((zeroDivisor p W).subschemeι ≫ W.subschemeι) ≫
        pullback.fst p (relativeProjectiveLine C.S ↘ C.S)) := by
    rw [Category.assoc]
    exact isClosedImmersion_zeroDivisor_subschemeι_comp p W
  rw [← ker_zeroDivisor_subschemeι_comp_subschemeι p W,
    ← cycleAssociatedToClosedSubscheme_ker C
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
      ((zeroDivisor p W).subschemeι ≫ W.subschemeι) k,
    properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp C
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) p
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S)) rfl
      ((zeroDivisor p W).subschemeι ≫ W.subschemeι) k,
    cycleAssociatedToClosedSubscheme_ker C p
      (((zeroDivisor p W).subschemeι ≫ W.subschemeι) ≫
        pullback.fst p (relativeProjectiveLine C.S ↘ C.S)) k,
    Category.assoc, ← fibreBaseProjection_def p W, ker_zeroDivisor_subschemeι_comp p W]

/-- **Stacks 0B07, the pushforward of part (1)(b), for the infinity section.** -/
theorem properPushforward_cycleAssociatedToClosedSubscheme_sup_ker_infinitySection
    [IsReduced W.subscheme] :
    properPushforward C (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) p
        (pullback.fst p (relativeProjectiveLine C.S ↘ C.S)) rfl k
        (cycleAssociatedToClosedSubscheme C
          (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
          (W ⊔ (infinitySection p).ker).subschemeι k) =
      cycleAssociatedToClosedSubscheme C p (infinityFiber p W).subschemeι k := by
  have hci : IsClosedImmersion
      (((infinityDivisor p W).subschemeι ≫ W.subschemeι) ≫
        pullback.fst p (relativeProjectiveLine C.S ↘ C.S)) := by
    rw [Category.assoc]
    exact isClosedImmersion_infinityDivisor_subschemeι_comp p W
  rw [← ker_infinityDivisor_subschemeι_comp_subschemeι p W,
    ← cycleAssociatedToClosedSubscheme_ker C
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
      ((infinityDivisor p W).subschemeι ≫ W.subschemeι) k,
    properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp C
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p) p
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S)) rfl
      ((infinityDivisor p W).subschemeι ≫ W.subschemeι) k,
    cycleAssociatedToClosedSubscheme_ker C p
      (((infinityDivisor p W).subschemeι ≫ W.subschemeι) ≫
        pullback.fst p (relativeProjectiveLine C.S ↘ C.S)) k,
    Category.assoc, ← fibreBaseProjection_def p W, ker_infinityDivisor_subschemeι_comp p W]

end Stacks.Chow

end
