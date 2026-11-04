module

public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.CoherentSupportDimension
public import StacksFrontier.AlgebraicGeometry.Chow.FamilyFibreDivisors.FibreDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.InverseImageDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.FibreCycleRationalEquivalence

/-!
# Proper intersection with a distinguished fibre, in the form the Tor formula consumes

Tag 0B07 assumes that the closed subvariety `W ⊆ X ×_S ℙ¹_S` of dimension `k + 1` *intersects
`X × a` properly*. The Section 43.14 product of Tag 0AZR consumes that hypothesis twice over:
as a bound on the delta-dimension of the scheme-theoretic intersection `W ∩ (X × a)`, cut out
by `W ⊔ (zeroSection p).ker`, and as a bound on the delta-dimension of the support of each
`Tor` sheaf of the two structure sheaves. This file derives both from the geometric hypothesis
of Section 43.8 that `W` is not contained in the section.

## Main results

* `Stacks.Chow.schemeDeltaDimension_sup_ker_zeroSection_le` and its infinity twin — for an
  integral `W` of relative dimension `k + 1` not contained in the section, the
  scheme-theoretic intersection `W ∩ (X × 0)` has delta-dimension at most `k`.

## References

* [Stacks Project, Tag 0B07](https://stacks.math.columbia.edu/tag/0B07)
* [Stacks Project, Tag 02S4](https://stacks.math.columbia.edu/tag/02S4)
* [Stacks Project, Tag 02RK](https://stacks.math.columbia.edu/tag/02RK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

attribute [local instance 100000] HasDerivedCategory.standard

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]
  (W : (projectiveLineProduct p).IdealSheafData)

/-- If a divisor `D` of `W` has kernel `W ⊔ K` in `X ×_S ℙ¹_S`, then `W ⊔ K` and `D` have the
same delta-dimension. -/
private theorem schemeDeltaDimension_sup_eq_of_ker_eq [IsReduced W.subscheme]
    {K : (projectiveLineProduct p).IdealSheafData} (D : W.subscheme.IdealSheafData)
    (hker : (D.subschemeι ≫ W.subschemeι).ker = W ⊔ K) :
    schemeDeltaDimension C ((W ⊔ K).subschemeι ≫
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)) =
      schemeDeltaDimension C (D.subschemeι ≫ familyBase p W) := by
  have hrange : Set.range (W ⊔ K).subschemeι.base =
      Set.range (D.subschemeι ≫ W.subschemeι).base := by
    rw [Scheme.IdealSheafData.range_subschemeι, ← hker, Scheme.Hom.support_ker]
    exact (IsClosedImmersion.isClosedEmbedding
      (D.subschemeι ≫ W.subschemeι)).isClosed_range.closure_eq
  rw [schemeDeltaDimension_eq_of_equal_ranges C
    (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)
    (W ⊔ K).subschemeι (D.subschemeι ≫ W.subschemeι) hrange]
  exact schemeDeltaDimension_congr C (Category.assoc D.subschemeι W.subschemeι
    (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p))

/-- **Proper intersection with the zero section, as a delta-dimension bound on the
scheme-theoretic intersection.** For an integral closed subscheme `W ⊆ X ×_S ℙ¹_S` of relative
dimension `k + 1` not contained in the image of the zero section, the closed subscheme
`W ∩ (X × 0)` cut out by `W ⊔ (zeroSection p).ker` has delta-dimension at most `k`.

Read on `X ×_S ℙ¹_S` this intersection has the same underlying closed set as the zero divisor
of `W`, an effective Cartier divisor on `W` by Tag 02S4, whose delta-dimension drops by one. -/
theorem schemeDeltaDimension_sup_ker_zeroSection_le [IsIntegral W.subscheme] {k : ℤ}
    (hDim : ∀ ξ : genericPoints W.subscheme,
      relativeDimension C.dimensionFunction (familyBase p W) ξ.1 = k + 1)
    (h₀ : ¬ Set.range W.subschemeι ⊆ Set.range (zeroSection p)) :
    schemeDeltaDimension C ((W ⊔ (zeroSection p).ker).subschemeι ≫
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)) ≤ (k : EInt) := by
  rw [schemeDeltaDimension_sup_eq_of_ker_eq C p W _
    (ker_zeroDivisor_subschemeι_comp_subschemeι p W),
    ← schemeDeltaDimension_zeroFiber_eq_zeroDivisor C p W]
  exact schemeDeltaDimension_zeroFiber_le C p W hDim h₀

/-- **Proper intersection with the infinity section.** The infinity-section twin of
`Stacks.Chow.schemeDeltaDimension_sup_ker_zeroSection_le`. -/
theorem schemeDeltaDimension_sup_ker_infinitySection_le [IsIntegral W.subscheme] {k : ℤ}
    (hDim : ∀ ξ : genericPoints W.subscheme,
      relativeDimension C.dimensionFunction (familyBase p W) ξ.1 = k + 1)
    (hInf : ¬ Set.range W.subschemeι ⊆ Set.range (infinitySection p)) :
    schemeDeltaDimension C ((W ⊔ (infinitySection p).ker).subschemeι ≫
      (pullback.fst p (relativeProjectiveLine C.S ↘ C.S) ≫ p)) ≤ (k : EInt) := by
  rw [schemeDeltaDimension_sup_eq_of_ker_eq C p W _
    (ker_infinityDivisor_subschemeι_comp_subschemeι p W),
    ← schemeDeltaDimension_infinityFiber_eq_infinityDivisor C p W]
  exact schemeDeltaDimension_infinityFiber_le C p W hDim hInf

end Stacks.Chow

end
