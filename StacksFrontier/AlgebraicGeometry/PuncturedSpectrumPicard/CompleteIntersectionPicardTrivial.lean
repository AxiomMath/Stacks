module

public import StacksFrontier.AlgebraicGeometry.PuncturedSpectrumPicard.CompleteIntersection
public import StacksFrontier.AlgebraicGeometry.PuncturedSpectrumPicard.FormalPicardAlgebraization
public import StacksFrontier.RingTheory.LocalCohomology.DepthVanishing.BelowDepth
public import StacksFrontier.RingTheory.AdicCompletion.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Picard group of the punctured spectrum of a complete intersection

Let `(A, 𝔪)` be a Noetherian local ring which is a complete intersection of dimension at least
four. Then the Picard group of the punctured spectrum of `A` is trivial. This is
[Stacks, Tag 0F2I].

## Main results

* `subsingleton_picardGroup_puncturedSpectrum_of_completeIntersection` (in
  `Stacks.PuncturedSpectrumPicard`): **[Stacks, Tag 0F2I]**.
* `Stacks.PuncturedSpectrumPicard.depth_quotient_span_add_one`: `depth(A/fA) + 1 = depth(A)` for
  a nonzerodivisor `f ∈ 𝔪`.
* `Stacks.PuncturedSpectrumPicard.isZero_localCohomology_quotient_of_five_le_depth`:
  `H^i_𝔪(A/fA) = 0` for `i < 4` when `f ∈ 𝔪` is a nonzerodivisor and `depth(A) ≥ 5`.
* `Stacks.PuncturedSpectrumPicard.isAdicComplete_span_of_isAdicComplete_maximalIdeal`: a
  Noetherian local ring complete for `𝔪` is `f`-adically complete for every `f ∈ 𝔪`.
* `Stacks.PuncturedSpectrumPicard.finite_localCohomology_quotient_of_five_le_depth`:
  `H^i_𝔪(A/fA)` is a finite `A`-module for `i < 4` under the same hypotheses.

## References

* [Stacks Project, Tag 0F2I](https://stacks.math.columbia.edu/tag/0F2I)
* [Stacks Project, Tag 0F2D](https://stacks.math.columbia.edu/tag/0F2D)
-/


@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.PuncturedSpectrumPicard

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A] {f : A}

/-- `A/fA` as an `A`-module is `QuotSMulTop f A`. -/
def quotSMulTopEquivQuotientSpan (f : A) : QuotSMulTop f A ≃ₗ[A] A ⧸ Ideal.span {f} :=
  (QuotSMulTop.equivQuotTensor f A).trans (TensorProduct.rid A (A ⧸ Ideal.span {f}))

/-- **Depth drops by one modulo a nonzerodivisor in the maximal ideal**, written for the quotient
ring `A/fA` regarded as an `A`-module: `depth(A/fA) + 1 = depth(A)` in `ℕ∞`. This is
[Stacks, Tag 090R] part (1). -/
theorem depth_quotient_span_add_one (hf : f ∈ maximalIdeal A) (hreg : IsSMulRegular A f) :
    Module.depth A (maximalIdeal A) (A ⧸ Ideal.span {f}) + 1 =
      Module.depth A (maximalIdeal A) A := by
  rw [← Module.depth_eq_depth_of_linearEquiv _ (quotSMulTopEquivQuotientSpan f)]
  exact (Module.depth_quotSMulTop_succ_eq_depth_and_exists_isRegular_append
    (maximalIdeal A) A).1 f hf hreg

/-- If `f ∈ 𝔪` is a nonzerodivisor and `depth(A) ≥ 5`, then `H^i_𝔪(A/fA) = 0` for every
`i < 4`. -/
theorem isZero_localCohomology_quotient_of_five_le_depth (hf : f ∈ maximalIdeal A)
    (hreg : IsSMulRegular A f) (hdepth : 5 ≤ Module.depth A (maximalIdeal A) A)
    (i : ℤ) (hi : i < 4) :
    IsZero (Stacks.LocalCohomology.localCohomologyWithSupportIn.{u, u} A {closedPoint A}
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        (ModuleCat.of A (A ⧸ Ideal.span {f}))) i) := by
  have hd : ((4 : ℕ) : ℕ∞) ≤ Module.depth A (maximalIdeal A) (A ⧸ Ideal.span {f}) := by
    have h := depth_quotient_span_add_one hf hreg
    rw [← h] at hdepth
    by_contra hlt
    push Not at hlt
    have : Module.depth A (maximalIdeal A) (A ⧸ Ideal.span {f}) + 1 ≤ 4 :=
      Order.add_one_le_of_lt hlt
    exact absurd (hdepth.trans this) (by norm_num)
  have hspan : Ideal.span {f} ≠ ⊤ :=
    ne_top_of_le_ne_top (maximalIdeal.isMaximal A).ne_top
      ((Ideal.span_singleton_le_iff_mem _).mpr hf)
  have : Nontrivial (A ⧸ Ideal.span {f}) := Ideal.Quotient.nontrivial_iff.mpr hspan
  have hIM : maximalIdeal A • (⊤ : Submodule A (A ⧸ Ideal.span {f})) ≠ ⊤ :=
    (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator (I := maximalIdeal A)
      (le_of_eq (IsLocalRing.jacobson_eq_maximalIdeal _
        (by rw [Ideal.annihilator_quotient]; exact hspan)).symm)).symm
  have h := Stacks.LocalCohomology.isZero_localCohomology_of_lt_depth.{u, u} (maximalIdeal A)
    (ModuleCat.of A (A ⧸ Ideal.span {f})) hIM 4 hd i (by exact_mod_cast hi)
  rwa [zeroLocus_maximalIdeal] at h

/-- If `f ∈ 𝔪` is a nonzerodivisor and `depth(A) ≥ 5`, then `H^i_𝔪(A/fA)` is a finite
`A`-module for every `i < 4`, being zero. -/
theorem finite_localCohomology_quotient_of_five_le_depth (hf : f ∈ maximalIdeal A)
    (hreg : IsSMulRegular A f) (hdepth : 5 ≤ Module.depth A (maximalIdeal A) A)
    (i : ℤ) (hi : i < 4) :
    Module.Finite A (Stacks.LocalCohomology.localCohomologyWithSupportIn.{u, u} A {closedPoint A}
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        (ModuleCat.of A (A ⧸ Ideal.span {f}))) i) :=
  have := ModuleCat.isZero_iff_subsingleton.mp
    (isZero_localCohomology_quotient_of_five_le_depth hf hreg hdepth i hi)
  Module.Finite.of_finite

/-- A Noetherian local ring complete for its maximal ideal is `f`-adically complete for every
`f ∈ 𝔪`. -/
theorem isAdicComplete_span_of_isAdicComplete_maximalIdeal [IsAdicComplete (maximalIdeal A) A]
    (hf : f ∈ maximalIdeal A) : IsAdicComplete (Ideal.span {f}) A :=
  isAdicComplete_of_le_of_fg_of_isAdicComplete ((Ideal.span_singleton_le_iff_mem _).mpr hf)
    inferInstance (Ideal.fg_of_isNoetherianRing _)

/-! ### Stacks 0F2I -/

/-- **[Stacks, Tag 0F2I]** (Grothendieck). Let `(A, 𝔪)` be a Noetherian local ring. If `A` is a
complete intersection of dimension at least four — its `𝔪`-adic completion is the quotient of a
regular local ring by an ideal generated by a regular sequence — then the Picard group of the
punctured spectrum `U = Spec A ∖ {𝔪}` of `A` is trivial.

The proof is the source's. The induction on the length of the regular sequence, through
[Stacks, Tag 0F2G], [Stacks, Tag 0F2H] and [Stacks, Tag 0F2F], is
`subsingleton_picardGroup_puncturedSpectrum_of_isCompleteIntersectionRing`, which takes the
conclusion of [Stacks, Tag 0F2D] as an input; that input is supplied here by the library's proof
of [Stacks, Tag 0F2D], `picardColimitSurjective`. Its conditions are discharged as in the
source: `f`-adic completeness follows from `𝔪`-adic completeness, the element is a
nonzerodivisor, and `depth(A') ≥ 5` gives `depth(A'/fA') ≥ 4`, so that `H^i_𝔪(A'/fA') = 0` for
`i < 4` (`isZero_localCohomology_quotient_of_five_le_depth`). -/
@[stacks 0F2I "proved in full: Stacks 0F2D is supplied by its proof picardColimitSurjective",
  sga "2 XI 3.13" "XI.3.13(ii)", sga "2 XII 4.9" "4.9 b)"]
theorem subsingleton_picardGroup_puncturedSpectrum_of_completeIntersection
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hA : LocalCompleteIntersection.IsCompleteIntersectionRing A)
    (hdim : 4 ≤ ringKrullDim A) :
    Subsingleton (Stacks.Divisors.puncturedSpectrum A).toScheme.picardGroup :=
  subsingleton_picardGroup_puncturedSpectrum_of_isCompleteIntersectionRing A
    (fun B _ _ _ _ g hg hgnzd hdepth =>
      have hreg : IsSMulRegular B g := Module.Flat.isSMulRegular_of_nonZeroDivisors hgnzd
      picardColimitSurjective B g hg (isAdicComplete_span_of_isAdicComplete_maximalIdeal hg) hreg
        (finite_localCohomology_quotient_of_five_le_depth hg hreg hdepth 1 (by norm_num))
        (finite_localCohomology_quotient_of_five_le_depth hg hreg hdepth 2 (by norm_num))
        (isZero_localCohomology_quotient_of_five_le_depth hg hreg hdepth 3 (by norm_num)))
    hA hdim

end Stacks.PuncturedSpectrumPicard

end
