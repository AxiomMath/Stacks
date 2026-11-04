module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierAffineLocal
public import StacksFrontier.RingTheory.DiscreteValuationRing.TFAE

/-!
# The local ring at the generic point of an integral effective Cartier divisor

Let `X` be a locally Noetherian scheme and `D ⊆ X` an integral closed subscheme which is also an
effective Cartier divisor. Then the local ring of `X` at the generic point of `D` is a discrete
valuation ring.

## Main results

* `AlgebraicGeometry.isDiscreteValuationRing_stalk_genericPoint`: the local ring of `X` at the
  generic point of `D` is a discrete valuation ring.

## References

* [Stacks Project, Tag 0AG9](https://stacks.math.columbia.edu/tag/0AG9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Divisors

universe u

namespace AlgebraicGeometry

/-- Let `X` be a locally Noetherian scheme and `D ⊆ X` an integral closed subscheme which is an
effective Cartier divisor. The local ring of `X` at the generic point of `D` is a discrete
valuation ring; in particular it is a domain. -/
@[stacks 0AG9, ega "IV 3.4.6" "partial"]
theorem isDiscreteValuationRing_stalk_genericPoint {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData) [IsIntegral I.subscheme] (hI : IsEffectiveCartierDivisor I) :
    ∃ _ : IsDomain (X.presheaf.stalk (I.subschemeι (_root_.genericPoint I.subscheme))),
      IsDiscreteValuationRing
        (X.presheaf.stalk (I.subschemeι (_root_.genericPoint I.subscheme))) := by
  set η := _root_.genericPoint I.subscheme
  set x := I.subschemeι η
  have hxsupp : x ∈ (I.support : Set X) := by
    rw [← I.range_subschemeι]
    exact Set.mem_range_self η
  have hx : x ∈ I.supportSet :=
    Scheme.IdealSheafData.mem_supportSet_iff_mem_support.mpr hxsupp
  obtain ⟨U, hU, hxU, f, hf, e, he⟩ :=
    (isEffectiveCartierDivisor_iff_affineLocal I).mp hI x hx
  have hηrange : η ∈ (pullback.fst I.subschemeι U.ι).opensRange := by
    rw [Scheme.Hom.opensRange_pullbackFst]
    simpa using hxU
  have _ : Nonempty ↥(pullback I.subschemeι U.ι) :=
    ⟨(pullback.fst I.subschemeι U.ι).isoOpensRange.inv ⟨η, hηrange⟩⟩
  have _ : IsIntegral (pullback I.subschemeι U.ι) :=
    isIntegral_of_isOpenImmersion (pullback.fst I.subschemeι U.ι)
  have _ : IsIntegral (Spec (.of (Γ(X, U) ⧸ Ideal.span {f}))) := IsIntegral.of_isIso e.hom
  have _ : IsDomain (Γ(X, U) ⧸ Ideal.span {f}) :=
    (affine_isIntegral_iff (.of (Γ(X, U) ⧸ Ideal.span {f}))).mp inferInstance
  have hgenW : pullback.fst I.subschemeι U.ι
      (_root_.genericPoint ↥(pullback I.subschemeι U.ι)) = η :=
    genericPoint_eq_of_isOpenImmersion _
  have hgenZ : e.hom (_root_.genericPoint ↥(pullback I.subschemeι U.ι)) =
      _root_.genericPoint ↥(Spec (.of (Γ(X, U) ⧸ Ideal.span {f}))) :=
    genericPoint_eq_of_isOpenImmersion e.hom
  have hsz : pullback.snd I.subschemeι U.ι
      (_root_.genericPoint ↥(pullback I.subschemeι U.ι)) = ⟨x, hxU⟩ := by
    refine Subtype.ext ?_
    have hc := congrArg (fun g => g (_root_.genericPoint ↥(pullback I.subschemeι U.ι)))
      (pullback.condition (f := I.subschemeι) (g := U.ι))
    simp only [Scheme.Hom.comp_apply, hgenW] at hc
    exact hc.symm
  have heval := congrArg (fun g : pullback I.subschemeι U.ι ⟶ Spec (.of (Γ(X, U))) =>
    g (_root_.genericPoint ↥(pullback I.subschemeι U.ι))) he
  simp only [Scheme.Hom.comp_apply] at heval
  have hpoint : hU.primeIdealOf ⟨x, hxU⟩ =
      PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {f})) ⊥ := by
    rwa [hsz, hgenZ, genericPoint_eq_bot_of_affine] at heval
  have hpideal : (hU.primeIdealOf ⟨x, hxU⟩).asIdeal = Ideal.span {f} := by
    rw [hpoint, PrimeSpectrum.comap_asIdeal]
    exact Ideal.mk_ker
  set R := X.presheaf.stalk x
  let _ := X.presheaf.algebra_section_stalk (⟨x, hxU⟩ : U)
  set π : R := algebraMap Γ(X, U) R f with hπdef
  have _ : IsLocalization.AtPrime R (hU.primeIdealOf ⟨x, hxU⟩).asIdeal :=
    hU.isLocalization_stalk ⟨x, hxU⟩
  have hπ : π ∈ nonZeroDivisors R :=
    IsLocalization.map_nonZeroDivisors_le (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl R
      ⟨f, hf.mem_nonZeroDivisors, rfl⟩
  have hmax : IsLocalRing.maximalIdeal R = Ideal.span {π} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal
      (hU.primeIdealOf ⟨x, hxU⟩).asIdeal R, hpideal]
    simp [hπdef, Ideal.map_span]
  have hunit : ¬ IsUnit π := fun hu =>
    (IsLocalRing.maximalIdeal.isMaximal R).ne_top
      (by rwa [hmax, Ideal.span_singleton_eq_top])
  have hdim : ringKrullDim R = 1 := by
    rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, hmax]
    exact_mod_cast Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors hπ hunit
  have hreg : IsRegularLocalRing R := by
    refine IsRegularLocalRing.of_spanFinrank_maximalIdeal_le (R := R) ?_
    rw [hdim, hmax]
    simpa using Submodule.spanFinrank_span_le_ncard_of_finite (s := ({π} : Set R)) (by simp)
  exact ((isDiscreteValuationRing_tfae R).out 3 1 rfl rfl).mp ⟨hreg, hdim⟩

end AlgebraicGeometry

end
