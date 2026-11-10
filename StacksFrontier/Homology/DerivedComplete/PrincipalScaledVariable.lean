module

public import Mathlib
public import StacksFrontier.Algebra.Homology.DerivedCategory.Products
public import StacksFrontier.Homology.DerivedComplete
public import StacksFrontier.Homology.DerivedComplete.CompleteAdic
public import StacksFrontier.Homology.DerivedComplete.PrincipalRecurrence

/-!
# A derived complete module which is not adically complete

For a prime `p`, substitute `pX` for `X` in the polynomial ring over the `p`-adic integers and
complete the resulting map `p`-adically. The cokernel is derived complete, but it is not
classically `p`-adically complete.

## Main definitions

There are no new definitions.

## Main results

* `scaledVariableCompletionCokernel_isDerivedComplete_not_isAdicComplete` gives the example and
  the geometric-series element witnessing its failure to be adically separated.

## Implementation notes

Both polynomial variables are represented by `Polynomial.X`, since their rings are canonically the
same polynomial algebra. The cokernel is the quotient by the range of the completed linear map,
and it is derived complete because the derived complete modules are closed under cokernels
(`DerivedCompleteRecurrence.completeModules`) while the two completions are adically complete,
hence derived complete by Stacks 091T. The compatible residues of the geometric series are its
truncations `∑_{i < n} pⁱ Xⁱ` modulo `pⁿ`.

## References

* [The Stacks Project, Tag 0G3F](https://stacks.math.columbia.edu/tag/0G3F)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

noncomputable section

universe u v

namespace PrincipalScaledVariable

open Polynomial DerivedCompleteRecurrence

variable {R : Type u} [CommRing R]

attribute [local instance] KoszulCompletion.derivedCountableProducts

private abbrev scaledVariable (r : R) : R[X] →ₗ[R] R[X] :=
  (Polynomial.aeval (r • (X : R[X]))).toLinearMap

private abbrev geometricPolynomial (r : R) (n : ℕ) : R[X] :=
  ∑ i ∈ Finset.range n, r ^ i • (X : R[X]) ^ i

private lemma scaledVariable_coeff (r : R) (f : R[X]) (k : ℕ) :
    (scaledVariable r f).coeff k = f.coeff k * r ^ k := by
  change (f.comp (r • X)).coeff k = _
  rw [smul_eq_C_mul, comp_C_mul_X_coeff]

private lemma geometricPolynomial_coeff (r : R) (n k : ℕ) :
    (geometricPolynomial r n).coeff k = if k < n then r ^ k else 0 := by
  simp [geometricPolynomial, finsetSum_coeff, coeff_X_pow]

private lemma mem_span_pow_smul_top_iff {M : Type*} [AddCommGroup M] [Module R M]
    (r : R) (n : ℕ) (x : M) :
    x ∈ (Ideal.span {r}) ^ n • (⊤ : Submodule R M) ↔ ∃ y, r ^ n • y = x := by
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  simp

private lemma coeff_sub_dvd_of_mk_eq (r : R) (n k : ℕ) {f g : R[X]}
    (h : Submodule.Quotient.mk (p := (Ideal.span {r}) ^ n • (⊤ : Submodule R R[X])) f =
      Submodule.Quotient.mk g) : r ^ n ∣ f.coeff k - g.coeff k := by
  obtain ⟨y, hy⟩ := (mem_span_pow_smul_top_iff r n _).mp (SModEq.sub_mem.mp h)
  exact ⟨y.coeff k, by rw [← coeff_sub, ← hy, coeff_smul, smul_eq_mul]⟩

private lemma geometricPolynomial_smodEq (r : R) {m n : ℕ} (hmn : m ≤ n) :
    Submodule.Quotient.mk (p := (Ideal.span {r}) ^ m • (⊤ : Submodule R R[X]))
      (geometricPolynomial r n) = Submodule.Quotient.mk (geometricPolynomial r m) := by
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ n hmn ih =>
    rw [show geometricPolynomial r (n + 1) = geometricPolynomial r n + r ^ n • (X : R[X]) ^ n
      by simp [geometricPolynomial, Finset.sum_range_succ], Submodule.Quotient.mk_add, ih,
      add_eq_left, Submodule.Quotient.mk_eq_zero]
    refine (mem_span_pow_smul_top_iff r m _).mpr ⟨r ^ (n - m) • (X : R[X]) ^ n, ?_⟩
    rw [smul_smul, ← pow_add, Nat.add_sub_of_le hmn]

private lemma exists_geometricCompletion (r : R) :
    ∃ z : AdicCompletion (Ideal.span {r}) R[X],
      ∀ n, z.val n = Submodule.Quotient.mk (geometricPolynomial r n) :=
  ⟨⟨fun n ↦ Submodule.Quotient.mk (geometricPolynomial r n),
    fun hmn ↦ geometricPolynomial_smodEq r hmn⟩, fun _ ↦ rfl⟩

private lemma geometricCompletion_not_mem_range [IsDomain R] (r : R)
    (hr : r ≠ 0) (hu : ¬ IsUnit r)
    (z : AdicCompletion (Ideal.span {r}) R[X])
    (hz : ∀ n, z.val n = Submodule.Quotient.mk (geometricPolynomial r n)) :
    z ∉ LinearMap.range
      ((AdicCompletion.map (Ideal.span {r}) (scaledVariable r)).restrictScalars R) := by
  rintro ⟨w, hw⟩
  obtain ⟨f, hf⟩ := Submodule.Quotient.mk_surjective _ (w.val 1)
  let k := f.natDegree + 1
  obtain ⟨g, hg⟩ := Submodule.Quotient.mk_surjective _ (w.val (k + 1))
  have hgf : Submodule.Quotient.mk
      (p := (Ideal.span {r}) ^ 1 • (⊤ : Submodule R R[X])) g =
      Submodule.Quotient.mk f := by
    rw [hf, ← w.property (show 1 ≤ k + 1 by omega), ← hg]
    rfl
  have hdg : r ∣ g.coeff k := by
    simpa [coeff_eq_zero_of_natDegree_lt (show f.natDegree < k by omega)] using
      coeff_sub_dvd_of_mk_eq r 1 k hgf
  have hφg : Submodule.Quotient.mk
      (p := (Ideal.span {r}) ^ (k + 1) • (⊤ : Submodule R R[X])) (scaledVariable r g) =
      Submodule.Quotient.mk (geometricPolynomial r (k + 1)) := by
    have hw' := congrArg (fun a : AdicCompletion (Ideal.span {r}) R[X] ↦ a.val (k + 1)) hw
    change (AdicCompletion.map (Ideal.span {r}) (scaledVariable r) w).val (k + 1) = _ at hw'
    simpa only [AdicCompletion.map_val_apply, ← hg, LinearMap.reduceModIdeal_apply, hz] using hw'
  have hd : r ^ (k + 1) ∣ r ^ k * (g.coeff k - 1) := by
    have hsub := coeff_sub_dvd_of_mk_eq r (k + 1) k hφg
    rw [scaledVariable_coeff, geometricPolynomial_coeff] at hsub
    simpa [mul_sub, mul_comm] using hsub
  have hd' : r ∣ g.coeff k - 1 := by
    obtain ⟨a, ha⟩ := hd
    exact ⟨a, mul_left_cancel₀ (pow_ne_zero k hr) (by simpa only [pow_succ, mul_assoc] using ha)⟩
  exact hu (isUnit_of_dvd_one (by simpa using dvd_sub hdg hd'))

private lemma scaledVariable_geometricPolynomial (r : R) (n : ℕ) :
    scaledVariable r (∑ i ∈ Finset.range n, (X : R[X]) ^ i) =
      geometricPolynomial r n := by
  simp [scaledVariable, geometricPolynomial, _root_.smul_pow]

private lemma geometricCompletion_mk_mem_pow (r : R)
    (z : AdicCompletion (Ideal.span {r}) R[X])
    (hz : ∀ n, z.val n = Submodule.Quotient.mk (geometricPolynomial r n)) (n : ℕ) :
    let S := LinearMap.range
      ((AdicCompletion.map (Ideal.span {r}) (scaledVariable r)).restrictScalars R)
    Submodule.Quotient.mk z ∈ (Ideal.span {r}) ^ n •
      (⊤ : Submodule R (AdicCompletion (Ideal.span {r}) R[X] ⧸ S)) := by
  dsimp only
  let I : Ideal R := Ideal.span {r}
  let φ := (AdicCompletion.map I (scaledVariable r)).restrictScalars R
  let S := LinearMap.range φ
  let a := AdicCompletion.of I R[X] (∑ i ∈ Finset.range n, (X : R[X]) ^ i)
  change S.mkQ z ∈ I ^ n • (⊤ : Submodule R (_ ⧸ S))
  have heval : z - φ a ∈ I ^ n • (⊤ : Submodule R (AdicCompletion I R[X])) := by
    rw [AdicCompletion.pow_smul_top_eq_ker_eval (Submodule.fg_span_singleton r)]
    change z.val n - (AdicCompletion.map I (scaledVariable r)
      (AdicCompletion.of I R[X] (∑ i ∈ Finset.range n, (X : R[X]) ^ i))).val n = 0
    rw [AdicCompletion.map_of, scaledVariable_geometricPolynomial, AdicCompletion.of_apply, hz]
    exact sub_self _
  have hmap := Submodule.mem_map_of_mem (f := S.mkQ) heval
  rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ] at hmap
  have hφ : S.mkQ (φ a) = 0 := (Submodule.Quotient.mk_eq_zero S).mpr ⟨a, rfl⟩
  simpa only [map_sub, hφ, sub_zero] using hmap

private lemma isDerivedCompleteModule_range_quotient
    (I : Ideal R) (hI : I.FG) {L N : Type v} [AddCommGroup L] [Module R L]
    [AddCommGroup N] [Module R N] (f : L →ₗ[R] N)
    (hL : IsAdicComplete I L) (hN : IsAdicComplete I N) :
    IsDerivedCompleteModule I (ModuleCat.of R (N ⧸ f.range)) :=
  completeModules_rangeQuotient I (ModuleCat.ofHom f)
    ((isAdicComplete_iff_isDerivedCompleteModule_and_iInf_pow_smul_top_eq_bot R I hI L).mp hL).1
    ((isAdicComplete_iff_isDerivedCompleteModule_and_iInf_pow_smul_top_eq_bot R I hI N).mp hN).1

/-- **Stacks 0G3F.** Let `p` be prime. The cokernel of the map between the `p`-adic
completions of `ℤ_[p][X]` induced by `X ↦ pX` is derived complete but not adically complete.
The image of `1 + pX + p²X² + ⋯` is a nonzero element belonging to every `p^n M`. -/
@[stacks 0G3F]
theorem scaledVariableCompletionCokernel_isDerivedComplete_not_isAdicComplete
    (p : ℕ) [Fact p.Prime] :
    let A := ℤ_[p]
    let I : Ideal A := Ideal.span {(p : A)}
    let φ : Polynomial A →ₗ[A] Polynomial A :=
      (Polynomial.aeval ((p : A) • Polynomial.X)).toLinearMap
    let φhat := AdicCompletion.map I φ
    let M := HasQuotient.Quotient (AdicCompletion I (Polynomial A))
      (LinearMap.range (φhat.restrictScalars A))
    letI : HasExactLimitsOfShape (Discrete ℕ) (ModuleCat A) :=
      moduleCat_hasExactLimitsOfShape_discrete A ℕ
    letI : HasProductsOfShape ℕ (DerivedCategory (ModuleCat A)) :=
      Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
    IsDerivedCompleteModule I (ModuleCat.of A M) ∧
      ¬ IsAdicComplete I M ∧
      ∃ z : AdicCompletion I (Polynomial A),
        (∀ n : ℕ, z.val n =
          Submodule.Quotient.mk
            (∑ i ∈ Finset.range n, (p : A) ^ i • (Polynomial.X : Polynomial A) ^ i)) ∧
        Submodule.Quotient.mk z ≠ (0 : M) ∧
        ∀ n : ℕ, Submodule.Quotient.mk z ∈ I ^ n • (⊤ : Submodule A M) := by
  let A := ℤ_[p]
  let I : Ideal A := Ideal.span {(p : A)}
  let φ := (AdicCompletion.map I (scaledVariable (p : A))).restrictScalars A
  let M := AdicCompletion I A[X] ⧸ φ.range
  change IsDerivedCompleteModule I (ModuleCat.of A M) ∧
    ¬ IsAdicComplete I M ∧ ∃ z : AdicCompletion I A[X],
      (∀ n, z.val n = Submodule.Quotient.mk (geometricPolynomial (p : A) n)) ∧
      Submodule.Quotient.mk z ≠ (0 : M) ∧
      ∀ n, Submodule.Quotient.mk z ∈ I ^ n • (⊤ : Submodule A M)
  have hI : I.FG := Submodule.fg_span_singleton _
  have hc : IsAdicComplete I (AdicCompletion I A[X]) := AdicCompletion.isAdicComplete hI
  obtain ⟨z, hz⟩ := exists_geometricCompletion (p : A)
  have hne : Submodule.Quotient.mk z ≠ (0 : M) := fun h ↦
    geometricCompletion_not_mem_range (p : A) PadicInt.prime_p.ne_zero
      PadicInt.prime_p.not_isUnit z hz ((Submodule.Quotient.mk_eq_zero _).mp h)
  have hall : ∀ n, Submodule.Quotient.mk z ∈ I ^ n • (⊤ : Submodule A M) :=
    geometricCompletion_mk_mem_pow (p : A) z hz
  exact ⟨isDerivedCompleteModule_range_quotient I hI φ hc hc,
    fun h ↦ hne (h.toIsHausdorff.haus _ fun n ↦ SModEq.zero.mpr (hall n)), z, hz, hne, hall⟩

end PrincipalScaledVariable

end

end
