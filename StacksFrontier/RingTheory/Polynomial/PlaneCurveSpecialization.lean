module

public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.Integer
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.PolynomialIrreducibility
public import StacksFrontier.RingTheory.Polynomial.PlaneCurveIntersection

/-!
# Specializing an absolutely irreducible plane curve

Let `E` be the fraction field of a domain `D` over `k`, and let `R ∈ E[X][Y]` be monic and
absolutely irreducible, dividing a polynomial `P(Λ, Y)` obtained from `P ∈ k[t][Y]` by substituting
polynomials `Λᵢ ∈ E[X]` for the `t`'s. Then there are a nonzero `h ∈ D` and degree bounds `d, e`
such that for every `k`-algebra map `D → F` to a field that does not kill `h`, there is a plane
curve `f` over `F`, of degree at most `d` and absolutely irreducible, together with a `g'` of
degree at most `e` that `f` does not divide, and every point of `f = 0, g' ≠ 0` gives a point of
the hypersurface `P = 0` off `g = 0`.

## Main results

* `Polynomial.Bivariate.map_equivMvPolynomial`: the identification `R[X][Y] ≃ R[x₀, x₁]`
  commutes with base change.
* `MvPolynomial.totalDegree_map_le`: base change does not raise the total degree.
* `Polynomial.exists_specialization_planeCurve`: the specialization statement above.

## References

* [Stacks Project, Tag 0557](https://stacks.math.columbia.edu/tag/0557)
-/

@[expose] public section

open Polynomial

namespace Polynomial.Bivariate

variable {A B : Type*} [CommRing A] [CommRing B]

/-- The two-variable polynomial attached to `p ∈ A[X][Y]` commutes with base change. -/
theorem map_equivMvPolynomial (ψ : A →+* B) (p : A[X][X]) :
    (equivMvPolynomial A p).map ψ = equivMvPolynomial B (p.map (mapRingHom ψ)) := by
  have h : (MvPolynomial.map ψ).comp (equivMvPolynomial A).toRingEquiv.toRingHom =
      (equivMvPolynomial B).toRingEquiv.toRingHom.comp (mapRingHom (mapRingHom ψ)) := by
    apply Polynomial.ringHom_ext
    · intro a
      induction a using Polynomial.induction_on' with
      | add p q hp hq => simp only [map_add] at hp hq ⊢; rw [hp, hq]
      | monomial n a => simp [← C_mul_X_pow_eq_monomial]
    · simp
  exact RingHom.congr_fun h p

/-- The inverse of the two-variable identification commutes with base change. -/
private theorem equivMvPolynomial_symm_map (ψ : A →+* B) (p : MvPolynomial (Fin 2) A) :
    (equivMvPolynomial B).symm (p.map ψ) = ((equivMvPolynomial A).symm p).map (mapRingHom ψ) := by
  apply (equivMvPolynomial B).injective
  rw [AlgEquiv.apply_symm_apply, ← map_equivMvPolynomial, AlgEquiv.apply_symm_apply]

end Polynomial.Bivariate

namespace MvPolynomial

/-- Mapping the coefficients does not raise the total degree. -/
theorem totalDegree_map_le {R S σ : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S)
    (p : MvPolynomial σ R) : (p.map f).totalDegree ≤ p.totalDegree :=
  Finset.sup_mono (support_map_subset f p)

end MvPolynomial

namespace Polynomial

universe w

variable {k D E : Type*} [Field k] [CommRing D] [IsDomain D] [Algebra k D] [Field E]
  [Algebra k E] [Algebra D E] [IsScalarTower k D E] [IsFractionRing D E]

/-- **Specializing an absolutely irreducible plane curve.** Let `E` be the fraction field of a
domain `D` over `k`, let `P ∈ k[t][Y]` and `g ∈ k[t]`, and let `Λ : k[t] → E[X]` be a substitution
of polynomials in one variable for the `t`'s. Let `R ∈ E[X][Y]` be monic of positive degree,
dividing `P(Λ, Y)` and absolutely irreducible, and suppose `g(Λ) ≠ 0`.

Then there are a nonzero `h ∈ D` and degree bounds `d, e` such that every `k`-algebra map
`φ : D → F` to a field with `φ(h) ≠ 0` produces plane curves `f, g'` over `F`, of total degrees at
most `d` and `e`, with `f` absolutely irreducible and not dividing `g'`, and such that every zero
of `f` that is not a zero of `g'` yields a `k`-algebra map `ψ : k[t][Y] → F` killing `P` but not
`g`.
-/
theorem exists_specialization_planeCurve {n : ℕ} (P : Polynomial (MvPolynomial (Fin n) k))
    (g : MvPolynomial (Fin n) k) (Λ : Fin n → Polynomial E) {R : Polynomial (Polynomial E)}
    (hRm : R.Monic) (hRdeg : 0 < R.natDegree)
    (hdvd : R ∣ P.map (MvPolynomial.aeval Λ).toRingHom)
    (hR : Irreducible ((Bivariate.equivMvPolynomial E R).map (algebraMap E (AlgebraicClosure E))))
    (hg : MvPolynomial.aeval Λ g ≠ 0) :
    ∃ h : D, h ≠ 0 ∧ ∃ d e : ℕ, ∀ (F : Type w) [Field F] [Algebra k F] (φ : D →ₐ[k] F),
      φ h ≠ 0 → ∃ f g' : MvPolynomial (Fin 2) F, f.totalDegree ≤ d ∧ g'.totalDegree ≤ e ∧
        Irreducible (f.map (algebraMap F (AlgebraicClosure F))) ∧ ¬ f ∣ g' ∧
        ∀ x : Fin 2 → F, MvPolynomial.eval x f = 0 → MvPolynomial.eval x g' ≠ 0 →
          ∃ ψ : Polynomial (MvPolynomial (Fin n) k) →ₐ[k] F, ψ P = 0 ∧ ψ (C g) ≠ 0 := by
  classical
  obtain ⟨H, hH⟩ := hdvd
  set Rm := Bivariate.equivMvPolynomial E R
  set Hm := Bivariate.equivMvPolynomial E H
  let Z : Finset E := Rm.coeffs ∪ Hm.coeffs ∪ Finset.univ.biUnion fun i ↦ (Λ i).coeffs
  obtain ⟨⟨Δ, hΔ⟩, hZ⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors D) Z
  have hΔ0 : Δ ≠ 0 := nonZeroDivisors.ne_zero hΔ
  have hΔE : algebraMap D E Δ ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hΔ
  let S := Localization.Away Δ
  let : Algebra S E := (IsLocalization.Away.lift Δ (isUnit_iff_ne_zero.mpr hΔE)).toAlgebra
  have : IsScalarTower D S E := IsScalarTower.of_algebraMap_eq fun a ↦
    (IsLocalization.Away.lift_eq Δ (isUnit_iff_ne_zero.mpr hΔE) a).symm
  have hpow : Submonoid.powers Δ ≤ nonZeroDivisors D :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hΔ0
  have : IsFractionRing S E :=
    IsFractionRing.isFractionRing_of_isLocalization (Submonoid.powers Δ) S E hpow
  have : IsDomain S := IsLocalization.isDomain_localization hpow
  have hinj : Function.Injective (algebraMap S E) := IsFractionRing.injective S E
  have hZS : ∀ a ∈ Z, a ∈ Set.range (algebraMap S E) := by
    intro a ha
    obtain ⟨r, hr⟩ := hZ a ha
    refine ⟨IsLocalization.mk' S r (⟨Δ, 1, pow_one Δ⟩ : Submonoid.powers Δ), ?_⟩
    change IsLocalization.lift _ _ = a
    rw [IsLocalization.lift_mk'_spec, hr, Algebra.smul_def]
  have hlift : ∀ m : MvPolynomial (Fin 2) E, (∀ a ∈ m.coeffs, a ∈ Z) →
      ∃ mS : MvPolynomial (Fin 2) S, mS.map (algebraMap S E) = m := fun m hm ↦
    MvPolynomial.mem_range_map_iff_coeffs_subset.mpr fun a ha ↦ hZS a (hm a ha)
  obtain ⟨RS, hRS⟩ := hlift Rm fun a ha ↦ Finset.mem_union_left _ (Finset.mem_union_left _ ha)
  obtain ⟨HS, hHS⟩ := hlift Hm fun a ha ↦ Finset.mem_union_left _ (Finset.mem_union_right _ ha)
  have hΛS : ∀ i, ∃ q : Polynomial S, q.map (algebraMap S E) = Λ i := by
    intro i
    refine (mem_lifts _).mp ((lifts_iff_coeff_lifts _).mpr fun m ↦ ?_)
    by_cases hm : (Λ i).coeff m = 0
    · rw [hm]
      exact ⟨0, map_zero _⟩
    · exact hZS _ (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _,
        coeff_mem_coeffs hm⟩))
  choose ΛS hΛS using hΛS
  let lamS : MvPolynomial (Fin n) k →ₐ[k] Polynomial S := MvPolynomial.aeval ΛS
  have : IsScalarTower k S E := IsScalarTower.of_algebraMap_eq fun c ↦ by
    rw [IsScalarTower.algebraMap_apply k D S, ← IsScalarTower.algebraMap_apply D S E,
      ← IsScalarTower.algebraMap_apply k D E]
  have hlam :
      (mapRingHom (algebraMap S E)).comp lamS.toRingHom = (MvPolynomial.aeval Λ).toRingHom := by
    have : (Polynomial.mapAlgHom (IsScalarTower.toAlgHom k S E)).comp lamS =
        MvPolynomial.aeval Λ := by
      apply MvPolynomial.algHom_ext
      intro i
      simp [lamS, hΛS]
    exact congrArg AlgHom.toRingHom this
  set QS := P.map lamS.toRingHom
  have hQS : QS.map (mapRingHom (algebraMap S E)) = P.map (MvPolynomial.aeval Λ).toRingHom := by
    rw [Polynomial.map_map, hlam]
  have hid : Bivariate.equivMvPolynomial S QS = RS * HS := by
    apply MvPolynomial.map_injective _ hinj
    rw [Bivariate.map_equivMvPolynomial, hQS, hH, map_mul, map_mul, hRS, hHS]
  set GS := Bivariate.equivMvPolynomial S (C (lamS g))
  have hGS : GS.map (algebraMap S E) =
      Bivariate.equivMvPolynomial E (C (MvPolynomial.aeval Λ g)) := by
    rw [Bivariate.map_equivMvPolynomial, Polynomial.map_C, coe_mapRingHom]
    congr 2
    exact RingHom.congr_fun hlam g
  have hGS0 : GS ≠ 0 := fun h ↦ hg (by
    rwa [h, map_zero, eq_comm, map_eq_zero_iff _ (Bivariate.equivMvPolynomial E).injective,
      C_eq_zero] at hGS)
  set RS' := (Bivariate.equivMvPolynomial S).symm RS
  have hi : Function.Injective (mapRingHom (algebraMap S E)) := Polynomial.map_injective _ hinj
  have hRS' : RS'.map (mapRingHom (algebraMap S E)) = R := by
    rw [← Bivariate.equivMvPolynomial_symm_map, hRS]
    exact AlgEquiv.symm_apply_apply _ _
  have hRS'm : RS'.Monic := by
    have h := leadingCoeff_map_of_injective hi RS'
    rw [hRS', hRm.leadingCoeff] at h
    exact hi (h.symm.trans (map_one _).symm)
  have hRS'deg : RS'.natDegree = R.natDegree := by
    rw [← hRS', natDegree_map_eq_of_injective hi]
  obtain ⟨f, hf0, hf⟩ := MvPolynomial.exists_away_irreducible_map.{_, _, _, _, w} S E
    (AlgebraicClosure E) (Fin 2)
    RS (by rwa [← MvPolynomial.map_map, hRS])
  obtain ⟨m0, hm0⟩ := MvPolynomial.ne_zero_iff.mp hGS0
  have hnum : ∀ a : S, a ≠ 0 → ∃ a₀ : D, a₀ ≠ 0 ∧ ∃ s : Submonoid.powers Δ,
      IsLocalization.mk' S a₀ s = a := fun a ha ↦ by
    obtain ⟨⟨a₀, s⟩, h⟩ := IsLocalization.mk'_surjective (Submonoid.powers Δ) a
    refine ⟨a₀, ?_, s, h⟩
    rintro rfl
    simp only [IsLocalization.mk'_zero] at h
    exact ha h.symm
  obtain ⟨f₀, hf₀0, sf, hf₀⟩ := hnum f hf0
  obtain ⟨c₀, hc₀0, sc, hc₀⟩ := hnum _ hm0
  refine ⟨Δ * f₀ * c₀, mul_ne_zero (mul_ne_zero hΔ0 hf₀0) hc₀0, RS.totalDegree, GS.totalDegree,
    fun F _ _ φ hφ ↦ ?_⟩
  rw [map_mul, map_mul] at hφ
  obtain ⟨hφΔf, hφc⟩ := mul_ne_zero_iff.mp hφ
  obtain ⟨hφΔ, hφf⟩ := mul_ne_zero_iff.mp hφΔf
  let φS : S →ₐ[k] F := IsLocalization.liftAlgHom (M := Submonoid.powers Δ) (f := φ)
    fun ⟨x, hx⟩ ↦ by
      obtain ⟨m, rfl⟩ := hx
      change IsUnit (φ (Δ ^ m))
      rw [map_pow]
      exact (isUnit_iff_ne_zero.mpr hφΔ).pow m
  have hφS : ∀ (a : D) (s : Submonoid.powers Δ), φ a ≠ 0 →
      φS (IsLocalization.mk' S a s) ≠ 0 := by
    intro a s ha h
    have h' : φ a = φ s * φS (IsLocalization.mk' S a s) :=
      (IsLocalization.lift_mk'_spec _ _ _ _).mp rfl
    rw [h, mul_zero] at h'
    exact ha h'
  have hφSf : φS f ≠ 0 := hf₀ ▸ hφS _ _ hφf
  have hφSc : φS (GS.coeff m0) ≠ 0 := hc₀ ▸ hφS _ _ hφc
  let fF := RS.map φS.toRingHom
  let gF := GS.map φS.toRingHom
  have hgF0 : gF ≠ 0 := by
    intro h
    have := congrArg (fun p : MvPolynomial (Fin 2) _ ↦ p.coeff m0) h
    simp only [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at this
    exact hφSc this
  refine ⟨fF, gF, MvPolynomial.totalDegree_map_le _ _, MvPolynomial.totalDegree_map_le _ _, ?_,
    ?_, ?_⟩
  · have hunit : IsUnit ((algebraMap F (AlgebraicClosure F)).comp φS.toRingHom f) :=
      isUnit_iff_ne_zero.mpr (by simpa using hφSf)
    have h := hf (AlgebraicClosure F) (IsLocalization.Away.lift f hunit)
    rwa [IsLocalization.Away.lift_comp, ← MvPolynomial.map_map] at h
  · intro hdvd
    have hfF' : (Bivariate.equivMvPolynomial F).symm fF = RS'.map (mapRingHom φS.toRingHom) :=
      Bivariate.equivMvPolynomial_symm_map _ _
    have hgF' : (Bivariate.equivMvPolynomial F).symm gF = C ((lamS g).map φS.toRingHom) := by
      rw [Bivariate.equivMvPolynomial_symm_map, AlgEquiv.symm_apply_apply, Polynomial.map_C]
      rfl
    have hm : ((Bivariate.equivMvPolynomial F).symm fF).Monic := hfF' ▸ hRS'm.map _
    have hdeg : ((Bivariate.equivMvPolynomial F).symm fF).natDegree = R.natDegree := by
      rw [hfF', hRS'm.natDegree_map, hRS'deg]
    obtain ⟨q, hq⟩ := hdvd
    have hdvd' : (Bivariate.equivMvPolynomial F).symm fF ∣ C ((lamS g).map φS.toRingHom) :=
      ⟨(Bivariate.equivMvPolynomial F).symm q, by rw [← hgF', hq, map_mul]⟩
    have hC0 : C ((lamS g).map φS.toRingHom) ≠ 0 := by
      rw [← hgF']
      exact (map_ne_zero_iff _ (Bivariate.equivMvPolynomial F).symm.injective).mpr hgF0
    have := natDegree_le_of_dvd hdvd' hC0
    rw [natDegree_C, hdeg] at this
    lia
  · intro x hx0 hx1
    let ψ0 : Polynomial (MvPolynomial (Fin n) k) →+* F := (evalEvalRingHom (x 0) (x 1)).comp
      ((mapRingHom (mapRingHom φS.toRingHom)).comp (mapRingHom lamS.toRingHom))
    let ψ : Polynomial (MvPolynomial (Fin n) k) →ₐ[k] F :=
      { ψ0 with commutes' := fun c ↦ by simp [ψ0] }
    have hψ : ∀ p, ψ p = MvPolynomial.eval x (Bivariate.equivMvPolynomial F
        ((p.map lamS.toRingHom).map (mapRingHom φS.toRingHom))) := by
      intro p
      rw [Bivariate.eval_equivMvPolynomial]
      rfl
    refine ⟨ψ, ?_, ?_⟩
    · rw [hψ, ← Bivariate.map_equivMvPolynomial, hid, map_mul, map_mul]
      change MvPolynomial.eval x fF * _ = 0
      rw [hx0, zero_mul]
    · rw [hψ, ← Bivariate.map_equivMvPolynomial, Polynomial.map_C]
      exact hx1

end Polynomial
