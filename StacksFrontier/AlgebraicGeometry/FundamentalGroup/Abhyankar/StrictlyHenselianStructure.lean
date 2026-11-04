module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.Abhyankar.StrictlyHenselianDomain
public import StacksFrontier.RingTheory.IntegrallyClosed.ProductOfDomains

/-!
# Abhyankar's lemma over a strictly henselian local ring

Let `A` be a strictly henselian local ring and `φ ∈ A`. A finite étale `A_φ`-algebra `B` is a
finite product of standard tamely ramified algebras `A[x]/(x^{e_i} - φ)_φ` with every `e_i`
invertible in `A`, in each of the following two cases:

* `φ` is a unit (then `B` is split, and all `e_i = 1`);
* `A` is regular, `φ ∈ 𝔪_A` is nonzero with `A/φA` regular, and `B` is tamely ramified over
  `Spec A` in codimension one (Abhyankar's lemma, [Stacks, Tag 0EYG]).

## Main results

* `AlgebraicGeometry.Abhyankar.isTamelyRamifiedInCodimensionOne_of_surjective`: tameness passes to
  quotients of the cover.
* `AlgebraicGeometry.Abhyankar.exists_ringEquiv_pi_of_isUnit`: the split case.
* `AlgebraicGeometry.Abhyankar.exists_ringEquiv_pi_of_isRegularLocalRing`: the regular case,
  granted purity for regular local rings.

## References

* [Stacks Project, Tag 0EYG](https://stacks.math.columbia.edu/tag/0EYG)
* [Stacks Project, Tag 030C](https://stacks.math.columbia.edu/tag/030C)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry.Abhyankar

/-- **Tameness passes to quotients of the cover.** If `q : B → B₁` is a surjection of
`A_φ`-algebras and `Spec B ⟶ D(φ)` is tamely ramified over `Spec A` in codimension one, then so is
`Spec B₁ ⟶ D(φ)`: a field factor of `B₁` is one of `B`. -/
theorem isTamelyRamifiedInCodimensionOne_of_surjective {R : CommRingCat.{u}} (φ : R)
    {B B₁ : Type u} [CommRing B] [CommRing B₁] [Algebra (Localization.Away φ) B]
    [Algebra (Localization.Away φ) B₁] (q : B →ₐ[Localization.Away φ] B₁)
    (hq : Function.Surjective q)
    (htame : Stacks.FundamentalGroup.IsTamelyRamifiedInCodimensionOne
      (Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen φ))
      (AffineFieldFactors.coverMap φ B)) :
    Stacks.FundamentalGroup.IsTamelyRamifiedInCodimensionOne
      (Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen φ))
      (AffineFieldFactors.coverMap φ B₁) := by
  intro Z hZ hD hV K L _ _ _ _ _ _ _ _ _ hFF
  let : Algebra R ((Spec R).presheaf.stalk Z.genericPoint) :=
    StructureSheaf.stalkAlgebra R Z.genericPoint
  have : IsLocalization.AtPrime ((Spec R).presheaf.stalk Z.genericPoint)
      Z.genericPoint.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk R Z.genericPoint
  have hρ : Spec.map (CommRingCat.ofHom (algebraMap R ((Spec R).presheaf.stalk Z.genericPoint))) =
      (Spec R).fromSpecStalk Z.genericPoint := by
    rw [Spec.fromSpecStalk_eq']
    rfl
  obtain ⟨ψ, hψ, hgen⟩ := AffineFieldFactors.exists_ringHom_of_isFieldFactorAt Z.genericPoint hρ hFF
  refine htame Z hZ hD hV K L (AffineFieldFactors.isFieldFactorAt_of_ringHom Z.genericPoint hρ ?_
    (ψ.comp q.toRingHom) (fun r ↦ ?_) ?_)
  · have hu : IsUnit (ψ (algebraMap (Localization.Away φ) B₁ (algebraMap R _ φ))) :=
      ((IsLocalization.Away.algebraMap_isUnit φ).map _).map _
    rw [hψ φ, IsScalarTower.algebraMap_apply _ K L] at hu
    exact isUnit_iff_ne_zero.mpr fun h ↦ hu.ne_zero (by rw [h, map_zero])
  · simpa only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
      using hψ r
  · have hq' : Function.Surjective q.toRingHom := hq
    rw [RingHom.coe_comp, hq'.range_comp]
    exact hgen

/-- The localization at a nonzero element of an integrally closed domain is a normal ring. -/
theorem isNormalRing_localizationAway {A : Type u} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    {φ : A} (hφ0 : φ ≠ 0) : IsNormalRing (Localization.Away φ) := by
  have : IsDomain (Localization.Away φ) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hφ0)
  have : IsIntegrallyClosed (Localization.Away φ) :=
    isIntegrallyClosed_of_isLocalization (Localization.Away φ) (Submonoid.powers φ)
      (powers_le_nonZeroDivisors_of_noZeroDivisors hφ0)
  intro P _
  exact ⟨IsLocalization.isDomain_localization P.primeCompl_le_nonZeroDivisors,
    isIntegrallyClosed_of_isLocalization _ P.primeCompl P.primeCompl_le_nonZeroDivisors⟩

/-- **Abhyankar's lemma over a strictly henselian regular local ring.** Let `A` be a strictly
henselian regular local ring, `0 ≠ φ ∈ 𝔪_A` with `A/φA` regular, and `B` a finite étale
`A_φ`-algebra which is tamely ramified over `Spec A` in codimension one. Then
`B ≅ ∏ᵢ A[x]/(x^{eᵢ} - φ)_φ` over `A_φ` with every `eᵢ ≥ 1` invertible in `A`. The argument
`h0BMA` is purity for regular local rings ([Stacks, Tag 0BMA] (1)). -/
theorem exists_ringEquiv_pi_of_isRegularLocalRing (h0BMA : PurityAtRegularLocalRings.{u})
    (A : Type u) [CommRing A] [StrictlyHenselianLocalRing A] [IsRegularLocalRing A]
    (φ : A) (hφ : φ ∈ maximalIdeal A) (hφ0 : φ ≠ 0)
    (hreg : IsRegularLocalRing (A ⧸ Ideal.span {φ}))
    (B : Type u) [CommRing B] [Algebra (Localization.Away φ) B]
    [Module.Finite (Localization.Away φ) B] [Algebra.Etale (Localization.Away φ) B]
    (htame : Stacks.FundamentalGroup.IsTamelyRamifiedInCodimensionOne
      (Scheme.Opens.ι (X := Spec (.of A)) (PrimeSpectrum.basicOpen φ))
      (AffineFieldFactors.coverMap (R := .of A) φ B)) :
    ∃ (n : ℕ) (e : Fin n → ℕ), (∀ i, 0 < e i ∧ IsUnit (e i : A)) ∧
      ∃ σ : (∀ i, Localization.Away
          (algebraMap A (standardTamelyRamifiedAlgebra A φ (e i)) φ)) ≃+* B,
        ∀ r, σ (fun i ↦ Localization.awayMap
          (algebraMap A (standardTamelyRamifiedAlgebra A φ (e i))) φ r) = algebraMap _ B r := by
  classical
  have : IsDomain A := IsRegularLocalRing.isDomain A
  have : IsIntegrallyClosed A := isIntegrallyClosed_of_isRegularLocalRing A
  have : IsNoetherianRing (Localization.Away φ) :=
    IsLocalization.isNoetherianRing (Submonoid.powers φ) _ inferInstance
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing (Localization.Away φ) B
  have hBnorm : IsNormalRing B := IsNormalRing.of_etale (isNormalRing_localizationAway hφ0)
  have : _root_.IsReduced B := hBnorm.isReduced
  have hfin := minimalPrimes.finite_of_isNoetherianRing B
  obtain ⟨-, hbij⟩ := ((isIntegrallyClosed_tfae_of_finite_minimalPrimes hfin).out 1 4).mp hBnorm
  have : Fintype (minimalPrimes B) := hfin.fintype
  let Q : minimalPrimes B → Type u := fun P ↦ B ⧸ (P : Ideal B)
  let ε : B →ₐ[Localization.Away φ] (∀ P, Q P) :=
    Pi.algHom _ Q (fun P ↦ Ideal.Quotient.mkₐ _ (P : Ideal B))
  let εe := AlgEquiv.ofBijective ε hbij
  have : Algebra.Etale (Localization.Away φ) (∀ P, Q P) := Algebra.Etale.of_equiv εe
  have hfac : ∀ P : minimalPrimes B, ∃ d : ℕ, 0 < d ∧ IsUnit (d : A) ∧
      ∃ σ : Localization.Away (algebraMap A (standardTamelyRamifiedAlgebra A φ d) φ) ≃+* Q P,
        ∀ r, σ (Localization.awayMap (algebraMap A (standardTamelyRamifiedAlgebra A φ d)) φ r) =
          algebraMap _ (Q P) r := by
    intro P
    have : (P : Ideal B).IsPrime := Ideal.minimalPrimes_isPrime P.2
    have : IsDomain (Q P) := Ideal.Quotient.isDomain _
    have : Module.Finite (Localization.Away φ) (Q P) :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ _ (P : Ideal B)).toLinearMap
        Ideal.Quotient.mk_surjective
    have : Algebra.FormallyEtale (Localization.Away φ) (Q P) :=
      (Algebra.FormallyEtale.pi_iff Q).mp inferInstance P
    have : Algebra.FinitePresentation (Localization.Away φ) (Q P) :=
      Algebra.FinitePresentation.of_finiteType.mp inferInstance
    have : Algebra.Etale (Localization.Away φ) (Q P) := ⟨inferInstance, inferInstance⟩
    exact exists_ringEquiv_of_isDomain h0BMA A φ hφ hφ0 hreg (Q P)
      (isTamelyRamifiedInCodimensionOne_of_surjective (R := .of A) φ
        (Ideal.Quotient.mkₐ _ (P : Ideal B)) Ideal.Quotient.mk_surjective htame)
  choose d hd0 hdu σP hσP using hfac
  let eq := Fintype.equivFin (minimalPrimes B)
  refine ⟨Fintype.card (minimalPrimes B), fun i ↦ d (eq.symm i), fun i ↦ ⟨hd0 _, hdu _⟩,
    (RingEquiv.piCongrRight fun i ↦ σP (eq.symm i)).trans
      ((RingEquiv.piCongrLeft Q eq.symm).trans εe.symm.toRingEquiv), fun r ↦ ?_⟩
  apply εe.injective
  simp only [RingEquiv.trans_apply, AlgEquiv.coe_ringEquiv,
    AlgEquiv.apply_symm_apply, AlgEquiv.commutes]
  funext P
  obtain ⟨i, rfl⟩ := eq.symm.surjective P
  exact (Equiv.piCongrLeft_apply_apply (P := Q) eq.symm _ i).trans (hσP _ r)

/-- **The split case.** If `A` is a strictly henselian local ring and `φ ∈ A` is a unit, then every
finite étale `A_φ`-algebra is a finite product of copies of `A[x]/(x - φ)_φ`. -/
theorem exists_ringEquiv_pi_of_isUnit (A : Type u) [CommRing A] [StrictlyHenselianLocalRing A]
    (φ : A) (hφ : IsUnit φ)
    (B : Type u) [CommRing B] [Algebra (Localization.Away φ) B]
    [Module.Finite (Localization.Away φ) B] [Algebra.Etale (Localization.Away φ) B] :
    ∃ (n : ℕ) (e : Fin n → ℕ), (∀ i, 0 < e i ∧ IsUnit (e i : A)) ∧
      ∃ σ : (∀ i, Localization.Away
          (algebraMap A (standardTamelyRamifiedAlgebra A φ (e i)) φ)) ≃+* B,
        ∀ r, σ (fun i ↦ Localization.awayMap
          (algebraMap A (standardTamelyRamifiedAlgebra A φ (e i))) φ r) = algebraMap _ B r := by
  classical
  let eA : A ≃ₐ[A] Localization.Away φ :=
    IsLocalization.atUnits _ _ (Submonoid.powers_le.mpr hφ)
  let : Algebra A B := ((algebraMap (Localization.Away φ) B).comp
    (algebraMap A (Localization.Away φ))).toAlgebra
  have : IsScalarTower A (Localization.Away φ) B := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : Module.Finite A (Localization.Away φ) := Module.Finite.equiv eA.toLinearEquiv
  have : Module.Finite A B := Module.Finite.trans (Localization.Away φ) B
  have : Algebra.Etale A (Localization.Away φ) := Algebra.Etale.of_isLocalizationAway φ
  have : Algebra.Etale A B := Algebra.Etale.comp A (Localization.Away φ) B
  obtain ⟨n, ⟨eB⟩⟩ := exists_algEquiv_pi_of_henselian_of_isSepClosed A B
  let C := standardTamelyRamifiedAlgebra A φ 1
  let e₁ : C ≃ₐ[A] A := (Ideal.quotientEquivAlgOfEq A (by rw [pow_one])).trans
    (Polynomial.quotientSpanXSubCAlgEquiv φ)
  have hCu : IsUnit (algebraMap A C φ) := hφ.map _
  let eC : C ≃ₐ[C] Localization.Away (algebraMap A C φ) :=
    IsLocalization.atUnits _ _ (Submonoid.powers_le.mpr hCu)
  let eK : Localization.Away (algebraMap A C φ) ≃+* A :=
    eC.symm.toRingEquiv.trans e₁.toRingEquiv
  have heK : ∀ a : A, eK (Localization.awayMap (algebraMap A C) φ (algebraMap A _ a)) = a := by
    intro a
    have h1 : Localization.awayMap (algebraMap A C) φ (algebraMap A _ a) =
        algebraMap C _ (algebraMap A C a) := IsLocalization.map_eq _ _
    rw [h1]
    show e₁ (eC.symm (eC (algebraMap A C a))) = a
    rw [AlgEquiv.symm_apply_apply, AlgEquiv.commutes]
    rfl
  refine ⟨n, fun _ ↦ 1, fun _ ↦ ⟨one_pos, by simp⟩,
    (RingEquiv.piCongrRight fun _ ↦ eK).trans eB.symm.toRingEquiv, fun r ↦ ?_⟩
  obtain ⟨a, rfl⟩ := eA.surjective r
  rw [show eA a = algebraMap A (Localization.Away φ) a from eA.commutes a]
  show eB.symm (fun _ ↦ eK (Localization.awayMap (algebraMap A C) φ (algebraMap A _ a))) = _
  simp only [heK]
  exact eB.symm.commutes a

end AlgebraicGeometry.Abhyankar
