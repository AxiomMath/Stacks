module

public import StacksFrontier.RingTheory.DiscreteValuationRing.Abhyankar.UniformizerPowerSmoothness

/-!
# Abhyankar's lemma

Abhyankar's lemma: if the residue characteristic of `A` is zero, or if it is prime to the
ramification index `e` of `A → B` and the residue-field extension `κ_B / κ_A` is separable, then
the local factors after a finite fraction-field extension are formally smooth as soon as `e`
divides the ramification index downstairs. This file also defines the Kummer-overfield property
used to characterize tame ramification, together with the first auxiliary lemmas for that
characterization.

## Main definitions

* `IsDiscreteValuationRing.HasUnramifiedKummerOverfield`: for a fixed exponent `n`, the property
  that `L` embeds into an unramified extension of the Kummer extension `K[π^(1/n)]`.

## Main results

* `IsDiscreteValuationRing.formallySmooth_localizations_of_ramificationIndex_dvd`: Abhyankar's
  lemma for extensions of discrete valuation rings.

## Implementation notes

The rings `A[π^(1/n)]` and fields `K[π^(1/n)]` are the canonical Kummer models of Tag 09EV.

## References

* [The Stacks Project, Tag 0BRM](https://stacks.math.columbia.edu/tag/0BRM)
-/

@[expose] public section

namespace IsDiscreteValuationRing

section

universe u v w x y z

open scoped TensorProduct

open Polynomial

/-- In a tower `R / S / T / U`, if `R / S / T`, `S / T / U` and `R / T / U` are scalar towers, then
so is `R / S / U`. -/
private theorem isScalarTower_skip_third (R S T U : Type*) [CommSemiring R] [CommSemiring S]
    [CommSemiring T] [CommSemiring U] [Algebra R S] [Algebra R T] [Algebra R U] [Algebra S T]
    [Algebra S U] [Algebra T U] [IsScalarTower R S T] [IsScalarTower S T U]
    [IsScalarTower R T U] : IsScalarTower R S U :=
  .of_algebraMap_eq fun r ↦ by
    rw [IsScalarTower.algebraMap_apply R T U, IsScalarTower.algebraMap_apply R S T,
      ← IsScalarTower.algebraMap_apply S T U]

/-- In a tower `R / S / T / U`, if `R / S / T`, `S / T / U` and `R / S / U` are scalar towers, then
so is `R / T / U`. -/
private theorem isScalarTower_skip_second (R S T U : Type*) [CommSemiring R] [CommSemiring S]
    [CommSemiring T] [CommSemiring U] [Algebra R S] [Algebra R T] [Algebra R U] [Algebra S T]
    [Algebra S U] [Algebra T U] [IsScalarTower R S T] [IsScalarTower S T U]
    [IsScalarTower R S U] : IsScalarTower R T U :=
  .of_algebraMap_eq fun r ↦ by
    rw [IsScalarTower.algebraMap_apply R S U, IsScalarTower.algebraMap_apply R S T,
      ← IsScalarTower.algebraMap_apply S T U]

/-- If `C` is faithful over `A` and `D` is the localization of `C` at a prime, then `D` is faithful
over `A`. -/
private theorem faithfulSMul_of_isLocalization_atPrime (A C D : Type*) [CommRing A] [CommRing C]
    [IsDomain C] [CommRing D] [Algebra A C] [Algebra C D] [Algebra A D] [IsScalarTower A C D]
    [FaithfulSMul A C] (p : Ideal C) [p.IsPrime] [IsLocalization.AtPrime D p] :
    FaithfulSMul A D := by
  refine (faithfulSMul_iff_algebraMap_injective A D).mpr ?_
  rw [IsScalarTower.algebraMap_eq A C D]
  exact (IsLocalization.injective D p.primeCompl_le_nonZeroDivisors).comp
    (FaithfulSMul.algebraMap_injective A C)

/-- A ring map between integral closures that is compatible with the inclusions into the fields
is injective. -/
private theorem injective_of_coe_eq_algebraMap {A B K E : Type*} [CommRing A] [CommRing B]
    [Field K] [Field E] [Algebra A K] [Algebra B E] [Algebra K E]
    (f : integralClosure A K →+* integralClosure B E)
    (hf : ∀ z, ((f z : integralClosure B E) : E) = algebraMap K E z) : Function.Injective f :=
  fun a b h ↦ Subtype.ext ((algebraMap K E).injective (by rw [← hf, ← hf, h]))

set_option maxHeartbeats 4000000 in
-- Elaborating the many nested localization and tensor-product algebra structures here is
-- expensive.
set_option synthInstance.maxHeartbeats 200000 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- Comparing the nested localization algebras requires additional reduction steps.
-- Their maps are characterized in the common fraction fields.
/-- **Abhyankar's lemma.** A tamely ramified extension of discrete valuation rings becomes
formally smooth at every local factor after a finite fraction-field extension whose local
ramification index is divisible by the original one. -/
@[stacks 0BRM]
theorem formallySmooth_localizations_of_ramificationIndex_dvd
    (A : Type u) (B : Type v) (K : Type w) (L : Type x) (K₁ : Type y)
    [CommRing A] [CommRing B] [Field K] [Field L] [Field K₁]
    [IsDomain A] [IsDomain B] [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Algebra A B] [IsExtension A B]
    [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L] [Algebra K K₁]
    [Algebra A K₁]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsScalarTower A K K₁]
    [IsFractionRing A K] [IsFractionRing B L] [Module.Finite K K₁]
    (htame : ringChar (IsLocalRing.ResidueField A) = 0 ∨
      Nat.Coprime (ringChar (IsLocalRing.ResidueField A))
          (ramificationIndex A B) ∧
        Algebra.IsSeparableExtension (IsLocalRing.ResidueField A)
          (IsLocalRing.ResidueField B)) :
    ∃ (n : ℕ) (E : Fin n → Type (max u v w x y))
      (_ : ∀ i, Field (E i))
      (_ : ∀ i, Algebra K (E i))
      (_ : ∀ i, Algebra L (E i))
      (_ : ∀ i, Algebra K₁ (E i))
      (_ : ∀ i, Algebra B (E i))
      (_ : ∀ i, IsScalarTower K L (E i))
      (_ : ∀ i, IsScalarTower K K₁ (E i))
      (_ : ∀ i, Module.Finite L (E i))
      (decomp : ((L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁)) ≃ₐ[K] ∀ i, E i),
      0 < n ∧
      (∀ i (z : L),
        decomp (Ideal.Quotient.mk _
          ((Algebra.TensorProduct.includeLeft : L →ₐ[K] L ⊗[K] K₁) z)) i =
          algebraMap L (E i) z) ∧
      (∀ i (z : K₁),
        decomp (Ideal.Quotient.mk _
          ((Algebra.TensorProduct.includeRight : K₁ →ₐ[K] L ⊗[K] K₁) z)) i =
          algebraMap K₁ (E i) z) ∧
      (∀ i (z : B), algebraMap B (E i) z =
        algebraMap L (E i) (algebraMap B L z)) ∧
      ∀ i, let A₁ := integralClosure A K₁
        let B₁ := integralClosure B (E i)
        ∃ f : A₁ →+* B₁,
          (∀ z : A₁, ((f z : B₁) : E i) =
            algebraMap K₁ (E i) ((z : A₁) : K₁)) ∧
          (∀ z : A, f (algebraMap A A₁ z) =
            algebraMap B B₁ (algebraMap A B z)) ∧
          ∀ p : Ideal A₁, p.IsMaximal →
            ramificationIndex A B ∣ p.ramificationIdx A →
            ∀ q : Ideal B₁, q.IsMaximal → q.comap f = p →
              ∃ (_ : q.IsPrime) (_ : p.IsPrime),
                (∃ _ : IsDomain (Localization p.primeCompl),
                  IsDiscreteValuationRing (Localization p.primeCompl)) ∧
                (∃ _ : IsDomain (Localization q.primeCompl),
                  IsDiscreteValuationRing (Localization q.primeCompl)) ∧
                ∃ φ : Localization p.primeCompl →+* Localization q.primeCompl,
                  Function.Injective φ ∧ IsLocalHom φ ∧
                    (∀ z : A₁, φ (algebraMap A₁ _ z) =
                      algebraMap B₁ _ (f z)) ∧
                    RingHom.FormallySmoothNAdic φ
                      (IsLocalRing.maximalIdeal (Localization q.primeCompl)) := by
  classical
  obtain ⟨n, E, hE, hKE, hLE, hK₁E, hKLE, hKK₁E, hfin, decomp, hn, hleft, hright⟩ :=
    exists_tensorProduct_quotNilradical_equiv_pi_fields.{w, x, y, max u v w x y} K L K₁
  let := hE
  let := hKE
  let := hLE
  let := hK₁E
  let := hKLE
  let := hKK₁E
  let := hfin
  let (i : Fin n) : Algebra B (E i) :=
    ((algebraMap L (E i)).comp (algebraMap B L)).toAlgebra
  let (i : Fin n) : IsScalarTower B L (E i) := .of_algebraMap_eq fun _ ↦ rfl
  refine ⟨n, E, hE, hKE, hLE, hK₁E, inferInstance, hKLE, hKK₁E, hfin,
    decomp, hn, hleft, hright, (fun _ _ ↦ rfl), ?_⟩
  intro i
  let : Algebra A (E i) := ((algebraMap L (E i)).comp (algebraMap A L)).toAlgebra
  let : IsScalarTower A L (E i) := .of_algebraMap_eq fun _ ↦ rfl
  let : IsScalarTower A B (E i) := isScalarTower_skip_third A B L (E i)
  let : IsScalarTower A K (E i) := isScalarTower_skip_third A K L (E i)
  let : IsScalarTower A K₁ (E i) := isScalarTower_skip_second A K K₁ (E i)
  obtain ⟨f, hf, hfA⟩ := exists_integralClosure_hom A B K₁ (E i)
  refine ⟨f, hf, hfA, ?_⟩
  intro p hp hdiv q hq hpq
  let := hp
  let := hq
  let A₁ := integralClosure A K₁
  let B₁ := integralClosure B (E i)
  have hA₁ : IsDedekindDomain A₁ :=
    (IsIntegralClosure.isDedekindDomain_and_comap_surjective_and_quasiFinite A K K₁ A₁).1
  have hB₁ : IsDedekindDomain B₁ :=
    (IsIntegralClosure.isDedekindDomain_and_comap_surjective_and_quasiFinite B L (E i) B₁).1
  let := hA₁
  let := hB₁
  let : FaithfulSMul A K₁ := .trans A K K₁
  let : FaithfulSMul B (E i) := .trans B L (E i)
  let : IsDiscreteValuationRing (Localization.AtPrime p) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A₁
      (maximalIdeal_ne_bot_of_isIntegral A A₁ p) _
  let : IsDiscreteValuationRing (Localization.AtPrime q) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B₁
      (maximalIdeal_ne_bot_of_isIntegral B B₁ q) _
  obtain ⟨φ, hφinj, hφlocal, hφ⟩ :=
    exists_injective_localRingHom f (injective_of_coe_eq_algebraMap f hf) p q hpq
  refine ⟨inferInstance, inferInstance, ⟨inferInstance, inferInstance⟩,
    ⟨inferInstance, inferInstance⟩, φ, hφinj, hφlocal, hφ, ?_⟩
  obtain ⟨fE, hfE, hfEK₁⟩ := exists_surjective_tensorProduct_projection E decomp hleft hright i
  by_cases he : ramificationIndex A B = 1
  · apply formallySmoothNAdic_tensorProduct_fieldFactor A B K L K₁ (E i)
      fE hfE hfEK₁ f hf p q hpq φ hφ
    apply (formallySmooth_iff_weaklyUnramified_and_isSeparableExtension A B).mpr
    refine ⟨he, ?_⟩
    rcases htame with h | h
    · exact isSeparableExtension_of_ringChar_eq_zero _ _ h
    · exact h.2
  let R := Localization.AtPrime p
  let D := Localization.AtPrime q
  let : CommRing D := inferInstanceAs (CommRing (Localization.AtPrime q))
  let : IsDomain D := inferInstanceAs (IsDomain (Localization.AtPrime q))
  let : CommRing R := inferInstanceAs (CommRing (Localization.AtPrime p))
  let : IsDomain R := inferInstanceAs (IsDomain (Localization.AtPrime p))
  let : IsLocalHom (algebraMap A R) := isLocalHom_localizationAtPrime_of_isIntegral A A₁ R p
  let : FaithfulSMul A R := faithfulSMul_of_isLocalization_atPrime A A₁ R p
  let : IsExtension A R := ⟨⟩
  let : IsFractionRing A₁ K₁ := integralClosure.isFractionRing_of_finite_extension K K₁
  obtain ⟨hRK₁, hA₁RK₁, hFracR⟩ := exists_fractionRing_localizationAtPrime_algebra A₁ K₁ p
  let := hRK₁
  let := hA₁RK₁
  let := hFracR
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hepos := (ramificationIndex_characterization A B).1
  have hen0 : ramificationIndex A B ≠ 0 := by omega
  have heunit : IsUnit (ramificationIndex A B : R) := by
    have h := isUnit_natCast_of_residueChar (R := A) hen0 (htame.imp_right And.left)
    simpa only [map_natCast] using h.map (algebraMap A R)
  have hdivR : ramificationIndex A B ∣ ramificationIndex A R := by
    rw [ramificationIndex_eq_ramificationIdx A R,
      ramificationIdx_maximalIdeal_localizationAtPrime A A₁ p]
    exact hdiv
  obtain ⟨K₂, hK₂, hK₁K₂, hRK₂, hRK₁K₂, hK₂fin, hK₂sep,
    hnormfin, hnormetale, θ, hθ⟩ :=
    exists_finite_separable_extension_uniformizer_pow_eq A R K₁ π hπ hen0 heunit hdivR
  let := hK₂
  let := hK₁K₂
  let := hRK₂
  let := hRK₁K₂
  let := hK₂fin
  let : Algebra K K₂ := ((algebraMap K₁ K₂).comp (algebraMap K K₁)).toAlgebra
  let : IsScalarTower K K₁ K₂ := .of_algebraMap_eq fun _ ↦ rfl
  let : Module.Finite K K₂ := Module.Finite.trans K₁ K₂
  let : IsScalarTower A R K₁ := isScalarTower_skip_second A A₁ R K₁
  let : Algebra A K₂ := ((algebraMap K₁ K₂).comp (algebraMap A K₁)).toAlgebra
  let : IsScalarTower A K₁ K₂ := .of_algebraMap_eq fun _ ↦ rfl
  let : IsScalarTower A R K₂ := isScalarTower_skip_third A R K₁ K₂
  let : IsScalarTower A K K₂ := isScalarTower_skip_third A K K₁ K₂
  let e := ramificationIndex A B
  have he2 : 2 ≤ e := by dsimp only [e]; omega
  let : Fact (Irreducible (Stacks.KummerExtension.kummerPoly K π e)) :=
    ⟨Stacks.KummerExtension.kummerPoly_irreducible K π e (by omega) hπ⟩
  let Kroot := Stacks.KummerExtension.K1 K π e
  let Aroot := Stacks.KummerExtension.A1 K π e
  have hθeval : (Stacks.KummerExtension.kummerPoly K π e).eval₂ (algebraMap K K₂) θ = 0 := by
    rw [Stacks.KummerExtension.kummerPoly, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, hθ,
      ← IsScalarTower.algebraMap_apply A R K₂, ← IsScalarTower.algebraMap_apply A K K₂,
      sub_self]
  obtain ⟨hKrootK₂, hKKrootK₂, hKrootfin, hroot⟩ :=
    exists_finite_algebra_adjoinRoot_of_eval_eq_zero (Stacks.KummerExtension.kummerPoly K π e) θ
      hθeval
  let := hKrootK₂
  let := hKKrootK₂
  let := hKrootfin
  let : IsDiscreteValuationRing Aroot := Stacks.KummerExtension.isDiscreteValuationRing_A1 K π e he2
    hπ
  let : IsLocalHom (algebraMap A Aroot) := Stacks.LocalHom.isLocalHom_of_isIntegral A Aroot
  let : FaithfulSMul A Kroot := .trans A K Kroot
  let : IsExtension A Aroot := ⟨⟩
  let : IsFractionRing B₁ (E i) := integralClosure.isFractionRing_of_finite_extension L (E i)
  obtain ⟨hDE, hB₁DE, hFracD⟩ := exists_fractionRing_localizationAtPrime_algebra B₁ (E i) q
  let := hDE
  let := hB₁DE
  let := hFracD
  let : Algebra R D := φ.toAlgebra
  let : Algebra R (E i) := ((algebraMap K₁ (E i)).comp (algebraMap R K₁)).toAlgebra
  let : IsScalarTower R K₁ (E i) := .of_algebraMap_eq fun _ ↦ rfl
  have hRD : (algebraMap D (E i)).comp φ =
      (algebraMap K₁ (E i)).comp (algebraMap R K₁) := by
    apply IsLocalization.ringHom_ext p.primeCompl
    ext a
    change algebraMap D (E i) (φ (algebraMap A₁ R a)) =
      algebraMap K₁ (E i) (algebraMap R K₁ (algebraMap A₁ R a))
    rw [hφ, ← IsScalarTower.algebraMap_apply B₁ D (E i),
      ← IsScalarTower.algebraMap_apply A₁ R K₁]
    exact hf a
  let : IsScalarTower R D (E i) := .of_algebraMap_eq fun r ↦
    (RingHom.congr_fun hRD r).symm
  obtain ⟨n₂, E₂, hE₂, hK₁E₂, hEE₂, hK₂E₂, hK₁EE₂, hK₁K₂E₂,
    hE₂fin, decomp₂, hn₂, hleft₂, hright₂⟩ :=
    exists_tensorProduct_quotNilradical_equiv_pi_fields.{y, max u v w x y, y, max u v w x y}
      K₁ (E i) K₂
  let := hE₂
  let := hK₁E₂
  let := hEE₂
  let := hK₂E₂
  let := hK₁EE₂
  let := hK₁K₂E₂
  let := hE₂fin
  let j : Fin n₂ := ⟨0, hn₂⟩
  let E' := E₂ j
  let : Algebra D E' := ((algebraMap (E i) E').comp (algebraMap D (E i))).toAlgebra
  let : IsScalarTower D (E i) E' := .of_algebraMap_eq fun _ ↦ rfl
  let : Algebra R E' := ((algebraMap (E i) E').comp (algebraMap R (E i))).toAlgebra
  let : IsScalarTower R (E i) E' := .of_algebraMap_eq fun _ ↦ rfl
  let : IsScalarTower R D E' := isScalarTower_skip_third R D (E i) E'
  let : IsScalarTower R K₁ E' := isScalarTower_skip_third R K₁ (E i) E'
  let : IsScalarTower R K₂ E' := isScalarTower_skip_second R K₁ K₂ E'
  let C₂ := integralClosure D E'
  let : IsDedekindDomain C₂ :=
    (IsIntegralClosure.isDedekindDomain_and_comap_surjective_and_quasiFinite D (E i) E' C₂).1
  obtain ⟨g₂, hg₂, hg₂R⟩ := exists_integralClosure_hom R D K₂ E'
  let R₂ := integralClosure R K₂
  let : IsLocalHom (algebraMap R D) := hφlocal
  obtain ⟨q₂, hq₂⟩ := Ideal.exists_maximal C₂
  let := hq₂
  let p₂ := q₂.comap g₂
  let : p₂.IsMaximal := isMaximal_comap_of_integral_square R D R₂ C₂ g₂
    (by ext r; exact congrArg Subtype.val (hg₂R r)) q₂
  let : IsDedekindDomain R₂ :=
    (IsIntegralClosure.isDedekindDomain_and_comap_surjective_and_quasiFinite R K₁ K₂ R₂).1
  let : FaithfulSMul R K₂ := .trans R K₁ K₂
  let : FaithfulSMul D E' := .trans D (E i) E'
  let : FaithfulSMul R R₂ := (faithfulSMul_iff_algebraMap_injective R R₂).mpr (by
    intro a b h
    apply FaithfulSMul.algebraMap_injective R K₂
    exact congrArg Subtype.val h)
  let : FaithfulSMul D C₂ := (faithfulSMul_iff_algebraMap_injective D C₂).mpr (by
    intro a b h
    apply FaithfulSMul.algebraMap_injective D E'
    exact congrArg Subtype.val h)
  let : IsDiscreteValuationRing (Localization.AtPrime p₂) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R₂
      (maximalIdeal_ne_bot_of_isIntegral R R₂ p₂) _
  let : IsDiscreteValuationRing (Localization.AtPrime q₂) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain C₂
      (maximalIdeal_ne_bot_of_isIntegral D C₂ q₂) _
  obtain ⟨φ₂, hφ₂inj, hφ₂local, hφ₂⟩ :=
    exists_injective_localRingHom g₂ (injective_of_coe_eq_algebraMap g₂ hg₂) p₂ q₂ rfl
  have hupper : RingHom.FormallySmoothNAdic.{y} (algebraMap R (Localization.AtPrime p₂))
      (IsLocalRing.maximalIdeal (Localization.AtPrime p₂)) := by
    let := hnormetale
    exact formallySmoothNAdic_localization_of_formallySmooth p₂
  let S := Localization.AtPrime p₂
  let T := Localization.AtPrime q₂
  let : CommRing S := inferInstanceAs (CommRing (Localization.AtPrime p₂))
  let : CommRing T := inferInstanceAs (CommRing (Localization.AtPrime q₂))
  let : IsDomain S := inferInstanceAs (IsDomain (Localization.AtPrime p₂))
  let : IsDomain T := inferInstanceAs (IsDomain (Localization.AtPrime q₂))
  let : IsFractionRing R₂ K₂ := integralClosure.isFractionRing_of_finite_extension K₁ K₂
  obtain ⟨hSK₂, hR₂SK₂, hFracS⟩ := exists_fractionRing_localizationAtPrime_algebra R₂ K₂ p₂
  let := hSK₂
  let := hR₂SK₂
  let := hFracS
  let : IsFractionRing C₂ E' := integralClosure.isFractionRing_of_finite_extension (E i) E'
  obtain ⟨hTE', hC₂TE', hFracT⟩ := exists_fractionRing_localizationAtPrime_algebra C₂ E' q₂
  let := hTE'
  let := hC₂TE'
  let := hFracT
  let : IsLocalHom (algebraMap R S) := isLocalHom_localizationAtPrime_of_isIntegral R R₂ S p₂
  let : FaithfulSMul R S := faithfulSMul_of_isLocalization_atPrime R R₂ S p₂
  let : IsExtension R S := ⟨⟩
  let : IsLocalHom (algebraMap D T) := isLocalHom_localizationAtPrime_of_isIntegral D C₂ T q₂
  let : FaithfulSMul D T := faithfulSMul_of_isLocalization_atPrime D C₂ T q₂
  let : IsExtension D T := ⟨⟩
  let : Algebra S T := φ₂.toAlgebra
  let : IsLocalHom (algebraMap S T) := hφ₂local
  let : FaithfulSMul S T := (faithfulSMul_iff_algebraMap_injective S T).mpr hφ₂inj
  let : IsExtension S T := ⟨⟩
  let : IsScalarTower R D T := inferInstance
  let : IsScalarTower R S T := .of_algebraMap_eq fun r ↦ by
    rw [IsScalarTower.algebraMap_apply R D T]
    change algebraMap D T (algebraMap R D r) = φ₂ (algebraMap R S r)
    rw [IsScalarTower.algebraMap_apply R R₂ S, hφ₂, hg₂R,
      ← IsScalarTower.algebraMap_apply D C₂ T]
  let : IsLocalHom (algebraMap R T) := by
    rw [IsScalarTower.algebraMap_eq R D T]
    infer_instance
  let : FaithfulSMul R D := (faithfulSMul_iff_algebraMap_injective R D).mpr hφinj
  let : IsExtension R D := ⟨⟩
  let : FaithfulSMul R T := .trans R D T
  let : IsExtension R T := ⟨⟩
  let : IsScalarTower R S K₂ := .of_algebraMap_eq fun r ↦ by
    rw [IsScalarTower.algebraMap_apply R R₂ S, ← IsScalarTower.algebraMap_apply R₂ S K₂]
    rfl
  let : IsScalarTower A R S := inferInstance
  let : IsScalarTower A S K₂ := isScalarTower_skip_second A R S K₂
  let : IsLocalHom (algebraMap A S) := by
    rw [IsScalarTower.algebraMap_eq A R S]
    infer_instance
  let : FaithfulSMul A S := .trans A R S
  let : IsExtension A S := ⟨⟩
  let : Algebra B E' := ((algebraMap (E i) E').comp (algebraMap B (E i))).toAlgebra
  let : IsScalarTower B (E i) E' := .of_algebraMap_eq fun _ ↦ rfl
  let : IsScalarTower B B₁ E' := isScalarTower_skip_third B B₁ (E i) E'
  let : IsScalarTower B₁ D E' := isScalarTower_skip_third B₁ D (E i) E'
  let : IsScalarTower B D E' := isScalarTower_skip_second B B₁ D E'
  let : IsScalarTower D T E' := .of_algebraMap_eq fun d ↦ by
    rw [IsScalarTower.algebraMap_apply D C₂ T, ← IsScalarTower.algebraMap_apply C₂ T E']
    rfl
  let : IsScalarTower B T E' := isScalarTower_skip_second B D T E'
  let : IsLocalHom (algebraMap B D) := isLocalHom_localizationAtPrime_of_isIntegral B B₁ D q
  let : FaithfulSMul B D := faithfulSMul_of_isLocalization_atPrime B B₁ D q
  let : IsLocalHom (algebraMap B T) := by
    rw [IsScalarTower.algebraMap_eq B D T]
    infer_instance
  let : FaithfulSMul B T := .trans B D T
  let : IsExtension B T := ⟨⟩
  let : Algebra S E' := ((algebraMap K₂ E').comp (algebraMap S K₂)).toAlgebra
  let : IsScalarTower S K₂ E' := .of_algebraMap_eq fun _ ↦ rfl
  let : IsScalarTower S T E' := .of_algebraMap_eq fun s ↦ by
    have hc : (algebraMap T E').comp φ₂ = (algebraMap K₂ E').comp (algebraMap S K₂) := by
      apply IsLocalization.ringHom_ext p₂.primeCompl
      ext r
      change algebraMap T E' (φ₂ (algebraMap R₂ S r)) =
        algebraMap K₂ E' (algebraMap S K₂ (algebraMap R₂ S r))
      rw [hφ₂, ← IsScalarTower.algebraMap_apply C₂ T E',
        ← IsScalarTower.algebraMap_apply R₂ S K₂]
      exact hg₂ r
    exact (RingHom.congr_fun hc s).symm
  let : Algebra K E' := ((algebraMap K₁ E').comp (algebraMap K K₁)).toAlgebra
  let : IsScalarTower K K₁ E' := .of_algebraMap_eq fun _ ↦ rfl
  let : Algebra L E' := ((algebraMap (E i) E').comp (algebraMap L (E i))).toAlgebra
  let : IsScalarTower L (E i) E' := .of_algebraMap_eq fun _ ↦ rfl
  let : IsScalarTower K L E' := .of_algebraMap_eq fun k ↦ by
    rw [IsScalarTower.algebraMap_apply K K₁ E', IsScalarTower.algebraMap_apply K₁ (E i) E',
      ← IsScalarTower.algebraMap_apply K K₁ (E i), IsScalarTower.algebraMap_apply K L (E i),
      ← IsScalarTower.algebraMap_apply L (E i) E']
  let : IsScalarTower K K₂ E' := isScalarTower_skip_second K K₁ K₂ E'
  let : IsScalarTower B L E' := isScalarTower_skip_third B L (E i) E'
  obtain ⟨fE', hfE', hfE'K₂⟩ :=
    exists_surjective_tensorProduct_projection E₂ decomp₂ hleft₂ hright₂ j
  let fnew : L ⊗[K] K₂ →ₐ[L] E' := Algebra.TensorProduct.lift
    (Algebra.ofId L E') (IsScalarTower.toAlgHom K K₂ E') (fun _ _ ↦ Commute.all _ _)
  have hfnewK₂ (a : K₂) : fnew (Algebra.TensorProduct.includeRight a) = algebraMap K₂ E' a := by
    simp [fnew]
  have hfnew : Function.Surjective fnew := by
    intro e'
    apply mem_of_surjective_tensorProduct fE' hfE' (RingHom.id E') fnew.range.toSubring
    · apply mem_of_surjective_tensorProduct fE hfE (algebraMap (E i) E') fnew.range.toSubring
      · intro l
        exact ⟨algebraMap L (L ⊗[K] K₂) l, by
          change fnew (algebraMap L _ l) = algebraMap (E i) E' (algebraMap L (E i) l)
          rw [fnew.commutes, ← IsScalarTower.algebraMap_apply L (E i) E']⟩
      · intro a
        exact ⟨Algebra.TensorProduct.includeRight (algebraMap K₁ K₂ a), by
          change fnew (Algebra.TensorProduct.includeRight (algebraMap K₁ K₂ a)) =
            algebraMap (E i) E' (fE (Algebra.TensorProduct.includeRight a))
          rw [hfnewK₂, hfEK₁, ← IsScalarTower.algebraMap_apply K₁ K₂ E',
            ← IsScalarTower.algebraMap_apply K₁ (E i) E']⟩
    · intro a
      exact ⟨Algebra.TensorProduct.includeRight a, (hfnewK₂ a).trans (hfE'K₂ a).symm⟩
  have hsmooth :=
    formallySmoothNAdic_of_uniformizer_pow_eq A B K L K₂ E' S T fnew hfnew hfnewK₂
      π hπ θ (by rw [IsScalarTower.algebraMap_apply A R K₂]; exact hθ) he2 htame
  have hRT :=
    formallySmoothNAdic_trans R S T hupper hsmooth
  exact formallySmoothNAdic_of_max_universe R D (formallySmoothNAdic_tower_bot R D T hRT)

end

section

universe u v w x y z v' w'

/-- For a fixed positive exponent `e` invertible in the residue field, there is a finite
separable extension of `K[π^(1/e)]`, unramified with respect to `A[π^(1/e)]`, into
which `L` embeds over `K`. -/
def HasUnramifiedKummerOverfield
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (π : A) (hπ : Irreducible π) (e : ℕ) : Prop :=
  ∃ he : 1 ≤ e,
    IsUnit (e : IsLocalRing.ResidueField A) ∧
      letI : Fact (Irreducible (Stacks.KummerExtension.kummerPoly K π e)) :=
        ⟨Stacks.KummerExtension.kummerPoly_irreducible K π e he hπ⟩
      ∃ (L' : Type (max u v w)) (_ : Field L')
        (_ : Algebra (Stacks.KummerExtension.K1 K π e) L')
        (_ : Algebra K L')
        (_ : IsScalarTower K (Stacks.KummerExtension.K1 K π e) L')
        (_ : Algebra A L')
        (_ : IsScalarTower A (Stacks.KummerExtension.K1 K π e) L')
        (_ : FiniteDimensional (Stacks.KummerExtension.K1 K π e) L')
        (_ : Algebra.IsSeparable (Stacks.KummerExtension.K1 K π e) L')
        (_ : IsDiscreteValuationRing (Stacks.KummerExtension.A1 K π e))
        (_ : Algebra (Stacks.KummerExtension.A1 K π e) L'),
        (∀ x : Stacks.KummerExtension.A1 K π e,
          algebraMap (Stacks.KummerExtension.A1 K π e) L' x =
            algebraMap (Stacks.KummerExtension.K1 K π e) L' (x : Stacks.KummerExtension.K1 K π e)) ∧
        Nonempty (L →ₐ[K] L') ∧
          ∀ m : Ideal (integralClosure (Stacks.KummerExtension.A1 K π e) L'), m.IsMaximal →
            ∀ _ : m.LiesOver (IsLocalRing.maximalIdeal (Stacks.KummerExtension.A1 K π e)),
              Ideal.ramificationIdx'
                  (IsLocalRing.maximalIdeal (Stacks.KummerExtension.A1 K π e)) m = 1 ∧
                @Algebra.IsSeparable
                  ((Stacks.KummerExtension.A1 K π e) ⧸
                    IsLocalRing.maximalIdeal (Stacks.KummerExtension.A1 K π e))
                  (integralClosure (Stacks.KummerExtension.A1 K π e) L' ⧸ m) _ _
                  (Ideal.Quotient.algebraOfLiesOver m
                    (IsLocalRing.maximalIdeal (Stacks.KummerExtension.A1 K π e)))

open Polynomial
open scoped TensorProduct

theorem exists_separable_tensor_factor
    (K : Type u) (L : Type v) (F : Type w)
    [Field K] [Field L] [Field F] [Algebra K L] [Algebra K F]
    [Module.Finite K L] [Algebra.IsSeparable K L] :
    ∃ (E : Type (max v w z)) (_ : Field E) (_ : Algebra F E)
      (_ : Module.Finite F E) (_ : Algebra.IsSeparable F E)
      (q : (F ⊗[K] L) →ₐ[F] E), Function.Surjective q := by
  classical
  have : Algebra.Etale K L :=
    ⟨Algebra.FormallyEtale.of_isSeparable K L,
      Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
  let T := ULift.{z} (F ⊗[K] L)
  have : Algebra.Etale F T := Algebra.Etale.of_equiv ULift.algEquiv.symm
  obtain ⟨I, hI, E, hfield, halg, e, h⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod F T).mp inferInstance
  have : Nonempty I := by
    by_contra hn
    have : IsEmpty I := not_nonempty_iff.mp hn
    exact zero_ne_one (e.injective (Subsingleton.elim _ _))
  obtain ⟨i⟩ := this
  let up : (F ⊗[K] L) ≃ₐ[F] T := ULift.algEquiv.symm
  let q := (Pi.evalAlgHom F E i).comp (e.toAlgHom.comp up.toAlgHom)
  exact ⟨E i, hfield i, halg i, (h i).1, (h i).2, q,
    (Function.surjective_eval i).comp (e.surjective.comp up.surjective)⟩

theorem exists_algEquiv_of_surjective_pi
    (R : Type u) [CommRing R] {I : Type v} [Finite I] (E : I → Type w)
    [∀ i, Field (E i)] [∀ i, Algebra R (E i)]
    (F : Type z) [Field F] [Algebra R F]
    (f : (∀ i, E i) →ₐ[R] F) (hf : Function.Surjective f) :
    ∃ (i : I) (g : E i ≃ₐ[R] F), g.toAlgHom.comp (Pi.evalAlgHom R E i) = f := by
  classical
  let _ := Fintype.ofFinite I
  have hsum : ∑ i : I, Pi.single i (1 : E i) = 1 := by
    ext i
    simp
  obtain ⟨i, hi⟩ : ∃ i : I, f (Pi.single i (1 : E i)) ≠ 0 := by
    by_contra! h
    have heq := congrArg f hsum
    simp only [map_sum, h, Finset.sum_const_zero, map_one] at heq
    exact zero_ne_one heq
  let π := Pi.evalAlgHom R E i
  have hπ : Function.Surjective π := Function.surjective_eval i
  have hker : RingHom.ker π.toRingHom ≤ RingHom.ker f.toRingHom := by
    intro z hz
    change f z = 0
    have hz' : z i = 0 := hz
    have hmul : z * Pi.single i (1 : E i) = 0 := by
      ext j
      by_cases hji : j = i
      · subst j; simp [hz']
      · simp [Pi.single_eq_of_ne hji]
    have heq := congrArg f hmul
    rw [map_mul, map_zero] at heq
    exact (mul_eq_zero.mp heq).resolve_right hi
  let g := π.liftOfSurjective hπ f hker
  exact ⟨i, AlgEquiv.ofBijective g
    ⟨g.injective, π.liftOfSurjective_surjective hπ f hker hf⟩,
    π.liftOfSurjective_comp hπ f hker⟩

theorem isLocalization_integralClosure
    (B : Type u) (R : Type v) (E : Type w) (C : Type x)
    [CommRing B] [CommRing R] [Field E] [CommRing C]
    [Algebra B R] [Algebra B E] [Algebra R E] [IsScalarTower B R E]
    [Algebra B C] [Algebra C E] [IsScalarTower B C E]
    [IsIntegralClosure C B E]
    [Algebra C (integralClosure R E)]
    [IsScalarTower C (integralClosure R E) E]
    [IsScalarTower B C (integralClosure R E)]
    (S : Submonoid B) [IsLocalization S R]
    [IsLocalization (Algebra.algebraMapSubmonoid E S) E] :
    IsLocalization (Algebra.algebraMapSubmonoid C S) (integralClosure R E) := by
  let D := integralClosure R E
  let C₀ := integralClosure B E
  let e : C₀ ≃ₐ[B] C := IsIntegralClosure.equiv B C₀ E C
  have hsub : C₀ ≤ Subalgebra.restrictScalars B D := fun z hz => hz.tower_top
  let : Algebra C₀ D := (Subalgebra.inclusion hsub).toAlgebra
  have : IsScalarTower C₀ D E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower B C₀ D := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsLocalization (Algebra.algebraMapSubmonoid C₀ S) D :=
    IsLocalization.integralClosure (R := B) (S := E) (Rf := R) (Sf := E) S
  have hmap : (Algebra.algebraMapSubmonoid C S).map e.symm.toMonoidHom =
      Algebra.algebraMapSubmonoid C₀ S := by
    change (Algebra.algebraMapSubmonoid C S).map e.symm.toAlgHom.toMonoidHom = _
    exact Algebra.algebraMapSubmonoid_map_eq S e.symm.toAlgHom
  apply IsLocalization.of_ringEquiv_left e.symm.toRingEquiv hmap
  intro c
  apply FaithfulSMul.algebraMap_injective D E
  rw [← IsScalarTower.algebraMap_apply C D E]
  change algebraMap C E c = (e.symm c).1
  exact (IsIntegralClosure.algebraMap_equiv B C E C₀ c).symm

private theorem isSeparable_of_isSeparablyGenerated
    (k : Type u) (F : Type v) [Field k] [Field F] [Algebra k F]
    [Algebra.IsAlgebraic k F] [Algebra.IsSeparablyGenerated k F] :
    Algebra.IsSeparable k F := by
  obtain ⟨s, hs, hsep⟩ :=
    Algebra.IsSeparablyGenerated.isSeparable (k := k) (K := F)
  have : IsEmpty s := hs.1.isEmpty_of_isAlgebraic
  have hs0 : s = ∅ := Set.isEmpty_coe_sort.mp this
  subst s
  rw [IntermediateField.adjoin_empty] at hsep
  have := hsep
  exact Algebra.IsSeparable.of_equiv_equiv
    (IntermediateField.botEquiv k F).toRingEquiv (RingEquiv.refl F) (by
      ext x
      change algebraMap k F ((IntermediateField.botEquiv k F) x) = x.1
      exact congrArg Subtype.val ((IntermediateField.botEquiv k F).symm_apply_apply x))

theorem isSeparable_of_isSeparableExtension
    (k : Type u) (F : Type v) [Field k] [Field F] [Algebra k F]
    [Module.Finite k F] [Algebra.IsSeparableExtension k F] :
    Algebra.IsSeparable k F := by
  have : Algebra.IsSeparable k (⊤ : IntermediateField k F) :=
    isSeparable_of_isSeparablyGenerated k (⊤ : IntermediateField k F)
  exact Algebra.IsSeparable.of_algHom k (⊤ : IntermediateField k F)
    IntermediateField.topEquiv.symm.toAlgHom

theorem isSeparableExtension_of_isSeparable
    (k : Type u) (F : Type v) [Field k] [Field F] [Algebra k F]
    [Algebra.IsSeparable k F] : Algebra.IsSeparableExtension k F := by
  constructor
  intro F' _
  have : Algebra.IsSeparable k F' :=
    Algebra.IsSeparable.of_algHom k F F'.val
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis k F'
  exact ⟨s, hs, Algebra.isSeparable_tower_top_of_isSeparable k _ _⟩

theorem ramificationIdx_atPrime
    (A B R : Type*) [CommRing A] [CommRing B] [CommRing R]
    [Algebra A B] [Algebra B R] [Algebra A R] [IsScalarTower A B R]
    (m : Ideal B) [m.IsPrime] [IsLocalization.AtPrime R m] [IsLocalRing R] :
    (IsLocalRing.maximalIdeal R).ramificationIdx A = m.ramificationIdx A := by
  have : (IsLocalRing.maximalIdeal R).LiesOver m :=
    ⟨(IsLocalization.AtPrime.under_maximalIdeal R m).symm⟩
  have : Module.Flat B R := IsLocalization.flat R m.primeCompl
  have : Algebra.EssFiniteType B R := Algebra.EssFiniteType.of_isLocalization R m.primeCompl
  have : Algebra.FormallyUnramified B R :=
    Algebra.FormallyUnramified.of_isLocalization m.primeCompl
  have hram := Ideal.ramificationIdx_tower (R := A) m (IsLocalRing.maximalIdeal R)
  have h1 : (IsLocalRing.maximalIdeal R).ramificationIdx B = 1 :=
    Ideal.ramificationIdx_eq_one _ B
  simpa [h1] using hram

theorem exists_large_unit_multiple
    (k : Type*) [Field k] (e : ℕ) (he : 1 ≤ e) (hu : IsUnit (e : k)) :
    ∃ e' : ℕ, 2 ≤ e' ∧ IsUnit (e' : k) ∧ e ∣ e' := by
  have h : ∃ n : ℕ, 2 ≤ n ∧ IsUnit (n : k) := by
    by_cases h2 : IsUnit (2 : k)
    · exact ⟨2, le_rfl, h2⟩
    · refine ⟨3, by omega, isUnit_iff_ne_zero.mpr ?_⟩
      have h20 : (2 : k) = 0 := by simpa only [isUnit_iff_ne_zero, not_not] using h2
      intro h30
      have : (1 : k) = 0 := by linear_combination h30 - h20
      exact one_ne_zero this
  obtain ⟨n, hn, hun⟩ := h
  exact ⟨n * e, by nlinarith, by simpa using hun.mul hu, dvd_mul_left e n⟩

open IsLocalRing in
theorem unram_transport {R S M : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S]
    [CommRing M] [Algebra R M] [Algebra S M] (σ : R ≃+* S)
    (hσ : ∀ r, algebraMap S M (σ r) = algebraMap R M r)
    (h : ∀ m : Ideal (integralClosure R M), m.IsMaximal →
      ∀ _ : m.LiesOver (IsLocalRing.maximalIdeal R),
        Ideal.ramificationIdx' (IsLocalRing.maximalIdeal R) m = 1 ∧
          @Algebra.IsSeparable (R ⧸ IsLocalRing.maximalIdeal R) (integralClosure R M ⧸ m) _ _
            (Ideal.Quotient.algebraOfLiesOver m (IsLocalRing.maximalIdeal R))) :
    ∀ m : Ideal (integralClosure S M), m.IsMaximal →
      ∀ _ : m.LiesOver (IsLocalRing.maximalIdeal S),
        Ideal.ramificationIdx' (IsLocalRing.maximalIdeal S) m = 1 ∧
          @Algebra.IsSeparable (S ⧸ IsLocalRing.maximalIdeal S) (integralClosure S M ⧸ m) _ _
            (Ideal.Quotient.algebraOfLiesOver m (IsLocalRing.maximalIdeal S)) := by
  have hcomp : (algebraMap S M).comp (σ : R →+* S) = (RingHom.id M).comp (algebraMap R M) := by
    ext r; exact hσ r
  have hcomp' : (algebraMap R M).comp (σ.symm : S →+* R) =
      (RingHom.id M).comp (algebraMap S M) := by
    ext s; simpa using (hσ (σ.symm s)).symm
  let τ : integralClosure R M ≃+* integralClosure S M :=
    { toFun := fun x => ⟨x.1, IsIntegral.map_of_comp_eq (σ : R →+* S) (RingHom.id M) hcomp x.2⟩
      invFun := fun y => ⟨y.1, IsIntegral.map_of_comp_eq (σ.symm : S →+* R) (RingHom.id M)
        hcomp' y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }
  have hτ : (τ : integralClosure R M →+* integralClosure S M).comp
      (algebraMap R (integralClosure R M)) =
      (algebraMap S (integralClosure S M)).comp (σ : R →+* S) := by
    ext r; exact (hσ r).symm
  have hmax : IsLocalRing.maximalIdeal S = (IsLocalRing.maximalIdeal R).map (σ : R →+* S) :=
    (map_ringEquiv_maximalIdeal σ).symm
  intro m' hm' hlies
  let m : Ideal (integralClosure R M) := m'.comap (τ : integralClosure R M →+* integralClosure S M)
  have hmm' : m' = m.map (τ : integralClosure R M →+* integralClosure S M) :=
    (Ideal.map_comap_of_surjective _ τ.surjective m').symm
  have hmmax : m.IsMaximal := Ideal.comap_isMaximal_of_surjective _ τ.surjective
  have hmlies : m.LiesOver (IsLocalRing.maximalIdeal R) := by
    constructor
    rw [Ideal.under, Ideal.comap_comap, hτ, ← Ideal.comap_comap, ← Ideal.under, ← hlies.over]
    rw [hmax, Ideal.map_comap_of_equiv]
    ext x
    simp [Ideal.mem_comap]
  obtain ⟨hram, hsep⟩ := h m hmmax hmlies
  have hle : ∀ (I J : Ideal (integralClosure R M)),
      I ≤ J ↔ I.map (τ : integralClosure R M →+* integralClosure S M) ≤
        J.map (τ : integralClosure R M →+* integralClosure S M) := by
    intro I J
    rw [Ideal.map_le_iff_le_comap, Ideal.map_comap_of_equiv]
    constructor <;> intro hIJ x hx <;> simpa [Ideal.mem_comap] using hIJ hx
  have hmapmax : ((IsLocalRing.maximalIdeal R).map (algebraMap R (integralClosure R M))).map
      (τ : integralClosure R M →+* integralClosure S M) =
      (IsLocalRing.maximalIdeal S).map (algebraMap S (integralClosure S M)) := by
    rw [Ideal.map_map, hτ, ← Ideal.map_map, ← hmax]
  refine ⟨?_, ?_⟩
  · rw [← hram]
    unfold Ideal.ramificationIdx'
    congr 1
    ext n
    simp only [Set.mem_ofPred_eq]
    rw [hle, hmapmax, Ideal.map_pow, ← hmm']
  · let : (IsLocalRing.maximalIdeal R).IsMaximal := IsLocalRing.maximalIdeal.isMaximal R
    let : (IsLocalRing.maximalIdeal S).IsMaximal := IsLocalRing.maximalIdeal.isMaximal S
    let : Field (R ⧸ IsLocalRing.maximalIdeal R) := Ideal.Quotient.field _
    let : Field (S ⧸ IsLocalRing.maximalIdeal S) := Ideal.Quotient.field _
    let := Ideal.Quotient.algebraOfLiesOver m (IsLocalRing.maximalIdeal R)
    let := Ideal.Quotient.algebraOfLiesOver m' (IsLocalRing.maximalIdeal S)
    refine Algebra.IsSeparable.of_equiv_equiv
      (Ideal.quotientEquiv (IsLocalRing.maximalIdeal R) (IsLocalRing.maximalIdeal S) σ hmax)
      (Ideal.quotientEquiv m m' τ hmm') ?_
    apply Ideal.Quotient.ringHom_ext
    ext r
    change Ideal.Quotient.mk m' (algebraMap S (integralClosure S M) (σ r)) =
      Ideal.Quotient.mk m' (τ (algebraMap R (integralClosure R M) r))
    exact congrArg (Ideal.Quotient.mk m') (RingHom.congr_fun hτ r).symm

end

end IsDiscreteValuationRing
