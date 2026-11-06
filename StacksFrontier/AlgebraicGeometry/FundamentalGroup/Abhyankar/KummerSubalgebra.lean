module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.Abhyankar.KummerAlgebra
public import StacksFrontier.RingTheory.DiscreteValuationRing.Kummer

/-!
# Normal subalgebras of a Kummer extension

Let `A` be a domain, `φ ∈ A` nonzero, `A₀` a discrete valuation ring dominating `A` in which `φ`
is a uniformizer, and `K` a common fraction field of `A` and `A₀`. Let `B` be a normal domain which
is integral over `A_φ`, and suppose that `B` embeds over `A_φ` into the Kummer extension
`K[φ^{1/e}]`, with `e ≥ 2` prime to the residue characteristic of `A₀`. Then `B` is the
localization at `φ` of a standard tamely ramified algebra `A[x]/(x^d - φ)` for a divisor `d` of
`e`, provided these algebras are normal domains.

## Main results

* `AlgebraicGeometry.Abhyankar.exists_ringEquiv_of_ringHom_K1`: the identification.
* `AlgebraicGeometry.Abhyankar.isUnit_natCast_of_etale`: if `A[x]/(x^d - φ)_φ` is étale over
  `A_φ`, then `d` is invertible in `A_φ`.
* `AlgebraicGeometry.Abhyankar.isUnit_of_isUnit_algebraMap_away`: over a Noetherian domain with
  `(φ)` prime, an element outside `(φ)` which is invertible in `A_φ` is invertible.

## References

* [Stacks Project, Tag 0EYG](https://stacks.math.columbia.edu/tag/0EYG)
* [Stacks Project, Tag 09EV](https://stacks.math.columbia.edu/tag/09EV)
-/

@[expose] public noncomputable section

open Polynomial IsLocalRing Stacks.KummerExtension
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Abhyankar

variable {A : Type u} [CommRing A] [IsDomain A] {φ : A}
  {A₀ K : Type u} [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀] [Field K]
  [Algebra A A₀] [Algebra A₀ K] [IsFractionRing A₀ K] [Algebra A K] [IsScalarTower A A₀ K]
  [IsFractionRing A K]

/-- A ring map `A_φ → S` and an `d`-th root `s` of the image of `φ` extend to a ring map on
`(A[x]/(x^d - φ))_φ` over `A_φ`, sending the root to `s`. -/
private theorem exists_away_standardTamelyRamifiedAlgebra_lift {A S : Type*} [CommRing A]
    [CommRing S] (φ : A) (d : ℕ) (ρ : Localization.Away φ →+* S) (s : S)
    (hs : s ^ d = ρ (algebraMap A _ φ)) :
    ∃ β : Localization.Away (algebraMap A (standardTamelyRamifiedAlgebra A φ d) φ) →+* S,
      β.comp (Localization.awayMap (algebraMap A (standardTamelyRamifiedAlgebra A φ d)) φ) = ρ ∧
      β (algebraMap _ _ (root A φ d)) = s ∧
      ∀ p : A[X], β (algebraMap _ _ (Ideal.Quotient.mk _ p :
          standardTamelyRamifiedAlgebra A φ d)) = p.eval₂ (ρ.comp (algebraMap A _)) s := by
  let β₀ : standardTamelyRamifiedAlgebra A φ d →+* S :=
    Ideal.Quotient.lift _ (eval₂RingHom (ρ.comp (algebraMap A _)) s) (by
      intro p hp
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hp
      simp [hs])
  have hβ₀ : ∀ p, β₀ (Ideal.Quotient.mk _ p) = p.eval₂ (ρ.comp (algebraMap A _)) s :=
    fun p ↦ Ideal.Quotient.lift_mk _ _ _
  have hβ₀A : ∀ a, β₀ (algebraMap A _ a) = ρ (algebraMap A _ a) := fun a ↦ by
    rw [← Ideal.Quotient.mk_algebraMap, Polynomial.algebraMap_eq, hβ₀, eval₂_C]
    rfl
  have hunit : IsUnit (β₀ (algebraMap A _ φ)) := by
    rw [hβ₀A]
    exact (IsLocalization.Away.algebraMap_isUnit φ).map ρ
  have hβ : ∀ c, IsLocalization.Away.lift _ hunit (algebraMap _
      (Localization.Away (algebraMap A (standardTamelyRamifiedAlgebra A φ d) φ)) c) = β₀ c :=
    IsLocalization.Away.lift_eq _ hunit
  refine ⟨IsLocalization.Away.lift _ hunit,
    IsLocalization.ringHom_ext (Submonoid.powers φ) (RingHom.ext fun a ↦ ?_), ?_, fun p ↦ ?_⟩
  · simp only [RingHom.comp_apply]
    rw [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq, hβ, hβ₀A]
  · rw [hβ]
    exact (hβ₀ X).trans (eval₂_X _ _)
  · rw [hβ, hβ₀]

/-- **A normal domain sandwiched in a Kummer extension is a standard tamely ramified algebra.**
Let `φ ∈ A` map to a uniformizer of the discrete valuation ring `A₀`, `K` a common fraction field,
`e ≥ 2` prime to the residue characteristic of `A₀`, and `B` a normal domain integral over `A_φ`
with an `A_φ`-embedding `τ : B → K[φ^{1/e}]`. If the algebras `A[x]/(x^d - φ)` are normal
domains, then `B ≅ A[x]/(x^d - φ)_φ` over `A_φ` for some divisor `d` of `e`. -/
theorem exists_ringEquiv_of_ringHom_K1 (hπ : Irreducible (algebraMap A A₀ φ)) {e : ℕ} (he : 2 ≤ e)
    (hcop : ringChar (A₀ ⧸ maximalIdeal A₀) = 0 ∨
      Nat.Coprime (ringChar (A₀ ⧸ maximalIdeal A₀)) e)
    (hdom : ∀ d, 0 < d → IsDomain (standardTamelyRamifiedAlgebra A φ d))
    (hnorm : ∀ d, 0 < d → IsIntegrallyClosed (standardTamelyRamifiedAlgebra A φ d))
    (B : Type u) [CommRing B] [IsDomain B] [Algebra (Localization.Away φ) B]
    [Algebra.IsIntegral (Localization.Away φ) B] [IsIntegrallyClosed B]
    (τ : B →+* K1 K (algebraMap A A₀ φ) e)
    (hτ : ∀ a : A, τ (algebraMap _ B (algebraMap A (Localization.Away φ) a)) =
      algebraMap K _ (algebraMap A K a)) :
    ∃ d, 0 < d ∧ d ∣ e ∧ ∃ σ : Localization.Away
        (algebraMap A (standardTamelyRamifiedAlgebra A φ d) φ) ≃+* B,
      ∀ r, σ (Localization.awayMap (algebraMap A (standardTamelyRamifiedAlgebra A φ d)) φ r) =
        algebraMap _ B r := by
  classical
  have : Fact (Irreducible (kummerPoly K (algebraMap A A₀ φ) e)) :=
    ⟨kummerPoly_irreducible K _ e (by lia) hπ⟩
  have hφ0 : φ ≠ 0 := fun h ↦ hπ.ne_zero (by rw [h, map_zero])
  have : IsDomain (Localization.Away φ) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hφ0)
  have hAK : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  have hφK : algebraMap A K φ ≠ 0 := fun h ↦ hφ0 (hAK (h.trans (map_zero _).symm))
  let gK1 : A →+* K1 K (algebraMap A A₀ φ) e :=
    (algebraMap K (K1 K (algebraMap A A₀ φ) e)).comp (algebraMap A K)
  have hgK1 : IsUnit (gK1 φ) :=
    (isUnit_iff_ne_zero.mpr hφK).map (algebraMap K (K1 K (algebraMap A A₀ φ) e))
  let ρ : Localization.Away φ →+* K1 K (algebraMap A A₀ φ) e := IsLocalization.Away.lift φ hgK1
  have hρ : ∀ a : A, ρ (algebraMap A (Localization.Away φ) a) = gK1 a :=
    IsLocalization.Away.lift_eq φ hgK1
  have hρinj : Function.Injective ρ := by
    rw [IsLocalization.injective_iff_map_algebraMap_eq (Submonoid.powers φ) ρ]
    intro x y
    rw [hρ, hρ]
    constructor
    · intro h
      have h' := congrArg (IsLocalization.Away.lift φ hgK1) h
      rwa [hρ, hρ] at h'
    · intro h
      have h' : algebraMap A K x = algebraMap A K y :=
        (algebraMap K (K1 K (algebraMap A A₀ φ) e)).injective h
      rw [hAK h']
  have hτρ : τ.comp (algebraMap (Localization.Away φ) B) = ρ :=
    IsLocalization.ringHom_ext (Submonoid.powers φ) (RingHom.ext fun a ↦ by
      simp only [RingHom.comp_apply]
      rw [hτ, hρ]
      rfl)
  have hτinj : Function.Injective τ := by
    rw [RingHom.injective_iff_ker_eq_bot]
    apply Ideal.eq_bot_of_comap_eq_bot (R := Localization.Away φ)
    rw [RingHom.ker_eq_comap_bot, Ideal.under_def, Ideal.comap_comap, hτρ, ← RingHom.ker_eq_comap_bot]
    exact (RingHom.injective_iff_ker_eq_bot ρ).mp hρinj
  let τF : FractionRing B →+* K1 K (algebraMap A A₀ φ) e := IsFractionRing.lift hτinj
  have hτF : ∀ b, τF (algebraMap B (FractionRing B) b) = τ b :=
    IsFractionRing.lift_algebraMap hτinj
  let ιA : A →+* B := (algebraMap (Localization.Away φ) B).comp (algebraMap A (Localization.Away φ))
  have hιA : ∀ a, τ (ιA a) = algebraMap K _ (algebraMap A K a) := hτ
  let M := IntermediateField.adjoin K (Set.range τ)
  obtain ⟨d, hd0, hde, hM, hMd, -⟩ :=
    intermediateField_eq_adjoin K (algebraMap A A₀ φ) e he hπ hcop M
  let y := piRoot K (algebraMap A A₀ φ) e ^ (e / d)
  have hKle : ∀ k : K, algebraMap K (K1 K (algebraMap A A₀ φ) e) k ∈ τF.fieldRange := by
    intro k
    obtain ⟨a, s, -, rfl⟩ := IsFractionRing.div_surjective (A := A) k
    rw [map_div₀]
    refine div_mem ⟨algebraMap B (FractionRing B) (ιA a), by rw [hτF, hιA]⟩
      ⟨algebraMap B (FractionRing B) (ιA s), by rw [hτF, hιA]⟩
  let MF : IntermediateField K (K1 K (algebraMap A A₀ φ) e) :=
    { τF.fieldRange with algebraMap_mem' := hKle }
  have hMle : M ≤ MF := IntermediateField.adjoin_le_iff.mpr (by
    rintro _ ⟨b, rfl⟩
    exact ⟨algebraMap B (FractionRing B) b, hτF b⟩)
  have hyM : y ∈ M := by
    rw [hM]
    exact IntermediateField.mem_adjoin_simple_self K _
  obtain ⟨w, hw⟩ := hMle hyM
  have hyd : y ^ d = τ (ιA φ) := by
    rw [hιA, ← pow_mul, Nat.div_mul_cancel hde, piRoot_pow,
      IsScalarTower.algebraMap_apply A₀ K, IsScalarTower.algebraMap_apply A A₀ K]
  have hwd : w ^ d = algebraMap B (FractionRing B) (ιA φ) := by
    apply (IsFractionRing.lift hτinj).injective
    show τF (w ^ d) = τF _
    rwa [map_pow, hτF, hw]
  obtain ⟨b₀, hb₀⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow (R := B)
    (K := FractionRing B) hd0 (by rw [hwd]; exact isIntegral_algebraMap)
  have hτb₀ : τ b₀ = y := by rwa [← hτF, hb₀]
  have hb₀d : b₀ ^ d = ιA φ := hτinj (by rw [map_pow, hτb₀, hyd])
  have : NeZero d := ⟨hd0.ne'⟩
  let C := standardTamelyRamifiedAlgebra A φ d
  have : IsDomain C := hdom d hd0
  have : IsIntegrallyClosed C := hnorm d hd0
  have hunitB : IsUnit (ιA φ) :=
    (IsLocalization.Away.algebraMap_isUnit φ).map (algebraMap (Localization.Away φ) B)
  obtain ⟨β, hβκ, -, hβ⟩ := exists_away_standardTamelyRamifiedAlgebra_lift φ d
    (algebraMap (Localization.Away φ) B) b₀ hb₀d
  let KA := Localization.Away (algebraMap A C φ)
  let κ : Localization.Away φ →+* KA := Localization.awayMap (algebraMap A C) φ
  have hκ : ∀ a, κ (algebraMap A (Localization.Away φ) a) = algebraMap C KA (algebraMap A C a) :=
    fun a ↦ IsLocalization.map_eq _ _
  have hβA : ∀ a, β (algebraMap C KA (algebraMap A C a)) = ιA a := fun a ↦ by
    rw [← hκ]
    exact RingHom.congr_fun hβκ _
  let : Algebra (Localization.Away φ) KA := κ.toAlgebra
  have hRB : Function.Injective (algebraMap (Localization.Away φ) B) := by
    intro r₁ r₂ h
    apply hρinj
    rw [← hτρ, RingHom.comp_apply, RingHom.comp_apply, h]
  have hφC : algebraMap A C φ ≠ 0 := fun h ↦
    hunitB.ne_zero ((hβA φ).symm.trans ((congrArg (β.comp (algebraMap C KA)) h).trans (map_zero _)))
  have : IsDomain KA :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hφC)
  have : IsIntegrallyClosed KA :=
    isIntegrallyClosed_of_isLocalization KA (Submonoid.powers (algebraMap A C φ))
      (powers_le_nonZeroDivisors_of_noZeroDivisors hφC)
  have : Algebra.IsIntegral (Localization.Away φ) KA := by
    constructor
    intro z
    obtain ⟨⟨c, ⟨_, n, rfl⟩⟩, rfl⟩ :=
      IsLocalization.mk'_surjective (Submonoid.powers (algebraMap A C φ)) z
    have hc : _root_.IsIntegral (Localization.Away φ) (algebraMap C KA c) :=
      IsIntegral.map_of_comp_eq (algebraMap A (Localization.Away φ)) (algebraMap C KA)
        (RingHom.ext fun a ↦ hκ a) (Algebra.IsIntegral.isIntegral (R := A) c)
    have hinv : IsLocalization.mk' KA (1 : C)
          (⟨(algebraMap A C φ) ^ n, n, rfl⟩ : Submonoid.powers (algebraMap A C φ)) =
        algebraMap (Localization.Away φ) KA (IsLocalization.mk' (Localization.Away φ) (1 : A)
          (⟨φ ^ n, n, rfl⟩ : Submonoid.powers φ)) := by
      rw [IsLocalization.mk'_eq_iff_eq_mul]
      show algebraMap C KA 1 = κ _ * algebraMap C KA ((algebraMap A C φ) ^ n)
      have h1 : IsLocalization.mk' (Localization.Away φ) (1 : A)
          (⟨φ ^ n, n, rfl⟩ : Submonoid.powers φ) * algebraMap A _ (φ ^ n) = 1 :=
        (IsLocalization.mk'_spec (Localization.Away φ) (1 : A)
          (⟨φ ^ n, n, rfl⟩ : Submonoid.powers φ)).trans (map_one _)
      rw [← map_pow, ← hκ, ← map_mul, h1, map_one, map_one]
    dsimp only
    rw [IsLocalization.mk'_eq_mul_mk'_one, hinv]
    exact hc.mul isIntegral_algebraMap
  have hβinj : Function.Injective β := by
    rw [RingHom.injective_iff_ker_eq_bot]
    apply Ideal.eq_bot_of_comap_eq_bot (R := Localization.Away φ)
    rw [RingHom.ker_eq_comap_bot, Ideal.under_def, Ideal.comap_comap]
    show Ideal.comap (β.comp κ) ⊥ = ⊥
    rw [hβκ, ← RingHom.ker_eq_comap_bot]
    exact (RingHom.injective_iff_ker_eq_bot _).mp hRB
  have hmul : ∀ b : B, ∃ (c : KA) (s : A), s ≠ 0 ∧ β c = ιA s * b := by
    intro b
    have hbM : τ b ∈ M := IntermediateField.subset_adjoin K _ ⟨b, rfl⟩
    rw [hM] at hbM
    have hyalg : IsAlgebraic K y := Algebra.IsAlgebraic.isAlgebraic y
    have hbK : τ b ∈ Algebra.adjoin K {y} := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hyalg]
      exact hbM
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hbK
    obtain ⟨p, hp⟩ := hbK
    obtain ⟨s, hs, hq⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors A) p
    refine ⟨algebraMap C KA (Ideal.Quotient.mk _ (IsLocalization.integerNormalization
      (nonZeroDivisors A) p)), s, nonZeroDivisors.ne_zero hs, hτinj ?_⟩
    have h1 : τ (β (algebraMap C KA (Ideal.Quotient.mk _ (IsLocalization.integerNormalization
        (nonZeroDivisors A) p)))) =
        (IsLocalization.integerNormalization (nonZeroDivisors A) p).eval₂ gK1 y := by
      rw [hβ, Polynomial.hom_eval₂, hτb₀]
      congr 1
      ext a
      exact hιA a
    have h2 : (IsLocalization.integerNormalization (nonZeroDivisors A) p).eval₂ gK1 y =
        (Polynomial.map (algebraMap A K)
          (IsLocalization.integerNormalization (nonZeroDivisors A) p)).eval₂
            (algebraMap K _) y := by
      rw [eval₂_map]
    rw [h1, h2, hq, map_mul, hιA, ← hp]
    show _ = _ * Polynomial.aeval y p
    rw [Polynomial.aeval_def, Algebra.smul_def, Polynomial.eval₂_mul,
      IsScalarTower.algebraMap_apply A K K[X], ← Polynomial.C_eq_algebraMap, Polynomial.eval₂_C]
  let : Algebra KA (FractionRing B) := ((algebraMap B (FractionRing B)).comp β).toAlgebra
  have hKAF : ∀ c, algebraMap KA (FractionRing B) c = algebraMap B (FractionRing B) (β c) :=
    fun _ ↦ rfl
  have : FaithfulSMul KA (FractionRing B) := (faithfulSMul_iff_algebraMap_injective _ _).mpr
    ((IsFractionRing.injective B (FractionRing B)).comp hβinj)
  have hιA0 : ∀ s : A, s ≠ 0 → algebraMap B (FractionRing B) (ιA s) ≠ 0 := by
    intro s hs h
    apply hs
    apply hAK
    apply (algebraMap K (K1 K (algebraMap A A₀ φ) e)).injective
    rw [map_zero, map_zero, ← hιA,
      IsFractionRing.injective B (FractionRing B) (h.trans (map_zero _).symm), map_zero]
  have : IsFractionRing KA (FractionRing B) := IsFractionRing.of_field KA (K := FractionRing B) (by
    intro z
    obtain ⟨b₁, b₂, hb₂, rfl⟩ := IsFractionRing.div_surjective (A := B) z
    obtain ⟨c₁, s₁, hs₁, h₁⟩ := hmul b₁
    obtain ⟨c₂, s₂, hs₂, h₂⟩ := hmul b₂
    refine ⟨c₁ * algebraMap C KA (algebraMap A C s₂), c₂ * algebraMap C KA (algebraMap A C s₁),
      ?_⟩
    have hb₂' : algebraMap B (FractionRing B) b₂ ≠ 0 :=
      fun h ↦ nonZeroDivisors.ne_zero hb₂ (IsFractionRing.injective B _ (h.trans (map_zero _).symm))
    rw [map_mul, map_mul, hKAF, hKAF, hKAF, hKAF, hβA, hβA, h₁, h₂, map_mul, map_mul]
    have := hιA0 s₁ hs₁
    have := hιA0 s₂ hs₂
    field_simp)
  have hβsurj : Function.Surjective β := by
    intro b
    have hint : _root_.IsIntegral KA (algebraMap B (FractionRing B) b) :=
      IsIntegral.map_of_comp_eq κ (algebraMap B (FractionRing B))
        (by rw [← hβκ]; rfl) (Algebra.IsIntegral.isIntegral (R := Localization.Away φ) b)
    obtain ⟨c, hc⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
    exact ⟨c, IsFractionRing.injective B (FractionRing B) hc⟩
  exact ⟨d, hd0, hde, RingEquiv.ofBijective β ⟨hβinj, hβsurj⟩,
    fun r ↦ RingHom.congr_fun hβκ r⟩

section Unit

/-- **An étale Kummer cover has invertible exponent.** If `A[x]/(x^d - φ)_φ` is étale over `A_φ`,
then `d` is invertible in `A_φ`. -/
theorem isUnit_natCast_of_etale (A : Type u) [CommRing A] (φ : A) (d : ℕ) [NeZero d]
    (h : letI :=
        (Localization.awayMap (algebraMap A (standardTamelyRamifiedAlgebra A φ d)) φ).toAlgebra
      Algebra.Etale (Localization.Away φ)
        (Localization.Away (algebraMap A (standardTamelyRamifiedAlgebra A φ d) φ))) :
    IsUnit (d : Localization.Away φ) := by
  classical
  let C := standardTamelyRamifiedAlgebra A φ d
  let KA := Localization.Away (algebraMap A C φ)
  let κ : Localization.Away φ →+* KA := Localization.awayMap (algebraMap A C) φ
  let : Algebra (Localization.Away φ) KA := κ.toAlgebra
  have hκ : ∀ a, κ (algebraMap A (Localization.Away φ) a) = algebraMap C KA (algebraMap A C a) :=
    fun a ↦ IsLocalization.map_eq _ _
  by_contra hd
  obtain ⟨Q, hQ, hdQ⟩ := exists_max_ideal_of_mem_nonunits hd
  have := hQ
  let : Field (Localization.Away φ ⧸ Q) := Ideal.Quotient.field Q
  let E := AlgebraicClosure (Localization.Away φ ⧸ Q)
  let ε : Localization.Away φ →+* E := algebraMap (Localization.Away φ) E
  have hdE : (d : E) = 0 := by
    rw [← map_natCast ε, IsScalarTower.algebraMap_apply (Localization.Away φ)
      (Localization.Away φ ⧸ Q) E, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem.mpr hdQ, map_zero]
  set ℓ := ringChar E
  have hℓd : ℓ ∣ d := (ringChar.spec E d).mp hdE
  have hℓ : ℓ.Prime := by
    have := ringChar.charP E
    rcases CharP.char_is_prime_or_zero E (ringChar E) with h | h
    · exact h
    · have h' : ringChar E ∣ d := hℓd
      rw [h, zero_dvd_iff] at h'
      exact absurd h' (NeZero.ne d)
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP E ℓ := ringChar.charP E
  obtain ⟨m, hm⟩ := hℓd
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp [NeZero.ne d] at hm)
  have hmd : m < d := by rw [hm]; exact lt_mul_left hm0 hℓ.one_lt
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (ε (algebraMap A _ φ)) (NeZero.pos d)
  let W' := AdjoinRoot (X ^ d - Polynomial.C (ε (algebraMap A _ φ)))
  have hroot : (AdjoinRoot.root (X ^ d - Polynomial.C (ε (algebraMap A _ φ)))) ^ d =
      algebraMap E W' (ε (algebraMap A _ φ)) := by
    have := AdjoinRoot.eval₂_root (X ^ d - Polynomial.C (ε (algebraMap A _ φ)))
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C] at this
    exact sub_eq_zero.mp this
  obtain ⟨ψ, hψκ, hψ, -⟩ := exists_away_standardTamelyRamifiedAlgebra_lift φ d
    ((algebraMap E W').comp ε) _ hroot
  let W := E ⊗[Localization.Away φ] KA
  have : Algebra.Etale E W := inferInstance
  have : _root_.IsReduced W := Algebra.FormallyUnramified.isReduced_of_field E W
  let ψA : KA →ₐ[Localization.Away φ] W' :=
    { ψ with
      commutes' := fun r ↦ (RingHom.congr_fun hψκ r).trans
        (IsScalarTower.algebraMap_apply (Localization.Away φ) E W' r).symm }
  let Ψ : W →ₐ[E] W' := Algebra.TensorProduct.lift (Algebra.ofId E W') ψA
    (fun _ _ ↦ Commute.all _ _)
  have : Nontrivial W' := AdjoinRoot.nontrivial _ (by
    rw [Polynomial.degree_X_pow_sub_C (NeZero.pos d)]
    exact_mod_cast NeZero.ne d)
  have : Nontrivial W := ⟨⟨0, 1, fun h ↦ zero_ne_one (congrArg Ψ h |>.trans (map_one Ψ))⟩⟩
  have : CharP W ℓ := charP_of_injective_algebraMap (algebraMap E W).injective ℓ
  let tW : W := (1 : E) ⊗ₜ algebraMap C KA (root A φ d)
  have hφW : tW ^ d = algebraMap E W (ε (algebraMap A _ φ)) := by
    rw [Algebra.TensorProduct.tmul_pow, one_pow, ← map_pow, root_pow, ← hκ]
    show (1 : E) ⊗ₜ[Localization.Away φ] algebraMap (Localization.Away φ) KA _ = _
    exact (Algebra.TensorProduct.algebraMap_apply' _).symm.trans
      (IsScalarTower.algebraMap_apply (Localization.Away φ) E W _)
  let z : W := tW ^ m - algebraMap E W (c ^ m)
  have hz : z ^ ℓ = 0 := by
    rw [sub_pow_char, ← pow_mul, ← map_pow, ← pow_mul, mul_comm m ℓ, ← hm, hφW, hc, sub_self]
  have hz0 : z = 0 := IsNilpotent.eq_zero ⟨ℓ, hz⟩
  have hΨz : Ψ z = AdjoinRoot.mk _ (X ^ m - Polynomial.C (c ^ m)) := by
    have htW : Ψ tW = AdjoinRoot.root _ := by
      show Algebra.TensorProduct.lift _ _ _ ((1 : E) ⊗ₜ _) = _
      rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
      exact hψ
    simp only [z, map_sub, map_pow, htW, AlgHom.commutes, AdjoinRoot.mk_X, AdjoinRoot.mk_C]
    rfl
  rw [hz0, map_zero, eq_comm, AdjoinRoot.mk_eq_zero] at hΨz
  have := Polynomial.natDegree_le_of_dvd hΨz (Polynomial.X_pow_sub_C_ne_zero hm0 _)
  rw [Polynomial.natDegree_X_pow_sub_C, Polynomial.natDegree_X_pow_sub_C] at this
  lia

/-- **Invertibility away from a height one prime.** Let `A` be a Noetherian domain, `φ ≠ 0` with
`(φ)` prime. An element `x ∉ (φ)` which becomes invertible in `A_φ` is invertible. -/
theorem isUnit_of_isUnit_algebraMap_away {A : Type u} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] {φ x : A} (hφ : (Ideal.span {φ}).IsPrime) (hφ0 : φ ≠ 0)
    (hx : IsUnit (algebraMap A (Localization.Away φ) x)) (hxφ : x ∉ Ideal.span {φ}) :
    IsUnit x := by
  by_contra hxu
  have hne : Ideal.span {x} ≠ ⊤ := by rwa [Ne, Ideal.span_singleton_eq_top]
  obtain ⟨M, hM, hxM⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨Q, hQ, -⟩ := Ideal.exists_minimalPrimes_le hxM
  have := hQ.1.1
  have hxQ : x ∈ Q := hQ.1.2 (Ideal.mem_span_singleton_self x)
  have hφQ : φ ∈ Q := by
    obtain ⟨y, hy⟩ := hx.exists_right_inv
    obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, ha⟩ := IsLocalization.surj (Submonoid.powers φ) y
    have h1 : algebraMap A (Localization.Away φ) (x * a) =
        algebraMap A (Localization.Away φ) (φ ^ n) := by
      rw [map_mul, ← ha, ← mul_assoc, hy, one_mul]
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers φ) _).mp h1
    have : φ ^ k * φ ^ n ∈ Q := by
      rw [← hk]
      exact Q.mul_mem_left _ (Q.mul_mem_right _ hxQ)
    rw [← pow_add] at this
    exact hQ.1.1.mem_of_pow_mem _ this
  have hle : Ideal.span {φ} ≤ Q := (Ideal.span_singleton_le_iff_mem _).mpr hφQ
  have hht : Q.height ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ Q hQ
  have hbot : (⊥ : Ideal A) < Ideal.span {φ} := by
    rwa [bot_lt_iff_ne_bot, Ne, Ideal.span_singleton_eq_bot]
  have hφht : 1 ≤ (Ideal.span {φ}).height := by
    have := Ideal.height_add_one_le_of_lt_of_isPrime hbot
    rwa [Ideal.height_bot, zero_add] at this
  have heq : Ideal.span {φ} = Q := by
    by_contra hne'
    have := Ideal.height_add_one_le_of_lt_of_isPrime (lt_of_le_of_ne hle hne')
    have h2 : (2 : ℕ∞) ≤ Q.height := le_trans (by
      have := add_le_add_left hφht 1
      rwa [add_comm (1 : ℕ∞)] at this) this
    exact absurd (h2.trans hht) (by decide)
  exact hxφ (heq ▸ hxQ)

end Unit

end AlgebraicGeometry.Abhyankar
