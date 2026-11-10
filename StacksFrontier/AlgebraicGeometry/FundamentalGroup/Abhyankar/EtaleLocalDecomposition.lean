module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.Abhyankar.StrictHenselizationDescent
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.Abhyankar.StrictlyHenselianStructure
public import StacksFrontier.RingTheory.RegularLocalRing.StrictHenselizationParameters

/-!
# Abhyankar's lemma for a regular divisor: the affine étale-local statement

Let `R` be a Noetherian ring, `φ ∈ R` a nonzerodivisor, `p ⊆ R` a prime and `B` a finite étale
`R_φ`-algebra. If `φ ∈ p`, assume that `R_p` and `R_p/φ` are regular and that the base change of
`B` to the strict henselization `Λ` of `R` at `p` is tamely ramified over `Spec Λ` in codimension
one. Then there are an étale `R`-algebra `D` with a prime over `p`, and integers `eᵢ ≥ 1`
invertible in `D`, such that `D_φ ⊗_{R_φ} B ≅ ∏ᵢ D[x]/(x^{eᵢ} - φ)_φ` over `D`
([Stacks, Tag 0EYG]).

## Main results

* `AlgebraicGeometry.Abhyankar.exists_etale_kummerAway_algEquiv`: the statement above.

## References

* [Stacks Project, Tag 0EYG](https://stacks.math.columbia.edu/tag/0EYG)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Abhyankar

/-- A ring isomorphism `∏ᵢ A[x]/(x^{eᵢ} - φ)_φ ≅ C` compatible with `A_φ` is `A`-linear. -/
def algEquivOfRingEquivKummerAway {A : Type u} [CommRing A] {φ : A} {n : ℕ} {e : Fin n → ℕ}
    {C : Type u} [CommRing C] [Algebra (Localization.Away φ) C] [Algebra A C]
    [IsScalarTower A (Localization.Away φ) C]
    (σ : (∀ i, Localization.Away (algebraMap A (standardTamelyRamifiedAlgebra A φ (e i)) φ)) ≃+* C)
    (hσ : ∀ r, σ (fun i ↦ Localization.awayMap
      (algebraMap A (standardTamelyRamifiedAlgebra A φ (e i))) φ r) = algebraMap _ C r) :
    (∀ i, Localization.Away (algebraMap A (standardTamelyRamifiedAlgebra A φ (e i)) φ)) ≃ₐ[A] C :=
  { σ with
    commutes' := fun a ↦ by
      have : (algebraMap A (∀ i, Localization.Away
          (algebraMap A (standardTamelyRamifiedAlgebra A φ (e i)) φ)) a) =
          fun i ↦ Localization.awayMap
            (algebraMap A (standardTamelyRamifiedAlgebra A φ (e i))) φ (algebraMap A _ a) := by
        funext i
        exact (IsScalarTower.algebraMap_apply A (standardTamelyRamifiedAlgebra A φ (e i)) _ a).trans
          (IsLocalization.map_eq _ _).symm
      change σ _ = _
      rw [this, hσ, ← IsScalarTower.algebraMap_apply] }

-- suggested change: make the private
-- `isRegularLocalRing_iff_and_ringKrullDim_eq_of_isHenselization` and its quotient version in
-- `StrictHenselizationParameters` public, and delete these two copies.
private theorem isRegularLocalRing_iff_of_isHenselization
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {Ash : Type u} [CommRing Ash] [IsLocalRing Ash] [Algebra A Ash]
    (L : Type u) [Field L] [Algebra (ResidueField A) L] [IsSepClosure (ResidueField A) L]
    [IsHenselization A L Ash] :
    IsRegularLocalRing A ↔ IsRegularLocalRing Ash := by
  obtain ⟨Ah, _, _, _, _⟩ := IsLocalRing.exists_isHenselization_residueField A
  exact (isRegularLocalRing_iff_henselizations A Ah Ash L).2

private theorem isRegularLocalRing_quotient_iff_of_isHenselization
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {Ash : Type u} [CommRing Ash] [IsLocalRing Ash] [Algebra A Ash]
    (L : Type u) [Field L] [Algebra (ResidueField A) L] [IsSepClosure (ResidueField A) L]
    [IsHenselization A L Ash] (I : Ideal A) (hI : I ≤ maximalIdeal A) :
    IsRegularLocalRing (A ⧸ I) ↔ IsRegularLocalRing (Ash ⧸ I.map (algebraMap A Ash)) := by
  have : IsLocalHom (algebraMap A Ash) := IsHenselization.isLocalHom (L := L)
  have : HenselianLocalRing Ash := IsHenselization.henselian (R := A) (L := L)
  obtain ⟨a, _, hsep, hres⟩ :=
    IsHenselization.exists_residueFieldAlgebra (R := A) (L := L) (Rh := Ash)
  have halg : a = ResidueField.instAlgebra (R := A) (S := Ash) :=
    Algebra.algebra_ext _ _ fun z ↦ by
      obtain ⟨r, rfl⟩ := residue_surjective z
      exact (hres r).trans (ResidueField.algebraMap_residue (S := Ash) r).symm
  subst halg
  have : IsSepClosure (ResidueField A) (ResidueField Ash) := hsep inferInstance
  obtain ⟨_, _, _, hhens, hind, _, _⟩ :=
    IsLocalRing.strictHenselization_quotient (R := A) (Rsh := Ash)
      (IsHenselization.ind_etale_of_universe_le.{u, u, u} L)
      (IsHenselization.map_maximalIdeal (R := A) (L := L) (Rh := Ash)) I hI
  have : IsHenselization (A ⧸ I) (ResidueField (Ash ⧸ I.map (algebraMap A Ash)))
      (Ash ⧸ I.map (algebraMap A Ash)) :=
    IsHenselization.of_ind_etale hhens hind
      ⟨RingEquiv.refl _, fun z ↦ ResidueField.algebraMap_residue z⟩
  exact isRegularLocalRing_iff_of_isHenselization (A := A ⧸ I)
    (Ash := Ash ⧸ I.map (algebraMap A Ash)) (ResidueField (Ash ⧸ I.map (algebraMap A Ash)))

/-- **Abhyankar's lemma for a regular divisor, affine étale-local form.** Let `R` be a Noetherian
ring, `φ ∈ R` a nonzerodivisor, `p ⊆ R` a prime, and `B` a finite étale `R_φ`-algebra. If `φ ∈ p`,
assume that `R_p` and `R_p/φ` are regular local rings and that, if the strict henselization `Λ` of
`R` at `p` is a regular local ring in which `φ ≠ 0`, the base change of `B` to `Λ` is tamely
ramified over `Spec Λ` in codimension one. Then there are
an étale `R`-algebra `D` with a prime `q` over `p` and integers `eᵢ ≥ 1` invertible in `D` with
`∏ᵢ D[x]/(x^{eᵢ} - φ)_φ ≅ D_φ ⊗_{R_φ} B` over `D`. -/
theorem exists_etale_kummerAway_algEquiv
    {R : Type u} [CommRing R] [IsNoetherianRing R] (φ : R) (hφ : φ ∈ nonZeroDivisors R)
    (p : Ideal R) [p.IsPrime]
    (hreg : φ ∈ p → IsRegularLocalRing (Localization.AtPrime p) ∧
      IsRegularLocalRing (Localization.AtPrime p ⧸
        Ideal.span {algebraMap R (Localization.AtPrime p) φ}))
    (B : Type u) [CommRing B] [Algebra (Localization.Away φ) B]
    [Module.Finite (Localization.Away φ) B] [Algebra.Etale (Localization.Away φ) B]
    (htame : φ ∈ p → IsRegularLocalRing (StacksDraft.strictHenselizationAtPrime R p) →
      algebraMap R (StacksDraft.strictHenselizationAtPrime R p) φ ≠ 0 →
      letI := (Localization.awayMap
        (algebraMap R (StacksDraft.strictHenselizationAtPrime R p)) φ).toAlgebra
      Stacks.FundamentalGroup.IsTamelyRamifiedInCodimensionOne
        (Scheme.Opens.ι (X := Spec (.of (StacksDraft.strictHenselizationAtPrime R p)))
          (PrimeSpectrum.basicOpen (algebraMap R (StacksDraft.strictHenselizationAtPrime R p) φ)))
        (AffineFieldFactors.coverMap (R := .of (StacksDraft.strictHenselizationAtPrime R p))
          (algebraMap R _ φ) (Localization.Away (algebraMap R
            (StacksDraft.strictHenselizationAtPrime R p) φ) ⊗[Localization.Away φ] B))) :
    ∃ (D : Type u) (_ : CommRing D) (_ : Algebra R D), Algebra.Etale R D ∧
      ∃ q : Ideal D, q.IsPrime ∧ q.comap (algebraMap R D) = p ∧
      ∃ (n : ℕ) (e : Fin n → ℕ), (∀ i, 0 < e i ∧ IsUnit (e i : D)) ∧
      letI := (Localization.awayMap (algebraMap R D) φ).toAlgebra
      Nonempty ((∀ i, Localization.Away (algebraMap D
          (standardTamelyRamifiedAlgebra D (algebraMap R D φ) (e i)) (algebraMap R D φ))) ≃ₐ[D]
        Localization.Away (algebraMap R D φ) ⊗[Localization.Away φ] B) := by
  classical
  let Λ := StacksDraft.strictHenselizationAtPrime R p
  let : Algebra (Localization.Away φ) (Localization.Away (algebraMap R Λ φ)) :=
    (Localization.awayMap (algebraMap R Λ) φ).toAlgebra
  have hmΛ : (maximalIdeal Λ).comap (algebraMap R Λ) = p :=
    StacksDraft.under_maximalIdeal_strictHenselizationAtPrime R p
  obtain ⟨n, e, he, hdec⟩ : ∃ (n : ℕ) (e : Fin n → ℕ), (∀ i, 0 < e i ∧ IsUnit (e i : Λ)) ∧
      Nonempty ((∀ i, Localization.Away (algebraMap Λ
        (standardTamelyRamifiedAlgebra Λ (algebraMap R Λ φ) (e i)) (algebraMap R Λ φ))) ≃ₐ[Λ]
        Localization.Away (algebraMap R Λ φ) ⊗[Localization.Away φ] B) := by
    by_cases hφp : φ ∈ p
    · obtain ⟨hRp, hRpq⟩ := hreg hφp
      let κ := SeparableClosure (ResidueField (Localization.AtPrime p))
      have hΛreg : IsRegularLocalRing Λ :=
        (isRegularLocalRing_iff_of_isHenselization (A := Localization.AtPrime p) κ).mp hRp
      have hφm : algebraMap R Λ φ ∈ maximalIdeal Λ := by rwa [← Ideal.mem_comap, hmΛ]
      have hφ0 : algebraMap R Λ φ ≠ 0 := by
        intro h
        have hreg' : IsSMulRegular Λ φ := Module.Flat.isSMulRegular_of_nonZeroDivisors hφ
        apply one_ne_zero (α := Λ)
        apply hreg'
        change φ • (1 : Λ) = φ • (0 : Λ)
        rw [smul_zero, Algebra.smul_def, h, zero_mul]
      have hI : Ideal.span {algebraMap R (Localization.AtPrime p) φ} ≤
          maximalIdeal (Localization.AtPrime p) :=
        Ideal.span_le.mpr <| Set.singleton_subset_iff.mpr <|
          (IsLocalization.AtPrime.to_map_mem_maximal_iff _ p φ).mpr hφp
      have hq := (isRegularLocalRing_quotient_iff_of_isHenselization
        (A := Localization.AtPrime p) (Ash := Λ) κ _ hI).mp hRpq
      have hmap : (Ideal.span {algebraMap R (Localization.AtPrime p) φ}).map
          (algebraMap (Localization.AtPrime p) Λ) = Ideal.span {algebraMap R Λ φ} := by
        rw [Ideal.map_span, Set.image_singleton, ← IsScalarTower.algebraMap_apply]
      have hq' : IsRegularLocalRing (Λ ⧸ Ideal.span {algebraMap R Λ φ}) :=
        IsRegularLocalRing.of_ringEquiv (Ideal.quotEquivOfEq hmap)
      obtain ⟨n, e, he, σ, hσ⟩ := exists_ringEquiv_pi_of_isRegularLocalRing Λ
        (algebraMap R Λ φ) hφm hφ0 hq'
        (Localization.Away (algebraMap R Λ φ) ⊗[Localization.Away φ] B) (htame hφp hΛreg hφ0)
      exact ⟨n, e, he, ⟨algEquivOfRingEquivKummerAway σ hσ⟩⟩
    · have hu : IsUnit (algebraMap R Λ φ) := by
        by_contra h
        exact hφp (hmΛ ▸ (IsLocalRing.mem_maximalIdeal _).mpr h)
      obtain ⟨n, e, he, σ, hσ⟩ := exists_ringEquiv_pi_of_isUnit Λ (algebraMap R Λ φ) hu
        (Localization.Away (algebraMap R Λ φ) ⊗[Localization.Away φ] B)
      exact ⟨n, e, he, ⟨algEquivOfRingEquivKummerAway σ hσ⟩⟩
  obtain ⟨σ⟩ := hdec
  obtain ⟨D, _, _, hD, q, hq, hqp, hunit, hiso⟩ :=
    exists_etale_algEquiv_of_strictHenselization φ p B e (fun i ↦ (he i).2) σ
  exact ⟨D, _, _, hD, q, hq, hqp, n, e, fun i ↦ ⟨(he i).1, hunit i⟩, hiso⟩

end AlgebraicGeometry.Abhyankar
