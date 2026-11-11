module

public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.MittagLeffler.MvPowerSeries
public import StacksFrontier.RingTheory.Length.FlatLocalHom
public import StacksFrontier.RingTheory.Length.RingEquiv
public import StacksFrontier.RingTheory.MvPowerSeries.MinimalPrimes

/-!
# Multiplicities along `A → A[[t₁, …, t_r]]`

Let `A` be a Noetherian ring and `A' = A[[t₁, …, t_r]]`. The morphism `Spec A' → Spec A` induces
a bijection on irreducible components (`MvPowerSeries.bijOn_map_C_minimalPrimes`) which preserves
multiplicities: the local rings `A_𝔭` and `A'_{𝔭 A'}` have the same length. This is the
"easy proof" omitted in the discussion preceding Stacks Definition 0DRC.

The map `A_𝔭 → A'_{𝔭 A'}` is a flat local homomorphism whose closed fibre is the residue field,
so the length identity of Stacks 02M1 gives equality.

## Main results

* `MvPowerSeries.map_C_comap_C_of_mem_minimalPrimes`: every minimal prime `𝔮` of `A'` is
  `(𝔮 ∩ A) A'`, with `𝔮 ∩ A` minimal.
* `MvPowerSeries.length_localization_map_C`: `length A'_{𝔭 A'} = length A_𝔭`.
* `MvPowerSeries.minimalPrimesEquivOfRingEquiv`: for `e : B ≃+* A[[t₁, …, t_r]]` and
  `φ : A → A[[t]] ≅ B`, the bijection `𝔭 ↦ φ(𝔭) B` from minimal primes of `A` to those of `B`.
* `MvPowerSeries.length_localization_minimalPrimesEquivOfRingEquiv`: it preserves the lengths of
  the localizations.
-/

@[expose] public noncomputable section

open IsLocalRing

universe u v

namespace MvPowerSeries

variable {A : Type u} [CommRing A] {r : ℕ} [IsNoetherianRing A]

/-- **Every minimal prime of the power series ring is extended from a minimal prime.** For a
minimal prime `𝔮` of `A[[t₁, …, t_r]]`, the contraction `𝔮 ∩ A` is a minimal prime of `A` and
`𝔮 = (𝔮 ∩ A) A[[t]]`. -/
theorem map_C_comap_C_of_mem_minimalPrimes {Q : Ideal (MvPowerSeries (Fin r) A)}
    (hQ : Q ∈ minimalPrimes (MvPowerSeries (Fin r) A)) :
    Q.comap C ∈ minimalPrimes A ∧ (Q.comap C).map C = Q := by
  obtain ⟨P, hP, rfl⟩ := exists_map_C_eq_of_mem_minimalPrimes hQ
  rw [comap_C_map_C]
  exact ⟨hP, rfl⟩

/-- **Lengths of localizations along `A → A[[t₁, …, t_r]]`.** For a prime `𝔭` of a Noetherian
ring `A`, the local rings `A_𝔭` and `A[[t]]_{𝔭 A[[t]]}` have the same length: the localized map
is flat and local with closed fibre the residue field (Stacks 02M1). -/
theorem length_localization_map_C (P : Ideal A) [P.IsPrime] :
    letI := isPrime_map_C (σ := Fin r) (p := P) inferInstance
    Module.length (Localization.AtPrime (P.map (C : A →+* MvPowerSeries (Fin r) A)))
        (Localization.AtPrime (P.map (C : A →+* MvPowerSeries (Fin r) A))) =
      Module.length (Localization.AtPrime P) (Localization.AtPrime P) := by
  have := isPrime_map_C (σ := Fin r) (p := P) inferInstance
  set Q := P.map (C : A →+* MvPowerSeries (Fin r) A)
  set B := Localization.AtPrime Q
  set Rp := Localization.AtPrime P
  have hPQ : P = Q.comap C := (comap_C_map_C P).symm
  let f : Rp →+* B := Localization.localRingHom P Q C hPQ
  let : Algebra Rp B := f.toAlgebra
  have : IsLocalHom (algebraMap Rp B) :=
    Localization.isLocalHom_localRingHom P Q C hPQ
  have hC : (C : A →+* MvPowerSeries (Fin r) A).Flat :=
    RingHom.flat_algebraMap_iff.mpr (Module.flat_and_mittagLeffler_mvPowerSeries A r).1
  have : Module.Flat Rp B := RingHom.Flat.localRingHom hC Q P hPQ
  have hext : extendedMaximalIdeal Rp B = maximalIdeal B := by
    rw [extendedMaximalIdeal, ← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map,
      ← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map]
    congr 1
    ext a
    exact Localization.localRingHom_to_map P Q C hPQ a
  have hfactor : Module.length B (B ⧸ extendedMaximalIdeal Rp B) = 1 := by
    rw [hext]
    have hsurj : Function.Surjective (algebraMap B (B ⧸ maximalIdeal B)) := by
      rw [Ideal.Quotient.algebraMap_eq]
      exact Ideal.Quotient.mk_surjective
    let := Ideal.Quotient.field (maximalIdeal B)
    have : IsSimpleModule B (B ⧸ maximalIdeal B) :=
      (isSimpleModule_iff_isSimpleModule_of_algebraMap_surjective hsurj).2 inferInstance
    exact Module.length_eq_one B _
  have key := length_baseChange_eq_length_mul_length_quotient Rp B Rp
  rw [(TensorProduct.AlgebraTensorModule.rid Rp B B).length_eq, hfactor, mul_one] at key
  exact key.symm

/-! ### Transport along an isomorphism `B ≅ A[[t₁, …, t_r]]` -/

variable {B : Type v} [CommRing B] (e : B ≃+* MvPowerSeries (Fin r) A)

/-- The ring map `A → A[[t₁, …, t_r]] ≅ B` attached to an isomorphism `e : B ≅ A[[t]]`. -/
abbrev ofRingEquivC : A →+* B :=
  (e.symm : MvPowerSeries (Fin r) A →+* B).comp C

omit [IsNoetherianRing A] in
/-- Extension along `A → A[[t]] ≅ B` is the pullback along `e` of extension along `C`. -/
theorem map_ofRingEquivC (I : Ideal A) :
    I.map (ofRingEquivC e) = (I.map C).comap (e : B →+* MvPowerSeries (Fin r) A) := by
  rw [← Ideal.map_map]
  exact Ideal.map_symm e

omit [IsNoetherianRing A] in
/-- Contraction along `A → A[[t]] ≅ B` is contraction along `C` of the pushforward along `e`. -/
theorem comap_ofRingEquivC (J : Ideal B) :
    J.comap (ofRingEquivC e) = (J.comap (e.symm : MvPowerSeries (Fin r) A →+* B)).comap C := by
  rw [Ideal.comap_comap]

omit [IsNoetherianRing A] in
/-- The pullback of a minimal prime of `B` along `e.symm : A[[t]] → B` is a minimal prime. -/
theorem comap_symm_mem_minimalPrimes {Q : Ideal B} (hQ : Q ∈ minimalPrimes B) :
    Q.comap (e.symm : MvPowerSeries (Fin r) A →+* B) ∈ minimalPrimes (MvPowerSeries (Fin r) A) :=
  Ideal.comap_mem_minimalPrimes_of_ringEquiv e.symm hQ

/-- **Minimal primes along `A → A[[t₁, …, t_r]] ≅ B`.** The extension `𝔭 ↦ φ(𝔭) B` is a
bijection from the minimal primes of `A` onto those of `B`, with inverse the contraction. -/
def minimalPrimesEquivOfRingEquiv : minimalPrimes A ≃ minimalPrimes B where
  toFun P := ⟨P.1.map (ofRingEquivC e), by
    rw [map_ofRingEquivC]
    exact Ideal.comap_mem_minimalPrimes_of_ringEquiv e (map_C_mem_minimalPrimes P.2)⟩
  invFun Q := ⟨Q.1.comap (ofRingEquivC e), by
    rw [comap_ofRingEquivC]
    exact (map_C_comap_C_of_mem_minimalPrimes (comap_symm_mem_minimalPrimes e Q.2)).1⟩
  left_inv P := by
    ext1
    change (P.1.map (ofRingEquivC e)).comap (ofRingEquivC e) = P.1
    rw [comap_ofRingEquivC, map_ofRingEquivC]
    exact (congrArg (Ideal.comap C) (Ideal.comap_comap_ringEquiv_symm e _)).trans
      (comap_C_map_C _)
  right_inv Q := by
    ext1
    change (Q.1.comap (ofRingEquivC e)).map (ofRingEquivC e) = Q.1
    rw [map_ofRingEquivC, comap_ofRingEquivC,
      (map_C_comap_C_of_mem_minimalPrimes (comap_symm_mem_minimalPrimes e Q.2)).2]
    exact Ideal.comap_comap_ringEquiv_symm e.symm Q.1

theorem coe_minimalPrimesEquivOfRingEquiv (P : minimalPrimes A) :
    (minimalPrimesEquivOfRingEquiv e P : Ideal B) = P.1.map (ofRingEquivC e) :=
  rfl

theorem coe_minimalPrimesEquivOfRingEquiv_symm (Q : minimalPrimes B) :
    ((minimalPrimesEquivOfRingEquiv e).symm Q : Ideal A) = Q.1.comap (ofRingEquivC e) :=
  rfl

/-- Localizations at primes matched by a ring isomorphism have the same length. -/
theorem length_localization_eq_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (g : R ≃+* S) (J : Ideal R) [J.IsPrime] (K : Ideal S) [K.IsPrime]
    (h : J = K.comap (g : R →+* S)) :
    Module.length (Localization.AtPrime J) (Localization.AtPrime J) =
      Module.length (Localization.AtPrime K) (Localization.AtPrime K) := by
  subst h
  exact Module.length_eq_of_ringEquiv (IsLocalization.ringEquivOfRingEquiv
    (M := (K.comap (g : R →+* S)).primeCompl) (T := K.primeCompl) _ _ g
    (g.map_primeCompl_comap_eq K))

/-- **Multiplicities along `A → A[[t₁, …, t_r]] ≅ B`.** A minimal prime `𝔭` of `A` and the
corresponding minimal prime `φ(𝔭) B` of `B` have localizations of the same length: the
irreducible components of `Spec A` and `Spec B` they cut out have the same multiplicity. This is
the fact the source invokes, with its proof omitted, to make Stacks Definition 0DRC independent of
the versal ring. -/
@[stacks 0DRC "Spec A[[t₁,…,t_r]] → Spec A induces a bijection on irreducible components \
preserving multiplicities, which makes the multiplicity independent of the versal ring"]
theorem length_localization_minimalPrimesEquivOfRingEquiv (P : minimalPrimes A) :
    letI : P.1.IsPrime := P.2.1.1
    letI : (minimalPrimesEquivOfRingEquiv e P).1.IsPrime :=
      (minimalPrimesEquivOfRingEquiv e P).2.1.1
    Module.length (Localization.AtPrime (minimalPrimesEquivOfRingEquiv e P).1)
        (Localization.AtPrime (minimalPrimesEquivOfRingEquiv e P).1) =
      Module.length (Localization.AtPrime P.1) (Localization.AtPrime P.1) := by
  have : P.1.IsPrime := P.2.1.1
  have := isPrime_map_C (σ := Fin r) P.2.1.1
  have : (minimalPrimesEquivOfRingEquiv e P).1.IsPrime :=
    (minimalPrimesEquivOfRingEquiv e P).2.1.1
  rw [← length_localization_map_C (r := r) P.1]
  have hcomap : (minimalPrimesEquivOfRingEquiv e P).1 =
      (P.1.map C).comap (e : B →+* MvPowerSeries (Fin r) A) := map_ofRingEquivC e P.1
  exact length_localization_eq_of_ringEquiv e _ _ hcomap

end MvPowerSeries
