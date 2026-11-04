module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.TorsionVanishingBoundTransport
public import StacksFrontier.AlgebraicGeometry.Variety.CompleteLocal.StrictlyHenselian
public import StacksFrontier.RingTheory.Etale.IndEtaleFibres
public import StacksFrontier.RingTheory.Henselian.HenselizationMinimalPrimes
public import StacksFrontier.RingTheory.Henselian.Quotient
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.QuasiFinite

/-!
# Travaux de Gabber XVIII-A, Corollary 1.2, as a statement, and its consequence for fibres

`FractionFieldVanishingBound n` is **Exposé XVIII-A, Corollary 1.2** of Travaux de Gabber for
coefficients killed by `n`: for a strictly henselian Noetherian local domain `B` of dimension
`e ≥ 1` in which `n` is invertible, the étale cohomology of `Spec (Frac B)` with coefficients
killed by `n` vanishes above `2e - 1`. It is not proved here; it is the hypothesis under which
the bound at the non-closed points of the base of Stacks 0DC6 is derived.

This file derives from it the bound for the fibres `κ(P) ⊗_A O` of an ind-étale algebra `O` over
a ring `A`, where `O` is a strictly henselian Noetherian local ring of dimension at most `D ≥ 1`
(the case of interest: `O` a strict henselization of a local ring of `A`). The fibre is the finite
product of the residue fields `κ(Q)` at the primes `Q` of `O` over `P`
(`StacksDraft.nonempty_tensor_residue_algEquiv`), and `κ(Q)` is the fraction field of the
strictly henselian Noetherian local domain `O ⧸ Q`, of dimension at most `D`. When that dimension
is `0`, `O ⧸ Q` is a separably closed field and the bound is `0`; otherwise it is Corollary 1.2.

## Main definitions

* `AlgebraicGeometry.Scheme.FractionFieldVanishingBound`: Exposé XVIII-A, Corollary 1.2.

## Main results

* `StrictlyHenselianLocalRing.quotient`: a quotient of a strictly henselian local ring by a
  proper ideal is strictly henselian.
* `AlgebraicGeometry.Scheme.isTorsionVanishingBound_spec_fractionRing`: the bound `2D - 1` for
  the fraction field of a strictly henselian Noetherian local domain of dimension at most `D`.
* `AlgebraicGeometry.Scheme.isTorsionVanishingBound_spec_tensor_residueField`: the bound
  `2D - 1` for the fibre `κ(P) ⊗_A O`.

## References

* L. Illusie, *Cohomological dimension: first results*, in Travaux de Gabber sur
  l'uniformisation locale et la cohomologie étale des schémas quasi-excellents, Exposé XVIII-A,
  Corollary 1.2, Astérisque 363–364 (2014)
* [Stacks Project, Tag 0DC6](https://stacks.math.columbia.edu/tag/0DC6)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry IsLocalRing
open scoped TensorProduct

universe u

/-- **A quotient of a strictly henselian local ring by a proper ideal is strictly henselian**: it
is henselian (`Stacks.Henselian.henselianLocalRing_quotient`) with the same residue field. -/
theorem StrictlyHenselianLocalRing.quotient {R : Type*} [CommRing R]
    [StrictlyHenselianLocalRing R] {I : Ideal R} (hI : I ≠ ⊤) :
    StrictlyHenselianLocalRing (R ⧸ I) := by
  have : HenselianLocalRing (R ⧸ I) := Stacks.Henselian.henselianLocalRing_quotient hI
  have : IsLocalHom (Ideal.Quotient.mk I) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  let φ := ResidueField.map (Ideal.Quotient.mk I)
  have hφ : Function.Bijective φ := by
    refine ⟨RingHom.injective φ, fun y => ?_⟩
    obtain ⟨z, rfl⟩ := residue_surjective y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨residue R x, ResidueField.map_residue _ x⟩
  have : IsSepClosed (ResidueField (R ⧸ I)) :=
    IsSepClosed.of_ringEquiv (RingEquiv.ofBijective φ hφ).symm
  exact ⟨⟩

namespace AlgebraicGeometry.Scheme

attribute [local instance high]
  Stacks.EtaleCohomology.ConstantTransport.hasExt_sheaf_smallEtaleTopology

/-- **Travaux de Gabber, Exposé XVIII-A, Corollary 1.2**, for coefficients killed by `n`: for a
strictly henselian Noetherian local domain `B` of dimension `e ≥ 1` with `n` invertible in `B`,
the étale cohomology of `Spec (Frac B)` with coefficients killed by `n` vanishes above
`2e - 1`. -/
def FractionFieldVanishingBound (n : ℕ) : Prop :=
  ∀ (B : Type u) [CommRing B] [IsDomain B] [IsNoetherianRing B] [StrictlyHenselianLocalRing B]
    (e : ℕ), ringKrullDim B = e → 0 < e → IsUnit (n : B) →
      IsTorsionVanishingBound (Spec (.of (FractionRing B))) n ((2 * e - 1 : ℕ) : WithBot ℕ∞)

/-- An element of `WithBot ℕ∞` which is nonnegative and bounded by a natural number is a natural
number. -/
private lemma exists_natCast_eq_of_nonneg_of_le {a : WithBot ℕ∞} {N : ℕ} (h0 : 0 ≤ a)
    (hN : a ≤ N) : ∃ m : ℕ, a = m := by
  induction a using WithBot.recBotCoe with
  | bot => exact absurd h0 (by simp)
  | coe b =>
    induction b using ENat.recTopCoe with
    | top =>
      exact absurd hN (by
        rw [← WithBot.coe_natCast, WithBot.coe_le_coe]
        simp)
    | coe m => exact ⟨m, by simp⟩

/-- **The fraction field of a strictly henselian Noetherian local domain of dimension at most
`D ≥ 1`**, given Corollary 1.2: its étale cohomology with coefficients killed by `n > 0`
(`n` invertible in `B`) vanishes above `2D - 1`. In dimension `0` the domain is a field, equal to
its residue field, hence separably closed, and the bound is `0`. -/
theorem isTorsionVanishingBound_spec_fractionRing {n : ℕ} (hn : 0 < n)
    (h : FractionFieldVanishingBound.{u} n) (B : Type u) [CommRing B] [IsDomain B]
    [IsNoetherianRing B] [StrictlyHenselianLocalRing B] {D : ℕ} (hD : 1 ≤ D)
    (hdim : ringKrullDim B ≤ D) (hnB : IsUnit (n : B)) :
    IsTorsionVanishingBound (Spec (.of (FractionRing B))) n ((2 * D - 1 : ℕ) : WithBot ℕ∞) := by
  obtain ⟨e, he⟩ := exists_natCast_eq_of_nonneg_of_le ringKrullDim_nonneg_of_nontrivial hdim
  have heD : e ≤ D := by
    rw [he] at hdim
    exact_mod_cast hdim
  rcases Nat.eq_zero_or_pos e with rfl | hpos
  · have : Ring.KrullDimLE 0 B := Ring.krullDimLE_iff.2 (by rw [he])
    have hfield : IsField B := Ring.KrullDimLE.isField_of_isDomain
    have hm : maximalIdeal B = ⊥ := isField_iff_maximalIdeal_eq.1 hfield
    have hres : Function.Bijective (IsLocalRing.residue B) := by
      refine ⟨?_, IsLocalRing.residue_surjective⟩
      rw [injective_iff_map_eq_zero]
      intro x hx
      have hx' : x ∈ RingHom.ker (IsLocalRing.residue B) := hx
      rwa [IsLocalRing.ker_residue, hm, Ideal.mem_bot] at hx'
    let e₁ : B ≃ₐ[B] FractionRing B := IsLocalization.atUnits B (nonZeroDivisors B)
      (fun y hy => (IsUnit.mem_submonoid_iff y).2
        (isUnit_iff_exists_inv.2 (hfield.mul_inv_cancel (nonZeroDivisors.ne_zero hy))))
    have : IsSepClosed (FractionRing B) :=
      IsSepClosed.of_ringEquiv (M := ResidueField B)
        (e₁.symm.toRingEquiv.trans (RingEquiv.ofBijective _ hres))
    exact (isTorsionVanishingBound_spec_of_isSepClosed (FractionRing B) hn).mono
      (by exact_mod_cast Nat.zero_le _)
  · exact (h B e he hpos hnB).mono (by exact_mod_cast (by omega : 2 * e - 1 ≤ 2 * D - 1))

/-- **The fibres of a strictly henselian Noetherian local ring, ind-étale over a ring**, given
Corollary 1.2. Let `O` be a strictly henselian Noetherian local ring of dimension at most
`D ≥ 1`, ind-étale over a ring `A`, with `n > 0` invertible in `O`, and let `P` be a prime of `A`.
Then the étale cohomology of `Spec (κ(P) ⊗_A O)` with coefficients killed by `n` vanishes above
`2D - 1`.

The fibre is the finite product of the residue fields `κ(Q)` at the primes `Q` of `O` over `P`,
each the fraction field of the strictly henselian Noetherian local domain `O ⧸ Q`. -/
theorem isTorsionVanishingBound_spec_tensor_residueField {n : ℕ} (hn : 0 < n)
    (h : FractionFieldVanishingBound.{u} n) {A : Type u} [CommRing A] (P : Ideal A) [P.IsPrime]
    (O : Type u) [CommRing O] [IsNoetherianRing O] [StrictlyHenselianLocalRing O] [Algebra A O]
    (hO : StacksDraft.IndEtale A O) {D : ℕ} (hD : 1 ≤ D) (hdim : ringKrullDim O ≤ D)
    (hnO : IsUnit (n : O)) :
    IsTorsionVanishingBound (Spec (.of (P.ResidueField ⊗[A] O))) n
      ((2 * D - 1 : ℕ) : WithBot ℕ∞) := by
  classical
  obtain ⟨e⟩ := StacksDraft.nonempty_tensor_residue_algEquiv hO P
  let e' : (P.ResidueField ⊗[A] O) ≃+* ∀ q : P.primesOver O, (q : Ideal O).ResidueField :=
    (Algebra.TensorProduct.comm A P.ResidueField O).toRingEquiv.trans e.toRingEquiv
  refine IsTorsionVanishingBound.of_iso (Scheme.Spec.mapIso e'.symm.toCommRingCatIso.op) ?_
  -- finitely many primes over `P`: the fibre is Artinian
  have : IsNoetherianRing (P.Fiber O) := P.isNoetherianRing_fiber O
  have : Ring.KrullDimLE 0 (P.Fiber O) := (StacksDraft.fiber_reduced_and_krullDimLE_zero hO P).2
  have : IsArtinianRing (P.Fiber O) := IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
  have : Finite (P.primesOver O) :=
    Finite.of_equiv _ (PrimeSpectrum.primesOverOrderIsoFiber A O P).toEquiv.symm
  refine isTorsionVanishingBound_spec_pi (fun q : P.primesOver O => (q : Ideal O).ResidueField)
    fun q => ?_
  -- `κ(Q)` is the fraction field of `O ⧸ Q`
  have hQ : (q : Ideal O) ≠ ⊤ := Ideal.IsPrime.ne_top inferInstance
  have : StrictlyHenselianLocalRing (O ⧸ (q : Ideal O)) := StrictlyHenselianLocalRing.quotient hQ
  let eq : (q : Ideal O).ResidueField ≃ₐ[O ⧸ (q : Ideal O)] FractionRing (O ⧸ (q : Ideal O)) :=
    IsLocalization.algEquiv (nonZeroDivisors (O ⧸ (q : Ideal O))) _ _
  refine IsTorsionVanishingBound.of_iso
    (Scheme.Spec.mapIso eq.toRingEquiv.symm.toCommRingCatIso.op) ?_
  refine isTorsionVanishingBound_spec_fractionRing hn h (O ⧸ (q : Ideal O)) hD
    ((ringKrullDim_quotient_le _).trans hdim) ?_
  simpa only [map_natCast] using hnO.map (Ideal.Quotient.mk (q : Ideal O))

end AlgebraicGeometry.Scheme

end
