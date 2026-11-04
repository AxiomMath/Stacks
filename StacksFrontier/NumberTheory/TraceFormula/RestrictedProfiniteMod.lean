module

public import Mathlib.Topology.Instances.ZMod
public import StacksFrontier.NumberTheory.TraceFormula.CommutativeExampleInverse
public import StacksFrontier.NumberTheory.TraceFormula.ProfiniteIntegersProcyclic

/-!
# Reduction of `Ẑ^(q)` modulo integers prime to `q`

For `N ≥ 1` prime to `q`, the ring `Ẑ^(q) = ∏_{ℓ ∤ q} ℤ_ℓ` maps onto `ℤ/N` through the Chinese
remainder theorem. These reductions are compatible, continuous for the discrete topology on
`ℤ/N`, and jointly injective along any family of moduli which every prime power `ℓ^e` (`ℓ ∤ q`)
divides. The reduction of `q^{-d}` (`Stacks.TraceFormula.inverseCharacter`) modulo `N` is
`(q⁻¹ mod N)^(d mod f)` whenever `q^f ≡ 1 (mod N)`.

## Main definitions

* `Stacks.TraceFormula.restrictedMod q N`: the reduction `Ẑ^(q) → ℤ/N`.

## Main results

* `Stacks.TraceFormula.castHom_restrictedMod_of_dvd`: compatibility.
* `Stacks.TraceFormula.continuous_restrictedMod`: continuity.
* `Stacks.TraceFormula.eq_of_forall_restrictedMod_eq`: joint injectivity.
* `Stacks.TraceFormula.restrictedMod_inverseCharacter`: the reduction of `q^{-d}`.
-/

@[expose] public noncomputable section

namespace Stacks.TraceFormula

open Finset

section Mod

variable (q N : ℕ) (hN : N ≠ 0) (hcop : N.Coprime q)

include hcop in
/-- If `N` is prime to `q`, no prime factor of `N` divides `q`. -/
theorem not_dvd_of_mem_primeFactors {p : ℕ} (hp : p ∈ N.primeFactors) : ¬ p ∣ q := fun h ↦
  (Nat.prime_of_mem_primeFactors hp).one_lt.ne'
    (Nat.dvd_one.mp (hcop.gcd_eq_one ▸ Nat.dvd_gcd (Nat.dvd_of_mem_primeFactors hp) h))

/-- A prime factor of `N`, prime to `q`, as an index of `Ẑ^(q)`. -/
def coprimeFactorIndex (p : N.primeFactors) : CoprimePrimes q :=
  ⟨p, Nat.prime_of_mem_primeFactors p.2, not_dvd_of_mem_primeFactors q N hcop p.2⟩

/-- **The reduction `Ẑ^(q) → ℤ/N`**, through the Chinese remainder theorem. -/
def restrictedMod : RestrictedProfiniteIntegers q →+* ZMod N :=
  (ZMod.equivPi N hN).symm.toRingHom.comp (Pi.ringHom fun p : N.primeFactors ↦
    (PadicInt.toZModPow (p := (coprimeFactorIndex q N hcop p).1) (N.factorization p)).comp
      (Pi.evalRingHom _ (coprimeFactorIndex q N hcop p)))

/-- The components of the reduction are the reductions modulo `p ^ v_p(N)`. -/
theorem castHom_restrictedMod (z : RestrictedProfiniteIntegers q) (p : N.primeFactors) :
    ZMod.castHom (Nat.ordProj_dvd N p) (ZMod ((p : ℕ) ^ N.factorization p))
        (restrictedMod q N hN hcop z) =
      PadicInt.toZModPow (N.factorization p) (z (coprimeFactorIndex q N hcop p)) := by
  rw [← equivPi_apply_eq_castHom N hN, restrictedMod, RingHom.comp_apply,
    RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]
  rfl

/-- Reducing the reduction modulo `N` further to `p ^ e`, `e ≤ v_p(N)`, gives `z mod p ^ e`. -/
private theorem castHom_restrictedMod_of_le (z : RestrictedProfiniteIntegers q) (p : N.primeFactors)
    {e : ℕ} (hle : e ≤ N.factorization p) (h : (p : ℕ) ^ e ∣ N) :
    ZMod.castHom h (ZMod ((p : ℕ) ^ e)) (restrictedMod q N hN hcop z) =
      PadicInt.toZModPow e (z (coprimeFactorIndex q N hcop p)) := by
  rw [← ZMod.castHom_comp (pow_dvd_pow _ hle) (Nat.ordProj_dvd N p), RingHom.comp_apply,
    castHom_restrictedMod]
  exact PadicInt.cast_toZModPow (p := (coprimeFactorIndex q N hcop p).1) _ _ hle _

/-- **The reductions are compatible**: `(z mod N) mod M = z mod M` for `M ∣ N`. -/
theorem castHom_restrictedMod_of_dvd {M : ℕ} (hM : M ≠ 0) (hMN : M ∣ N)
    (z : RestrictedProfiniteIntegers q) :
    ZMod.castHom hMN (ZMod M) (restrictedMod q N hN hcop z) =
      restrictedMod q M hM (hcop.coprime_dvd_left hMN) z := by
  refine eq_of_castHom_eq M hM fun p ↦ ?_
  rw [castHom_restrictedMod q M hM _ z p, ← RingHom.comp_apply, ZMod.castHom_comp]
  exact castHom_restrictedMod_of_le q N hN hcop z ⟨p, Nat.primeFactors_mono hMN hN p.2⟩
    ((Nat.factorization_le_iff_dvd hM hN).2 hMN p) _

/-- **The reduction is continuous** (for the discrete topology on `ℤ/N`). -/
theorem continuous_restrictedMod : Continuous (restrictedMod q N hN hcop) := by
  rw [continuous_discrete_rng]
  intro a
  rw [isOpen_iff_forall_mem_open]
  intro z hz
  refine ⟨{w | ∀ p : N.primeFactors,
      PadicInt.toZModPow (N.factorization p) (w (coprimeFactorIndex q N hcop p)) =
        PadicInt.toZModPow (N.factorization p) (z (coprimeFactorIndex q N hcop p))}, ?_, ?_,
    fun p ↦ rfl⟩
  · intro w hw
    show restrictedMod q N hN hcop w = a
    rw [← show restrictedMod q N hN hcop z = a from hz]
    exact eq_of_castHom_eq N hN fun p ↦ by
      rw [castHom_restrictedMod, castHom_restrictedMod, hw p]
  · rw [Set.setOf_forall]
    refine isOpen_iInter_of_finite fun p ↦ ?_
    show IsOpen ((fun w : RestrictedProfiniteIntegers q ↦ w (coprimeFactorIndex q N hcop p)) ⁻¹'
      {y | PadicInt.toZModPow (N.factorization p) y =
        PadicInt.toZModPow (N.factorization p) (z (coprimeFactorIndex q N hcop p))})
    exact (isOpen_fiber_toZModPow (coprimeFactorIndex q N hcop p).1 (N.factorization p) _).preimage
      (continuous_apply (coprimeFactorIndex q N hcop p))

end Mod

/-- **Joint injectivity of the reductions.** Let `S` be a family of moduli prime to `q` such that
every prime power `ℓ^e`, `ℓ ∤ q`, divides some member. Elements of `Ẑ^(q)` with the same
reductions modulo every member of `S` are equal. -/
theorem eq_of_forall_restrictedMod_eq (q : ℕ) (S : ℕ → ℕ) (hS0 : ∀ m, S m ≠ 0)
    (hScop : ∀ m, (S m).Coprime q) (hcof : ∀ (ℓ : CoprimePrimes q) (e : ℕ), ∃ m, ℓ.1 ^ e ∣ S m)
    {z w : RestrictedProfiniteIntegers q}
    (h : ∀ m, restrictedMod q (S m) (hS0 m) (hScop m) z =
      restrictedMod q (S m) (hS0 m) (hScop m) w) :
    z = w := by
  funext ℓ
  refine PadicInt.ext_of_toZModPow.mp fun e ↦ ?_
  rcases Nat.eq_zero_or_pos e with rfl | he
  · have : Subsingleton (ZMod (ℓ.1 ^ 0)) := by rw [pow_zero]; infer_instance
    exact Subsingleton.elim _ _
  obtain ⟨m, hm⟩ := hcof ℓ e
  have hℓ : ℓ.1 ∈ (S m).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨ℓ.2.1, (dvd_pow_self _ he.ne').trans hm, hS0 m⟩
  have hle : e ≤ (S m).factorization ℓ.1 :=
    (ℓ.2.1.pow_dvd_iff_le_factorization (hS0 m)).mp hm
  have h1 := castHom_restrictedMod_of_le q (S m) (hS0 m) (hScop m) z ⟨ℓ.1, hℓ⟩ hle hm
  have h2 := castHom_restrictedMod_of_le q (S m) (hS0 m) (hScop m) w ⟨ℓ.1, hℓ⟩ hle hm
  rw [h m] at h1
  exact h1.symm.trans h2

section Inverse

variable (q : ℕ) [NeZero q]

omit [NeZero q] in
/-- **The reduction of `q^{-d}` modulo `N`.** If `q^f ≡ 1 (mod N)`, the reduction of
`q^{-d} ∈ Ẑ^(q)` is `(q⁻¹ mod N)^(d mod f)`. -/
theorem restrictedMod_inverseCharacter (N : ℕ) (hN : N ≠ 0) (hcop : N.Coprime q) {f : ℕ}
    (hf0 : f ≠ 0) (hf : (q : ZMod N) ^ f = 1) (d : Multiplicative ProfiniteIntegers) :
    restrictedMod q N hN hcop ((inverseCharacter q d : (RestrictedProfiniteIntegers q)ˣ) :
        RestrictedProfiniteIntegers q) =
      restrictedMod q N hN hcop (qInv q : RestrictedProfiniteIntegers q) ^
        (restrictedMod 1 f hf0 (Nat.coprime_one_right f) (Multiplicative.toAdd d)).val := by
  set c := restrictedMod q N hN hcop (qInv q : RestrictedProfiniteIntegers q)
  have hc : c ^ f = 1 := by
    have h1 : (q : ZMod N) * c = 1 := by
      rw [← map_natCast (restrictedMod q N hN hcop), ← map_mul, natCast_mul_qInv, map_one]
    calc c ^ f = ((q : ZMod N) * c) ^ f := by rw [mul_pow, hf, one_mul]
      _ = 1 := by rw [h1, one_pow]
  let g₁ : ProfiniteIntegers → ZMod N := fun x ↦ restrictedMod q N hN hcop
    ((inverseCharacter q (Multiplicative.ofAdd x) : (RestrictedProfiniteIntegers q)ˣ) :
      RestrictedProfiniteIntegers q)
  let g₂ : ProfiniteIntegers → ZMod N := fun x ↦
    c ^ (restrictedMod 1 f hf0 (Nat.coprime_one_right f) x).val
  have hg₁ : Continuous g₁ :=
    (continuous_restrictedMod q N hN hcop).comp (Units.continuous_val.comp
      ((continuous_profinitePowers (qInv q)).comp continuous_ofAdd))
  have hg₂ : Continuous g₂ :=
    (continuous_of_discreteTopology (f := fun a : ZMod f ↦ c ^ a.val)).comp
      (continuous_restrictedMod 1 f hf0 (Nat.coprime_one_right f))
  have heq : g₁ = g₂ := by
    refine (denseRange_natCast_restrictedProfiniteIntegers 1).equalizer hg₁ hg₂ ?_
    funext n
    simp only [Function.comp_apply, g₁, g₂, map_natCast, ZMod.val_natCast]
    have : (Multiplicative.ofAdd (n : ProfiniteIntegers)) = (Multiplicative.ofAdd 1) ^ n := by
      rw [← ofAdd_nsmul, nsmul_one]
    rw [this, map_pow, inverseCharacter_ofAdd_one, Units.val_pow_eq_pow_val, map_pow]
    exact pow_eq_pow_mod n hc
  exact congrFun heq (Multiplicative.toAdd d)

end Inverse

end Stacks.TraceFormula

end
