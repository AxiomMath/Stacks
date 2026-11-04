module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.FieldTheory.Finite.Basic
public import StacksFrontier.NumberTheory.TraceFormula.ProfiniteIntegersProcyclic

/-!
# Profinite powers of a unit of `Ẑ^{(q)}`

For a unit `c` of `Ẑ^{(q)} = ∏_{ℓ ∤ q} ℤ_ℓ` there is a continuous homomorphism
`z ↦ c^z : Ẑ → (Ẑ^{(q)})^×` with `c^1 = c`. In the `ℓ`-th coordinate and modulo `ℓ^k`, `c^z` is
`c̄^{z mod φ(ℓ^k)}`, which only depends on the reduction of `z` modulo `φ(ℓ^k)`, since
`c̄^{φ(ℓ^k)} = 1` in `(ℤ/ℓ^k)^×`; these residues are compatible in `k` and assemble to an element
of `ℤ_ℓ` by `PadicInt.lift`.

## Main definitions

* `Stacks.TraceFormula.profiniteMod`: the reduction `Ẑ → ℤ/N`.
* `Stacks.TraceFormula.profinitePowers`: `z ↦ c^z`.

## Main results

* `Stacks.TraceFormula.profinitePowers_ofAdd_one`: `c^1 = c`.
* `Stacks.TraceFormula.continuous_profinitePowers`: continuity.

## References

* [Stacks Project, Tag 03VQ](https://stacks.math.columbia.edu/tag/03VQ)
-/

@[expose] public noncomputable section

namespace Stacks.TraceFormula

open Finset

/-! ### Reduction modulo `N` -/

section Mod

variable (N : ℕ) (hN : N ≠ 0)

/-- A prime factor of `N`, as an index of `Ẑ = ∏_ℓ ℤ_ℓ`. -/
public def primeFactorIndex (p : N.primeFactors) : CoprimePrimes 1 :=
  ⟨p, Nat.prime_of_mem_primeFactors p.2, fun h => (Nat.prime_of_mem_primeFactors p.2).one_lt.ne'
    (Nat.dvd_one.1 h)⟩

/-- **The reduction `Ẑ → ℤ/N`**, through the Chinese remainder theorem. -/
public def profiniteMod : ProfiniteIntegers →+* ZMod N :=
  (ZMod.equivPi N hN).symm.toRingHom.comp (Pi.ringHom fun p : N.primeFactors =>
    (PadicInt.toZModPow (p := (primeFactorIndex N p).1) (N.factorization p)).comp
      (Pi.evalRingHom _ (primeFactorIndex N p)))

/-- The components of the Chinese remainder theorem are the reductions. -/
public theorem equivPi_apply_eq_castHom (x : ZMod N) (p : N.primeFactors) :
    ZMod.equivPi N hN x p =
      ZMod.castHom (Nat.ordProj_dvd N p) (ZMod ((p : ℕ) ^ N.factorization p)) x :=
  RingHom.congr_fun
    (Subsingleton.elim ((Pi.evalRingHom _ p).comp (ZMod.equivPi N hN).toRingHom) _) x

/-- The reduction of `z` modulo `N` is characterized by its reductions modulo the prime powers
`p ^ v_p(N)`. -/
public theorem castHom_profiniteMod (z : ProfiniteIntegers) (p : N.primeFactors) :
    ZMod.castHom (Nat.ordProj_dvd N p) (ZMod ((p : ℕ) ^ N.factorization p)) (profiniteMod N hN z) =
      PadicInt.toZModPow (N.factorization p) (z (primeFactorIndex N p)) := by
  rw [← equivPi_apply_eq_castHom N hN, profiniteMod, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]
  rfl

include hN in
/-- Two elements of `ℤ/N` with the same reductions modulo the `p ^ v_p(N)` are equal. -/
public theorem eq_of_castHom_eq {x y : ZMod N}
    (h : ∀ p : N.primeFactors,
      ZMod.castHom (Nat.ordProj_dvd N p) (ZMod ((p : ℕ) ^ N.factorization p)) x =
        ZMod.castHom (Nat.ordProj_dvd N p) (ZMod ((p : ℕ) ^ N.factorization p)) y) : x = y := by
  apply (ZMod.equivPi N hN).injective
  funext p
  rw [equivPi_apply_eq_castHom, equivPi_apply_eq_castHom, h p]

/-- `z mod N` only depends on the components of `z` at the primes dividing `N`, modulo
`p ^ v_p(N)`. -/
public theorem profiniteMod_eq_of_forall {z w : ProfiniteIntegers}
    (h : ∀ p : N.primeFactors, PadicInt.toZModPow (N.factorization p) (w (primeFactorIndex N p)) =
      PadicInt.toZModPow (N.factorization p) (z (primeFactorIndex N p))) :
    profiniteMod N hN w = profiniteMod N hN z :=
  eq_of_castHom_eq N hN fun p => by rw [castHom_profiniteMod, castHom_profiniteMod, h p]

/-- **The reductions are compatible**: `(z mod N) mod M = z mod M` for `M ∣ N`. -/
public theorem castHom_profiniteMod_of_dvd {M : ℕ} (hM : M ≠ 0) (hMN : M ∣ N)
    (z : ProfiniteIntegers) :
    ZMod.castHom hMN (ZMod M) (profiniteMod N hN z) = profiniteMod M hM z := by
  refine eq_of_castHom_eq M hM fun p => ?_
  have hpN : (p : ℕ) ∈ N.primeFactors := Nat.primeFactors_mono hMN hN p.2
  have hle : M.factorization p ≤ N.factorization p :=
    (Nat.factorization_le_iff_dvd hM hN).2 hMN p
  have h1 : (p : ℕ) ^ M.factorization p ∣ (p : ℕ) ^ N.factorization p := pow_dvd_pow _ hle
  rw [castHom_profiniteMod M hM z p, ← RingHom.comp_apply, ZMod.castHom_comp,
    ← ZMod.castHom_comp h1 (Nat.ordProj_dvd N p), RingHom.comp_apply,
    castHom_profiniteMod N hN z ⟨p, hpN⟩]
  exact PadicInt.cast_toZModPow (p := (primeFactorIndex N ⟨p, hpN⟩).1) _ _ hle _

/-- The set of `w` agreeing with `z` modulo `p ^ v_p(N)` at every `p ∣ N` is open. -/
public theorem isOpen_profiniteMod_fiber (z : ProfiniteIntegers) :
    IsOpen {w : ProfiniteIntegers | ∀ p : N.primeFactors,
      PadicInt.toZModPow (N.factorization p) (w (primeFactorIndex N p)) =
        PadicInt.toZModPow (N.factorization p) (z (primeFactorIndex N p))} := by
  rw [Set.setOf_forall]
  refine isOpen_iInter_of_finite fun p => ?_
  change IsOpen ((fun w : ProfiniteIntegers => w (primeFactorIndex N p)) ⁻¹'
    {y : ℤ_[(primeFactorIndex N p).1] | PadicInt.toZModPow (N.factorization p) y =
      PadicInt.toZModPow (N.factorization p) (z (primeFactorIndex N p))})
  exact (isOpen_fiber_toZModPow (primeFactorIndex N p).1 (N.factorization p) _).preimage
    (continuous_apply (primeFactorIndex N p))

end Mod

/-! ### The powers -/

section Powers

variable {q : ℕ} (c : (RestrictedProfiniteIntegers q)ˣ) (ℓ : CoprimePrimes q)

/-- The `ℓ`-component of `c`, a unit of `ℤ_ℓ`. -/
public abbrev unitComponent : ℤ_[ℓ.1]ˣ :=
  Units.map (Pi.evalMonoidHom (fun ℓ : CoprimePrimes q => ℤ_[ℓ.1]) ℓ) c

/-- The reduction of the `ℓ`-component of `c` modulo `ℓ^k`. -/
public abbrev unitReduction (k : ℕ) : (ZMod (ℓ.1 ^ k))ˣ :=
  Units.map (PadicInt.toZModPow k).toMonoidHom (unitComponent c ℓ)

/-- `c̄^{φ(ℓ^k)} = 1` in `(ℤ/ℓ^k)^×`. -/
public theorem unitReduction_pow_totient (k : ℕ) :
    unitReduction c ℓ k ^ Nat.totient (ℓ.1 ^ k) = 1 :=
  ZMod.pow_totient _

/-- `φ(ℓ^k) ≠ 0`. -/
public theorem totient_ne_zero (k : ℕ) : Nat.totient (ℓ.1 ^ k) ≠ 0 :=
  (Nat.totient_pos.2 (pow_pos (Fact.out : ℓ.1.Prime).pos k)).ne'

/-- `x^a = x^{a mod N}` when `x^N = 1`. -/
public theorem pow_mod_of_pow_eq_one {G : Type*} [Monoid G] {x : G} {N : ℕ} (hx : x ^ N = 1)
    (a : ℕ) : x ^ (a % N) = x ^ a := by
  conv_rhs => rw [← Nat.div_add_mod a N, pow_add, pow_mul, hx, one_pow, one_mul]

/-- `c^z` modulo `ℓ^k`: `c̄^{z mod φ(ℓ^k)}`. -/
public def levelPowers (k : ℕ) : Multiplicative ProfiniteIntegers →* (ZMod (ℓ.1 ^ k))ˣ where
  toFun z := unitReduction c ℓ k ^
    (profiniteMod _ (totient_ne_zero ℓ k) (Multiplicative.toAdd z)).val
  map_one' := by simp
  map_mul' a b := by
    rw [toAdd_mul, map_add, ZMod.val_add, pow_mod_of_pow_eq_one (unitReduction_pow_totient c ℓ k),
      pow_add]

/-- The underlying element of `levelPowers`, as a power in `ℤ/ℓ^k`. -/
private theorem coe_levelPowers (k : ℕ) (z : Multiplicative ProfiniteIntegers) :
    (levelPowers c ℓ k z : ZMod (ℓ.1 ^ k)) = (unitReduction c ℓ k : ZMod (ℓ.1 ^ k)) ^
      (profiniteMod _ (totient_ne_zero ℓ k) (Multiplicative.toAdd z)).val :=
  Units.val_pow_eq_pow_val _ _

/-- The level powers are compatible. -/
public theorem castHom_levelPowers {k₁ k₂ : ℕ} (hk : k₁ ≤ k₂)
    (z : Multiplicative ProfiniteIntegers) :
    ZMod.castHom (pow_dvd_pow ℓ.1 hk) (ZMod (ℓ.1 ^ k₁)) (levelPowers c ℓ k₂ z : ZMod (ℓ.1 ^ k₂)) =
      (levelPowers c ℓ k₁ z : ZMod (ℓ.1 ^ k₁)) := by
  have hdvd : Nat.totient (ℓ.1 ^ k₁) ∣ Nat.totient (ℓ.1 ^ k₂) :=
    Nat.totient_dvd_of_dvd (pow_dvd_pow ℓ.1 hk)
  rw [coe_levelPowers, coe_levelPowers, map_pow]
  have hc : ZMod.castHom (pow_dvd_pow ℓ.1 hk) (ZMod (ℓ.1 ^ k₁))
      ((unitReduction c ℓ k₂ : (ZMod (ℓ.1 ^ k₂))ˣ) : ZMod (ℓ.1 ^ k₂)) =
      ((unitReduction c ℓ k₁ : (ZMod (ℓ.1 ^ k₁))ˣ) : ZMod (ℓ.1 ^ k₁)) :=
    PadicInt.cast_toZModPow k₁ k₂ hk _
  rw [hc]
  have hexp : (profiniteMod _ (totient_ne_zero ℓ k₂) (Multiplicative.toAdd z)).val %
      Nat.totient (ℓ.1 ^ k₁) =
        (profiniteMod _ (totient_ne_zero ℓ k₁) (Multiplicative.toAdd z)).val := by
    rw [← castHom_profiniteMod_of_dvd _ (totient_ne_zero ℓ k₂) (totient_ne_zero ℓ k₁) hdvd,
      ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]
  rw [← hexp, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val,
    pow_mod_of_pow_eq_one (unitReduction_pow_totient c ℓ k₁)]

/-- The level powers, as ring homomorphisms out of the group ring. -/
public def levelPowersRingHom (k : ℕ) :
    MonoidAlgebra ℤ (Multiplicative ProfiniteIntegers) →+* ZMod (ℓ.1 ^ k) :=
  (MonoidAlgebra.lift ℤ (ZMod (ℓ.1 ^ k)) (Multiplicative ProfiniteIntegers)
    ((Units.coeHom _).comp (levelPowers c ℓ k))).toRingHom

/-- The level powers ring homomorphisms are compatible with the reductions
`ℤ/ℓ^{k₂} → ℤ/ℓ^{k₁}`. -/
public theorem levelPowersRingHom_compat (k₁ k₂ : ℕ) (hk : k₁ ≤ k₂) :
    (ZMod.castHom (pow_dvd_pow ℓ.1 hk) _).comp (levelPowersRingHom c ℓ k₂) =
      levelPowersRingHom c ℓ k₁ := by
  refine MonoidAlgebra.ringHom_ext (fun a => ?_) (fun z => ?_)
  · simp [levelPowersRingHom]
  · simp only [levelPowersRingHom, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, MonoidAlgebra.lift_single, one_smul, MonoidHom.coe_comp,
      Units.coeHom_apply, Function.comp_apply]
    exact castHom_levelPowers c ℓ hk z

/-- **The `ℓ`-component of `z ↦ c^z`.** -/
public def componentPowers : Multiplicative ProfiniteIntegers →* ℤ_[ℓ.1] :=
  (PadicInt.lift (levelPowersRingHom_compat c ℓ)).toMonoidHom.comp
    (MonoidAlgebra.of ℤ (Multiplicative ProfiniteIntegers))

/-- The `ℓ`-component of `c^z`, reduced modulo `ℓ^k`, is `c̄^{z mod φ(ℓ^k)}`. -/
public theorem toZModPow_componentPowers (k : ℕ) (z : Multiplicative ProfiniteIntegers) :
    PadicInt.toZModPow k (componentPowers c ℓ z) = (levelPowers c ℓ k z : ZMod (ℓ.1 ^ k)) := by
  have := RingHom.congr_fun (PadicInt.lift_spec (levelPowersRingHom_compat c ℓ) k)
    (MonoidAlgebra.of ℤ (Multiplicative ProfiniteIntegers) z)
  rw [RingHom.comp_apply] at this
  refine this.trans ?_
  simp [levelPowersRingHom]

/-- **The profinite powers `z ↦ c^z`**. -/
public def profinitePowers : Multiplicative ProfiniteIntegers →* (RestrictedProfiniteIntegers q)ˣ :=
  (Pi.monoidHom fun ℓ : CoprimePrimes q => componentPowers c ℓ).toHomUnits

/-- The `ℓ`-coordinate of `c^z` is the `ℓ`-component of `z ↦ c^z`. -/
public theorem profinitePowers_apply (z : Multiplicative ProfiniteIntegers) (ℓ : CoprimePrimes q) :
    ((profinitePowers c z : (RestrictedProfiniteIntegers q)ˣ) : RestrictedProfiniteIntegers q) ℓ =
      componentPowers c ℓ z :=
  rfl

/-- `c^1 = c`. -/
public theorem profinitePowers_ofAdd_one :
    profinitePowers c (Multiplicative.ofAdd (1 : ProfiniteIntegers)) = c := by
  refine Units.ext (funext fun ℓ => ?_)
  rw [profinitePowers_apply]
  refine PadicInt.ext_of_toZModPow.1 fun k => ?_
  rw [toZModPow_componentPowers]
  rw [coe_levelPowers, toAdd_ofAdd, map_one, ZMod.val_one_eq_one_mod,
    ← Units.val_pow_eq_pow_val, pow_mod_of_pow_eq_one (unitReduction_pow_totient c ℓ k), pow_one]
  rfl

/-- The `ℓ`-component of `z ↦ c^z` is continuous. -/
public theorem continuous_componentPowers : Continuous (componentPowers c ℓ) := by
  rw [continuous_iff_continuousAt]
  intro z
  intro s hs
  obtain ⟨k, hk⟩ := exists_fiber_subset ℓ.1 hs
  set N := Nat.totient (ℓ.1 ^ k)
  have hN := totient_ne_zero ℓ k
  have hO := (isOpen_profiniteMod_fiber N (Multiplicative.toAdd z)).preimage continuous_toAdd
  refine Filter.mem_map.2 (Filter.mem_of_superset (hO.mem_nhds fun p => rfl) fun w hw => hk ?_)
  change PadicInt.toZModPow k (componentPowers c ℓ w) = PadicInt.toZModPow k (componentPowers c ℓ z)
  rw [toZModPow_componentPowers, toZModPow_componentPowers, coe_levelPowers, coe_levelPowers,
    profiniteMod_eq_of_forall N hN hw]

/-- **`z ↦ c^z` is continuous.** -/
public theorem continuous_profinitePowers : Continuous (profinitePowers c) := by
  have hval : Continuous fun z => ((profinitePowers c z : (RestrictedProfiniteIntegers q)ˣ) :
      RestrictedProfiniteIntegers q) :=
    continuous_pi fun ℓ => continuous_componentPowers c ℓ
  refine Units.continuous_iff.2 ⟨hval, ?_⟩
  have : (fun z => ((profinitePowers c z)⁻¹ : (RestrictedProfiniteIntegers q)ˣ).val) =
      (fun z => ((profinitePowers c z : (RestrictedProfiniteIntegers q)ˣ) :
        RestrictedProfiniteIntegers q)) ∘ (fun z => z⁻¹) := by
    funext z
    rw [Function.comp_apply, map_inv]
  rw [this]
  exact hval.comp continuous_inv

end Powers

end Stacks.TraceFormula

end
