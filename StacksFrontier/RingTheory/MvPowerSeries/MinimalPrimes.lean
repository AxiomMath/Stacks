module

public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.MvPowerSeries.Ideal
public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Minimal primes of a power series ring over a Noetherian ring

Let `R` be a Noetherian ring and `σ` a type of variables. Extension of ideals along the
constants `C : R → R[[σ]]` is a bijection from the minimal primes of `R` onto the minimal primes
of `R[[σ]]`. This is the computation the source leaves to the reader in **Stacks 0DR9**
("all of this is easy to prove by writing `A'` as a power series ring over `A`"): for a prime
`p` of `R`, the ideal `p R[[σ]]` is the kernel of `R[[σ]] → (R/p)[[σ]]`, so it is prime and
contracts to `p`, and every prime `Q` of `R[[σ]]` contains `(Q ∩ R) R[[σ]]`.

## Main results

* `MvPowerSeries.isPrime_map_C`: `p R[[σ]]` is prime for a prime `p` of `R`.
* `MvPowerSeries.comap_C_map_C`: `p R[[σ]]` contracts to `p`.
* `MvPowerSeries.bijOn_map_C_minimalPrimes`: extension along `C` is a bijection of minimal
  primes.
* `Ideal.bijOn_map_minimalPrimes_of_ringEquiv_mvPowerSeries`: the same for a ring map
  `φ : R → R'` with `R' ≅ R[[σ]]` carrying `φ` to `C`.

## References

* [Stacks Project, Tag 0DR9](https://stacks.math.columbia.edu/tag/0DR9)
-/

@[expose] public section

namespace MvPowerSeries

variable {R : Type*} [CommRing R] [IsNoetherianRing R] {σ : Type*}

/-- The extension of an ideal `p` of a Noetherian ring to the power series ring is the kernel of
the reduction `R[[σ]] → (R/p)[[σ]]`. -/
theorem ker_map_mk (p : Ideal R) :
    RingHom.ker (map (σ := σ) (Ideal.Quotient.mk p)) = p.map (C (σ := σ) (R := R)) := by
  rw [ker_map_of_fg _ (by rw [Ideal.mk_ker]; exact Ideal.fg_of_isNoetherianRing p),
    Ideal.mk_ker]

/-- **The extension of a prime of a Noetherian ring to a power series ring is prime**: it is the
kernel of the reduction onto the power series ring over the domain `R/p`. -/
theorem isPrime_map_C {p : Ideal R} (hp : p.IsPrime) :
    (p.map (C (σ := σ) (R := R))).IsPrime := by
  have : IsDomain (R ⧸ p) := Ideal.Quotient.isDomain p
  have : IsDomain (MvPowerSeries σ (R ⧸ p)) := NoZeroDivisors.to_isDomain _
  rw [← ker_map_mk]
  exact RingHom.ker_isPrime _

/-- **The extension of an ideal of a Noetherian ring to a power series ring contracts to the
ideal.** -/
theorem comap_C_map_C (p : Ideal R) :
    (p.map (C (σ := σ) (R := R))).comap (C (σ := σ) (R := R)) = p := by
  refine le_antisymm (fun x hx => ?_) Ideal.le_comap_map
  rw [Ideal.mem_comap, ← ker_map_mk, RingHom.mem_ker, map_C] at hx
  have hx' : Ideal.Quotient.mk p x = 0 := by
    simpa using congrArg (constantCoeff (σ := σ) (R := R ⧸ p)) hx
  exact Ideal.Quotient.eq_zero_iff_mem.mp hx'

omit [IsNoetherianRing R] in
/-- A prime of the power series ring contains the extension of its contraction. -/
theorem map_C_comap_C_le (Q : Ideal (MvPowerSeries σ R)) :
    (Q.comap (C (σ := σ) (R := R))).map (C (σ := σ) (R := R)) ≤ Q :=
  Ideal.map_comap_le

/-- **The extension of a minimal prime of a Noetherian ring to a power series ring is a minimal
prime.** -/
theorem map_C_mem_minimalPrimes {p : Ideal R} (hp : p ∈ minimalPrimes R) :
    p.map (C (σ := σ) (R := R)) ∈ minimalPrimes (MvPowerSeries σ R) := by
  have hpr : p.IsPrime := hp.1.1
  refine ⟨⟨isPrime_map_C hpr, bot_le⟩, fun Q hQ hle => ?_⟩
  have hQc : Q.comap (C (σ := σ) (R := R)) = p := by
    refine le_antisymm ?_ (hp.2 ⟨hQ.1.comap _, bot_le⟩ ?_)
    · calc Q.comap C ≤ (p.map C).comap C := Ideal.comap_mono hle
        _ = p := comap_C_map_C p
    · calc Q.comap C ≤ (p.map C).comap C := Ideal.comap_mono hle
        _ = p := comap_C_map_C p
  calc p.map C = (Q.comap C).map C := by rw [hQc]
    _ ≤ Q := map_C_comap_C_le Q

/-- **Every minimal prime of a power series ring over a Noetherian ring is the extension of a
minimal prime of the coefficients**, namely of its contraction. -/
theorem exists_map_C_eq_of_mem_minimalPrimes {Q : Ideal (MvPowerSeries σ R)}
    (hQ : Q ∈ minimalPrimes (MvPowerSeries σ R)) :
    ∃ p ∈ minimalPrimes R, p.map (C (σ := σ) (R := R)) = Q := by
  have hQp : (Q.comap (C (σ := σ) (R := R))).IsPrime := hQ.1.1.comap _
  obtain ⟨p, hp, hpQ⟩ := Ideal.exists_minimalPrimes_le
    (bot_le : (⊥ : Ideal R) ≤ Q.comap (C (σ := σ) (R := R)))
  have hle : p.map (C (σ := σ) (R := R)) ≤ Q :=
    (Ideal.map_mono hpQ).trans (map_C_comap_C_le Q)
  refine ⟨p, hp, le_antisymm hle (hQ.2 ⟨isPrime_map_C hp.1.1, bot_le⟩ hle)⟩

/-- **Extension along the constants is a bijection from the minimal primes of a Noetherian ring
onto the minimal primes of a power series ring over it.** -/
theorem bijOn_map_C_minimalPrimes :
    Set.BijOn (fun p : Ideal R => p.map (C (σ := σ) (R := R))) (minimalPrimes R)
      (minimalPrimes (MvPowerSeries σ R)) :=
  ⟨fun _ hp => map_C_mem_minimalPrimes hp,
    fun p _ q _ h => by
      rw [← comap_C_map_C (σ := σ) p, ← comap_C_map_C (σ := σ) q]
      exact congrArg _ h,
    fun _ hQ => exists_map_C_eq_of_mem_minimalPrimes hQ⟩

end MvPowerSeries

namespace Ideal

variable {R R' : Type*} [CommRing R] [IsNoetherianRing R] [CommRing R'] {σ : Type*}

/-- Contracting along a ring isomorphism and then along its inverse gives back the ideal. -/
theorem comap_comap_ringEquiv_symm {S S' : Type*} [CommRing S] [CommRing S'] (e : S ≃+* S')
    (Q : Ideal S') : (Q.comap e).comap e.symm = Q := by
  ext x
  rw [Ideal.mem_comap, Ideal.mem_comap, RingEquiv.apply_symm_apply]

/-- A ring isomorphism carries minimal primes of the target, by contraction, to minimal primes of
the source. -/
theorem comap_mem_minimalPrimes_of_ringEquiv {S S' : Type*} [CommRing S] [CommRing S']
    (e : S ≃+* S') {Q : Ideal S'} (hQ : Q ∈ minimalPrimes S') :
    Q.comap e ∈ minimalPrimes S := by
  refine ⟨⟨hQ.1.1.comap _, bot_le⟩, fun P hP hle => ?_⟩
  have h : P.comap e.symm ≤ Q := by
    rw [← comap_comap_ringEquiv_symm e Q]
    exact Ideal.comap_mono hle
  have h' := hQ.2 ⟨hP.1.comap _, bot_le⟩ h
  calc Q.comap e ≤ (P.comap e.symm).comap e := Ideal.comap_mono h'
    _ = P := by simpa using comap_comap_ringEquiv_symm e.symm P

/-- A ring isomorphism carries the minimal primes of the target, by contraction, bijectively onto
the minimal primes of the source. -/
theorem bijOn_comap_minimalPrimes_of_ringEquiv {S S' : Type*} [CommRing S] [CommRing S']
    (e : S ≃+* S') :
    Set.BijOn (fun Q : Ideal S' => Q.comap e) (minimalPrimes S') (minimalPrimes S) := by
  refine ⟨fun Q hQ => comap_mem_minimalPrimes_of_ringEquiv e hQ, fun Q _ Q' _ h => ?_,
    fun P hP => ⟨P.comap e.symm, comap_mem_minimalPrimes_of_ringEquiv e.symm hP, ?_⟩⟩
  · rw [← comap_comap_ringEquiv_symm e Q, ← comap_comap_ringEquiv_symm e Q']
    exact congrArg _ h
  · simpa using comap_comap_ringEquiv_symm e.symm P

/-- **Extension of minimal primes along a formally smooth comparison of complete rings.** Let
`R` be Noetherian and `φ : R → R'` a ring map for which there is an isomorphism
`E : R' ≅ R[[σ]]` carrying `φ` to the constants. Then `p ↦ φ(p) R'` is a bijection
from the minimal primes of `R` onto the minimal primes of `R'`. -/
theorem bijOn_map_minimalPrimes_of_ringEquiv_mvPowerSeries (φ : R →+* R')
    (E : R' ≃+* MvPowerSeries σ R) (hE : ∀ b, E (φ b) = MvPowerSeries.C b) :
    Set.BijOn (fun p : Ideal R => p.map φ) (minimalPrimes R) (minimalPrimes R') := by
  have hφ : φ = (E.symm : MvPowerSeries σ R →+* R').comp MvPowerSeries.C := by
    ext b
    simp [← hE b]
  have hfun : (fun p : Ideal R => p.map φ) =
      (fun Q : Ideal (MvPowerSeries σ R) => Q.comap E) ∘
        (fun p : Ideal R => p.map (MvPowerSeries.C (σ := σ) (R := R))) := by
    funext p
    simp only [Function.comp_apply, hφ, ← Ideal.map_map, Ideal.map_comap_of_equiv]
    rfl
  rw [hfun]
  exact (bijOn_comap_minimalPrimes_of_ringEquiv E).comp MvPowerSeries.bijOn_map_C_minimalPrimes

end Ideal
