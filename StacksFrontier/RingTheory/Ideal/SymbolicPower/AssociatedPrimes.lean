module

public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import StacksFrontier.RingTheory.Ideal.SymbolicPower
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.Defs
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Associated primes of a symbolic power

Let `R` be a Noetherian ring, `p ⊆ R` a prime ideal and `n > 0`. Then the only prime associated to
`R / p^{(n)}` is `p`, where a prime `q` is associated to an `R`-module `M` if `q = Ann_R(m)` for
some `m ∈ M`, and `p^{(n)} = R ∩ p^n R_p` is the `n`-th symbolic power of `p`.

## Main definitions

* `AssExactSpan`: the set `Ass_R(M)` of primes of `R` that are the annihilator of an element
  of `M`.

## Main results

* `exact_ann_of_isPrimary`: for a primary ideal `I` of a Noetherian ring with `radical I = p`, `p`
  is the annihilator of an element of `R ⧸ I`.
* `ass_quotient_symbolicPower`, `ass_quotient_symbolicPower'`: `Ass_R(R / p^{(n)}) = {p}`.
-/

@[expose] public section

open Pointwise

/-- The set `Ass_R(M)` of primes of `R` of the form `Ideal.torsionOf R M m` for some `m : M`; it
is `Stacks.AssociatedPrimes.assPrimes R M`. -/
@[sga "2 III 1.1"]
def AssExactSpan (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M] :
    Set (Ideal R) :=
  Stacks.AssociatedPrimes.assPrimes R M

/-- `x ∈ p^{(n)}` iff `ι(x) ∈ p^n R_p`, where `ι : R → R_p` is the localization map. -/
theorem mem_symbolicPower {R : Type*} [CommRing R] (p : Ideal R) [p.IsPrime] (n : ℕ) (x : R) :
    x ∈ symbolicPower' p n ↔
      algebraMap R (Localization.AtPrime p) x ∈
        (p ^ n).map (algebraMap R (Localization.AtPrime p)) :=
  Iff.rfl

/-- A prime of `R` that is the annihilator of an element of `M` is an associated prime of `M` in
the sense of `associatedPrimes`. -/
theorem assExactSpan_subset_associatedPrimes {R M : Type*} [CommRing R] [AddCommGroup M] [Module R
    M]
    {q : Ideal R} (hq : q ∈ AssExactSpan R M) : q ∈ associatedPrimes R M := by
  obtain ⟨hp, m, hm⟩ := hq
  refine ⟨hp, m, ?_⟩
  rw [Submodule.bot_colon', Ideal.annihilator_span_singleton_eq_torsionOf, hm, hp.radical]

/-- A prime of `R` that is the annihilator of an element of `M` is an associated prime of `M` in
the sense of `associatedPrimes`. -/
theorem assPrimes_subset_associatedPrimes {R M : Type*} [CommRing R] [AddCommGroup M] [Module R
    M]
    {q : Ideal R} (hq : q ∈ Stacks.AssociatedPrimes.assPrimes R M) : q ∈ associatedPrimes R M := by
  obtain ⟨hp, m, hm⟩ := hq
  refine ⟨hp, m, ?_⟩
  rw [Submodule.bot_colon', Ideal.annihilator_span_singleton_eq_torsionOf, hm, hp.radical]

/-- If `I` is a primary ideal of a Noetherian ring `R` with `radical I = p`, then `p` is the
annihilator of some element of `R ⧸ I`, i.e. `p ∈ Ass_R(R ⧸ I)`. -/
theorem exact_ann_of_isPrimary {R : Type*} [CommRing R] [IsNoetherianRing R] {I : Ideal R}
    (hI : I.IsPrimary) {p : Ideal R} (hp : I.radical = p) :
    ∃ z : R ⧸ I, Ideal.torsionOf R (R ⧸ I) z = p := by
  have hpprime : p.IsPrime := hp ▸ Ideal.isPrime_radical hI
  have hfg : I.radical.FG := IsNoetherian.noetherian _
  obtain ⟨m, hm⟩ := Ideal.exists_radical_pow_le_of_fg I hfg
  have hex : ∃ k, p ^ k ≤ I := ⟨m, hp ▸ hm⟩
  classical
  set k := Nat.find hex with hk
  have hkle : p ^ k ≤ I := Nat.find_spec hex
  have hkpos : 0 < k := Nat.pos_of_ne_zero fun h0 => hI.left (by simpa [h0] using hkle)
  have hnk : ¬ p ^ (k - 1) ≤ I := Nat.find_min hex (m := k - 1) (by omega)
  obtain ⟨z₀, hz₀mem, hz₀notI⟩ := Set.not_subset.mp hnk
  refine ⟨Ideal.Quotient.mk I z₀, ?_⟩
  have hkey : ∀ r : R, r • (Ideal.Quotient.mk I z₀) = 0 ↔ r * z₀ ∈ I := fun r => by
    rw [show r • (Ideal.Quotient.mk I z₀) = Ideal.Quotient.mk I (r * z₀) from rfl,
      Ideal.Quotient.eq_zero_iff_mem]
  refine le_antisymm (fun r hr => ?_) fun r hr => ?_
  · rw [Ideal.mem_torsionOf_iff, hkey] at hr
    by_contra hrp
    have hrnotrad : r ∉ I.radical := hp ▸ hrp
    have hz₀I : z₀ ∈ I := by
      rcases hI.right (show r • z₀ ∈ I by rwa [smul_eq_mul]) with h | h
      · exact h
      · exfalso
        apply hrnotrad
        obtain ⟨j, hj⟩ := h
        refine ⟨j, hj ?_⟩
        have h1 := Submodule.smul_mem_pointwise_smul (1 : R) (r ^ j) (⊤ : Ideal R) Submodule.mem_top
        simpa using h1
    exact hz₀notI hz₀I
  · rw [Ideal.mem_torsionOf_iff, hkey]
    refine hkle ?_
    rw [show k = (k - 1) + 1 by omega, pow_succ, mul_comm]
    exact Ideal.mul_mem_mul hr hz₀mem

/-- The associated primes of `R / p^{(n)}` are exactly `{p}`. -/
private theorem assPrimes_quotient_symbolicPower_eq {R : Type*} [CommRing R] [IsNoetherianRing R]
    (p : Ideal R) [p.IsPrime] (n : ℕ) (hn : 0 < n) :
    Stacks.AssociatedPrimes.assPrimes R (R ⧸ symbolicPower' p n) = {p} := by
  set ι := algebraMap R (Localization.AtPrime p) with hι
  have hrad : ((p ^ n).map ι).radical = IsLocalRing.maximalIdeal (Localization.AtPrime p) := by
    rw [Ideal.map_pow, Ideal.radical_pow _ (Nat.pos_iff_ne_zero.mp hn),
      Localization.AtPrime.map_eq_maximalIdeal]
    exact (IsLocalRing.maximalIdeal.isMaximal _).isPrime.radical
  have hprim : ((p ^ n).map ι).IsPrimary :=
    Ideal.isPrimary_of_isMaximal_radical (hrad ▸ IsLocalRing.maximalIdeal.isMaximal _)
  have hsymprim : (symbolicPower' p n).IsPrimary := hprim.comap ι
  have hsymrad : (symbolicPower' p n).radical = p := by
    rw [show symbolicPower' p n = ((p ^ n).map ι).comap ι from rfl, ← Ideal.comap_radical, hrad]
    exact IsLocalization.AtPrime.under_maximalIdeal _ _
  refine Set.eq_singleton_iff_unique_mem.mpr
    ⟨⟨‹p.IsPrime›, exact_ann_of_isPrimary hsymprim hsymrad⟩, fun q hq => ?_⟩
  simpa [associatedPrimes.eq_singleton_of_isPrimary hsymprim, hsymrad] using
    assPrimes_subset_associatedPrimes hq

/-- For a Noetherian ring `R`, a prime ideal `p`, and `n > 0`, the set of associated primes of
`R / p^{(n)}` is exactly `{p}`. -/
theorem ass_quotient_symbolicPower {R : Type*} [CommRing R] [IsNoetherianRing R]
    (p : Ideal R) [p.IsPrime] (n : ℕ) (hn : 0 < n) :
    AssExactSpan R (R ⧸ symbolicPower' p n) = {p} :=
  assPrimes_quotient_symbolicPower_eq p n hn

/-- For a Noetherian ring `R`, a prime ideal `p`, and `n > 0`, the set of associated primes of
`R / p^{(n)}` is exactly `{p}`. -/
@[stacks 0314]
theorem ass_quotient_symbolicPower' {R : Type*} [CommRing R] [IsNoetherianRing R]
    (p : Ideal R) [p.IsPrime] (n : ℕ) (hn : 0 < n) :
    Stacks.AssociatedPrimes.assPrimes R (R ⧸ symbolicPower' p n) = {p} :=
  assPrimes_quotient_symbolicPower_eq p n hn
