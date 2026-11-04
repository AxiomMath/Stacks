module

import StacksFrontier.RingTheory.Ideal.AssociatedPrime.Support
import StacksFrontier.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.RingTheory.KrullDimension.Module
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.PicardGroup
import Mathlib.Tactic.ENatToNat
import Std.Tactic.BVDecide.Normalize.Prop
import StacksCore.LinearAlgebra.Matrix.CommSemiring

public import StacksFrontier.RingTheory.Depth.Defs
public import StacksFrontier.RingTheory.Depth.Defs.Defs
public import StacksFrontier.RingTheory.Depth.Nakayama
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Serre conditions

A Noetherian ring `R` satisfies `(Rₖ)` when every prime of height at most `k` has regular
localization, and `(Sₖ)` when at every prime `𝔭` the depth of `R_𝔭` — or, for a finite module
`M`, the depth of `M_𝔭` — is at least `min(k, dim)`. Both conditions are defined here, following
Definition 031P, on top of the depth of a module along an ideal.

Two lemmas about small `k` follow. At `k = 1` the condition on a finite module `M` over a
Noetherian ring says exactly that `M` has no *embedded* associated prime, that is, that every
associated prime of `M` is minimal among the associated primes of `M`: an embedded associated
prime `𝔭 ⊋ 𝔮 ∈ Ass(M)` puts `𝔭R_𝔭` in `Ass(M_𝔭)` and `𝔮` in `Supp(M_𝔭)`, so `depth(M_𝔭) = 0`
while `dim Supp(M_𝔭) ≥ 1`; conversely at a prime where `(S₁)` fails `𝔭` is associated to `M`, and
so is a minimal prime of `Supp(M)` strictly inside it, exhibiting `𝔭` as embedded (Lemma 031Q).

At `k = 2` the condition is what Serre's criterion gives a Noetherian normal domain `R` with
fraction field `K`, and Lemma 031T is what it says about the *divisorial* quotients of `R` — the
quotients by the ideals `R ∩ xR` cut out by an element `x` of `K`. Their associated primes are
minimal among themselves and of height one, and `R` is the intersection, inside `K`, of its
localizations at the height-one primes.

## Main definitions

* `HasPropertyRk`: property `(Rₖ)`, regularity in codimension at most `k`.
* `PropertySkRing`, `PropertySkModule`: property `(Sₖ)` for a ring and for a finite module.
* `fibreRing`: the fibre ring `S ⊗_R κ(𝔭)` of an `R`-algebra `S` at a prime `𝔭` of `R`.

## Main results

* `Module.forall_minimal_mem_associatedPrimes_iff_min_one_supportDim_le_depth`: a finite module
  over a Noetherian ring has no embedded associated prime if and only if it satisfies `(S₁)`.
* `associatedPrimes_minimal_and_height_eq_one_and_iInf_localization_eq_bot`: for a Noetherian
  normal domain `R` with fraction field `K`, (1) every associated prime of `R/aR` with `a ≠ 0` is
  minimal among them and of height `1`, (2) `R` is the intersection of the subalgebras `R_𝔭 ⊆ K`
  over the height-one primes `𝔭`, and (3) the same as (1) for `R/(R ∩ xR)` with `0 ≠ x ∈ K`.

## Implementation notes

Property `(Rₖ)` uses no finiteness of the ring, so `HasPropertyRk` is stated over an arbitrary
commutative ring. The two `(Sₖ)` predicates keep the Noetherian hypothesis of Definition 031P.
Their conventions are Noetherian-local ones: `moduleDepth` is `0` on the zero module where the
source writes `∞`, and `unbotD 0` reads the source's `dim(∅) = -∞` as `0`, so the spelling agrees
with Definition 031P for a finite module over a Noetherian local ring. `fibreRing` is
`Ideal.Fiber` with the two tensor factors interchanged.

In `Module.forall_minimal_mem_associatedPrimes_iff_min_one_supportDim_le_depth`, property `(S₁)`
is spelled out as the inequality `min{1, dim Supp(M_𝔭)} ≤ depth_{𝔭R_𝔭}(M_𝔭)` rather than as
`PropertySkModule R M 1`: the predicates above are phrased with `moduleDepth` and
`moduleSupportDim`, which are stated for a local ring and truncate the dimension of the empty
support to `0`, while the lemma is phrased with `Module.depth` and `Module.supportDim`, whose
conventions `depth(0) = ⊤` and `dim(∅) = ⊥` are the source's `∞` and `-∞`. The inequality is
therefore read in `WithBot ℕ∞`, and the primes off the support impose no condition, so the
statement may quantify over all of `PrimeSpectrum R`, as Definition 0AAH does. Having no
embedded associated prime is spelled with `Minimal`, and the localizations are the canonical
models `Localization.AtPrime 𝔭` and `LocalizedModule 𝔭.primeCompl M`.

In `associatedPrimes_minimal_and_height_eq_one_and_iInf_localization_eq_bot` a normal domain is
`IsDomain` plus `IsIntegrallyClosed`, and heights are `Ideal.height`, taken in `R` and not in a
localization. Item (2) is the equality `⨅ 𝔭, R_𝔭 = ⊥` in the lattice of `R`-subalgebras of `K`,
each `R_𝔭` being `Localization.subalgebra.ofField` and `⊥` the image of `algebraMap R K`, as in
`IsDedekindDomain.HeightOneSpectrum.iInf_localization_eq_bot` and
`PrimeSpectrum.iInf_localization_eq_bot`. When `R` is a field the intersection is empty, and
`⊤ = ⊥` holds because `algebraMap R K` is then surjective. The ideal `R ∩ xR` is the pullback
`(Submodule.span R {x}).comap (Algebra.linearMap R K)` of the `R`-submodule `xR` of `K`; for
`x = algebraMap R K a` it equals `Ideal.span {a}`, so item (1) is the case `x ∈ R` of item (3),
though not definitionally.

## References

* [StacksProject 031P](https://stacks.math.columbia.edu/tag/031P)
* [StacksProject 031Q](https://stacks.math.columbia.edu/tag/031Q)
* [StacksProject 031T](https://stacks.math.columbia.edu/tag/031T)
-/

@[expose] public section

/-- Property `(Rₖ)`: every prime `𝔭` of `A` of height at most `k` has regular localization `A_𝔭`.
As `height 𝔭 = dim A_𝔭`, this is regularity of `A` in codimension at most `k`. -/
@[stacks 031P "Rk", ega "IV 5.8.2" "affine case", ega "IV 7.5.3" "partial"]
def HasPropertyRk (A : Type*) [CommRing A] (k : ℕ) : Prop :=
  ∀ (p : Ideal A) [p.IsPrime], p.height ≤ (k : ℕ∞) → IsRegularLocalRing (Localization.AtPrime p)

/-- Property `(Sₖ)` for a Noetherian commutative ring `R`: at every prime `𝔭` the depth of the
localization `R_𝔭` is at least `min(k, dim R_𝔭)`. -/
@[stacks 031P "Sk ring",
  ega "IV 5.7.2" "special case",
  ega "IV 5.7.3" "special case",
  ega "IV 7.5.3"]
def PropertySkRing (R : Type*) [CommRing R] [IsNoetherianRing R] (k : ℕ) : Prop :=
  ∀ (p : Ideal R) [p.IsPrime],
    min (k : ℕ∞) ((ringKrullDim (Localization.AtPrime p)).unbotD 0) ≤
      ringDepth (Localization.AtPrime p)

/-- Property `(Sₖ)` for a finite module `M` over a Noetherian commutative ring `R`: at every prime
`𝔭` the depth of the localization `M_𝔭` is at least `min(k, dim Supp(M_𝔭))`. -/
@[stacks 031P "Sk module",
  ega "IV 5.7.2" "special case",
  ega "IV 5.7.3",
  ega "IV 7.5.3" "more general"]
def PropertySkModule (R : Type*) [CommRing R] [IsNoetherianRing R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] (k : ℕ) : Prop :=
  ∀ (p : Ideal R) [p.IsPrime],
    min (k : ℕ∞)
        ((moduleSupportDim (Localization.AtPrime p) (LocalizedModule.AtPrime p M)).unbotD 0) ≤
      moduleDepth (Localization.AtPrime p) (LocalizedModule.AtPrime p M)

/-- The fibre ring `S ⊗_R κ(𝔭)` of an `R`-algebra `S` at a prime `𝔭` of `R`, where
`κ(𝔭) = Ideal.ResidueField 𝔭` is the residue field of `R` at `𝔭`. -/
@[ega "0 19.7.1" "more general",
  ega "III 6.9.10" "special case",
  ega "IV 1.8.6" "special case",
  ega "IV 12.1.1.4" "special case",
  ega "IV 15.4.1" "partial",
  ega "IV 2.2.1" "special case",
  ega "IV 5.5.2",
  ega "IV 7.3.13" "more general",
  ega "IV 7.8.1" "more general",
  ega "IV 9.4.1" "special case", sga "1 III 1.7"]
abbrev fibreRing (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) [p.IsPrime] : Type _ :=
  TensorProduct R S p.ResidueField

/-- For a finite module `M`, the Krull dimension `moduleSupportDim R M` of its support as a
subspace of `PrimeSpectrum R` equals `Module.supportDim R M`. -/
lemma moduleSupportDim_eq_Module_supportDim {R : Type*} [CommRing R] {M : Type*}
    [AddCommGroup M] [Module R M] [Module.Finite R M] :
    moduleSupportDim R M = Module.supportDim R M := by
  have hzero : topologicalKrullDim (PrimeSpectrum.zeroLocus
      ((Module.annihilator R M : Ideal R) : Set R)) =
      ringKrullDim (R ⧸ Module.annihilator R M) := by
    have hrange : Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk
        (Module.annihilator R M))) =
        PrimeSpectrum.zeroLocus ((Module.annihilator R M : Ideal R) : Set R) := by
      rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
    let e : PrimeSpectrum (R ⧸ Module.annihilator R M) ≃ₜ
        PrimeSpectrum.zeroLocus ((Module.annihilator R M : Ideal R) : Set R) :=
      (PrimeSpectrum.isEmbedding_comap_of_surjective _ _
        Ideal.Quotient.mk_surjective).toHomeomorph.trans (Homeomorph.setCongr hrange)
    rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
      IsHomeomorph.topologicalKrullDim_eq _ e.isHomeomorph]
  unfold moduleSupportDim
  rw [Module.support_eq_zeroLocus, hzero]
  exact (Module.supportDim_eq_ringKrullDim_quotient_annihilator R M).symm

/-! ### `(S₁)` and embedded associated primes -/

namespace Module

/-- Over a Noetherian local ring, a finite module has depth `0` along the maximal ideal exactly
when the maximal ideal is one of its associated primes. -/
@[ega "0 16.4.6", ega "IV 21.1.10" "more general"]
public lemma depth_eq_zero_iff_maximalIdeal_mem_associatedPrimes {S : Type*} [CommRing S]
    [IsLocalRing S] [IsNoetherianRing S] {N : Type*} [AddCommGroup N] [Module S N]
    [Module.Finite S N] :
    Module.depth S (IsLocalRing.maximalIdeal S) N = 0 ↔
      IsLocalRing.maximalIdeal S ∈ associatedPrimes S N := by
  rw [← Order.lt_one_iff, ← not_le,
    one_le_depth_iff_exists_isSMulRegular (IsLocalRing.maximalIdeal S),
    Ideal.exists_mem_isSMulRegular_iff_forall_associatedPrimes_not_le _ N
      (associatedPrimes.finite S N)]
  push Not
  refine ⟨fun ⟨q, hq, hle⟩ => ?_, fun h => ⟨_, h, le_rfl⟩⟩
  have : q.IsPrime := hq.isPrime
  exact le_antisymm hle (IsLocalRing.le_maximalIdeal_of_isPrime q) ▸ hq

/-- An associated prime of a module lies in its support. -/
@[sga "2 III 1.2" "(ii) ⇒ (i)"]
private lemma mem_support_of_asIdeal_mem_associatedPrimes {S : Type*} [CommRing S]
    {N : Type*} [AddCommGroup N] [Module S N] {q : PrimeSpectrum S}
    (hq : q.asIdeal ∈ associatedPrimes S N) : q ∈ Module.support S N := by
  obtain ⟨x, hx⟩ := hq.2
  rw [Submodule.bot_colon'] at hx
  exact Module.mem_support_iff_exists_annihilator.mpr ⟨x, hx ▸ Ideal.le_radical⟩

/-- Every point of the support of a finite module lies above a minimal point of the support. -/
private lemma exists_minimal_mem_support_le {S : Type*} [CommRing S]
    {N : Type*} [AddCommGroup N] [Module S N] [Module.Finite S N] {q : PrimeSpectrum S}
    (hq : q ∈ Module.support S N) :
    ∃ z : PrimeSpectrum S, Minimal (· ∈ Module.support S N) z ∧ z ≤ q := by
  obtain ⟨z, hz, hzq⟩ := Ideal.exists_minimalPrimes_le (J := q.asIdeal)
    (Module.mem_support_iff_of_finite.mp hq)
  refine ⟨⟨z, hz.isPrime⟩, ⟨Module.mem_support_iff_of_finite.mpr hz.1.2, ?_⟩, hzq⟩
  intro w hw hwz
  exact hz.2 ⟨w.2, Module.mem_support_iff_of_finite.mp hw⟩ hwz

/-- Over a Noetherian local ring the support of a finite module has dimension at least `1`
exactly when one of its associated primes is strictly contained in the maximal ideal. -/
private lemma zero_lt_supportDim_iff_exists_mem_associatedPrimes_lt {S : Type*} [CommRing S]
    [IsLocalRing S] [IsNoetherianRing S] {N : Type*} [AddCommGroup N] [Module S N]
    [Module.Finite S N] :
    0 < Module.supportDim S N ↔
      ∃ q ∈ associatedPrimes S N, q < IsLocalRing.maximalIdeal S := by
  rw [Module.supportDim, Order.krullDim_pos_iff]
  constructor
  · rintro ⟨x, y, hxy⟩
    obtain ⟨z, hzmin, hzx⟩ := exists_minimal_mem_support_le x.2
    refine ⟨z.asIdeal, ((Set.ext_iff.mp
      Module.setOf_minimal_support_eq_setOf_minimal_associatedPrimes z).mp hzmin).1,
      lt_of_le_of_lt hzx (lt_of_lt_of_le (Subtype.coe_lt_coe.mpr hxy)
        (IsLocalRing.le_maximalIdeal_of_isPrime y.1.asIdeal))⟩
  · rintro ⟨q, hq, hqm⟩
    have hqp : q.IsPrime := hq.isPrime
    have hqs : (⟨q, hqp⟩ : PrimeSpectrum S) ∈ Module.support S N :=
      mem_support_of_asIdeal_mem_associatedPrimes hq
    have : Nontrivial N := Module.nonempty_support_iff.mp ⟨_, hqs⟩
    exact ⟨⟨_, hqs⟩, ⟨_, IsLocalRing.closedPoint_mem_support S N⟩, hqm⟩

section

variable {R : Type*} [CommRing R] [IsNoetherianRing R]
  {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]

omit [Module.Finite R M] in
open Module.associatedPrimes in
/-- A prime of `R_𝔭` is associated to `M_𝔭` exactly when its contraction to `R` is associated
to `M`. -/
public lemma mem_associatedPrimes_localized_iff (p : PrimeSpectrum R)
    (z : Ideal (Localization.AtPrime p.asIdeal)) :
    z ∈ associatedPrimes (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl M) ↔
      Ideal.comap (algebraMap R (Localization.AtPrime p.asIdeal)) z ∈ associatedPrimes R M :=
  (Set.ext_iff.mp (preimage_comap_associatedPrimes_eq_associatedPrimes_of_isLocalizedModule
    p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal)
    (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M)) z).symm

/-- At a prime `𝔭` the localization `M_𝔭` has depth `0` exactly when `𝔭` is an associated prime
of `M`. -/
public lemma depth_localized_eq_zero_iff (p : PrimeSpectrum R) :
    Module.depth (Localization.AtPrime p.asIdeal)
        (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
        (LocalizedModule p.asIdeal.primeCompl M) = 0 ↔ p.asIdeal ∈ associatedPrimes R M := by
  rw [depth_eq_zero_iff_maximalIdeal_mem_associatedPrimes, mem_associatedPrimes_localized_iff p,
    show Ideal.comap (algebraMap R (Localization.AtPrime p.asIdeal))
      (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal)) = p.asIdeal from
      Localization.AtPrime.under_maximalIdeal]

omit [Module.Finite R M] in
/-- `M_𝔭` has an associated prime strictly inside `𝔭R_𝔭` exactly when `M` has an associated
prime strictly inside `𝔭`. -/
private lemma exists_mem_associatedPrimes_lt_maximalIdeal_localized_iff (p : PrimeSpectrum R) :
    (∃ z ∈ associatedPrimes (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl M),
      z < IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal)) ↔
      ∃ q ∈ associatedPrimes R M, q < p.asIdeal := by
  have hmax : Ideal.comap (algebraMap R (Localization.AtPrime p.asIdeal))
      (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal)) = p.asIdeal :=
    Localization.AtPrime.under_maximalIdeal
  constructor
  · rintro ⟨z, hz, hzm⟩
    refine ⟨_, (mem_associatedPrimes_localized_iff p z).mp hz,
      lt_of_le_of_ne ((Ideal.comap_mono hzm.le).trans hmax.le) fun heq => hzm.ne ?_⟩
    calc z = Ideal.map (algebraMap R (Localization.AtPrime p.asIdeal))
            (Ideal.comap (algebraMap R (Localization.AtPrime p.asIdeal)) z) :=
          (IsLocalization.map_under p.asIdeal.primeCompl _ z).symm
      _ = Ideal.map (algebraMap R (Localization.AtPrime p.asIdeal))
            (Ideal.comap (algebraMap R (Localization.AtPrime p.asIdeal))
              (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))) := by rw [heq, hmax]
      _ = _ := IsLocalization.map_under p.asIdeal.primeCompl _ _
  · rintro ⟨q, hq, hqp⟩
    have hqprime : q.IsPrime := hq.isPrime
    have hdisj : Disjoint (p.asIdeal.primeCompl : Set R) (q : Set R) := by
      simpa [Ideal.primeCompl, Set.disjoint_compl_left_iff_subset] using hqp.le
    have hunder : Ideal.comap (algebraMap R (Localization.AtPrime p.asIdeal))
        (Ideal.map (algebraMap R (Localization.AtPrime p.asIdeal)) q) = q :=
      IsLocalization.under_map_of_isPrime_disjoint _ _ hqprime hdisj
    have hprime : (Ideal.map (algebraMap R (Localization.AtPrime p.asIdeal)) q).IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint _ _ q hqprime hdisj
    exact ⟨_, (mem_associatedPrimes_localized_iff p _).mpr (by rw [hunder]; exact hq),
      lt_of_le_of_ne (IsLocalRing.le_maximalIdeal_of_isPrime _) fun heq => hqp.ne
        (by rw [← hunder, heq, hmax])⟩

/-- At a prime `𝔭` the support of `M_𝔭` has dimension at least `1` exactly when some associated
prime of `M` is strictly contained in `𝔭`. -/
private lemma zero_lt_supportDim_localized_iff (p : PrimeSpectrum R) :
    0 < Module.supportDim (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl M) ↔
      ∃ q ∈ associatedPrimes R M, q < p.asIdeal :=
  zero_lt_supportDim_iff_exists_mem_associatedPrimes_lt.trans
    (exists_mem_associatedPrimes_lt_maximalIdeal_localized_iff p)

/-- The support of `M_𝔭` has dimension at most `0` exactly when no associated prime of `M` lies
strictly inside `𝔭`. -/
public lemma supportDim_localized_le_zero_iff (p : PrimeSpectrum R) :
    Module.supportDim (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl M) ≤ 0 ↔
      ∀ q ∈ associatedPrimes R M, ¬ q < p.asIdeal := by
  rw [← not_lt, zero_lt_supportDim_localized_iff]
  push Not
  rfl

/-- Property `(S₁)` holds at `𝔭`, that is `min{1, dim Supp(M_𝔭)} ≤ depth(M_𝔭)`, exactly when
`𝔭` is not an embedded associated prime of `M`, i.e. when `𝔭 ∈ Ass(M)` forces `𝔭` to be minimal
in `Ass(M)`. -/
private lemma min_one_supportDim_le_depth_iff (p : PrimeSpectrum R) :
    min 1 (Module.supportDim (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl M)) ≤
      (Module.depth (Localization.AtPrime p.asIdeal)
        (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
        (LocalizedModule p.asIdeal.primeCompl M) : WithBot ℕ∞) ↔
      (p.asIdeal ∈ associatedPrimes R M → Minimal (· ∈ associatedPrimes R M) p.asIdeal) := by
  by_cases hd : Module.depth (Localization.AtPrime p.asIdeal)
      (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
      (LocalizedModule p.asIdeal.primeCompl M) = 0
  · have hp : p.asIdeal ∈ associatedPrimes R M := (depth_localized_eq_zero_iff p).mp hd
    have hmin : (p.asIdeal ∈ associatedPrimes R M →
          Minimal (· ∈ associatedPrimes R M) p.asIdeal) ↔
        ¬ ∃ q ∈ associatedPrimes R M, q < p.asIdeal := by
      simp only [hp, true_implies, minimal_iff_forall_lt, true_and, not_exists, not_and]
      exact ⟨fun h q hq hlt => h hlt hq, fun h q hlt hq => h q hq hlt⟩
    rw [hmin, ← zero_lt_supportDim_localized_iff, hd]
    simp [min_le_iff, not_lt]
  · have hp : p.asIdeal ∉ associatedPrimes R M :=
      fun h => hd ((depth_localized_eq_zero_iff p).mpr h)
    simp only [hp, false_implies, iff_true]
    exact le_trans (min_le_left _ _) (by exact_mod_cast Order.one_le_iff_ne_zero.mpr hd)

end

/-- Let `R` be a Noetherian ring and let `M` be a finite `R`-module. Then
`M` has no embedded associated prime — that is, every associated prime of `M` is minimal among
the associated primes of `M` — if and only if `M` has property `(S₁)`: for every prime `𝔭` of
`R` the depth of the `R_𝔭`-module `M_𝔭` along `𝔭R_𝔭` is at least `min{1, dim Supp(M_𝔭)}`, the
inequality being read in `WithBot ℕ∞`. Concretely the right-hand side says that
`depth(M_𝔭) ≥ 1` at every prime `𝔭` with `dim Supp(M_𝔭) ≥ 1`. -/
@[stacks 031Q "Property `(S₁)` is spelled out as the inequality \
  `min{1, dim Supp(M_𝔭)} ≤ depth_{𝔭R_𝔭}(M_𝔭)` of Definition 031P at `k = 1` rather than as \
  `PropertySkModule R M 1`, whose depth and dimension truncate the conventions this statement \
  needs; having no embedded associated prime is spelled out \
  with `Minimal`, as in tag 02M6; and the localizations are the canonical models \
  `Localization.AtPrime` and `LocalizedModule`, indexed by `PrimeSpectrum R` as in Definition \
  0AAH. See the module docstring."]
public theorem forall_minimal_mem_associatedPrimes_iff_min_one_supportDim_le_depth
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M] :
    (∀ p ∈ associatedPrimes R M, Minimal (· ∈ associatedPrimes R M) p) ↔
      ∀ p : PrimeSpectrum R,
        min 1 (supportDim (Localization.AtPrime p.asIdeal)
            (LocalizedModule p.asIdeal.primeCompl M)) ≤
          (depth (Localization.AtPrime p.asIdeal)
            (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
            (LocalizedModule p.asIdeal.primeCompl M) : WithBot ℕ∞) :=
  ⟨fun h1 p => (min_one_supportDim_le_depth_iff p).mpr (h1 p.asIdeal),
    fun h2 p hp => (min_one_supportDim_le_depth_iff ⟨p, hp.isPrime⟩).mp (h2 _) hp⟩

end Module

/-! ### Divisorial quotients of a Noetherian normal domain -/

/-- **The stabiliser of a nonzero ideal is the ring itself.** In a Noetherian integrally closed
domain `R` with fraction field `K`, an element `x` of `K` with `x𝔭 ⊆ 𝔭` for some nonzero ideal
`𝔭` of `R` already lies in `R`. -/
private theorem mem_bot_of_mul_ideal_le {R : Type*} [CommRing R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {p : Ideal R} (hp : p ≠ ⊥) {x : K}
    (hx : ∀ r ∈ p, ∃ s ∈ p, x * algebraMap R K r = algebraMap R K s) :
    x ∈ (⊥ : Subalgebra R K) := by
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff p).mp hp
  have hxi : IsIntegral R x := by
    refine isIntegral_of_smul_mem_submodule (Submodule.map (Algebra.linearMap R K) p)
      ((Submodule.ne_bot_iff _).mpr ⟨algebraMap R K v, ⟨v, hv, rfl⟩, by simpa using hv0⟩)
      ((IsNoetherian.noetherian p).map _) x ?_
    rintro y ⟨r, hr, rfl⟩
    obtain ⟨s, hs, hrs⟩ := hx r hr
    exact ⟨s, hs, by simpa [Algebra.smul_def] using hrs.symm⟩
  obtain ⟨w, hw⟩ := IsIntegrallyClosed.isIntegral_iff.mp hxi
  exact Algebra.mem_bot.mpr ⟨w, hw⟩

/-- **Normality in elementary form.** If `𝔭` is a nonzero ideal of a Noetherian normal domain,
`a ≠ 0`, and `b𝔭 ⊆ a𝔭`, then `a ∣ b`. -/
private theorem dvd_of_mul_ideal_le {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] {p : Ideal R} (hp : p ≠ ⊥) {a b : R} (ha : a ≠ 0)
    (h : ∀ r ∈ p, ∃ s ∈ p, r * b = a * s) : a ∣ b := by
  have hane : algebraMap R (FractionRing R) a ≠ 0 := by simp [ha]
  have key : ∀ r ∈ p, ∃ s ∈ p, algebraMap R (FractionRing R) b / algebraMap R (FractionRing R) a
      * algebraMap R (FractionRing R) r = algebraMap R (FractionRing R) s := by
    intro r hr
    obtain ⟨s, hs, hrs⟩ := h r hr
    have hrs' : algebraMap R (FractionRing R) r * algebraMap R (FractionRing R) b
        = algebraMap R (FractionRing R) a * algebraMap R (FractionRing R) s := by
      rw [← map_mul, ← map_mul, hrs]
    exact ⟨s, hs, by field_simp; linear_combination hrs'⟩
  obtain ⟨w, hw⟩ := Algebra.mem_bot.mp (mem_bot_of_mul_ideal_le hp key)
  refine ⟨w, IsFractionRing.injective R (FractionRing R) ?_⟩
  rw [map_mul, hw]
  field_simp

/-- The height of a prime is the height of the maximal ideal of the localization at it. -/
private theorem height_maximalIdeal_localization {R : Type*} [CommRing R] (p : Ideal R)
    [p.IsPrime] : (IsLocalRing.maximalIdeal (Localization.AtPrime p)).height = p.height := by
  rw [← IsLocalization.height_under p.primeCompl
    (IsLocalRing.maximalIdeal (Localization.AtPrime p)), Localization.AtPrime.under_maximalIdeal]

/-- **Krull's principal ideal theorem, localized.** A prime `𝔭` of a Noetherian ring which becomes
principal after inverting the complement of `𝔭` has height at most `1`: it suffices that some
`y ∈ 𝔭` divide every `r ∈ 𝔭` up to a factor `d ∉ 𝔭`. -/
private theorem height_le_one_of_forall_mul_eq {R : Type*} [CommRing R] [IsNoetherianRing R]
    {p : Ideal R} [p.IsPrime] {y : R} (hy : y ∈ p)
    (h : ∀ r ∈ p, ∃ d ∉ p, ∃ e : R, r * d = y * e) : p.height ≤ 1 := by
  have hmax : IsLocalRing.maximalIdeal (Localization.AtPrime p)
      = Ideal.span {algebraMap R (Localization.AtPrime p) y} := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    refine le_antisymm ?_ (Ideal.span_le.mpr (by simpa using Ideal.mem_map_of_mem _ hy))
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    obtain ⟨d, hd, e, hre⟩ := h r hr
    obtain ⟨u, hu⟩ := IsLocalization.map_units (Localization.AtPrime p) (⟨d, hd⟩ : p.primeCompl)
    simp only [Ideal.mem_comap, Ideal.mem_span_singleton]
    refine ⟨algebraMap R (Localization.AtPrime p) e * (↑u⁻¹ : Localization.AtPrime p), ?_⟩
    rw [← mul_assoc]
    refine (Units.eq_mul_inv_iff_mul_eq u).mpr ?_
    rw [hu, ← map_mul, ← map_mul]
    exact congrArg _ hre
  have : (IsLocalRing.maximalIdeal (Localization.AtPrime p)).IsPrincipal := ⟨_, hmax⟩
  rw [← height_maximalIdeal_localization p]
  exact Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes_of_isLocalRing
    (IsLocalRing.maximalIdeal (Localization.AtPrime p))
    (by rw [Ideal.minimalPrimes_eq_subsingleton_self]; rfl)

/-- In `R ⧸ aR`, the colon ideal `(0 : b)` consists of the `r : R` with `a ∣ r * b`. -/
private theorem mem_colon_singleton_quotient_iff {R : Type*} [CommRing R] {a b : R} {r : R} :
    r ∈ (⊥ : Submodule R (R ⧸ Ideal.span {a})).colon {Ideal.Quotient.mk (Ideal.span {a}) b} ↔
      a ∣ r * b := by
  rw [Submodule.mem_colon_singleton, Submodule.mem_bot,
    show r • Ideal.Quotient.mk (Ideal.span {a}) b = Ideal.Quotient.mk (Ideal.span {a}) (r * b)
      from rfl,
    Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]

/-- An associated prime of `R ⧸ aR` is a colon ideal `(aR : b)` with `b ∉ aR`: it consists of the
`r : R` with `a ∣ r * b`. -/
private theorem exists_forall_mem_iff_dvd_mul {R : Type*} [CommRing R] [IsNoetherianRing R]
    {a : R} {p : Ideal R} (hp : p ∈ associatedPrimes R (R ⧸ Ideal.span {a})) :
    ∃ b : R, ¬ a ∣ b ∧ ∀ r : R, r ∈ p ↔ a ∣ r * b := by
  obtain ⟨-, x0, hx0⟩ := isAssociatedPrime_iff.mp hp
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x0
  have hmem : ∀ r : R, r ∈ p ↔ a ∣ r * b := fun r => by
    rw [hx0, mem_colon_singleton_quotient_iff]
  exact ⟨b, fun hab => hp.isPrime.ne_top ((Ideal.eq_top_iff_one p).mpr
    ((hmem 1).mpr (by simpa using hab))), hmem⟩

/-- In a Noetherian normal domain `R`, every associated prime of `R/aR` with `a ≠ 0` has
height `1`. -/
private theorem height_eq_one_of_mem_associatedPrimes {R : Type*} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] {a : R} (ha : a ≠ 0) {p : Ideal R}
    (hp : p ∈ associatedPrimes R (R ⧸ Ideal.span {a})) : p.height = 1 := by
  have hpp : p.IsPrime := hp.isPrime
  obtain ⟨b, hab, hmem⟩ := exists_forall_mem_iff_dvd_mul hp
  have hap : a ∈ p := (hmem a).mpr (dvd_mul_right a b)
  have hpne : p ≠ ⊥ := fun h => ha (by simpa [h] using hap)
  refine le_antisymm ?_ ?_
  · obtain ⟨y, hy, d, hd, hyd⟩ : ∃ y ∈ p, ∃ d ∉ p, y * b = a * d := by
      by_contra hcon
      refine hab (dvd_of_mul_ideal_le hpne ha fun r hr => ?_)
      obtain ⟨e, he⟩ := (hmem r).mp hr
      exact ⟨e, not_not.mp fun hen => hcon ⟨r, hr, e, hen, he⟩, he⟩
    refine height_le_one_of_forall_mul_eq hy fun r hr => ⟨d, hd, ?_⟩
    obtain ⟨e, he⟩ := (hmem r).mp hr
    exact ⟨e, mul_left_cancel₀ ha (by linear_combination y * he - r * hyd)⟩
  · rwa [Order.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]

/-- A set of primes all of whose members have height `1` has no strict inclusions: every member is
minimal in it, and of course of height `1`. -/
private theorem minimal_and_height_eq_one {R : Type*} [CommRing R] {S : Set (Ideal R)}
    (hS : ∀ q ∈ S, q.IsPrime ∧ q.height = 1) {p : Ideal R} (hp : p ∈ S) :
    Minimal (· ∈ S) p ∧ p.height = 1 := by
  obtain ⟨hpp, hph⟩ := hS p hp
  refine ⟨⟨hp, fun q hq hqp => (hqp.eq_or_lt.resolve_right fun hlt => ?_).ge⟩, hph⟩
  obtain ⟨hqp', hqh⟩ := hS q hq
  have hle := Ideal.height_add_one_le_of_lt_of_isPrime hlt
  rw [hqh, hph, one_add_one_eq_two] at hle
  exact absurd hle (by decide)

/-- The ideal `R ∩ xR` cut out by `x = n / d` in the fraction field, `d ≠ 0`: an element `r` of
`R` lies in it exactly when `n ∣ r * d`. -/
private theorem mem_comap_span_singleton_div {R : Type*} [CommRing R] (K : Type*)
    [Field K] [Algebra R K] [IsFractionRing R K] {n d : R} (hd : d ≠ 0) (r : R) :
    r ∈ ((Submodule.span R {algebraMap R K n / algebraMap R K d}).comap
      (Algebra.linearMap R K) : Ideal R) ↔ n ∣ r * d := by
  have hdne : algebraMap R K d ≠ 0 := by simp [hd]
  simp only [Submodule.mem_comap, Algebra.linearMap_apply, Submodule.mem_span_singleton,
    Algebra.smul_def]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, IsFractionRing.injective R K ?_⟩
    field_simp at hc
    rw [map_mul, map_mul]
    linear_combination -hc
  · rintro ⟨c, hc⟩
    have hc' : algebraMap R K r * algebraMap R K d = algebraMap R K n * algebraMap R K c := by
      rw [← map_mul, ← map_mul, hc]
    exact ⟨c, by field_simp; linear_combination -hc'⟩

/-- An element of the fraction field whose denominators can be chosen outside every prime of
height `1` lies in `R`. -/
private theorem mem_bot_of_forall_height_eq_one {R : Type*} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] (K : Type*) [Field K] [Algebra R K]
    [IsFractionRing R K] {z : K}
    (hz : ∀ q : Ideal R, q.IsPrime → q.height = 1 →
      ∃ m s : R, s ∉ q ∧ z * algebraMap R K s = algebraMap R K m) :
    z ∈ (⊥ : Subalgebra R K) := by
  by_contra hnot
  obtain ⟨n, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := R) z
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have hdne : algebraMap R K d ≠ 0 := by simp [hd0]
  have hmk : Ideal.Quotient.mk (Ideal.span {d}) n ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    rintro ⟨c, rfl⟩
    exact hnot (Algebra.mem_bot.mpr ⟨c, by rw [map_mul]; field_simp⟩)
  obtain ⟨P, hP, hPle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing R _ hmk
  obtain ⟨m, s, hs, hzs⟩ := hz P hP.isPrime (height_eq_one_of_mem_associatedPrimes hd0 hP)
  refine hs (hPle ?_)
  rw [mem_colon_singleton_quotient_iff]
  refine ⟨m, IsFractionRing.injective R K ?_⟩
  rw [map_mul, map_mul]
  field_simp at hzs
  linear_combination hzs

/-- Let `R` be a Noetherian normal domain with fraction field `K`. Then
(1) for every nonzero `a : R` each associated prime of `R/aR` is minimal among the associated
primes of `R/aR` — that is, `R/aR` has no embedded primes — and has height `1`;
(2) `R` is the intersection, inside `K`, of the subalgebras `R_𝔭` over the primes `𝔭` of height
`1`; and (3) the same as (1) for the ideal `R ∩ xR` attached to a nonzero `x : K`. -/
@[stacks 031T "A normal domain is `IsDomain` plus `IsIntegrallyClosed`, as in Definition 0309; \
  having no embedded primes is spelled with `Minimal`, as in tags 02M6 and 031Q; item (2) is the \
  equality `⨅ 𝔭, R_𝔭 = ⊥` of `R`-subalgebras of `K`, as in \
  `IsDedekindDomain.HeightOneSpectrum.iInf_localization_eq_bot`; and `R ∩ xR` is the pullback of \
  `xR ⊆ K` along `Algebra.linearMap R K`. See the module docstring.",
  ega "0 23.2.9" "A normal (A = A')", ega "IV 7.8.3" "(viii), special case"]
public theorem associatedPrimes_minimal_and_height_eq_one_and_iInf_localization_eq_bot
    {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] :
    (∀ a : R, a ≠ 0 → ∀ p ∈ associatedPrimes R (R ⧸ Ideal.span {a}),
        Minimal (· ∈ associatedPrimes R (R ⧸ Ideal.span {a})) p ∧ p.height = 1) ∧
      ((⨅ p : PrimeSpectrum R, ⨅ _ : p.asIdeal.height = 1,
          Localization.subalgebra.ofField K _ p.asIdeal.primeCompl_le_nonZeroDivisors) = ⊥) ∧
      (∀ x : K, x ≠ 0 →
        ∀ p ∈ associatedPrimes R
            (R ⧸ ((Submodule.span R {x}).comap (Algebra.linearMap R K) : Ideal R)),
          Minimal (· ∈ associatedPrimes R
              (R ⧸ ((Submodule.span R {x}).comap (Algebra.linearMap R K) : Ideal R))) p ∧
            p.height = 1) := by
  refine ⟨fun a ha p hp => minimal_and_height_eq_one (fun q hq =>
      ⟨hq.isPrime, height_eq_one_of_mem_associatedPrimes ha hq⟩) hp, ?_, ?_⟩
  · refine bot_unique fun z hz => mem_bot_of_forall_height_eq_one K fun P hPp hPh => ?_
    obtain ⟨m, s, hs, hzs⟩ := Algebra.mem_iInf.mp (Algebra.mem_iInf.mp hz ⟨P, hPp⟩) hPh
    have hsne : algebraMap R K s ≠ 0 := by
      simp [show s ≠ 0 from fun h => hs (h ▸ P.zero_mem)]
    exact ⟨m, s, hs, by rw [hzs]; field_simp⟩
  · intro x hx p hp
    obtain ⟨n, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := R) x
    have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
    have hn0 : n ≠ 0 := by rintro rfl; simp at hx
    have hker : LinearMap.ker ((Submodule.mkQ (Ideal.span {n})).comp (LinearMap.mulRight R d))
        = ((Submodule.span R {algebraMap R K n / algebraMap R K d}).comap
          (Algebra.linearMap R K) : Ideal R) := by
      ext r
      simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply,
        LinearMap.mulRight_apply, Submodule.mkQ_apply, Ideal.Quotient.mk_eq_mk,
        Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton,
        mem_comap_span_singleton_div K hd0 r]
    have hinj : Function.Injective (((Submodule.span R {algebraMap R K n / algebraMap R K d}).comap
        (Algebra.linearMap R K) : Ideal R).liftQ _ hker.ge) :=
      LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot _ _ _ hker.le)
    exact minimal_and_height_eq_one (fun q hq => ⟨hq.isPrime,
      height_eq_one_of_mem_associatedPrimes hn0
        (associatedPrimes.subset_of_injective hinj hq)⟩) hp

end
