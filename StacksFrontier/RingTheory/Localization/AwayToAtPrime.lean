module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Noetherian.Defs
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A localization at an element embedding into a localization at a prime

Let `R` be a commutative ring with unit and `p ⊂ R` a prime ideal. For `f : R`
the localization `R_f` is the localization of `R` at the multiplicative submonoid
of powers of `f`, and `R_p` is the localization at the complement `R \ p`.

When `f ∉ p`, every power of `f` is a unit in `R_p`, since `p` is prime, so the
universal property of localization factors `R → R_p` uniquely through `R → R_f`
and yields a canonical ring homomorphism `R_f → R_p` sending `a / fⁿ` to
`a / fⁿ`. Injectivity of that map says precisely that its kernel is trivial: if
`a / fⁿ` maps to `0` in `R_p` then `a / fⁿ` is already `0` in `R_f`.

The result is that there exists `f ∉ p` making `R_f → R_p` injective in each of
three independent cases, rendered here as three separate statements.

1. `R` is an integral domain. Here one may take `f = 1`: over a domain the map
   `R → R_p` is already injective, because `R \ p` contains no zero divisor, and
   `R_1 = R`.
2. `R` is Noetherian.
3. `R` is reduced with finitely many minimal prime ideals.

Here `R_f` is modelled as `Localization.Away f` and `R_p` as
`Localization.AtPrime p`.

Case (3) is stated below under the weaker hypothesis that only the minimal
primes *not* contained in `p` are finite in number; that is all its proof uses.
The construction of the map itself needs only a commutative semiring, while all
three injectivity statements need a commutative ring.
-/

@[expose] public section

/-- The canonical ring homomorphism `R_f → R_p` for `f ∉ p`.

We model `R_f` as `Localization.Away f` and `R_p` as `Localization.AtPrime p`.
The map is induced by the identity `R →+* R` via the universal property of
localization (`IsLocalization.map`), using that the powers of `f` land in the
prime complement `p.primeCompl` (i.e. they are units in `R_p`). Concretely it
sends `a / f^n` to `a / f^n`. -/
@[ega "0 1.5.1" "special case"]
noncomputable def localizationAwayToAtPrime {R : Type*} [CommSemiring R] (f : R) (p : Ideal R)
    [p.IsPrime] (hf : f ∉ p) : Localization.Away f →+* Localization.AtPrime p :=
  IsLocalization.map (M := Submonoid.powers f) (T := p.primeCompl)
    (Localization.AtPrime p) (RingHom.id R)
    (Submonoid.powers_le.mpr hf)

/-- The canonical map `R_f → R_p` is injective exactly when every element killed in
`R_p` is annihilated by a power of `f`. -/
theorem localizationAwayToAtPrime_injective_iff {R : Type*} [CommRing R] {f : R} {p : Ideal R}
    [p.IsPrime] (hf : f ∉ p) :
    Function.Injective (localizationAwayToAtPrime f p hf) ↔
      ∀ a : R, algebraMap R (Localization.AtPrime p) a = 0 → ∃ n : ℕ, f ^ n * a = 0 := by
  have key (a : R) : localizationAwayToAtPrime f p hf (algebraMap R (Localization.Away f) a) =
      algebraMap R (Localization.AtPrime p) a := by
    rw [localizationAwayToAtPrime, IsLocalization.map_eq, RingHom.id_apply]
  refine ⟨fun hinj a ha => ?_, fun H => IsLocalization.injective_of_map_algebraMap_zero
    (M := Submonoid.powers f) _ _ fun a ha => ?_⟩
  · rw [← key, ← map_zero (localizationAwayToAtPrime f p hf)] at ha
    obtain ⟨⟨_, n, rfl⟩, hn⟩ :=
      (IsLocalization.map_eq_zero_iff (Submonoid.powers f) _ a).1 (hinj ha)
    exact ⟨n, hn⟩
  · obtain ⟨n, hn⟩ := H a (by rwa [← key])
    exact (IsLocalization.map_eq_zero_iff (Submonoid.powers f) _ a).2
      ⟨⟨f ^ n, pow_mem (Submonoid.mem_powers f) n⟩, hn⟩

/-- An element of `R` maps to zero in `R_p` iff it is killed by some element outside `p`. -/
private theorem algebraMap_atPrime_eq_zero_iff {R : Type*} [CommRing R] {p : Ideal R}
    [p.IsPrime] (a : R) :
    algebraMap R (Localization.AtPrime p) a = 0 ↔ ∃ s : R, s ∉ p ∧ s * a = 0 :=
  (IsLocalization.map_eq_zero_iff p.primeCompl _ a).trans
    ⟨fun ⟨m, hm⟩ => ⟨m, m.2, hm⟩, fun ⟨s, hs, hsa⟩ => ⟨⟨s, hs⟩, hsa⟩⟩

/-- General injectivity criterion: if every element annihilated by some element
outside `p` is also annihilated by a power of `f`, then the canonical map
`R_f → R_p` is injective. -/
theorem injective_localizationAwayToAtPrime_of_ann
    {R : Type*} [CommRing R] (f : R) (p : Ideal R) [p.IsPrime] (hf : f ∉ p)
    (H : ∀ a : R, (∃ s : R, s ∉ p ∧ s * a = 0) → ∃ n : ℕ, f ^ n * a = 0) :
    Function.Injective (localizationAwayToAtPrime f p hf) := by
  exact (localizationAwayToAtPrime_injective_iff hf).2 fun a ha =>
    H a ((algebraMap_atPrime_eq_zero_iff a).1 ha)

/-- Case (1): `R` an integral domain. There exists `f ∉ p` such that the
canonical map `R_f → R_p` is injective. (One may take `f = 1`.) -/
@[stacks 0BX1 "(1)"]
theorem exists_injective_localizationAwayToAtPrime_of_isDomain
    {R : Type*} [CommRing R] [IsDomain R] (p : Ideal R) [p.IsPrime] :
    ∃ f : R, ∃ hf : f ∉ p, Function.Injective (localizationAwayToAtPrime f p hf) := by
  have hf : (1 : R) ∉ p := (Ideal.ne_top_iff_one p).mp ‹p.IsPrime›.ne_top
  exact ⟨1, hf, injective_localizationAwayToAtPrime_of_ann 1 p hf fun a ⟨s, hs, hsa⟩ =>
    ⟨0, by simpa using (mul_eq_zero.mp hsa).resolve_left fun h => hs (h ▸ p.zero_mem)⟩⟩

/-- Case (2): `R` Noetherian. There exists `f ∉ p` such that the canonical
map `R_f → R_p` is injective. -/
@[stacks 0BX1 "(2)"]
theorem exists_injective_localizationAwayToAtPrime_of_isNoetherianRing
    {R : Type*} [CommRing R] [IsNoetherianRing R] (p : Ideal R) [p.IsPrime] :
    ∃ f : R, ∃ hf : f ∉ p, Function.Injective (localizationAwayToAtPrime f p hf) := by
  classical
  set I : Ideal R := RingHom.ker (algebraMap R (Localization.AtPrime p))
  have hmem : ∀ a : R, a ∈ I ↔ ∃ s : R, s ∉ p ∧ s * a = 0 := fun a =>
    (RingHom.mem_ker).trans (algebraMap_atPrime_eq_zero_iff a)
  obtain ⟨s, hs⟩ := IsNoetherian.noetherian I
  choose! t ht_mem ht_ann using fun g (hg : g ∈ I) => (hmem g).mp hg
  set f : R := ∏ g ∈ s, t g with hf
  have hgI : ∀ g ∈ s, g ∈ I := fun g hgs => by rw [← hs]; exact Ideal.subset_span hgs
  have hfann : ∀ g ∈ s, f * g = 0 := fun g hgs => by
    rw [hf, ← Finset.mul_prod_erase s t hgs, mul_right_comm, ht_ann g (hgI g hgs), zero_mul]
  have hfp : f ∉ p := fun h => by
    obtain ⟨g, hgs, hgp⟩ := Ideal.IsPrime.prod_mem_iff.1 h
    exact ht_mem g (hgI g hgs) hgp
  refine ⟨f, hfp, injective_localizationAwayToAtPrime_of_ann f p hfp ?_⟩
  intro a ⟨sa, hsa, hsaa⟩
  refine ⟨1, ?_⟩
  rw [pow_one]
  have haI : a ∈ I := (hmem a).mpr ⟨sa, hsa, hsaa⟩
  rw [← hs] at haI
  refine Submodule.span_induction hfann (mul_zero f)
    (fun x y _ _ hx hy => by rw [mul_add, hx, hy, add_zero])
    (fun c x _ hx => by rw [smul_eq_mul, mul_left_comm, hx, mul_zero]) haI

/-- Case (3): `R` reduced with finitely many minimal primes not contained in `p`.
There exists `f ∉ p` such that the canonical map `R_f → R_p` is injective.

The hypothesis is weaker than the `(minimalPrimes R).Finite` of 0BX1 (3), which
implies it by `Set.Finite.subset _ (Set.sep_subset _ _)`. -/
@[stacks 0BX1 "(3)"]
theorem exists_injective_localizationAwayToAtPrime_of_isReduced_finite_minimalPrimes
    {R : Type*} [CommRing R] [IsReduced R] (p : Ideal R) [p.IsPrime]
    (hfin : {q ∈ minimalPrimes R | ¬ q ≤ p}.Finite) :
    ∃ f : R, ∃ hf : f ∉ p, Function.Injective (localizationAwayToAtPrime f p hf) := by
  obtain ⟨f, hfT, hfp⟩ : ∃ f ∈ hfin.toFinset.inf id, f ∉ p := by
    by_contra! H
    obtain ⟨q, hq, hqp⟩ := (Ideal.IsPrime.inf_le' ‹p.IsPrime›).1 H
    exact (hfin.mem_toFinset.1 hq).2 hqp
  refine ⟨f, hfp, (localizationAwayToAtPrime_injective_iff hfp).2 fun a ha => ⟨1, ?_⟩⟩
  obtain ⟨s, hs, hsa⟩ := (algebraMap_atPrime_eq_zero_iff a).1 ha
  have : f ^ 1 * a ∈ sInf (⊥ : Ideal R).minimalPrimes := Ideal.mem_sInf.2 fun q hq => by
    have hq' : q.IsPrime := Ideal.IsMinimalPrime.isPrime hq
    by_cases hqp : q ≤ p
    · exact Ideal.mul_mem_left q _ ((hq'.mem_or_mem (hsa ▸ q.zero_mem)).resolve_left
        fun h => hs (hqp h))
    · exact Ideal.mul_mem_right _ q (q.pow_mem_of_mem (Finset.inf_le (f := id)
        (hfin.mem_toFinset.2 ⟨hq, hqp⟩) hfT) 1 one_pos)
  rwa [Ideal.sInf_minimalPrimes, Ideal.radical_bot_of_isReduced, Ideal.mem_bot] at this
