module

public import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
public import Mathlib.RingTheory.Ideal.UFD
public import Mathlib.RingTheory.Lasker
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.Embedded

/-!
# Codimension-one ideals in a Noetherian unique factorization domain

An ideal of a Noetherian unique factorization domain is principal as soon as its quotient has
no embedded primes and every minimal prime over it has height one.

## Main results

* `Ideal.isPrincipal_of_noEmbeddedAssociatedPrimes_of_minimalPrimes_height_eq_one`: such an
  ideal has a single generator.

## Implementation notes

The absence of embedded primes is expressed for the quotient ring as a module over itself, and
the conclusion uses `Ideal.IsPrincipal`, which is the existence of a generator. The proof takes
a minimal primary decomposition of the ideal, shows that each associated prime is minimal over
it and hence principal of height one, deduces that each primary component is a power of the
corresponding generator, and finally that a finite infimum of principal ideals in a GCD monoid
is principal.

## References

* [Stacks Project, Tag 0BXI](https://stacks.math.columbia.edu/tag/0BXI)
-/

@[expose] public section

namespace Ideal

private theorem associatedPrime_map_quotient {R : Type*} [CommRing R] {I p : Ideal R}
    (hp : p ∈ associatedPrimes R (R ⧸ I)) :
    IsAssociatedPrime (p.map (Ideal.Quotient.mk I)) (R ⧸ I) := by
  classical
  obtain ⟨hp', x, hx⟩ := hp
  let f : R →+* R ⧸ I := Ideal.Quotient.mk I
  let cR : Ideal R := Submodule.colon (⊥ : Submodule R (R ⧸ I)) {x}
  let cQ : Ideal (R ⧸ I) := Submodule.colon (⊥ : Submodule (R ⧸ I) (R ⧸ I)) {x}
  have hp_eq : p = cR.radical := by simpa [cR, Submodule.colon] using hx
  have hc : Ideal.comap f cQ = cR := by
    ext r
    change f r ∈ (⊥ : Submodule (R ⧸ I) (R ⧸ I)).colon {x} ↔
      r ∈ (⊥ : Submodule R (R ⧸ I)).colon {x}
    simp only [Submodule.mem_colon_singleton]
    rfl
  have hIle : I ≤ cR := fun r hr ↦ hc.le (by
    rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hr]
    exact cQ.zero_mem)
  have hprime : (p.map f).IsPrime := Ideal.map_isPrime_of_surjective f.surjective (by
    rw [Ideal.mk_ker]
    exact hIle.trans (Ideal.le_radical.trans_eq hp_eq.symm))
  refine ⟨hprime, x, ?_⟩
  calc
    p.map f = (Ideal.comap f cQ.radical).map f := by rw [Ideal.comap_radical, hc, hp_eq]
    _ = cQ.radical := Ideal.map_comap_of_surjective f f.surjective _

private theorem colon_quotient_mk {R : Type*} [CommRing R] (I : Ideal R) (x : R) :
    (⊥ : Submodule R (R ⧸ I)).colon {Ideal.Quotient.mk I x} = I.colon {x} := by
  ext r
  simp only [Submodule.mem_colon_singleton, Algebra.smul_def, Ideal.Quotient.algebraMap_eq]
  rw [← map_mul]
  exact Ideal.Quotient.eq_zero_iff_mem

private theorem associatedPrimes_ideal_quotient_iff {R : Type*} [CommRing R] (I p : Ideal R) :
    p ∈ I.associatedPrimes ↔ p ∈ associatedPrimes R (R ⧸ I) := by
  rw [Submodule.AssociatePrimes.mem_iff, AssociatedPrimes.mem_iff]
  constructor
  · rintro ⟨hp, x, hx⟩
    refine ⟨hp, Ideal.Quotient.mk I x, ?_⟩
    simpa [colon_quotient_mk] using hx
  · rintro ⟨hp, y, hy⟩
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨hp, x, ?_⟩
    simpa [colon_quotient_mk] using hy

private theorem primary_eq_span_pow {R : Type*} [CommRing R] [IsDomain R]
    {q p : Ideal R} {π : R} (hq : q.IsPrimary) (hqp : q.radical = p)
    (hp : p = Ideal.span ({π} : Set R)) :
    ∃ n : ℕ, q = Ideal.span ({π ^ n} : Set R) := by
  classical
  have hpow : ∃ n : ℕ, π ^ n ∈ q := Ideal.mem_radical_iff.mp (by
    rw [hqp, hp]
    exact Ideal.mem_span_singleton_self _)
  let n₀ := Nat.find hpow
  have hn₀ : π ^ n₀ ∈ q := Nat.find_spec hpow
  have hmin (k : ℕ) (hk : k < n₀) : π ^ k ∉ q :=
    fun hkq ↦ (Nat.not_le_of_gt hk) (Nat.find_min' hpow hkq)
  have hdiv (x : R) (hx : x ∈ q) : ∃ y, x = π ^ n₀ * y := by
    have hstep : ∀ k ≤ n₀, ∃ y, x = π ^ k * y := by
      intro k hk
      induction k with
      | zero => exact ⟨x, by simp⟩
      | succ k ih =>
          obtain ⟨y, rfl⟩ := ih (by omega)
          have hy : y ∈ q.radical := by
            have hmul : y • (π ^ k) ∈ q := by simpa [Algebra.smul_def, mul_comm] using hx
            have hy' : y ∈ (q.colon Set.univ).radical :=
              (hq.mem_or_mem (r := y) (m := π ^ k) hmul).resolve_left (hmin k (by omega))
            simpa [Submodule.colon_univ] using hy'
          rw [hqp, hp, Ideal.mem_span_singleton] at hy
          obtain ⟨z, rfl⟩ := hy
          exact ⟨z, by ring⟩
    exact hstep n₀ le_rfl
  refine ⟨n₀, le_antisymm ?_ ((Ideal.span_singleton_le_iff_mem q).2 hn₀)⟩
  intro x hx
  obtain ⟨y, hxy⟩ := hdiv x hx
  exact Ideal.mem_span_singleton.mpr ⟨y, hxy⟩

private theorem inf_principal_of_principal {R : Type*} [CommRing R] [GCDMonoid R]
    (J K : Ideal R) (hJ : J.IsPrincipal) (hK : K.IsPrincipal) : (J ⊓ K).IsPrincipal := by
  obtain ⟨x, hx⟩ := hJ.principal
  obtain ⟨y, hy⟩ := hK.principal
  refine ⟨GCDMonoid.lcm x y, ?_⟩
  rw [hx, hy]
  ext z
  simp only [Ideal.mem_inf, Ideal.mem_span_singleton, lcm_dvd_iff]

private theorem finset_inf_principal {R : Type*} [CommRing R] [GCDMonoid R]
    {α : Type*} (s : Finset α) (f : α → Ideal R)
    (h : ∀ i ∈ s, (f i).IsPrincipal) : (s.inf f).IsPrincipal := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (show (⊤ : Ideal R).IsPrincipal from ⟨1, by simp⟩)
  | @insert a s ha ih =>
      rw [Finset.inf_insert]
      exact inf_principal_of_principal _ _ (h a (Finset.mem_insert_self a s))
        (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi))

/-- An ideal of pure height one with no embedded primes in a Noetherian UFD is principal. -/
@[stacks 0BXI, ega "IV 21.12.9" "special case"]
theorem isPrincipal_of_noEmbeddedAssociatedPrimes_of_minimalPrimes_height_eq_one
    {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [UniqueFactorizationMonoid R] (I : Ideal R)
    (hI : HasNoEmbeddedAssociatedPrimes (R ⧸ I) (R ⧸ I))
    (hheight : ∀ p ∈ I.minimalPrimes, p.height = 1) :
    I.IsPrincipal := by
  classical
  have hmin : I.minimalPrimes ⊆ associatedPrimes R (R ⧸ I) := by
    simpa [Ideal.annihilator_quotient] using
      (Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes R (R ⧸ I))
  obtain ⟨t, hdec⟩ := Submodule.IsLasker.exists_isMinimalPrimaryDecomposition
    (Submodule.isLasker R R) I
  let f : R →+* (R ⧸ I) := Ideal.Quotient.mk I
  have hassoc_contains : ∀ p ∈ associatedPrimes R (R ⧸ I), I ≤ p := by
    intro p hp
    rw [← Ideal.annihilator_quotient (I := I), ← Submodule.annihilator_top]
    exact IsAssociatedPrime.annihilator_le (AssociatedPrimes.mem_iff.mp hp)
  have hassoc_min : ∀ p ∈ associatedPrimes R (R ⧸ I), p ∈ I.minimalPrimes := by
    intro p hp
    obtain ⟨m, hm, hmp⟩ := @Ideal.exists_minimalPrimes_le R _ I p
      (AssociatedPrimes.mem_iff.mp hp).isPrime (hassoc_contains p hp)
    have hmap : (m.map f) = (p.map f) :=
      hI (associatedPrime_map_quotient hp) (associatedPrime_map_quotient (hmin hm))
        (Ideal.map_mono hmp)
    have hmpEq : m = p := by
      have hc := congrArg (Ideal.comap f) hmap
      rwa [Ideal.comap_map_of_surjective f f.surjective m,
        Ideal.comap_map_of_surjective f f.surjective p,
        ← RingHom.ker_eq_comap_bot, Ideal.mk_ker,
        sup_of_le_left hm.1.2, sup_of_le_left (hassoc_contains p hp)] at hc
    exact hmpEq ▸ hm
  have hpri : ∀ q ∈ t, q.IsPrincipal := by
    intro q hq
    let qi : Ideal R := q
    let p : Ideal R := qi.radical
    have hqI : qi.IsPrimary := hdec.primary hq
    have hp : p.IsPrime := Ideal.isPrime_radical hqI
    have hpAssoc : p ∈ associatedPrimes R (R ⧸ I) :=
      (associatedPrimes_ideal_quotient_iff I p).1 (by
        simpa [p, Submodule.colon_univ] using hdec.mem_associatedPrimes hq)
    have hph : p.height = 1 := hheight p (hassoc_min p hpAssoc)
    obtain ⟨π, hπ⟩ := @UniqueFactorizationMonoid.isPrincipal_of_height_eq_one
      R _ _ _ p hp hph
    obtain ⟨n, hn⟩ := primary_eq_span_pow hqI rfl (by simpa using hπ)
    exact ⟨π ^ n, hn⟩
  rw [← hdec.inf_eq]
  exact @finset_inf_principal R _ (UniqueFactorizationMonoid.toGCDMonoid R) _ t id hpri

end Ideal
