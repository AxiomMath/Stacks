module

public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.RingTheory.LocalProperties.Submodule
public import StacksFrontier.RingTheory.Flat.NonZeroDivisors

/-!
# Total rings of fractions glue along a cover by principal opens

Let `A` be a commutative ring with finitely many minimal primes, every zerodivisor of which lies
in one of them, and let `C` be an `A`-algebra.  Let `s ⊆ A` generate the unit ideal.  If for every
`r ∈ s` the localization `C_r` is the total ring of fractions of `A_r`, then `C` is the total ring
of fractions of `A`.

Being a unit and being zero are local on `Spec A`, which gives the first and the last axiom of a
localization.  For the second, the elements of `A` which carry a given `c ∈ C` into the image of
`A` form an ideal `J`; locally `J` contains a nonzerodivisor, so `J` lies in no minimal prime of
`A`, and by prime avoidance `J` is not contained in the union of the minimal primes, which by
hypothesis contains all zerodivisors.

## Main results

* `IsLocalization.isUnit_of_isUnit_algebraMap_away`: an element of `C` which becomes a unit in
  every `C_r` is a unit.
* `IsLocalization.nonZeroDivisors_of_away_span`: the gluing statement.
-/

@[expose] public section

open scoped nonZeroDivisors

/-- An ideal consisting of zerodivisors, in a ring with finitely many minimal primes containing
all zerodivisors, lies in a minimal prime. -/
theorem Ideal.exists_mem_minimalPrimes_le_of_forall_notMem_nonZeroDivisors {A : Type*}
    [CommRing A] (hfin : (minimalPrimes A).Finite)
    (hzd : ∀ a : A, a ∉ A⁰ → ∃ q ∈ minimalPrimes A, a ∈ q) (J : Ideal A)
    (hJ : ∀ a ∈ J, a ∉ A⁰) : ∃ p ∈ minimalPrimes A, J ≤ p := by
  classical
  have hsub : (J : Set A) ⊆ ⋃ q ∈ hfin.toFinset, (q : Set A) := fun a ha => by
    obtain ⟨q, hq, haq⟩ := hzd a (hJ a ha)
    exact Set.mem_biUnion (hfin.mem_toFinset.mpr hq) haq
  obtain ⟨i, -, -⟩ := Set.mem_iUnion₂.mp (hsub J.zero_mem)
  obtain ⟨p, hpmem, hle⟩ := (Ideal.subset_union_prime i i
    (fun j hj _ _ => (hfin.mem_toFinset.mp hj).1.1)).mp (by simpa using hsub)
  exact ⟨p, hfin.mem_toFinset.mp hpmem, hle⟩

namespace IsLocalization

/-- A minimal prime disjoint from `M` maps to a minimal prime of the localization at `M`. -/
theorem map_mem_minimalPrimes_of_disjoint {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (M : Submonoid A) [IsLocalization M B] {p : Ideal A} (hp : p ∈ minimalPrimes A)
    (hdisj : Disjoint (M : Set A) p) : p.map (algebraMap A B) ∈ minimalPrimes B := by
  have hmin := IsLocalization.minimalPrimes_map M B (⊥ : Ideal A)
  rw [Ideal.map_bot] at hmin
  change p.map (algebraMap A B) ∈ (⊥ : Ideal B).minimalPrimes
  rw [hmin]
  change (p.map (algebraMap A B)).comap (algebraMap A B) ∈ minimalPrimes A
  have hu := IsLocalization.under_map_of_isPrime_disjoint M B hp.1.1 hdisj
  rw [Ideal.under] at hu
  rw [hu]
  exact hp

/-- Elements with equal image in the localization at the powers of `r` agree after multiplying
by a power of `r`. -/
private theorem exists_pow_mul_eq_of_algebraMap_eq {R D : Type*} [CommRing R] [CommRing D]
    [Algebra R D] (r : R) [IsLocalization.Away r D] {x y : R}
    (h : algebraMap R D x = algebraMap R D y) : ∃ m : ℕ, r ^ m * x = r ^ m * y := by
  obtain ⟨⟨_, m, rfl⟩, hm⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers r) D).mp h
  exact ⟨m, hm⟩

variable {A C : Type*} [CommRing A] [CommRing C] [Algebra A C]
  (s : Set A) (hs : Ideal.span s = ⊤)
  (Aₛ : s → Type*) [∀ r, CommRing (Aₛ r)] [∀ r, Algebra A (Aₛ r)]
  [∀ r : s, IsLocalization.Away (r : A) (Aₛ r)]
  (Cₛ : s → Type*) [∀ r, CommRing (Cₛ r)] [∀ r, Algebra C (Cₛ r)]
  [∀ r : s, IsLocalization.Away (algebraMap A C r) (Cₛ r)]

include hs in
/-- An element of an `A`-algebra `C` which becomes a unit in `C_r` for every `r` in a set `s`
generating the unit ideal of `A` is a unit. -/
theorem isUnit_of_isUnit_algebraMap_away (x : C)
    (hx : ∀ r : s, IsUnit (algebraMap C (Cₛ r) x)) : IsUnit x := by
  by_contra hne
  let I : Ideal A := (Ideal.span {x}).comap (algebraMap A C)
  have hI : I ≠ ⊤ := by
    intro htop
    apply hne
    have h1 : (1 : A) ∈ I := htop ▸ Submodule.mem_top
    have h1' : (1 : C) ∈ Ideal.span {x} := by simpa [I] using h1
    exact Ideal.span_singleton_eq_top.mp ((Ideal.eq_top_iff_one _).mpr h1')
  obtain ⟨r, hr, hdisj⟩ := Ideal.exists_disjoint_powers_of_span_eq_top s hs I hI
  obtain ⟨u, hu⟩ := hx ⟨r, hr⟩
  have : IsLocalization.Away (algebraMap A C r) (Cₛ ⟨r, hr⟩) :=
    inferInstanceAs (IsLocalization.Away (algebraMap A C ((⟨r, hr⟩ : s) : A)) _)
  obtain ⟨⟨c, ⟨_, n, rfl⟩⟩, hc⟩ := IsLocalization.surj
    (Submonoid.powers (algebraMap A C r)) (↑u⁻¹ : Cₛ ⟨r, hr⟩)
  have key : algebraMap C (Cₛ ⟨r, hr⟩) ((algebraMap A C r) ^ n) =
      algebraMap C (Cₛ ⟨r, hr⟩) (x * c) := by
    rw [map_mul, ← hc, ← hu, ← mul_assoc, Units.mul_inv, one_mul]
  obtain ⟨m, hm⟩ := exists_pow_mul_eq_of_algebraMap_eq (algebraMap A C r) key
  have hmem : r ^ (m + n) ∈ I := by
    change algebraMap A C (r ^ (m + n)) ∈ Ideal.span {x}
    rw [map_pow, pow_add, hm]
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self x))
  exact Set.disjoint_left.mp hdisj hmem ⟨m + n, rfl⟩

variable [∀ r, Algebra (Aₛ r) (Cₛ r)] [∀ r, Algebra A (Cₛ r)]
  [∀ r, IsScalarTower A (Aₛ r) (Cₛ r)] [∀ r, IsScalarTower A C (Cₛ r)]

include hs in
/-- **Total rings of fractions glue along principal opens.**  Let `A` have finitely many minimal
primes, every zerodivisor lying in one of them, let `s ⊆ A` generate the unit ideal and let `C` be
an `A`-algebra such that `C_r` is the total ring of fractions of `A_r` for every `r ∈ s`.  Then
`C` is the total ring of fractions of `A`. -/
theorem nonZeroDivisors_of_away_span
    (hfin : (minimalPrimes A).Finite)
    (hzd : ∀ a : A, a ∉ A⁰ → ∃ q ∈ minimalPrimes A, a ∈ q)
    (h : ∀ r, IsLocalization (Aₛ r)⁰ (Cₛ r)) :
    IsLocalization A⁰ C where
  map_units := by
    rintro ⟨t, ht⟩
    refine isUnit_of_isUnit_algebraMap_away s hs Cₛ _ fun r => ?_
    have := h r
    have : Module.Flat A (Aₛ r) := IsLocalization.flat (Aₛ r) (Submonoid.powers (r : A))
    rw [← IsScalarTower.algebraMap_apply A C, IsScalarTower.algebraMap_apply A (Aₛ r) (Cₛ r)]
    exact IsLocalization.map_units (Cₛ r)
      (⟨_, algebraMap_mem_nonZeroDivisors_of_flat ht⟩ : (Aₛ r)⁰)
  surj := by
    intro c
    let J : Ideal A :=
      (LinearMap.range (Algebra.linearMap A C)).comap (LinearMap.toSpanSingleton A C c)
    suffices ∃ t ∈ J, t ∈ A⁰ by
      obtain ⟨t, ⟨b, hb⟩, ht⟩ := this
      exact ⟨⟨b, ⟨t, ht⟩⟩, by simpa [Algebra.smul_def, mul_comm] using hb.symm⟩
    by_contra hno
    push Not at hno
    obtain ⟨p, hp, hle⟩ :=
      Ideal.exists_mem_minimalPrimes_le_of_forall_notMem_nonZeroDivisors hfin hzd J hno
    have hpp : p.IsPrime := hp.1.1
    obtain ⟨r, hr, hrp⟩ := Set.not_subset.mp fun H =>
      hpp.ne_top (eq_top_iff.mpr (hs ▸ Ideal.span_le.mpr H))
    let r' : s := ⟨r, hr⟩
    have hloc := h r'
    have : IsLocalization.Away r (Aₛ r') := inferInstanceAs (IsLocalization.Away (r' : A) _)
    have : IsLocalization.Away (algebraMap A C r) (Cₛ r') :=
      inferInstanceAs (IsLocalization.Away (algebraMap A C (r' : A)) _)
    obtain ⟨⟨x, t⟩, hxt⟩ := IsLocalization.surj (Aₛ r')⁰ (algebraMap C (Cₛ r') c)
    obtain ⟨⟨x0, ⟨_, k, rfl⟩⟩, hx0⟩ := IsLocalization.surj (Submonoid.powers r) x
    obtain ⟨⟨t0, ⟨_, l, rfl⟩⟩, ht0⟩ := IsLocalization.surj (Submonoid.powers r) (t : Aₛ r')
    simp only at hxt hx0 ht0
    have ht0reg : algebraMap A (Aₛ r') t0 ∈ (Aₛ r')⁰ := by
      rw [← ht0]
      exact Submonoid.mul_mem _ t.2
        (IsLocalization.map_units (Aₛ r')
          (⟨r ^ l, l, rfl⟩ : Submonoid.powers r)).mem_nonZeroDivisors
    have e1 : ∀ a, algebraMap C (Cₛ r') (algebraMap A C a) =
        algebraMap (Aₛ r') (Cₛ r') (algebraMap A (Aₛ r') a) := fun a => by
      rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
    have key : algebraMap C (Cₛ r') (algebraMap A C (t0 * r ^ k) * c) =
        algebraMap C (Cₛ r') (algebraMap A C (x0 * r ^ l)) := by
      simp only [map_mul, e1, ← ht0, ← hx0]
      rw [← hxt]
      ring
    obtain ⟨m, hm⟩ := exists_pow_mul_eq_of_algebraMap_eq (algebraMap A C r) key
    have hJ : t0 * r ^ k * r ^ m ∈ J := by
      refine ⟨r ^ m * (x0 * r ^ l), ?_⟩
      change algebraMap A C (r ^ m * (x0 * r ^ l)) = (t0 * r ^ k * r ^ m) • c
      rw [Algebra.smul_def, map_mul, map_pow, ← hm]
      simp only [map_mul, map_pow]
      ring
    have hrp' : ∀ n, r ^ n ∉ p := fun n h => hrp (hpp.mem_of_pow_mem n h)
    have ht0p : t0 ∈ p := by simpa [hpp.mul_mem_iff_mem_or_mem, hrp'] using hle hJ
    exact notMem_nonZeroDivisors_of_mem_mem_minimalPrimes (Ideal.mem_map_of_mem _ ht0p)
      (map_mem_minimalPrimes_of_disjoint (Submonoid.powers r) hp
        ((Ideal.disjoint_powers_iff_notMem _ hpp.isRadical).mpr hrp)) ht0reg
  exists_of_eq := by
    intro a b hab
    refine ⟨1, ?_⟩
    simp only [OneMemClass.coe_one, one_mul]
    refine Module.eq_of_isLocalized_span s hs (fun r => Aₛ r)
      (fun r => Algebra.linearMap A (Aₛ r)) a b fun r => ?_
    have := h r
    apply IsLocalization.injective (Cₛ r) (le_refl (Aₛ r)⁰)
    simp only [Algebra.linearMap_apply]
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply A C, hab, ← IsScalarTower.algebraMap_apply A C]

end IsLocalization
