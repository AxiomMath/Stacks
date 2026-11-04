module

public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import StacksFrontier.RingTheory.Module.LocallyFree.SheafBridge

/-!
# A generator of a rank one module away from an element avoiding the minimal primes

Let `A` be a Noetherian ring and let `M` be a finite locally free `A`-module of rank one.  Then
there are an element `f ∈ A` lying in no minimal prime of `A` and an element `s ∈ M` such that
`s` generates `M_f` freely over `A_f`.  Geometrically: an invertible module on a Noetherian
affine scheme is trivial on a dense basic open subset.

The argument is elementary.  Near every minimal prime `p` the module is free on some generator,
by local freeness; a combination of these generators with coefficients separating the finitely
many minimal primes from one another is a generator near every minimal prime at once; and since
`A` is Noetherian and `M` finite, the elements away from which it generates form an ideal
contained in no minimal prime, which by prime avoidance contains an element outside all of them.

## Main definitions

* `Module.IsFreeGeneratorAway f s`: the element `s` generates `M` freely after inverting `f`,
  stated without localizations: whatever kills `s` is killed by a power of `f`, and a power of
  `f` moves every element into `A s`.

## Main results

* `Module.isFreeGeneratorAway_bijective_smul`: if `s` generates `M` freely away from `f`, then
  `b ↦ b • s` is a bijection `A_f ≅ M_f` for any localizations `A_f` and `M_f`.
* `Module.IsFiniteLocallyFreeOfRank.exists_isFreeGeneratorAway`: a finite locally free module of
  rank one has a free generator away from some element outside any given prime.
* `Module.exists_isFreeGeneratorAway_forall_notMem_minimalPrimes`: over a Noetherian ring, a
  finite module with a free generator away from an element outside each minimal prime has one
  away from a single element outside all minimal primes.

## References

* [Stacks Project, Tag 0DMM](https://stacks.math.columbia.edu/tag/0DMM)
* [Stacks Project, Tag 00DS](https://stacks.math.columbia.edu/tag/00DS)
-/

@[expose] public section

namespace Module

variable {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]

/-- The element `s` **generates `M` freely after inverting `f`**: an element of `A` killing `s`
is killed by a power of `f`, and a power of `f` carries every element of `M` into `A s`. -/
def IsFreeGeneratorAway (f : A) (s : M) : Prop :=
  (∀ a : A, a • s = 0 → ∃ n : ℕ, f ^ n * a = 0) ∧ ∀ x : M, ∃ (n : ℕ) (a : A), f ^ n • x = a • s

/-- If `m` generates `M` freely away from `g` and `gⁿ s = α m`, then `s` generates `M` freely
away from `g α`. -/
theorem IsFreeGeneratorAway.of_pow_smul_eq {g α : A} {m s : M} (hm : IsFreeGeneratorAway g m)
    (n : ℕ) (h : g ^ n • s = α • m) : IsFreeGeneratorAway (g * α) s := by
  refine ⟨fun a ha => ?_, fun x => ?_⟩
  · obtain ⟨k, hk⟩ := hm.1 (a * α) (by
      rw [mul_smul, ← h, smul_comm, ha, smul_zero])
    exact ⟨k + 1, by
      calc (g * α) ^ (k + 1) * a = (g * α ^ k) * (g ^ k * (a * α)) := by ring
        _ = 0 := by rw [hk, mul_zero]⟩
  · obtain ⟨k, b, hk⟩ := hm.2 x
    refine ⟨k + 1, g ^ (n + 1) * α ^ k * b, ?_⟩
    calc (g * α) ^ (k + 1) • x = (g * α ^ (k + 1)) • (g ^ k • x) := by
          rw [smul_smul]
          congr 1
          ring
      _ = (g * α ^ k * b) • (α • m) := by
          rw [hk, smul_smul, smul_smul]
          congr 1
          ring
      _ = (g ^ (n + 1) * α ^ k * b) • s := by
          rw [← h, smul_smul]
          congr 1
          ring

/-- **A free generator away from `f` is a free generator of the localizations.**  For any
localization `A'` of `A` away from `f` and any localization `g : M → N` of `M` away from `f`,
`b ↦ b • g s` is a bijection `A' ≅ N`. -/
theorem isFreeGeneratorAway_bijective_smul {A' : Type*} [CommRing A'] [Algebra A A']
    {N : Type*} [AddCommGroup N] [Module A N] [Module A' N] [IsScalarTower A A' N]
    {f : A} [IsLocalization.Away f A'] (g : M →ₗ[A] N)
    [IsLocalizedModule (Submonoid.powers f) g] {s : M} (hs : IsFreeGeneratorAway f s) :
    Function.Bijective (fun b : A' => b • g s) := by
  have hpow : ∀ k : ℕ, f ^ k ∈ Submonoid.powers f := fun k =>
    (Submonoid.mem_powers_iff _ _).mpr ⟨k, rfl⟩
  have hunit : ∀ k : ℕ, IsUnit (algebraMap A A' (f ^ k)) := fun k =>
    IsLocalization.map_units A' (⟨f ^ k, hpow k⟩ : Submonoid.powers f)
  have hzero : ∀ a : A, a • s = 0 → algebraMap A A' a = 0 := fun a ha => by
    obtain ⟨n, hn⟩ := hs.1 a ha
    exact (hunit n).mul_right_eq_zero.mp (by rw [← map_mul, hn, map_zero])
  refine ⟨fun b b' h => ?_, fun y => ?_⟩
  · rw [← sub_eq_zero]
    have h0 : (b - b') • g s = 0 := by
      rw [sub_smul, sub_eq_zero]
      exact h
    obtain ⟨⟨a, t⟩, hab⟩ := IsLocalization.surj (Submonoid.powers f) (b - b')
    have hga : g (a • s) = 0 := by
      rw [map_smul, ← algebraMap_smul A', ← hab, mul_comm, mul_smul, h0, smul_zero]
    obtain ⟨⟨c, hc⟩, hcz⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers f) (f := g)
      (hga.trans (map_zero g).symm)
    obtain ⟨k, rfl⟩ := hc
    have hka : algebraMap A A' (f ^ k * a) = 0 := by
      refine hzero _ ?_
      simpa [Submonoid.smul_def, smul_smul] using hcz
    rw [map_mul] at hka
    obtain ⟨_, l, rfl⟩ := t
    rw [(hunit k).mul_right_eq_zero.mp hka] at hab
    exact (hunit l).mul_left_eq_zero.mp hab
  · obtain ⟨⟨x, ⟨_, k, rfl⟩⟩, hx⟩ := IsLocalizedModule.surj (Submonoid.powers f) g y
    have hx' : f ^ k • y = g x := hx
    obtain ⟨n, a, hna⟩ := hs.2 x
    refine ⟨IsLocalization.mk' A' a (⟨f ^ (n + k), hpow (n + k)⟩ : Submonoid.powers f), ?_⟩
    simp only
    refine ((hunit (n + k)).smul_left_cancel).mp ?_
    rw [smul_smul, IsLocalization.mk'_spec' A' a (⟨f ^ (n + k), hpow (n + k)⟩ :
      Submonoid.powers f), algebraMap_smul, ← map_smul, ← hna, map_smul, pow_add, map_mul,
      mul_smul, algebraMap_smul, algebraMap_smul, hx']

/-- **A finite locally free module of rank one is free near every prime**: for every prime `p`
there are `g ∉ p` and `m ∈ M` with `m` generating `M` freely away from `g`. -/
theorem IsFiniteLocallyFreeOfRank.exists_isFreeGeneratorAway
    (h : Module.IsFiniteLocallyFreeOfRank A M 1) (p : Ideal A) [p.IsPrime] :
    ∃ g : A, g ∉ p ∧ ∃ m : M, IsFreeGeneratorAway g m := by
  obtain ⟨ι, f, hspan, hb⟩ := h
  obtain ⟨i, hi⟩ : ∃ i, f i ∉ p := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    have hle : Ideal.span (Set.range f) ≤ p :=
      Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hcon i)
    exact Ideal.IsPrime.ne_top ‹_› (top_le_iff.mp (hspan ▸ hle))
  obtain ⟨b⟩ := hb i
  refine ⟨f i, hi, ?_⟩
  obtain ⟨⟨m, ⟨_, l, rfl⟩⟩, hmt⟩ :=
    IsLocalizedModule.surj (Submonoid.powers (f i))
      (LocalizedModule.mkLinearMap (Submonoid.powers (f i)) M) (b 0)
  have hmt' : f i ^ l • b 0 = LocalizedModule.mkLinearMap (Submonoid.powers (f i)) M m := hmt
  refine ⟨m, ?_, ?_⟩
  · intro a ha
    have h1 : (algebraMap A (Localization.Away (f i)) (a * f i ^ l)) • b 0 = 0 := by
      rw [map_mul, mul_smul, algebraMap_smul, algebraMap_smul, hmt', ← map_smul, ha, map_zero]
    have h2 : algebraMap A (Localization.Away (f i)) (a * f i ^ l) = 0 := by
      have := b.linearIndependent
      rw [Fintype.linearIndependent_iff] at this
      exact this (fun _ => algebraMap A (Localization.Away (f i)) (a * f i ^ l))
        (by simpa [Fin.sum_univ_one] using h1) 0
    obtain ⟨⟨c, ⟨k, rfl⟩⟩, hc⟩ :=
      (IsLocalization.map_eq_zero_iff (Submonoid.powers (f i)) _ _).mp h2
    exact ⟨k + l, by
      calc f i ^ (k + l) * a = f i ^ k * (a * f i ^ l) := by ring
        _ = 0 := hc⟩
  · intro x
    obtain ⟨c, hc⟩ : ∃ c : Localization.Away (f i),
        LocalizedModule.mkLinearMap (Submonoid.powers (f i)) M x = c • b 0 := by
      refine ⟨b.repr (LocalizedModule.mkLinearMap (Submonoid.powers (f i)) M x) 0, ?_⟩
      have := b.sum_repr (LocalizedModule.mkLinearMap (Submonoid.powers (f i)) M x)
      rw [Fin.sum_univ_one] at this
      exact this.symm
    obtain ⟨⟨a, ⟨_, k, rfl⟩⟩, hau⟩ := IsLocalization.surj (Submonoid.powers (f i)) c
    have hau' : c * algebraMap A (Localization.Away (f i)) (f i ^ k) =
        algebraMap A (Localization.Away (f i)) a := hau
    have h1 : LocalizedModule.mkLinearMap (Submonoid.powers (f i)) M (f i ^ (k + l) • x) =
        LocalizedModule.mkLinearMap (Submonoid.powers (f i)) M (a • m) := by
      rw [pow_add, mul_smul, map_smul, map_smul, hc, smul_comm (f i ^ l) c (b 0), hmt',
        ← algebraMap_smul (Localization.Away (f i)) (f i ^ k), smul_smul, mul_comm, hau',
        algebraMap_smul, ← map_smul]
    obtain ⟨⟨c', ⟨j, rfl⟩⟩, hj⟩ := IsLocalizedModule.exists_of_eq
      (S := Submonoid.powers (f i)) h1
    have hj' : f i ^ j • f i ^ (k + l) • x = f i ^ j • a • m := hj
    exact ⟨j + (k + l), f i ^ j * a, by rw [pow_add, mul_smul, hj', smul_smul]⟩

/-- If every element of a set of generators of a submodule `N` is carried into `P` by some power
of `h`, then a single power of `h` carries all of `N` into `P`. -/
theorem exists_pow_smul_mem_of_fg {N P : Submodule A M} (hN : N.FG) (h : A)
    (hx : ∀ x ∈ N, ∃ n : ℕ, h ^ n • x ∈ P) : ∃ n : ℕ, ∀ x ∈ N, h ^ n • x ∈ P := by
  classical
  obtain ⟨T, rfl⟩ := hN
  choose! e he using fun x (hxT : x ∈ T) => hx x (Submodule.subset_span hxT)
  refine ⟨T.sum e, fun x hxN => ?_⟩
  induction hxN using Submodule.span_induction with
  | mem y hy =>
    have hle : e y ≤ T.sum e := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hy
    rw [← Nat.sub_add_cancel hle, pow_add, mul_smul]
    exact P.smul_mem _ (he y hy)
  | zero => rw [smul_zero]; exact P.zero_mem
  | add y z _ _ hy hz => rw [smul_add]; exact P.add_mem hy hz
  | smul c y _ hy => rw [smul_comm]; exact P.smul_mem c hy

/-! ### Combining free generators near the minimal primes -/

/-- Adding two elements which are near `g` multiples of `m` gives a multiple of `m`. -/
private theorem pow_add_smul_add_eq {g : A} {m x y : M} {n₁ n₂ : ℕ} {a₁ a₂ : A}
    (h₁ : g ^ n₁ • x = a₁ • m) (h₂ : g ^ n₂ • y = a₂ • m) :
    g ^ (n₁ + n₂) • (x + y) = (g ^ n₂ * a₁ + g ^ n₁ * a₂) • m := by
  rw [smul_add, pow_add, mul_smul, mul_smul, smul_comm (g ^ n₁) (g ^ n₂) x, h₁, h₂, smul_smul,
    smul_smul, add_smul]

/-- A free generator near `p` plus an element which near `p` is a multiple of the generator by
an element of `p` is again, near `p`, a multiple of the generator by an element outside `p`. -/
private theorem exists_pow_smul_add {p : Ideal A} [p.IsPrime] {g : A} (hg : g ∉ p) {m x y : M}
    (hx : ∃ (n : ℕ) (α : A), α ∉ p ∧ g ^ n • x = α • m)
    (hy : ∃ (n : ℕ) (a : A), a ∈ p ∧ g ^ n • y = a • m) :
    ∃ (n : ℕ) (α : A), α ∉ p ∧ g ^ n • (x + y) = α • m := by
  obtain ⟨n₁, α, hα, h₁⟩ := hx
  obtain ⟨n₂, a, ha, h₂⟩ := hy
  refine ⟨n₁ + n₂, _, fun hmem => ?_, pow_add_smul_add_eq h₁ h₂⟩
  have h1 : g ^ n₂ * α ∈ p := by simpa using p.sub_mem hmem (p.mul_mem_left (g ^ n₁) ha)
  exact Ideal.IsPrime.mul_notMem ‹_› (fun h => hg (Ideal.IsPrime.mem_of_pow_mem ‹_› _ h)) hα h1

/-- The elements which near `p` are multiples of the generator by elements of `p` are closed
under addition. -/
private theorem exists_pow_smul_add_mem {p : Ideal A} {g : A} {m x y : M}
    (hx : ∃ (n : ℕ) (a : A), a ∈ p ∧ g ^ n • x = a • m)
    (hy : ∃ (n : ℕ) (a : A), a ∈ p ∧ g ^ n • y = a • m) :
    ∃ (n : ℕ) (a : A), a ∈ p ∧ g ^ n • (x + y) = a • m := by
  obtain ⟨n₁, a₁, ha₁, h₁⟩ := hx
  obtain ⟨n₂, a₂, ha₂, h₂⟩ := hy
  exact ⟨n₁ + n₂, _, p.add_mem (p.mul_mem_left _ ha₁) (p.mul_mem_left _ ha₂),
    pow_add_smul_add_eq h₁ h₂⟩

/-- A multiple of any element by an element of `p` is, near `p`, a multiple of the generator by
an element of `p`. -/
private theorem exists_pow_smul_smul_mem {p : Ideal A} {g : A} {m : M}
    (hm : IsFreeGeneratorAway g m) {c : A} (hc : c ∈ p) (x : M) :
    ∃ (n : ℕ) (a : A), a ∈ p ∧ g ^ n • (c • x) = a • m := by
  obtain ⟨n, a, h⟩ := hm.2 x
  exact ⟨n, c * a, p.mul_mem_right _ hc, by rw [smul_comm, h, smul_smul]⟩

/-- **A single free generator near all the minimal primes at once.**  Over a Noetherian ring, if
near each minimal prime `p` some element of a finite module `M` generates `M` freely away from an
element outside `p`, then there are `f` outside every minimal prime and `s ∈ M` such that `s`
generates `M` freely away from `f`.

The generators near the finitely many minimal primes are combined with coefficients lying in all
minimal primes but one; the combination is near each `p` a unit multiple of the generator there.
The elements away from which it generates freely contain the ideal `Ann(K) ∩ (A s : M)`, where
`K` is the annihilator of `s`; both are finitely generated conditions, so that ideal is
contained in no minimal prime, and prime avoidance (Stacks 00DS) produces `f`. -/
theorem exists_isFreeGeneratorAway_forall_notMem_minimalPrimes [IsNoetherianRing A]
    [Module.Finite A M]
    (h : ∀ p ∈ minimalPrimes A, ∃ g : A, g ∉ p ∧ ∃ m : M, IsFreeGeneratorAway g m) :
    ∃ f : A, (∀ p ∈ minimalPrimes A, f ∉ p) ∧ ∃ s : M, IsFreeGeneratorAway f s := by
  classical
  set P : Finset (Ideal A) := (minimalPrimes.finite_of_isNoetherianRing A).toFinset with hP
  have hPmem : ∀ {p}, p ∈ P ↔ p ∈ minimalPrimes A := fun {p} => Set.Finite.mem_toFinset _
  have hprime : ∀ p ∈ P, p.IsPrime := fun p hp => (hPmem.mp hp).1.1
  choose! g hg m hm using h
  -- Coefficients separating the minimal primes from one another.
  have hsep : ∀ p ∈ P, ∃ c : A, c ∈ (P.erase p).inf id ∧ c ∉ p := by
    intro p hp
    have := hprime p hp
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    obtain ⟨q, hq, hqp⟩ := (Ideal.IsPrime.inf_le' ‹p.IsPrime›).mp (fun c hc => hcon c hc)
    have hqmin := hPmem.mp (Finset.mem_of_mem_erase hq)
    have hpq : p ≤ q := (hPmem.mp hp).2 ⟨hqmin.1.1, bot_le⟩ hqp
    exact Finset.ne_of_mem_erase hq (le_antisymm hqp hpq)
  choose! c hc hcp using hsep
  set s : M := ∑ q ∈ P, c q • m q with hs
  -- Near each minimal prime the combination is a unit multiple of the local generator.
  have hnear : ∀ p ∈ P, ∃ (n : ℕ) (α : A), α ∉ p ∧ g p ^ n • s = α • m p := by
    intro p hp
    have := hprime p hp
    have hmp := hm p (hPmem.mp hp)
    have hgp := hg p (hPmem.mp hp)
    rw [hs, ← Finset.add_sum_erase P _ hp]
    refine exists_pow_smul_add hgp ⟨0, c p, hcp p hp, by rw [pow_zero, one_smul]⟩ ?_
    refine Finset.sum_induction _ (fun y => ∃ (n : ℕ) (a : A), a ∈ p ∧ g p ^ n • y = a • m p)
      (fun _ _ => exists_pow_smul_add_mem) ⟨0, 0, p.zero_mem, by simp⟩ fun q hq => ?_
    have hcq : c q ∈ p := by
      have hq' := Finset.mem_erase.mp hq
      have hpq : p ∈ P.erase q := Finset.mem_erase.mpr ⟨fun e => hq'.1 e.symm, hp⟩
      exact Finset.inf_le (f := id) hpq (hc q hq'.2)
    exact exists_pow_smul_smul_mem hmp hcq (m q)
  -- Hence the combination generates freely away from an element outside each minimal prime.
  have hfree : ∀ p ∈ P, ∃ h : A, h ∉ p ∧ IsFreeGeneratorAway h s := by
    intro p hp
    have := hprime p hp
    obtain ⟨n, α, hα, hn⟩ := hnear p hp
    exact ⟨g p * α, Ideal.IsPrime.mul_notMem ‹_› (hg p (hPmem.mp hp)) hα,
      (hm p (hPmem.mp hp)).of_pow_smul_eq n hn⟩
  -- The ideal of elements away from which `s` generates freely.
  set K : Ideal A := LinearMap.ker (LinearMap.toSpanSingleton A M s) with hK
  set I : Ideal A := Submodule.annihilator K ⊓ (A ∙ s).colon (⊤ : Submodule A M) with hI
  have hInot : ∀ p ∈ P, ¬ I ≤ p := by
    intro p hp hIp
    have := hprime p hp
    obtain ⟨h, hh, hhs⟩ := hfree p hp
    obtain ⟨n₁, hn₁⟩ := exists_pow_smul_mem_of_fg (IsNoetherian.noetherian K) h
      (P := (⊥ : Ideal A)) fun x hx => by
        obtain ⟨n, hn⟩ := hhs.1 x (by simpa [hK] using hx)
        exact ⟨n, by simpa [smul_eq_mul] using hn⟩
    obtain ⟨n₂, hn₂⟩ := exists_pow_smul_mem_of_fg (Module.Finite.fg_top (R := A) (M := M)) h
      (P := A ∙ s) fun x _ => by
        obtain ⟨n, a, hn⟩ := hhs.2 x
        exact ⟨n, by rw [hn]; exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self s)⟩
    have hmemI : h ^ (n₁ + n₂) ∈ I := by
      refine Submodule.mem_inf.mpr ⟨Submodule.mem_annihilator.mpr fun x hx => ?_,
        Submodule.mem_colon.mpr fun x _ => ?_⟩
      · have := hn₁ x hx
        rw [Submodule.mem_bot, smul_eq_mul] at this
        rw [smul_eq_mul, pow_add, mul_comm (h ^ n₁), mul_assoc, this, mul_zero]
      · rw [pow_add, mul_smul]
        exact Submodule.smul_mem _ _ (hn₂ x Submodule.mem_top)
    exact hh (Ideal.IsPrime.mem_of_pow_mem ‹_› _ (hIp hmemI))
  -- Prime avoidance.
  have hnsub : ¬ ((I : Set A) ⊆ ⋃ p ∈ (↑P : Set (Ideal A)), (p : Set A)) := by
    intro hsub
    obtain ⟨p, hp, hIp⟩ := (Ideal.subset_union_prime (f := id) (⊥ : Ideal A) ⊥
      (fun p hp _ _ => hprime p hp)).mp hsub
    exact hInot p hp hIp
  obtain ⟨f, hfI, hfP⟩ := Set.not_subset.mp hnsub
  simp only [Set.mem_iUnion, SetLike.mem_coe, not_exists] at hfP
  have hfI' := Submodule.mem_inf.mp hfI
  refine ⟨f, fun p hp hfp => hfP p (hPmem.mpr hp) hfp, s, fun a ha => ⟨1, ?_⟩, fun x => ?_⟩
  · have haK : a ∈ K := by simpa [hK] using ha
    rw [pow_one, ← smul_eq_mul]
    exact Submodule.mem_annihilator.mp hfI'.1 a haK
  · obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp
      ((Submodule.mem_colon.mp hfI'.2) x Submodule.mem_top)
    exact ⟨1, a, by rw [pow_one, ha]⟩

end Module
