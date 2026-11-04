module

public import StacksFrontier.RingTheory.Flat.SliceNonZeroDivisor

/-!
# Flatness of a localization from flatness at the primes it survives at

Let `A → B` be a ring map and let `M` be a `B`-module. Openness of the flat locus produces a
basic open `D(g) ⊆ Spec B` on which `M` is flat over `A` *pointwise*: `M_q` is flat over `A` for
every prime `q` of `B` with `g ∉ q`. What a consumer wants instead is the single statement that
the localization `M_g` is flat over `A`. This file supplies the passage from the first to the
second, and uses it to upgrade two statements whose existing forms are pointwise.

## Main results

* `Module.flat_localizedModule_iff_forall_flat_atPrime`: for a submonoid `T` of `B`, the
  localization `LocalizedModule T M` is flat over `A` if and only if `M_q` is flat over `A` for
  every prime `q` of `B` disjoint from `T`. No finiteness or Noetherian hypothesis is used.
* `Module.flat_localizedModule_away_of_forall_flat_atPrime`: the case `T = {gⁿ}` of the
  implication that is not formal, stated with the hypothesis as `g ∉ q`.
* `Module.exists_away_flat_localizedModule_of_flat_atPrime`: openness of the flat locus in its
  basic-open form. If `M` is a finite module over a finite type algebra `B` over a Noetherian
  ring `A` and `M_q` is flat over `A` at one prime `q`, then there is `g ∉ q` with
  `LocalizedModule (Submonoid.powers g) M` flat over `A`.
* `Stacks.Flatness.exists_notMem_mem_nonZeroDivisors_away_and_flat_quotient`: the algebraic claim
  in the proof of Stacks Tag 056Y, in the ring-level form in which the Stacks Project states it:
  after replacing `B` by a localization `B_g` with `g ∉ q`, the element `h` is a nonzerodivisor
  and the quotient `B_g / h B_g` is flat over `A`.

## Implementation notes

The two sides of `Module.flat_localizedModule_iff_forall_flat_atPrime` are equivalent, as they
must be: flatness over `A` passes to any further localization, which is the easy direction and is
`Module.Flat.of_isLocalizedModule_of_tower`. The content is the other direction, and it is the
step named as missing in the implementation notes of
`StacksFrontier/RingTheory/Flat/SliceNonZeroDivisor.lean`; the statement is phrased as an
equivalence so that it cannot silently weaken a consumer in either direction.

That direction is proved by applying `Module.flat_of_isLocalized_maximal` over the ring
`Localization T` rather than over `B`: a maximal ideal `P` of `Localization T` has a prime
contraction `q = P ∩ B` disjoint from `T`, and the localization of `LocalizedModule T M` at `P`
is identified with `M_q`.

That identification is where the work is. Mathlib's `Module.flat_of_isLocalized_maximal` demands
a localization at `P.primeCompl`, a submonoid of `Localization T`, whereas `M_q` is presented as
a localization at `q.primeCompl`, a submonoid of `B`. The two are reconciled by localizing
`LocalizedModule T M` at the *image* `S₀` of `q.primeCompl` in `Localization T`:

* `S₀ ≤ P.primeCompl`, and every element of `P.primeCompl` has a multiple in `S₀` — because an
  element of `Localization T` outside `P` becomes, after multiplication by an element of `T`, the
  image of an element of `B` outside `q` — so `IsLocalizedModule.of_exists_mul_mem` turns the
  canonical localization at `S₀` into a localization at `P.primeCompl`;
* restricting scalars from `Localization T` to `B` turns that same canonical map into a
  localization at `q.primeCompl`, by `IsLocalizedModule.restrictScalars`, since `S₀` is by
  construction `Algebra.algebraMapSubmonoid (Localization T) q.primeCompl`;
* `IsLocalizedModule.liftOfLE` presents `M_q` as a localization of `LocalizedModule T M` at
  `q.primeCompl` as well, using `T ≤ q.primeCompl`, and uniqueness of localizations gives the
  `B`-linear equivalence, hence the `A`-linear one.

Disjointness of `q` from `T` is spelled `T ≤ q.primeCompl` throughout, which is the form in which
both `IsLocalizedModule.liftOfLE` and the `Submonoid.powers` specialization want it.

## References

* [Stacks Project, Tag 00HT](https://stacks.math.columbia.edu/tag/00HT)
* [Stacks Project, Tag 00RC](https://stacks.math.columbia.edu/tag/00RC)
* [Stacks Project, Tag 056Y](https://stacks.math.columbia.edu/tag/056Y)
-/

@[expose] public section

namespace Stacks.Flatness

section Comap

variable {B : Type*} [CommRing B] {T : Submonoid B}

/-- Localizing a module over `Localization T` at the image of the complement of the contraction
of a prime `P` is the same as localizing it at the complement of `P` itself.

Every element of `Localization T` outside `P` becomes the image of an element of `B` outside
`P ∩ B` after multiplication by an element of `T`, which is exactly the hypothesis of
`IsLocalizedModule.of_exists_mul_mem`. -/
theorem isLocalizedModule_atPrime_mkLinearMap_algebraMapSubmonoid_comap
    (P : Ideal (Localization T)) [P.IsPrime]
    (N : Type*) [AddCommGroup N] [Module (Localization T) N] :
    IsLocalizedModule.AtPrime P
      (LocalizedModule.mkLinearMap
        (Algebra.algebraMapSubmonoid (Localization T)
          (P.comap (algebraMap B (Localization T))).primeCompl) N) := by
  have hle : Algebra.algebraMapSubmonoid (Localization T)
      (P.comap (algebraMap B (Localization T))).primeCompl ≤ P.primeCompl := by
    rintro x hx
    obtain ⟨b, hb, rfl⟩ := hx
    exact hb
  refine IsLocalizedModule.of_exists_mul_mem _ _ hle ?_ _
  rintro ⟨x, hx⟩
  obtain ⟨⟨a, t⟩, ha⟩ := IsLocalization.surj T x
  have hane : a ∈ (P.comap (algebraMap B (Localization T))).primeCompl := by
    intro hmem
    refine hx ?_
    have h1 : x * algebraMap B (Localization T) (t : B) ∈ P := ha ▸ hmem
    rw [mul_comm] at h1
    exact (Ideal.unit_mul_mem_iff_mem _ (IsLocalization.map_units _ t)).mp h1
  exact ⟨algebraMap B (Localization T) (t : B), by
    rw [mul_comm, ha]; exact Algebra.mem_algebraMapSubmonoid_of_mem ⟨a, hane⟩⟩

/-- The contraction of a prime of `Localization T` is disjoint from `T`, since every element of
`T` becomes a unit. -/
theorem le_primeCompl_comap (P : Ideal (Localization T)) [hP : P.IsPrime] :
    T ≤ (P.comap (algebraMap B (Localization T))).primeCompl := by
  intro t ht hmem
  exact hP.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem (IsLocalization.map_units _ ⟨t, ht⟩))

end Comap

section LocalGlobal

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  {M : Type*} [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]

/-- **Flatness of a localization from flatness at the primes it survives at.** Let `A → B` be a
ring map, `M` a `B`-module and `T` a submonoid of `B`. If `M_q` is flat over `A` for every prime
`q` of `B` disjoint from `T`, then `LocalizedModule T M` is flat over `A`.

This is the direction of `Module.flat_localizedModule_iff_forall_flat_atPrime` that is not
formal; see that statement and the implementation notes of this file. -/
theorem _root_.Module.flat_localizedModule_of_forall_flat_atPrime {T : Submonoid B}
    (H : ∀ q : Ideal B, ∀ _ : q.IsPrime, T ≤ q.primeCompl →
      Module.Flat A (LocalizedModule q.primeCompl M)) :
    Module.Flat A (LocalizedModule T M) := by
  have hinst : ∀ P : Ideal (Localization T), ∀ _ : P.IsPrime,
      IsLocalizedModule.AtPrime P
        (LocalizedModule.mkLinearMap (Algebra.algebraMapSubmonoid (Localization T)
          (P.comap (algebraMap B (Localization T))).primeCompl) (LocalizedModule T M)) :=
    fun P _ => isLocalizedModule_atPrime_mkLinearMap_algebraMapSubmonoid_comap P _
  refine Module.flat_of_isLocalized_maximal (Localization T) _
    (fun P _ => LocalizedModule (Algebra.algebraMapSubmonoid (Localization T)
      (P.comap (algebraMap B (Localization T))).primeCompl) (LocalizedModule T M))
    (fun P _ => LocalizedModule.mkLinearMap _ _) ?_
  intro P _
  have hTq : T ≤ (P.comap (algebraMap B (Localization T))).primeCompl := le_primeCompl_comap P
  have : IsLocalizedModule (P.comap (algebraMap B (Localization T))).primeCompl
      ((LocalizedModule.mkLinearMap (Algebra.algebraMapSubmonoid (Localization T)
        (P.comap (algebraMap B (Localization T))).primeCompl)
        (LocalizedModule T M)).restrictScalars B) :=
    IsLocalizedModule.restrictScalars _ _
  have := H _ (inferInstanceAs (P.comap (algebraMap B (Localization T))).IsPrime) hTq
  exact Module.Flat.of_linearEquiv (LinearEquiv.restrictScalars A
    (IsLocalizedModule.linearEquiv (P.comap (algebraMap B (Localization T))).primeCompl
      ((LocalizedModule.mkLinearMap (Algebra.algebraMapSubmonoid (Localization T)
        (P.comap (algebraMap B (Localization T))).primeCompl)
        (LocalizedModule T M)).restrictScalars B)
      (IsLocalizedModule.liftOfLE T (P.comap (algebraMap B (Localization T))).primeCompl hTq
        (LocalizedModule.mkLinearMap T M)
        (LocalizedModule.mkLinearMap
          (P.comap (algebraMap B (Localization T))).primeCompl M))))

/-- **Flatness of a localization is flatness at each prime it survives at.** For a submonoid `T`
of `B`, the localization `LocalizedModule T M` is flat over `A` exactly when `M_q` is flat over
`A` for every prime `q` of `B` disjoint from `T`.

The forward implication is formal: `M_q` is a further localization of `LocalizedModule T M`, and
a localization of an `A`-flat module is `A`-flat. The reverse implication is
`Module.flat_localizedModule_of_forall_flat_atPrime`. -/
theorem _root_.Module.flat_localizedModule_iff_forall_flat_atPrime {T : Submonoid B} :
    Module.Flat A (LocalizedModule T M) ↔
      ∀ q : Ideal B, ∀ _ : q.IsPrime, T ≤ q.primeCompl →
        Module.Flat A (LocalizedModule q.primeCompl M) := by
  refine ⟨fun hT q hq hTq => ?_, Module.flat_localizedModule_of_forall_flat_atPrime⟩
  exact Module.Flat.of_isLocalizedModule_of_tower q.primeCompl
    (IsLocalizedModule.liftOfLE T q.primeCompl hTq (LocalizedModule.mkLinearMap T M)
      (LocalizedModule.mkLinearMap q.primeCompl M))

/-- **Flatness over a basic open from flatness at its primes.** If `M_q` is flat over `A` for
every prime `q` of `B` with `g ∉ q`, then the localization of `M` away from `g` is flat over
`A`. -/
theorem _root_.Module.flat_localizedModule_away_of_forall_flat_atPrime {g : B}
    (H : ∀ q : Ideal B, ∀ _ : q.IsPrime, g ∉ q →
      Module.Flat A (LocalizedModule q.primeCompl M)) :
    Module.Flat A (LocalizedModule (Submonoid.powers g) M) :=
  Module.flat_localizedModule_of_forall_flat_atPrime
    fun q hq hTq => H q hq (hTq (Submonoid.mem_powers g))

/-- **Stacks 00RC over a Noetherian base, in basic-open form.** For a Noetherian ring `A`, a
finite type `A`-algebra `B` and a finite `B`-module `M`, if `M_q` is flat over `A` at a prime `q`
of `B`, then there is `g ∉ q` such that the localization of `M` away from `g` is flat over `A`.

Openness of the flat locus is a statement about the *set* of primes at which the localization is
flat; this is the same statement read as one flatness assertion over a basic open, which is the
form in which it is used. -/
theorem _root_.Module.exists_away_flat_localizedModule_of_flat_atPrime [IsNoetherianRing A]
    [Algebra.FiniteType A B] [Module.Finite B M] (q : Ideal B) [hq : q.IsPrime]
    (hflatq : Module.Flat A (LocalizedModule.AtPrime q M)) :
    ∃ g ∈ q.primeCompl, Module.Flat A (LocalizedModule (Submonoid.powers g) M) := by
  obtain ⟨V, ⟨g, rfl⟩, hmem, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (a := (⟨q, hq⟩ : PrimeSpectrum B)) hflatq
      (Module.isOpen_setOf_flat_localizedModule_atPrime_of_isNoetherianRing (R := A) (S := B)
        (M := M))
  exact ⟨g, hmem, Module.flat_localizedModule_away_of_forall_flat_atPrime
    fun q' hq' hgq' => hsub
      (show (⟨q', hq'⟩ : PrimeSpectrum B) ∈ PrimeSpectrum.basicOpen g from hgq')⟩

end LocalGlobal

section Slice

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-- **The algebraic claim in the proof of Stacks Tag 056Y, in ring-level form.** Let `A → B` be a
flat ring map of finite type between Noetherian rings, let `q` be a prime of `B` and
`p = q ∩ A`. Let `h ∈ q` map to a nonzerodivisor in the fibre `B_q / p B_q`. Then there is
`g ∉ q` such that

* `h` is a nonzerodivisor in `B_g`, and
* `B_g / h B_g` is flat over `A`.

This is the statement the Stacks Project's proof of Tag 056Y isolates as "the corresponding
algebra statement". It strengthens
`Stacks.Flatness.exists_notMem_mem_nonZeroDivisors_away_and_forall_flat`, whose second
conclusion is the pointwise assertion that `B/hB` is flat over `A` at every prime of `D(g)`, to
the single flatness assertion over `D(g)` itself; the passage between the two is
`Module.flat_localizedModule_away_of_forall_flat_atPrime`. -/
theorem exists_notMem_mem_nonZeroDivisors_away_and_flat_quotient [IsNoetherianRing A]
    [IsNoetherianRing B] [Algebra.FiniteType A B] [Module.Flat A B]
    (q : Ideal B) [q.IsPrime] {h : B} (hhq : h ∈ q)
    (hreg : Ideal.Quotient.mk (Ideal.map (algebraMap A (Localization.AtPrime q))
        (q.comap (algebraMap A B))) (algebraMap B (Localization.AtPrime q) h) ∈
      nonZeroDivisors (Localization.AtPrime q ⧸
        Ideal.map (algebraMap A (Localization.AtPrime q)) (q.comap (algebraMap A B)))) :
    ∃ g ∈ q.primeCompl,
      algebraMap B (Localization.Away g) h ∈ nonZeroDivisors (Localization.Away g) ∧
        Module.Flat A (Localization.Away g ⧸
          Ideal.span {algebraMap B (Localization.Away g) h}) := by
  obtain ⟨g, hg, hnzd, hflat⟩ :=
    exists_notMem_mem_nonZeroDivisors_away_and_forall_flat q hhq hreg
  refine ⟨g, hg, hnzd, ?_⟩
  rw [flat_localizedModule_quotient_iff (Submonoid.powers g) h]
  exact Module.flat_localizedModule_away_of_forall_flat_atPrime
    fun q' hq' hgq' => hflat q' hq' hgq'

end Slice

end Stacks.Flatness

end
