module

public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.Homeomorph.Lemmas
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.ConstructibleStratification

/-!
# The localizations `A_Z^~` and the vanishing-pattern stratification of an affine spectrum

Let `A` be a ring and `X = Spec A`. For a locally closed subset `Z = D(f) ∩ V(I)` of `X` the
source localizes `A` at the multiplicative set of elements which are invertible on `Z`, and the
resulting `A`-algebra `A_Z^~` has `Spec` the set of points of `X` specializing to `Z`. Running
this construction over the strata of the vanishing pattern of a finite subset `E ⊆ A` and then
over all finite subsets is how the source builds the canonical w-local cover `A → A_w`.

This file provides the two inputs to that construction: the algebra `A_Z^~`, with all four
assertions of the source's localization lemma, and the vanishing-pattern stratification, with
the identification of each stratum as a locally closed subset of the above shape and the fact
that the strata partition `X`.

## Main definitions

* `AlgebraicGeometry.ProEtale.nonvanishingSubmonoid`: the multiplicative subset of `A` of
  elements lying in no prime of a prescribed subset `Z` of `Spec A`. Localizing at it gives the
  algebra the source calls `A_Z^~`.
* `AlgebraicGeometry.ProEtale.basicLocallyClosed`: the locally closed subset `D(f) ∩ V(I)`.
* `AlgebraicGeometry.ProEtale.homeomorphSetOfSpecializesTo`: the homeomorphism of
  `Spec (A_Z^~)` onto the set of points of `Spec A` specializing to `Z`.
* `AlgebraicGeometry.ProEtale.algEquivOfBasicLocallyClosedEq`: the comparison isomorphism
  between the algebras attached to two presentations of the same locally closed subset.
* `AlgebraicGeometry.ProEtale.quotientAwayLift`: the canonical map from `A_Z^~` onto the ring of
  functions `Γ(Z, 𝒪_Z) = (A/I)_f` of the stratum.
* `AlgebraicGeometry.ProEtale.basicStratum`: the locally closed subset on which the elements
  of one finite set are invertible and those of another vanish.
* `AlgebraicGeometry.ProEtale.vanishingPatternStratum`: the stratum of the vanishing pattern
  `σ : A → Bool` on a finite subset `E ⊆ A`, where `σ g` true means that `g` vanishes.

## Main results

* `AlgebraicGeometry.ProEtale.range_comap_algebraMap`: assertion (1) of Tag 096V, the image of
  `Spec (A_Z^~)` is the set of points specializing to `Z`.
* `AlgebraicGeometry.ProEtale.nonvanishingSubmonoid_eq_of_basicLocallyClosed_eq`: assertion (2),
  the multiplicative set the source localizes at depends only on the subset `Z`.
* `AlgebraicGeometry.ProEtale.surjective_quotientAwayLift`: assertion (3), `Z` is cut out in
  `Spec (A_Z^~)` by a surjection of rings.
* `AlgebraicGeometry.ProEtale.existsUnique_ringHom_comp_algebraMap`: the final assertion, the
  unique `A`-algebra map induced by a ring map carrying one locally closed subset into another.
* `AlgebraicGeometry.ProEtale.mem_nonvanishingSubmonoid_iff_isUnit`: the submonoid localized at
  is the source's own — the elements invertible in `Γ(Z, 𝒪_Z)`.
* `AlgebraicGeometry.ProEtale.basicStratum_eq_basicLocallyClosed`: equation 096W, a stratum is
  `D(∏ E') ∩ V(∑ E'' A)`.
* `AlgebraicGeometry.ProEtale.exists_mem_vanishingPatternStratum`,
  `AlgebraicGeometry.ProEtale.vanishingPatternStratum_disjoint` and
  `AlgebraicGeometry.ProEtale.isConstructible_basicStratum`: equation 096X, the strata of a
  vanishing pattern cover `Spec A`, are pairwise disjoint, and are constructible.
* `AlgebraicGeometry.ProEtale.isPartition_vanishingPatternStrata` and
  `AlgebraicGeometry.ProEtale.finite_vanishingPatternStrata`: the strata form a finite partition,
  which is the input shape of Tag 096Y.

## Implementation notes

The source defines `S ⊆ A` as the set of elements mapping to invertible elements of
`Γ(Z, 𝒪_Z) = (A/I)_f`. Here `nonvanishingSubmonoid Z` is instead defined as the set of elements
lying in no prime of `Z`, which is manifestly a submonoid and manifestly a function of the
*subset* `Z` alone. The two descriptions agree: membership is equivalent to
`f ^ n - a * b ∈ I` for some `n` and `b` (`mem_nonvanishingSubmonoid_basicLocallyClosed`), and
therefore to invertibility of the image of `a` in `(A/I)_f`
(`mem_nonvanishingSubmonoid_iff_isUnit`). That agreement is what makes assertion (2) of the
source available at all; with the set-level definition the assertion itself is a rewrite of the
explicit condition along the equality of subsets. Elementary radical arguments replace the
source's passage through `Γ(Z, 𝒪_Z)` in the proofs: a prime fails to specialize into `Z`
precisely when some power of `f` lies in its sum with `I`.

The algebra `A_Z^~` is never fixed to a particular model. Every statement takes an arbitrary
`A`-algebra `B` with `IsLocalization (nonvanishingSubmonoid Z) B`, so `Localization` and any
other construction of the localization are covered at once. Assertions about `Z` as a closed
subscheme are stated for an arbitrary localization `C` of `A/I` away from the image of `f`.

Functoriality is proved for arbitrary subsets `Z ⊆ Spec A` and `Z' ⊆ Spec A'`, since the
argument uses nothing about their shape; the source's locally closed subsets are a special case.

The strata of a vanishing pattern are indexed by a Boolean-valued function `σ` on `A` rather
than by a decomposition `E = E' ⨿ E''`. The two indexings carry the same information — `E'` and
`E''` are the two filters of `E` along `σ` — and the functional one needs no `DecidableEq A` and
makes the behaviour of a stratum under enlarging `E` a monotonicity statement in `E` alone.

## References

* [Stacks Project, Tag 096V](https://stacks.math.columbia.edu/tag/096V)
* [Stacks Project, Tag 096W](https://stacks.math.columbia.edu/tag/096W)
* [Stacks Project, Tag 096X](https://stacks.math.columbia.edu/tag/096X)
* [Stacks Project, Tag 096Y](https://stacks.math.columbia.edu/tag/096Y)
* [Stacks Project, Tag 0975](https://stacks.math.columbia.edu/tag/0975)
-/

@[expose] public section

namespace AlgebraicGeometry.ProEtale

open PrimeSpectrum

universe u

variable {A : Type u} [CommRing A]

/-! ## The multiplicative set of elements nonvanishing on a subset of the spectrum -/

/-- The elements of `A` lying in no prime belonging to `Z ⊆ Spec A`, that is, the elements
vanishing at no point of `Z`. Localizing `A` at this submonoid is the source's `A_Z^~`. -/
def nonvanishingSubmonoid (Z : Set (PrimeSpectrum A)) : Submonoid A where
  carrier := {a : A | ∀ q ∈ Z, a ∉ q.asIdeal}
  one_mem' q _ := q.asIdeal.primeCompl.one_mem
  mul_mem' ha hb q hq hmem := (q.isPrime.mem_or_mem hmem).elim (ha q hq) (hb q hq)

/-- Membership in `nonvanishingSubmonoid Z` unfolds to lying in no prime of `Z`. -/
theorem mem_nonvanishingSubmonoid {Z : Set (PrimeSpectrum A)} {a : A} :
    a ∈ nonvanishingSubmonoid Z ↔ ∀ q ∈ Z, a ∉ q.asIdeal := Iff.rfl

/-- Shrinking the subset enlarges the submonoid of elements nonvanishing on it. -/
theorem nonvanishingSubmonoid_le_of_subset {Z Z' : Set (PrimeSpectrum A)} (h : Z' ⊆ Z) :
    nonvanishingSubmonoid Z ≤ nonvanishingSubmonoid Z' :=
  fun _ ha q hq ↦ ha q (h hq)

/-- A ring map carrying `Z'` into `Z` pulls elements nonvanishing on `Z` back to elements
nonvanishing on `Z'`. -/
theorem nonvanishingSubmonoid_le_comap {A' : Type u} [CommRing A'] (φ : A →+* A')
    {Z : Set (PrimeSpectrum A)} {Z' : Set (PrimeSpectrum A')}
    (h : PrimeSpectrum.comap φ '' Z' ⊆ Z) :
    nonvanishingSubmonoid Z ≤ (nonvanishingSubmonoid Z').comap φ :=
  fun _ ha q' hq' hmem ↦ ha (PrimeSpectrum.comap φ q') (h ⟨q', hq', rfl⟩) hmem

/-- **Stacks Project, Tag 096V**, the final assertion. A ring map `A → A'` carrying a subset
`Z' ⊆ Spec A'` into a subset `Z ⊆ Spec A` induces exactly one `A`-algebra map
`A_Z^~ → (A')_{Z'}^~`. -/
@[stacks 096V "functoriality: the unique induced algebra map"]
theorem existsUnique_ringHom_comp_algebraMap {A' : Type u} [CommRing A'] (φ : A →+* A')
    {Z : Set (PrimeSpectrum A)} {Z' : Set (PrimeSpectrum A')}
    (h : PrimeSpectrum.comap φ '' Z' ⊆ Z) (B : Type u) [CommRing B] [Algebra A B]
    [IsLocalization (nonvanishingSubmonoid Z) B] (B' : Type u) [CommRing B'] [Algebra A' B']
    [IsLocalization (nonvanishingSubmonoid Z') B'] :
    ∃! ψ : B →+* B', ψ.comp (algebraMap A B) = (algebraMap A' B').comp φ := by
  refine ⟨IsLocalization.map B' φ (nonvanishingSubmonoid_le_comap φ h),
    IsLocalization.map_comp _, fun ψ hψ ↦ ?_⟩
  exact IsLocalization.ringHom_ext (nonvanishingSubmonoid Z)
    (hψ.trans (IsLocalization.map_comp (M := nonvanishingSubmonoid Z)
      (T := nonvanishingSubmonoid Z') (S := B) (Q := B') (g := φ)
      (nonvanishingSubmonoid_le_comap φ h)).symm)

/-- For nested subsets `Z' ⊆ Z` of `Spec A` there is exactly one `A`-algebra map
`A_Z^~ → A_{Z'}^~`. These are the transition maps of the source's system over the finite subsets
of `A`. -/
theorem existsUnique_ringHom_of_subset {Z Z' : Set (PrimeSpectrum A)} (h : Z' ⊆ Z) (B : Type u)
    [CommRing B] [Algebra A B] [IsLocalization (nonvanishingSubmonoid Z) B] (B' : Type u)
    [CommRing B'] [Algebra A B'] [IsLocalization (nonvanishingSubmonoid Z') B'] :
    ∃! ψ : B →+* B', ψ.comp (algebraMap A B) = algebraMap A B' := by
  simpa using existsUnique_ringHom_comp_algebraMap (RingHom.id A) (by simpa using h) B B'

/-! ## Locally closed subsets of the form `D(f) ∩ V(I)` -/

/-- The locally closed subset `D(f) ∩ V(I)` of `Spec A`. These are the subsets to which the
source's localization lemma applies. -/
def basicLocallyClosed (f : A) (I : Ideal A) : Set (PrimeSpectrum A) :=
  (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum A)) ∩ PrimeSpectrum.zeroLocus (I : Set A)

/-- A prime lies in `D(f) ∩ V(I)` exactly when it avoids `f` and contains `I`. -/
theorem mem_basicLocallyClosed {f : A} {I : Ideal A} {q : PrimeSpectrum A} :
    q ∈ basicLocallyClosed f I ↔ f ∉ q.asIdeal ∧ I ≤ q.asIdeal := by
  simp [basicLocallyClosed, PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe]

/-- If no power of `f` lies in an ideal `J`, some prime containing `J` avoids `f`. -/
private theorem exists_prime_le_notMem_of_forall_pow_notMem {J : Ideal A} {f : A}
    (h : ∀ n : ℕ, f ^ n ∉ J) : ∃ q : PrimeSpectrum A, J ≤ q.asIdeal ∧ f ∉ q.asIdeal := by
  obtain ⟨q, hq, hle, hdis⟩ := Ideal.exists_le_prime_disjoint J (Submonoid.powers f)
    (Set.disjoint_right.2 (by rintro - ⟨n, rfl⟩; exact h n))
  exact ⟨⟨q, hq⟩, hle, by simpa using Set.disjoint_right.mp hdis (Submonoid.mem_powers f)⟩

/-- An element is nonvanishing on `D(f) ∩ V(I)` exactly when its image in `A/I` divides a power
of the image of `f`, which is the source's condition of being invertible in
`Γ(Z, 𝒪_Z) = (A/I)_f`. -/
theorem mem_nonvanishingSubmonoid_basicLocallyClosed {f : A} {I : Ideal A} {a : A} :
    a ∈ nonvanishingSubmonoid (basicLocallyClosed f I) ↔ ∃ n : ℕ, ∃ b : A, f ^ n - a * b ∈ I := by
  constructor
  · intro ha
    have hrad : ∃ n : ℕ, f ^ n ∈ I ⊔ Ideal.span {a} := by
      by_contra hcon
      push Not at hcon
      obtain ⟨q, hle, hf⟩ := exists_prime_le_notMem_of_forall_pow_notMem hcon
      exact ha q (mem_basicLocallyClosed.mpr ⟨hf, le_sup_left.trans hle⟩)
        (hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self a)))
    obtain ⟨n, hn⟩ := hrad
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hn
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp hz
    have hsub : f ^ n - a * b = y := by rw [← hyz]; ring
    exact ⟨n, b, hsub ▸ hy⟩
  · rintro ⟨n, b, h⟩ q hq hmem
    obtain ⟨hf, hI⟩ := mem_basicLocallyClosed.mp hq
    refine hf (q.isPrime.mem_of_pow_mem n ?_)
    have hfn : f ^ n = f ^ n - a * b + a * b := by ring
    rw [hfn]
    exact q.asIdeal.add_mem (hI h) (Ideal.mul_mem_right b _ hmem)

/-- Every power of `f` is nonvanishing on `D(f) ∩ V(I)`. -/
theorem pow_mem_nonvanishingSubmonoid (f : A) (I : Ideal A) (n : ℕ) :
    f ^ n ∈ nonvanishingSubmonoid (basicLocallyClosed f I) :=
  mem_nonvanishingSubmonoid_basicLocallyClosed.mpr ⟨n, 1, by simp⟩

/-- A prime avoids every element nonvanishing on `D(f) ∩ V(I)` exactly when it specializes to a
point of `D(f) ∩ V(I)`. -/
theorem disjoint_nonvanishingSubmonoid_iff_exists_specializes (f : A) (I : Ideal A)
    (p : PrimeSpectrum A) :
    Disjoint (nonvanishingSubmonoid (basicLocallyClosed f I) : Set A) (p.asIdeal : Set A) ↔
      ∃ q ∈ basicLocallyClosed f I, p ⤳ q := by
  constructor
  · intro hdisj
    obtain ⟨q, hle, hf⟩ := exists_prime_le_notMem_of_forall_pow_notMem (J := p.asIdeal ⊔ I) (f := f)
      fun n hmem ↦ by
      obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hmem
      refine Set.disjoint_left.mp hdisj
        (mem_nonvanishingSubmonoid_basicLocallyClosed.mpr ⟨n, 1, ?_⟩) hy
      have hsub : f ^ n - y * 1 = z := by rw [← hyz]; ring
      exact hsub ▸ hz
    exact ⟨q, mem_basicLocallyClosed.mpr ⟨hf, le_sup_right.trans hle⟩,
      (PrimeSpectrum.le_iff_specializes p q).mp (le_sup_left.trans hle)⟩
  · rintro ⟨q, hq, hpq⟩
    exact Set.disjoint_left.2 fun a ha hmem ↦
      ha q hq (((PrimeSpectrum.le_iff_specializes p q).mpr hpq) hmem)

/-- **Stacks Project, Tag 096V**, assertion (1). The spectrum of `A_Z^~` maps onto the set of
points of `Spec A` specializing to `Z = D(f) ∩ V(I)`. -/
@[stacks 096V "part (1), the image of Spec of the localization"]
theorem range_comap_algebraMap (f : A) (I : Ideal A) (B : Type u) [CommRing B] [Algebra A B]
    [IsLocalization (nonvanishingSubmonoid (basicLocallyClosed f I)) B] :
    Set.range (PrimeSpectrum.comap (algebraMap A B)) =
      {p : PrimeSpectrum A | ∃ q ∈ basicLocallyClosed f I, p ⤳ q} :=
  (PrimeSpectrum.localization_comap_range B
    (nonvanishingSubmonoid (basicLocallyClosed f I))).trans
      (Set.ext fun p ↦ disjoint_nonvanishingSubmonoid_iff_exists_specializes f I p)

/-- **Stacks Project, Tag 096V**, assertion (1) as the homeomorphism it asserts:
`Spec (A_Z^~)` is homeomorphic to the set of points of `Spec A` specializing to
`Z = D(f) ∩ V(I)`. -/
@[stacks 096V "part (1), the homeomorphism onto the set of specializations"]
noncomputable def homeomorphSetOfSpecializesTo (f : A) (I : Ideal A) (B : Type u) [CommRing B]
    [Algebra A B] [IsLocalization (nonvanishingSubmonoid (basicLocallyClosed f I)) B] :
    PrimeSpectrum B ≃ₜ {p : PrimeSpectrum A | ∃ q ∈ basicLocallyClosed f I, p ⤳ q} :=
  (PrimeSpectrum.localization_comap_isEmbedding B
    (nonvanishingSubmonoid (basicLocallyClosed f I))).toHomeomorph.trans
      (Homeomorph.setCongr (range_comap_algebraMap f I B))

/-- **Stacks Project, Tag 096V**, assertion (2). The source's multiplicative set — the elements
whose image in `A/I` divides a power of the image of `f` — depends only on the underlying subset
`D(f) ∩ V(I)`, and so therefore does `A_Z^~`. -/
@[stacks 096V "part (2), dependence only on the underlying subset"]
theorem nonvanishingSubmonoid_eq_of_basicLocallyClosed_eq {f f' : A} {I I' : Ideal A}
    (h : basicLocallyClosed f I = basicLocallyClosed f' I') (a : A) :
    (∃ n : ℕ, ∃ b : A, f ^ n - a * b ∈ I) ↔ ∃ n : ℕ, ∃ b : A, f' ^ n - a * b ∈ I' := by
  rw [← mem_nonvanishingSubmonoid_basicLocallyClosed,
    ← mem_nonvanishingSubmonoid_basicLocallyClosed, h]

/-- Two presentations of the same locally closed subset localize `A` at the same submonoid. -/
theorem nonvanishingSubmonoid_congr {f f' : A} {I I' : Ideal A}
    (h : basicLocallyClosed f I = basicLocallyClosed f' I') :
    nonvanishingSubmonoid (basicLocallyClosed f I) =
      nonvanishingSubmonoid (basicLocallyClosed f' I') := by
  rw [h]

/-- **Stacks Project, Tag 096V**, assertion (2) as the statement about the algebra: the algebras
attached to two presentations of one locally closed subset are isomorphic as `A`-algebras. -/
@[stacks 096V "part (2), the algebra attached to the subset"]
noncomputable def algEquivOfBasicLocallyClosedEq {f f' : A} {I I' : Ideal A}
    (h : basicLocallyClosed f I = basicLocallyClosed f' I') (B B' : Type u) [CommRing B]
    [Algebra A B] [IsLocalization (nonvanishingSubmonoid (basicLocallyClosed f I)) B]
    [CommRing B'] [Algebra A B']
    [IsLocalization (nonvanishingSubmonoid (basicLocallyClosed f' I')) B'] : B ≃ₐ[A] B' :=
  haveI : IsLocalization (nonvanishingSubmonoid (basicLocallyClosed f I)) B' :=
    nonvanishingSubmonoid_congr h ▸ inferInstance
  IsLocalization.algEquiv (nonvanishingSubmonoid (basicLocallyClosed f I)) B B'

/-- **Stacks Project, Tag 096V**, the topological half of assertion (3). Inside the image of
`Spec (A_Z^~)` the subset `Z = D(f) ∩ V(I)` is cut out by `I` alone: a prime specializing into
`Z` and containing `I` already avoids `f`, so `Z` is closed in that image. -/
@[stacks 096V "part (3), Z is closed in the image of Spec of the localization"]
theorem basicLocallyClosed_eq_range_inter_zeroLocus (f : A) (I : Ideal A) (B : Type u)
    [CommRing B] [Algebra A B]
    [IsLocalization (nonvanishingSubmonoid (basicLocallyClosed f I)) B] :
    basicLocallyClosed f I =
      Set.range (PrimeSpectrum.comap (algebraMap A B)) ∩ PrimeSpectrum.zeroLocus (I : Set A) := by
  rw [range_comap_algebraMap f I B]
  refine Set.ext fun p ↦ ⟨fun hp ↦ ⟨⟨p, hp, specializes_rfl⟩, ?_⟩, ?_⟩
  · exact (PrimeSpectrum.mem_zeroLocus _ _).mpr (mem_basicLocallyClosed.mp hp).2
  · rintro ⟨⟨q, hq, hpq⟩, hpI⟩
    refine mem_basicLocallyClosed.mpr ⟨fun hf ↦ (mem_basicLocallyClosed.mp hq).1 ?_, ?_⟩
    · exact ((PrimeSpectrum.le_iff_specializes p q).mpr hpq) hf
    · exact SetLike.coe_subset_coe.mp ((PrimeSpectrum.mem_zeroLocus _ _).mp hpI)

/-- The submonoid at which the source localizes is exactly the source's own: an element of `A`
is nonvanishing on `Z = D(f) ∩ V(I)` precisely when its image is invertible in
`Γ(Z, 𝒪_Z) = (A/I)_f`. -/
theorem mem_nonvanishingSubmonoid_iff_isUnit (f : A) (I : Ideal A) (C : Type u) [CommRing C]
    [Algebra (A ⧸ I) C] [IsLocalization.Away (Ideal.Quotient.mk I f) C] (a : A) :
    a ∈ nonvanishingSubmonoid (basicLocallyClosed f I) ↔
      IsUnit (algebraMap (A ⧸ I) C (Ideal.Quotient.mk I a)) := by
  rw [IsLocalization.Away.algebraMap_isUnit_iff (x := Ideal.Quotient.mk I f),
    mem_nonvanishingSubmonoid_basicLocallyClosed]
  constructor
  · rintro ⟨n, b, h⟩
    refine ⟨n, Ideal.Quotient.mk I b, ?_⟩
    rw [← map_pow, ← map_mul, ← sub_eq_zero, ← map_sub]
    exact (Ideal.Quotient.eq_zero_iff_mem).mpr h
  · rintro ⟨n, c, hc⟩
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective c
    refine ⟨n, b, ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, map_mul, hc, sub_self]

/-- An element nonvanishing on `D(f) ∩ V(I)` becomes a unit in a localization of `A/I` away from
the image of `f`. -/
theorem isUnit_quotientAway_of_mem (f : A) (I : Ideal A) (C : Type u) [CommRing C]
    [Algebra (A ⧸ I) C] [IsLocalization.Away (Ideal.Quotient.mk I f) C]
    (s : nonvanishingSubmonoid (basicLocallyClosed f I)) :
    IsUnit (((algebraMap (A ⧸ I) C).comp (Ideal.Quotient.mk I)) (s : A)) :=
  (mem_nonvanishingSubmonoid_iff_isUnit f I C (s : A)).mp s.2

/-- The canonical map from `A_Z^~` to the ring of functions `Γ(Z, 𝒪_Z) = (A/I)_f` of the
stratum `Z = D(f) ∩ V(I)`, obtained from `A → A/I → (A/I)_f` by the universal property of the
localization. -/
noncomputable def quotientAwayLift (f : A) (I : Ideal A) (B : Type u) [CommRing B] [Algebra A B]
    [IsLocalization (nonvanishingSubmonoid (basicLocallyClosed f I)) B] (C : Type u) [CommRing C]
    [Algebra (A ⧸ I) C] [IsLocalization.Away (Ideal.Quotient.mk I f) C] : B →+* C :=
  IsLocalization.lift (M := nonvanishingSubmonoid (basicLocallyClosed f I))
    (g := (algebraMap (A ⧸ I) C).comp (Ideal.Quotient.mk I)) (isUnit_quotientAway_of_mem f I C)

/-- **Stacks Project, Tag 096V**, assertion (3). The ring `A_Z^~` surjects onto
`Γ(Z, 𝒪_Z) = (A/I)_f`, so `Z` is a closed subscheme of `Spec (A_Z^~)`. -/
@[stacks 096V "part (3), Z is a closed subscheme of Spec of the localization"]
theorem surjective_quotientAwayLift (f : A) (I : Ideal A) (B : Type u) [CommRing B] [Algebra A B]
    [IsLocalization (nonvanishingSubmonoid (basicLocallyClosed f I)) B] (C : Type u) [CommRing C]
    [Algebra (A ⧸ I) C] [IsLocalization.Away (Ideal.Quotient.mk I f) C] :
    Function.Surjective (quotientAwayLift f I B C) := by
  intro c
  obtain ⟨⟨x, y⟩, rfl⟩ :=
    IsLocalization.mk'_surjective (Submonoid.powers (Ideal.Quotient.mk I f)) c
  obtain ⟨n, hn⟩ := y.2
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine ⟨IsLocalization.mk' B a ⟨f ^ n, pow_mem_nonvanishingSubmonoid f I n⟩, ?_⟩
  rw [IsLocalization.eq_mk'_iff_mul_eq]
  have hy : (algebraMap (A ⧸ I) C) (y : A ⧸ I) =
      quotientAwayLift f I B C (algebraMap A B (f ^ n)) := by
    rw [quotientAwayLift, IsLocalization.lift_eq]
    simp [← hn]
  rw [hy, ← map_mul, IsLocalization.mk'_spec, quotientAwayLift, IsLocalization.lift_eq]
  rfl

/-! ## The stratification of an affine spectrum by a vanishing pattern -/

/-- The set of points of `Spec A` at which every element of `E'` is invertible and every element
of `E''` vanishes, that is, `D(E') ∩ V(E'')`. These are the source's strata `Z(E', E'')`. -/
def basicStratum (E' E'' : Finset A) : Set (PrimeSpectrum A) :=
  {q : PrimeSpectrum A | (∀ g ∈ E', g ∉ q.asIdeal) ∧ ∀ g ∈ E'', g ∈ q.asIdeal}

/-- Membership in `basicStratum E' E''` unfolds to the prescribed vanishing behaviour. -/
theorem mem_basicStratum {E' E'' : Finset A} {q : PrimeSpectrum A} :
    q ∈ basicStratum E' E'' ↔
      (∀ g ∈ E', g ∉ q.asIdeal) ∧ ∀ g ∈ E'', g ∈ q.asIdeal := Iff.rfl

/-- **Stacks Project, Tag 096W.** The stratum `Z(E', E'')` is the locally closed subset
`D(∏_{f ∈ E'} f) ∩ V(∑_{f ∈ E''} f A)`, hence of the shape to which Tag 096V applies. -/
@[stacks 096W]
theorem basicStratum_eq_basicLocallyClosed (E' E'' : Finset A) :
    basicStratum E' E'' = basicLocallyClosed (∏ g ∈ E', g) (Ideal.span (E'' : Set A)) := by
  refine Set.ext fun q ↦ ?_
  rw [mem_basicStratum, mem_basicLocallyClosed, Ideal.span_le]
  refine and_congr ?_ ?_
  · rw [not_iff_not.mpr (Ideal.IsPrime.prod_mem_iff (hp := q.isPrime))]
    simp
  · simp [Set.subset_def]

/-- Prescribing the behaviour of fewer elements gives a larger stratum. -/
theorem basicStratum_subset {E' E'' F' F'' : Finset A} (h' : F' ⊆ E') (h'' : F'' ⊆ E'') :
    basicStratum E' E'' ⊆ basicStratum F' F'' :=
  fun _ hq ↦ ⟨fun g hg ↦ hq.1 g (h' hg), fun g hg ↦ hq.2 g (h'' hg)⟩

/-- **Stacks Project, Tag 096X**, the observation that each stratum is constructible: a stratum
is a finite intersection of basic opens and complements of basic opens. -/
@[stacks 096X "each stratum is constructible"]
theorem isConstructible_basicStratum (E' E'' : Finset A) :
    Topology.IsConstructible (basicStratum E' E'') := by
  have hD : ∀ g : A,
      Topology.IsConstructible ((PrimeSpectrum.basicOpen g : Set (PrimeSpectrum A))) := fun g ↦
    ((QuasiSeparatedSpace.isRetrocompact_iff_isCompact
      (PrimeSpectrum.basicOpen g).2).mpr (PrimeSpectrum.isCompact_basicOpen g)).isConstructible
        (PrimeSpectrum.basicOpen g).2
  have heq : basicStratum E' E'' =
      (⋂ g ∈ E', (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum A))) ∩
        ⋂ g ∈ E'', ((PrimeSpectrum.basicOpen g : Set (PrimeSpectrum A)))ᶜ := by
    ext q
    simp [mem_basicStratum]
  rw [heq]
  exact (Topology.IsConstructible.biInter E'.finite_toSet fun g _ ↦ hD g).inter
    (Topology.IsConstructible.biInter E''.finite_toSet fun g _ ↦ (hD g).compl)

/-- The stratum of `Spec A` on which the elements of the finite set `E` have vanishing pattern
`σ`: an element `g ∈ E` vanishes where `σ g` is true and is invertible where it is false. The
decomposition `E = E' ⨿ E''` of the source is the pair of filters of `E` along `σ`. -/
def vanishingPatternStratum (E : Finset A) (σ : A → Bool) : Set (PrimeSpectrum A) :=
  basicStratum (E.filter fun g ↦ ¬ σ g) (E.filter fun g ↦ σ g)

/-- Membership in a vanishing-pattern stratum says that the vanishing pattern of `q` on `E`
is `σ`. -/
theorem mem_vanishingPatternStratum {E : Finset A} {σ : A → Bool} {q : PrimeSpectrum A} :
    q ∈ vanishingPatternStratum E σ ↔ ∀ g ∈ E, (g ∈ q.asIdeal ↔ σ g) := by
  simp only [vanishingPatternStratum, mem_basicStratum, Finset.mem_filter]
  constructor
  · rintro ⟨hout, hin⟩ g hg
    refine ⟨fun hgq ↦ ?_, fun hσ ↦ hin g ⟨hg, hσ⟩⟩
    by_contra hσ
    exact hout g ⟨hg, by simpa using hσ⟩ hgq
  · intro h
    exact ⟨fun g hg hgq ↦ (by simpa using hg.2 : ¬ (σ g = true)) ((h g hg.1).mp hgq),
      fun g hg ↦ (h g hg.1).mpr hg.2⟩

/-- A vanishing-pattern stratum is locally closed of the shape required by Tag 096V. -/
theorem vanishingPatternStratum_eq_basicLocallyClosed (E : Finset A) (σ : A → Bool) :
    vanishingPatternStratum E σ =
      basicLocallyClosed (∏ g ∈ E.filter (fun g ↦ ¬ σ g), g)
        (Ideal.span ((E.filter fun g ↦ σ g : Finset A) : Set A)) :=
  basicStratum_eq_basicLocallyClosed _ _

/-- Each stratum of a vanishing pattern is constructible. -/
theorem isConstructible_vanishingPatternStratum (E : Finset A) (σ : A → Bool) :
    Topology.IsConstructible (vanishingPatternStratum E σ) :=
  isConstructible_basicStratum _ _

/-- Only the restriction of the pattern to `E` matters. -/
theorem vanishingPatternStratum_congr {E : Finset A} {σ τ : A → Bool}
    (h : ∀ g ∈ E, σ g = τ g) :
    vanishingPatternStratum E σ = vanishingPatternStratum E τ :=
  Set.ext fun q ↦ by
    rw [mem_vanishingPatternStratum, mem_vanishingPatternStratum]
    exact forall₂_congr fun g hg ↦ by rw [h g hg]

/-- Enlarging the finite set shrinks each stratum of a vanishing pattern. This is the inclusion
along which the source's transition maps are built. -/
theorem vanishingPatternStratum_subset_of_subset {E₁ E₂ : Finset A} (h : E₁ ⊆ E₂)
    (σ : A → Bool) : vanishingPatternStratum E₂ σ ⊆ vanishingPatternStratum E₁ σ :=
  fun _ hq ↦ mem_vanishingPatternStratum.mpr
    fun g hg ↦ mem_vanishingPatternStratum.mp hq g (h hg)

/-- The vanishing-pattern stratum of a pattern agreeing on `E` with the vanishing pattern of `p`
is the fiber of `p`. -/
private theorem vanishingPatternStratum_eq_fiber {E : Finset A} {σ : A → Bool}
    {p : PrimeSpectrum A} (h : ∀ g ∈ E, (g ∈ p.asIdeal ↔ σ g)) :
    vanishingPatternStratum E σ = {q | ∀ f ∈ E, (f ∈ p.asIdeal ↔ f ∈ q.asIdeal)} :=
  Set.ext fun q ↦ by
    rw [mem_vanishingPatternStratum]
    exact forall₂_congr fun g hg ↦ by rw [← h g hg]; tauto

/-- **Stacks Project, Tag 096X**, the covering half. Every point of `Spec A` lies in the stratum
of its own vanishing pattern on `E`. -/
@[stacks 096X "the strata cover the spectrum"]
theorem exists_mem_vanishingPatternStratum (E : Finset A) (q : PrimeSpectrum A) :
    ∃ σ : A → Bool, q ∈ vanishingPatternStratum E σ := by
  classical
  refine ⟨fun g ↦ decide (g ∈ q.asIdeal), mem_vanishingPatternStratum.mpr fun g _ ↦ ?_⟩
  simp

/-- A point determines its vanishing pattern on `E`. -/
theorem eqOn_of_mem_vanishingPatternStratum {E : Finset A} {σ τ : A → Bool}
    {q : PrimeSpectrum A} (hσ : q ∈ vanishingPatternStratum E σ)
    (hτ : q ∈ vanishingPatternStratum E τ) : ∀ g ∈ E, σ g = τ g := by
  intro g hg
  simpa using (mem_vanishingPatternStratum.mp hσ g hg).symm.trans
    (mem_vanishingPatternStratum.mp hτ g hg)

/-- **Stacks Project, Tag 096X**, the disjointness half. Two vanishing patterns differing on `E`
have disjoint strata. -/
@[stacks 096X "the strata are pairwise disjoint"]
theorem vanishingPatternStratum_disjoint {E : Finset A} {σ τ : A → Bool}
    (h : ∃ g ∈ E, σ g ≠ τ g) :
    Disjoint (vanishingPatternStratum E σ) (vanishingPatternStratum E τ) := by
  obtain ⟨g, hg, hne⟩ := h
  exact Set.disjoint_left.2 fun q hσ hτ ↦ hne (eqOn_of_mem_vanishingPatternStratum hσ hτ g hg)

/-- The strata recorded by `vanishingPatternStrata` are exactly the nonempty strata of a
vanishing pattern, so the refinement supplied by Tag 096Y is a refinement by the strata
constructed here. -/
theorem exists_eq_vanishingPatternStratum (E : Finset A) {T : Set (PrimeSpectrum A)}
    (hT : T ∈ vanishingPatternStrata E) : ∃ σ : A → Bool, T = vanishingPatternStratum E σ := by
  classical
  obtain ⟨p, rfl⟩ := hT
  exact ⟨fun g ↦ decide (g ∈ p.asIdeal),
    (vanishingPatternStratum_eq_fiber fun g _ ↦ (decide_eq_true_iff).symm).symm⟩

/-- Conversely, a nonempty stratum of a vanishing pattern on `E` is recorded by
`vanishingPatternStrata E`. -/
theorem vanishingPatternStratum_mem_vanishingPatternStrata (E : Finset A) (σ : A → Bool)
    (hne : (vanishingPatternStratum E σ).Nonempty) :
    vanishingPatternStratum E σ ∈ vanishingPatternStrata E := by
  obtain ⟨p, hp⟩ := hne
  exact ⟨p, (vanishingPatternStratum_eq_fiber (mem_vanishingPatternStratum.mp hp)).symm⟩

/-- No stratum recorded by `vanishingPatternStrata` is empty: the fiber through a point contains
that point. -/
theorem notMem_vanishingPatternStrata_empty (E : Finset A) :
    (∅ : Set (PrimeSpectrum A)) ∉ vanishingPatternStrata E := by
  rintro ⟨p, hp⟩
  exact (Set.eq_empty_iff_forall_notMem.mp hp) p fun _ _ ↦ Iff.rfl

/-- The strata of the vanishing pattern of `E` form a partition of `Spec A`. Together with
`finite_vanishingPatternStrata` and `isConstructible_vanishingPatternStratum` this is the input
shape of Tag 096Y, so the refinement supplied by that lemma can be iterated. -/
theorem isPartition_vanishingPatternStrata (E : Finset A) :
    Setoid.IsPartition (vanishingPatternStrata E) := by
  refine ⟨notMem_vanishingPatternStrata_empty E, fun q ↦ ?_⟩
  refine ⟨{r : PrimeSpectrum A | ∀ f ∈ E, (f ∈ q.asIdeal ↔ f ∈ r.asIdeal)},
    ⟨⟨q, rfl⟩, fun _ _ ↦ Iff.rfl⟩, ?_⟩
  rintro T ⟨⟨p, rfl⟩, hqT⟩
  exact Set.ext fun r ↦ ⟨fun h f hf ↦ (hqT f hf).symm.trans (h f hf),
    fun h f hf ↦ (hqT f hf).trans (h f hf)⟩

/-- There are only finitely many strata of a vanishing pattern on a finite set `E`, since a
stratum is determined by the pattern of any of its points on `E`. -/
theorem finite_vanishingPatternStrata (E : Finset A) : (vanishingPatternStrata E).Finite := by
  classical
  refine Set.Finite.subset (Set.finite_range (fun σ : {g : A // g ∈ E} → Bool ↦
    {q : PrimeSpectrum A | ∀ g : {g : A // g ∈ E}, (g.1 ∈ q.asIdeal ↔ σ g)})) ?_
  rintro T ⟨p, rfl⟩
  refine ⟨fun g ↦ decide (g.1 ∈ p.asIdeal), Set.ext fun q ↦ ?_⟩
  simp only [decide_eq_true_eq, Subtype.forall]
  exact forall₂_congr fun g _ ↦ by tauto

end AlgebraicGeometry.ProEtale
