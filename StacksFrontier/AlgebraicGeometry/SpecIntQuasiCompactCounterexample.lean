module

public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.Localization
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Sites.Canonical
public import Mathlib.Data.Nat.Prime.Int
public import Mathlib.Data.Set.Card.Arithmetic
public import Mathlib.Order.Filter.Ultrafilter.Basic
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.TensorProduct.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EffectiveEpi.FromAffine
public import StacksFrontier.AlgebraicGeometry.Descent.EffectiveEpi.Surjective
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact
public import StacksFrontier.Topology.Spectral.ConstructibleTopology
public import StacksFrontier.Topology.Spectral.ConstructiblyClosedStable

/-!
# The spectrum of the integers is not quasi-compact for the canonical topology

The canonical topology on the category of schemes has a covering of `Spec(ℤ)` that cannot be
refined by a covering factoring through finitely many of its members, so `Spec(ℤ)` is not a
quasi-compact object of the canonical site: this is **Stacks 0EUG**.

## Main results

* `specInt_not_isQuasiCompactObject_canonicalTopology` — the spectrum of the integers is not a
  quasi-compact object of the canonical site of schemes.

## Implementation notes

The statement is about the ordinary spectrum of the integers, so the ambient category is
`Scheme.{0}`: `ℤ` is a type in the bottom universe and the tag is about that scheme and not
about a lift of it. `IsQuasiCompactObject` is the site-theoretic notion of
`StacksFrontier.CategoryTheory.Sites.QuasiCompact`: every covering family admits a covering
refinement through finitely many of its members.

The descent arguments for the affine criterion of Stacks 0EUD,
`AlgebraicGeometry.isUniversalEffectiveEpiFamily_of_affine_of_submersive`, happen in
`AffineScheme`, where the underlying scheme of an object is reached through the projection of a
semireducible definition. Every morphism and isomorphism of schemes used in them is therefore bound
with its source and target written in one fixed spelling, so that the goals rewriting acts on are
type-correct without unfolding that definition.

## References

* [Stacks Project, Tag 0EUG](https://stacks.math.columbia.edu/tag/0EUG)
-/

public section

open AlgebraicGeometry CategoryTheory

namespace Stacks.AlgebraicGeometry.SpecIntQuasiCompactCounterexample

universe u

/-! A nonprincipal ultrafilter on the (infinite) type of primes: the hyperfilter, which extends
the cofinite filter. -/

private noncomputable def primeUltrafilter : Ultrafilter Nat.Primes :=
  Filter.hyperfilter Nat.Primes

private theorem primeUltrafilter_mem_infinite {A : Set Nat.Primes}
    (hA : A ∈ primeUltrafilter) : A.Infinite := by
  intro hfinite
  have hcofinite : Aᶜ ∈ (Filter.cofinite : Filter Nat.Primes) := by
    simp [hfinite]
  have hnot : Aᶜ ∈ primeUltrafilter :=
    Ultrafilter.of_le (Filter.cofinite : Filter Nat.Primes) hcofinite
  have hempty : (∅ : Set Nat.Primes) ∈ primeUltrafilter := by
    simpa using Filter.inter_mem hA hnot
  exact Ultrafilter.empty_notMem (f := primeUltrafilter) hempty

private theorem finite_of_diff_mem_ultrafilter_finite {α : Type*}
    (U : Ultrafilter α) {S : Set α}
    (h : ∀ A ∈ U, (S \ A).Finite) : S.Finite := by
  by_contra hS
  obtain ⟨T, V, hTV, hd, hcard⟩ :=
    Set.Infinite.exists_union_disjoint_cardinal_eq_of_infinite hS
  have hfin : T.Finite ↔ V.Finite := by
    rw [← Cardinal.lt_aleph0_iff_set_finite,
      ← Cardinal.lt_aleph0_iff_set_finite, hcard]
  have hnT : T.Infinite := fun hf => hS (hTV ▸ hf.union (hfin.mp hf))
  have hnV : V.Infinite := fun hf => hnT (hfin.mpr hf)
  rcases U.mem_or_compl_mem T with hT | hT
  · apply hnV
    apply (h T hT).subset
    intro x hx
    exact ⟨hTV ▸ Set.mem_union_right T hx, fun hxT => Set.disjoint_left.mp hd hxT hx⟩
  · apply hnT
    apply (h Tᶜ hT).subset
    intro x hx
    exact ⟨hTV ▸ Set.mem_union_left V hx, by simpa using hx⟩

private theorem isCompact_of_ultrafilter_restrictions {α X : Type*}
    [TopologicalSpace X] (U : Ultrafilter α) (hU : (U : Filter α) ≤ Filter.cofinite)
    (V : α → Set X) (hV : ∀ a, IsOpen (V a))
    (hd : Pairwise fun a b => Disjoint (V a) (V b)) (T : Set X)
    (hcompact : ∀ A ∈ U, IsCompact (T \ ⋃ a ∈ A, V a)) : IsCompact T := by
  classical
  apply isCompact_of_finite_subcover
  intro ι O hO hTO
  have hgeneric := hcompact Set.univ (Filter.univ_mem : Set.univ ∈ U)
  simp only [Set.mem_univ, Set.iUnion_true] at hgeneric
  obtain ⟨F, hF⟩ := hgeneric.elim_finite_subcover O hO
    (Set.Subset.trans Set.sdiff_subset hTO)
  let W : Set X := ⋃ i ∈ F, O i
  have hW : IsOpen W := isOpen_biUnion (fun i _ => hO i)
  let K : Set X := T \ W
  have hKV : K ⊆ ⋃ a, V a := by
    intro x hx
    by_contra hn
    exact hx.2 (hF ⟨hx.1, hn⟩)
  have hKcompact (A : Set α) (hA : A ∈ U) :
      IsCompact (K \ ⋃ a ∈ A, V a) := by
    have h := (hcompact A hA).diff hW
    convert h using 1
    ext x
    simp only [K, Set.mem_sdiff]
    tauto
  let S : Set α := {a | (K ∩ V a).Nonempty}
  have hS : S.Finite := by
    apply finite_of_diff_mem_ultrafilter_finite U
    intro A hA
    obtain ⟨G, hG⟩ := (hKcompact A hA).elim_finite_subcover V hV
      (Set.Subset.trans Set.sdiff_subset hKV)
    apply G.finite_toSet.subset
    rintro a ⟨⟨x, hxK, hxa⟩, haA⟩
    have hx : x ∈ K \ ⋃ b ∈ A, V b := by
      refine ⟨hxK, ?_⟩
      simp only [Set.mem_iUnion]
      rintro ⟨b, hbA, hxb⟩
      have hab : a ≠ b := fun e => haA (e ▸ hbA)
      exact Set.disjoint_left.mp (hd hab) hxa hxb
    obtain ⟨b, hbG, hxb⟩ := Set.mem_iUnion₂.mp (hG hx)
    have hab : a = b := by
      by_contra hn
      exact Set.disjoint_left.mp (hd hn) hxa hxb
    exact hab ▸ hbG
  have hAc : Sᶜ ∈ U := hU (by simpa using hS)
  have hK : IsCompact K := by
    convert hKcompact Sᶜ hAc using 1
    ext x
    constructor
    · intro hx
      refine ⟨hx, ?_⟩
      simp only [Set.mem_iUnion]
      rintro ⟨a, ha, hxa⟩
      exact ha ⟨x, hx, hxa⟩
    · exact fun hx => hx.1
  obtain ⟨G, hG⟩ := hK.elim_finite_subcover O hO
    (Set.Subset.trans Set.sdiff_subset hTO)
  refine ⟨F ∪ G, ?_⟩
  intro x hx
  by_cases hxW : x ∈ W
  · obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hxW
    exact Set.mem_iUnion₂.mpr ⟨i, Finset.mem_union_left G hi, hxi⟩
  · obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (hG ⟨hx, hxW⟩)
    exact Set.mem_iUnion₂.mpr ⟨i, Finset.mem_union_right F hi, hxi⟩

private theorem primeUltrafilter_common_mem_finite {ι : Type*} (s : Set ι)
    (hs : s.Finite) (A : ι → Set Nat.Primes)
    (hA : ∀ i ∈ s, A i ∈ primeUltrafilter) :
    ∃ p : Nat.Primes, ∀ i ∈ s, p ∈ A i := by
  have hInter : (⋂ i ∈ s, A i) ∈ primeUltrafilter :=
    (Filter.biInter_mem hs).2 hA
  obtain ⟨p, hp⟩ := (primeUltrafilter_mem_infinite hInter).nonempty
  exact ⟨p, by simpa only [Set.mem_iInter] using hp⟩

/-! For `A` in the ultrafilter, localize the integers by inverting the primes
belonging to `A`. -/

private def primeLocalizationSubmonoid (A : Set Nat.Primes) : Submonoid ℤ :=
  Submonoid.closure {z : ℤ | ∃ p : Nat.Primes, p ∈ A ∧ z = p.val}

private abbrev primeLocalization (A : Set Nat.Primes) :=
  Localization (primeLocalizationSubmonoid A)

private noncomputable def primeLocalizationToSpecInt (A : Set Nat.Primes) :
    Spec (CommRingCat.of (primeLocalization A)) ⟶ Spec (CommRingCat.of ℤ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℤ (primeLocalization A)))

private abbrev primeLocalizationIndex :=
  {A : Set Nat.Primes // A ∈ primeUltrafilter}

private noncomputable abbrev primeLocalizationFamilySource (A : primeLocalizationIndex) : Scheme :=
  Spec (CommRingCat.of (primeLocalization A.val))

private noncomputable abbrev primeLocalizationFamilyMap (A : primeLocalizationIndex) :
    primeLocalizationFamilySource A ⟶ Spec (CommRingCat.of ℤ) :=
  primeLocalizationToSpecInt A.val

private theorem primeLocalizationIndex_common_prime (s : Set primeLocalizationIndex)
    (hs : s.Finite) : ∃ p : Nat.Primes, ∀ A ∈ s, p ∈ A.val := by
  exact primeUltrafilter_common_mem_finite s hs (fun A => A.val) fun A _ => A.property

private theorem primeLocalization_isUnit (A : Set Nat.Primes) (p : Nat.Primes)
    (hp : p ∈ A) : IsUnit (algebraMap ℤ (primeLocalization A) p.val) := by
  exact IsLocalization.map_units (M := primeLocalizationSubmonoid A)
    (primeLocalization A)
    ⟨(p.val : ℤ), Submonoid.subset_closure ⟨p, hp, rfl⟩⟩

private noncomputable def primeLocalizationAwayMap (A : Set Nat.Primes)
    (p : Nat.Primes) (hp : p ∈ A) :
    Localization.Away (p.val : ℤ) →+* primeLocalization A :=
  IsLocalization.lift (M := Submonoid.powers (p.val : ℤ))
    (S := Localization.Away (p.val : ℤ))
    (g := algebraMap ℤ (primeLocalization A)) <| by
    rintro ⟨x, n, rfl⟩
    change IsUnit (algebraMap ℤ (primeLocalization A) ((p.val : ℤ) ^ n))
    rw [map_pow]
    exact (primeLocalization_isUnit A p hp).pow n

private theorem primeLocalizationAwayMap_comp (A : Set Nat.Primes) (p : Nat.Primes)
    (hp : p ∈ A) :
    (primeLocalizationAwayMap A p hp).comp
      (algebraMap ℤ (Localization.Away (p.val : ℤ))) =
        algebraMap ℤ (primeLocalization A) := by
  ext z
  simp [primeLocalizationAwayMap]

private theorem primeLocalizationToSpecInt_factors (A : Set Nat.Primes)
    (p : Nat.Primes) (hp : p ∈ A) :
    primeLocalizationToSpecInt A =
      Spec.map (CommRingCat.ofHom (primeLocalizationAwayMap A p hp)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap ℤ (Localization.Away (p.val : ℤ)))) := by
  rw [primeLocalizationToSpecInt, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    primeLocalizationAwayMap_comp A p hp]

private noncomputable def closedPrimePoint (p : Nat.Primes) : PrimeSpectrum ℤ := by
  have hnz : (p.val : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr p.2.ne_zero
  have hp : Prime (p.val : ℤ) :=
    (Nat.prime_iff_prime_int (p := (p.val : ℕ))).mp p.2
  have hI : (Ideal.span {(p.val : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime hnz).2 hp
  exact ⟨Ideal.span {(p.val : ℤ)}, hI⟩

private theorem closedPrimePoint_not_mem_basicOpen (p : Nat.Primes) :
    closedPrimePoint p ∉ PrimeSpectrum.basicOpen (p.val : ℤ) := by
  rw [PrimeSpectrum.mem_basicOpen]
  push Not
  show (p.val : ℤ) ∈ Ideal.span {(p.val : ℤ)}
  exact Ideal.mem_span_singleton_self _

/-! A finite collection of members of the localization family misses a closed point.
The common prime belongs to every inverted multiplicative set, so every map factors
through the basic open obtained by deleting that point. -/

private theorem primeLocalizationToSpecInt_range_subset_basicOpen
    (A : Set Nat.Primes) (p : Nat.Primes) (hp : p ∈ A) :
    Set.range (primeLocalizationToSpecInt A).base ⊆
      (PrimeSpectrum.basicOpen (p.val : ℤ) : Set (PrimeSpectrum ℤ)) := by
  intro x hx
  obtain ⟨y, rfl⟩ := hx
  rw [primeLocalizationToSpecInt_factors A p hp]
  show PrimeSpectrum.comap (algebraMap ℤ (Localization.Away (p.val : ℤ)))
    ((Spec.map (CommRingCat.ofHom (primeLocalizationAwayMap A p hp))).base y) ∈ _
  rw [← PrimeSpectrum.localization_away_comap_range
    (Localization.Away (p.val : ℤ)) (p.val : ℤ)]
  exact ⟨_, rfl⟩

private theorem primeLocalizationIndex_finite_range_avoids_closedPoint
    (s : Set primeLocalizationIndex) (hs : s.Finite) :
    ∃ p : Nat.Primes, ∀ A ∈ s,
      closedPrimePoint p ∉ Set.range (primeLocalizationFamilyMap A).base := by
  obtain ⟨p, hp⟩ := primeLocalizationIndex_common_prime s hs
  refine ⟨p, fun A hA hmem => ?_⟩
  have hbasic := primeLocalizationToSpecInt_range_subset_basicOpen A.val p (hp A hA)
  exact closedPrimePoint_not_mem_basicOpen p (hbasic hmem)

private abbrev primeLocalizationSubmonoidOver (R : Type*) [CommRing R] [Algebra ℤ R]
    (A : Set Nat.Primes) : Submonoid R :=
  Algebra.algebraMapSubmonoid R (primeLocalizationSubmonoid A)

private abbrev primeLocalizationOver (R : Type*) [CommRing R] [Algebra ℤ R]
    (A : Set Nat.Primes) := Localization (primeLocalizationSubmonoidOver R A)

/-- Distinct primes of `ℤ` cannot both map into the same prime ideal of an `ℤ`-algebra. -/
private theorem false_of_ne_primes_mem_prime {R : Type*} [CommRing R] [Algebra ℤ R]
    {x : PrimeSpectrum R} {p q : Nat.Primes} (hpq : p ≠ q)
    (hp : algebraMap ℤ R p.val ∈ x.asIdeal) (hq : algebraMap ℤ R q.val ∈ x.asIdeal) : False :=
  x.2.notMem_of_isCoprime_of_mem
    (((Nat.coprime_primes p.2 q.2).2 fun h => hpq (Subtype.ext h)).isCoprime.map
      (algebraMap ℤ R)) hp hq

private theorem finite_primes_mem_prime_over {R : Type*} [CommRing R] [Algebra ℤ R]
    (x : PrimeSpectrum R) :
    {p : Nat.Primes | algebraMap ℤ R p.val ∈ x.asIdeal}.Finite := by
  classical
  let T : Set Nat.Primes := {p | algebraMap ℤ R p.val ∈ x.asIdeal}
  by_cases hne : T.Nonempty
  · obtain ⟨p, hp⟩ := hne
    apply Set.Finite.subset (Set.finite_singleton p)
    intro q hq
    by_contra hpq
    exact false_of_ne_primes_mem_prime (Ne.symm hpq) hp hq
  · exact Set.Finite.subset Set.finite_empty (by
      intro p hp
      exact (hne ⟨p, hp⟩).elim)

private theorem primeLocalizationOver_range {R : Type*} [CommRing R] [Algebra ℤ R]
    (A : Set Nat.Primes) :
    Set.range (PrimeSpectrum.comap (algebraMap R (primeLocalizationOver R A))) =
      {x | ∀ p ∈ A, algebraMap ℤ R p.val ∉ x.asIdeal} := by
  ext x
  rw [PrimeSpectrum.localization_comap_range (primeLocalizationOver R A)
    (primeLocalizationSubmonoidOver R A)]
  let : x.asIdeal.IsPrime := x.2
  constructor
  · intro h p hp
    apply Set.disjoint_left.mp h
    exact ⟨_, Submonoid.subset_closure ⟨p, hp, rfl⟩, rfl⟩
  · intro h
    have hle : primeLocalizationSubmonoid A ≤
        x.asIdeal.primeCompl.comap (algebraMap ℤ R) := by
      rw [primeLocalizationSubmonoid, Submonoid.closure_le]
      rintro z ⟨p, hp, rfl⟩
      exact h p hp
    show Disjoint _ _
    rw [Set.disjoint_left]
    rintro z ⟨w, hw, rfl⟩ hz
    exact hle hw hz

private theorem primeLocalizationOver_base_surjective {R : Type*} [CommRing R]
    [Algebra ℤ R] (x : PrimeSpectrum R) :
    ∃ A : primeLocalizationIndex,
      x ∈ Set.range
        (PrimeSpectrum.comap (algebraMap R (primeLocalizationOver R A.val))) := by
  classical
  have hA : {p : Nat.Primes | algebraMap ℤ R p.val ∈ x.asIdeal}ᶜ ∈ primeUltrafilter :=
    Ultrafilter.of_le (Filter.cofinite : Filter Nat.Primes)
      (by simpa using finite_primes_mem_prime_over x)
  refine ⟨⟨_, hA⟩, ?_⟩
  rw [primeLocalizationOver_range]
  exact fun p hp => hp

private theorem isClosed_of_primeLocalizationOver_preimage {R : Type*} [CommRing R]
    [Algebra ℤ R] (T : Set (PrimeSpectrum R))
    (hT : ∀ A : primeLocalizationIndex,
      IsClosed (PrimeSpectrum.comap (algebraMap R (primeLocalizationOver R A.val)) ⁻¹' T)) :
    IsClosed T := by
  classical
  let V : Nat.Primes → Set (PrimeSpectrum R) :=
    fun p => {x | algebraMap ℤ R p.val ∈ x.asIdeal}
  have hVeq (p) : V p = (PrimeSpectrum.basicOpen (algebraMap ℤ R p.val) : Set _)ᶜ := by
    ext x
    simp [V]
  have hV (p) : @IsOpen _ (constructibleTopology (PrimeSpectrum R)) (V p) := by
    rw [hVeq]
    exact (@IsClopen.compl _ (constructibleTopology (PrimeSpectrum R)) _
      ((PrimeSpectrum.isCompact_basicOpen _).isClopen_constructibleTopology
        (PrimeSpectrum.basicOpen _).isOpen)).2
  have hd : Pairwise fun p q => Disjoint (V p) (V q) := fun p q hpq =>
    Set.disjoint_left.2 fun _ hp hq => false_of_ne_primes_mem_prime hpq hp hq
  have hcompact : @IsCompact _ (constructibleTopology (PrimeSpectrum R)) T := by
    apply @isCompact_of_ultrafilter_restrictions Nat.Primes (PrimeSpectrum R)
      (constructibleTopology (PrimeSpectrum R)) primeUltrafilter
      (Ultrafilter.of_le Filter.cofinite) V hV hd T
    intro A hA
    let f := PrimeSpectrum.comap (algebraMap R (primeLocalizationOver R A))
    have heq : T \ ⋃ p ∈ A, V p = f '' (f ⁻¹' T) := by
      rw [Set.image_preimage_eq_inter_range]
      rw [primeLocalizationOver_range]
      ext x
      simp only [Set.mem_sdiff, Set.mem_iUnion, not_exists, Set.mem_inter_iff,
        Set.mem_ofPred_eq, V]
    rw [heq]
    have hc : @IsCompact _ (constructibleTopology (PrimeSpectrum (primeLocalizationOver R A)))
        (f ⁻¹' T) :=
      IsClosed.isCompact_constructibleTopology
        (IsClosed.isClosed_constructibleTopology (hT ⟨A, hA⟩))
    exact @IsCompact.image _ _ (constructibleTopology _) (constructibleTopology _) _ f hc
      (PrimeSpectrum.isSpectralMap_comap _).continuous_constructibleTopology
  apply isClosed_of_isClosed_constructibleTopology_of_stableUnderSpecialization
    (@IsCompact.isClosed _ (constructibleTopology _) (t2Space_constructibleTopology _) T hcompact)
  intro x y hxy hx
  obtain ⟨A, y', hy'⟩ := primeLocalizationOver_base_surjective y
  have hxrange : x ∈ Set.range
      (PrimeSpectrum.comap (algebraMap R (primeLocalizationOver R A.val))) := by
    rw [primeLocalizationOver_range]
    have hyrange : y ∈ Set.range
        (PrimeSpectrum.comap (algebraMap R (primeLocalizationOver R A.val))) := ⟨y', hy'⟩
    rw [primeLocalizationOver_range] at hyrange
    intro p hp hpx
    exact hyrange p hp ((PrimeSpectrum.le_iff_specializes x y).mpr hxy hpx)
  obtain ⟨x', hx'⟩ := hxrange
  have hxy' : x' ⤳ y' :=
    (PrimeSpectrum.localization_comap_isInducing (primeLocalizationOver R A.val)
      (primeLocalizationSubmonoidOver R A.val)).specializes_iff.mp (by rwa [hx', hy'])
  have h := (hT A).stableUnderSpecialization hxy' (by simpa [hx'] using hx)
  simpa [hy'] using h

private theorem isQuotientMap_primeLocalizationOver {R : Type*} [CommRing R]
    [Algebra ℤ R] :
    Topology.IsQuotientMap (fun p : Σ A : primeLocalizationIndex,
      PrimeSpectrum (primeLocalizationOver R A.val) =>
        PrimeSpectrum.comap (algebraMap R (primeLocalizationOver R p.1.val)) p.2) := by
  rw [Topology.isQuotientMap_iff_isClosed]
  constructor
  · intro x
    obtain ⟨A, y, hy⟩ := primeLocalizationOver_base_surjective x
    exact ⟨⟨A, y⟩, hy⟩
  · intro T
    rw [isClosed_sigma_iff]
    constructor
    · intro h A
      exact h.preimage (PrimeSpectrum.continuous_comap
        (algebraMap R (primeLocalizationOver R A.val)))
    · exact isClosed_of_primeLocalizationOver_preimage T

private theorem submonoid_le_primeCompl_comap {R L : Type*} [CommRing R] [CommRing L]
    [Algebra R L] (S : Submonoid R) [IsLocalization S L] (x : PrimeSpectrum L) :
    S ≤ (PrimeSpectrum.comap (algebraMap R L) x).asIdeal.primeCompl := by
  have hx : PrimeSpectrum.comap (algebraMap R L) x ∈
      Set.range (PrimeSpectrum.comap (algebraMap R L)) := ⟨x, rfl⟩
  rw [PrimeSpectrum.localization_comap_range L S] at hx
  exact fun s hs => Set.disjoint_left.mp hx hs

private theorem exists_index_submonoid_le_primeCompl {R : Type*} [CommRing R] [Algebra ℤ R]
    (p : PrimeSpectrum R) :
    ∃ A : primeLocalizationIndex,
      primeLocalizationSubmonoidOver R A.val ≤ p.asIdeal.primeCompl := by
  obtain ⟨A, y, hy⟩ := primeLocalizationOver_base_surjective p
  refine ⟨A, ?_⟩
  rw [← hy]
  exact submonoid_le_primeCompl_comap _ y

private theorem exists_eq_mk_of_fraction_on_primeLocalizationOver
    {R M : Type u} [CommRing R] [Algebra ℤ R] [AddCommGroup M] [Module R M]
    (v : ∀ x : PrimeSpectrum R, LocalizedModule x.asIdeal.primeCompl M)
    (hv : ∀ A : primeLocalizationIndex, ∃ (m : M) (s : R)
      (hs : s ∈ primeLocalizationSubmonoidOver R A.val),
      ∀ (x : PrimeSpectrum R) (hx : primeLocalizationSubmonoidOver R A.val ≤
        x.asIdeal.primeCompl), v x = LocalizedModule.mk m ⟨s, hx hs⟩) :
    ∃ m : M, ∀ x : PrimeSpectrum R, v x = LocalizedModule.mk m 1 := by
  classical
  let E (m : M) (s : R) : Set (PrimeSpectrum R) :=
    {x | ∃ hs : s ∉ x.asIdeal, v x = LocalizedModule.mk m ⟨s, hs⟩}
  have hE (m : M) (s : R) : IsOpen (E m s) := by
    suffices h : IsClosed (E m s)ᶜ by simpa only [isClosed_compl_iff] using h
    apply isClosed_of_primeLocalizationOver_preimage
    intro A
    rw [Set.preimage_compl, isClosed_compl_iff]
    obtain ⟨a, b, hb, hrep⟩ := hv A
    apply isOpen_iff_mem_nhds.mpr
    intro y hy
    let x := PrimeSpectrum.comap (algebraMap R (primeLocalizationOver R A.val)) y
    have hle := submonoid_le_primeCompl_comap (primeLocalizationSubmonoidOver R A.val) y
    obtain ⟨hs, he⟩ := hy
    have heq : LocalizedModule.mk a ⟨b, hle hb⟩ =
        LocalizedModule.mk m (⟨s, hs⟩ : x.asIdeal.primeCompl) :=
      (hrep x hle).symm.trans he
    obtain ⟨t, ht⟩ := LocalizedModule.mk_eq.mp heq
    let W := PrimeSpectrum.basicOpen (algebraMap R (primeLocalizationOver R A.val) (s * t.val))
    have hyW : y ∈ W := by
      show s * t.val ∉ x.asIdeal
      exact x.asIdeal.primeCompl.mul_mem hs t.property
    apply Filter.mem_of_superset (W.isOpen.mem_nhds hyW)
    intro z hz
    let q := PrimeSpectrum.comap (algebraMap R (primeLocalizationOver R A.val)) z
    have hq : s * t.val ∉ q.asIdeal := hz
    have hs' : s ∉ q.asIdeal := fun h => hq (q.asIdeal.mul_mem_right _ h)
    have ht' : t.val ∉ q.asIdeal := fun h => hq (q.asIdeal.mul_mem_left _ h)
    refine ⟨hs', ?_⟩
    rw [hrep q (submonoid_le_primeCompl_comap (primeLocalizationSubmonoidOver R A.val) z)]
    exact LocalizedModule.mk_eq.mpr ⟨⟨t.val, ht'⟩, ht⟩
  let sectionTop : (structureSheafInType R M).obj.obj (Opposite.op ⊤) :=
    ⟨fun x => v x.1, by
      intro x
      obtain ⟨A, hle⟩ := exists_index_submonoid_le_primeCompl x.1
      obtain ⟨m, s, hs, hrep⟩ := hv A
      let W : TopologicalSpace.Opens (PrimeSpectrum R) := ⟨E m s, hE m s⟩
      refine ⟨W, ⟨hle hs, hrep x.1 hle⟩, homOfLE le_top, m, s, ?_⟩
      intro z
      exact z.property⟩
  obtain ⟨m, hm⟩ := StructureSheaf.toOpenₗ_top_bijective.surjective sectionTop
  refine ⟨m, fun x => ?_⟩
  exact (congrArg (fun t => t.val ⟨x, trivial⟩) hm).symm

private theorem liftOfLE_mk {R M : Type*} [CommSemiring R] [AddCommMonoid M]
    [Module R M] (S T : Submonoid R) (h : S ≤ T) (m : M) (s : S) :
    IsLocalizedModule.liftOfLE S T h (LocalizedModule.mkLinearMap S M)
      (LocalizedModule.mkLinearMap T M) (LocalizedModule.mk m s) =
        LocalizedModule.mk m ⟨s.val, h s.property⟩ := by
  simpa only [← IsLocalizedModule.mk_eq_mk'] using
    IsLocalizedModule.liftOfLE_mk' S T h (LocalizedModule.mkLinearMap S M)
      (LocalizedModule.mkLinearMap T M) m s

private theorem localizedModule_ext_primes {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (S : Submonoid R) (a b : LocalizedModule S M)
    (h : ∀ (p : PrimeSpectrum R) (hp : S ≤ p.asIdeal.primeCompl),
      IsLocalizedModule.liftOfLE S p.asIdeal.primeCompl hp (LocalizedModule.mkLinearMap S M)
        (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M) a =
      IsLocalizedModule.liftOfLE S p.asIdeal.primeCompl hp (LocalizedModule.mkLinearMap S M)
        (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M) b) : a = b := by
  induction a using LocalizedModule.induction_on with | h a s => ?_
  induction b using LocalizedModule.induction_on with | h b t => ?_
  by_contra hn
  let I : Ideal R := LinearMap.ker (LinearMap.toSpanSingleton R M (t.val • a - s.val • b))
  have hI : Disjoint (I : Set R) (S : Set R) := by
    rw [Set.disjoint_left]
    intro z hz hzS
    apply hn
    apply LocalizedModule.mk_eq.mpr
    refine ⟨⟨z, hzS⟩, ?_⟩
    change z • (t.val • a - s.val • b) = 0 at hz
    simpa only [smul_sub, sub_eq_zero, Submonoid.smul_def] using hz
  obtain ⟨p, hp, hIp, hpS⟩ := I.exists_le_prime_disjoint S hI
  let q : PrimeSpectrum R := ⟨p, hp⟩
  have hSq : S ≤ q.asIdeal.primeCompl :=
    fun z hz hzp => Set.disjoint_left.mp hpS hzp hz
  have heq := h q hSq
  simp only [liftOfLE_mk] at heq
  obtain ⟨z, hz⟩ := LocalizedModule.mk_eq.mp heq
  apply z.property
  apply hIp
  show z.val • (t.val • a - s.val • b) = 0
  simpa only [smul_sub, sub_eq_zero, Submonoid.smul_def] using hz

private theorem primeLocalizationOver_module_equalizer
    {R M : Type u} [CommRing R] [Algebra ℤ R] [AddCommGroup M] [Module R M]
    (s : ∀ A : primeLocalizationIndex,
      LocalizedModule (primeLocalizationSubmonoidOver R A.val) M)
    (hs : ∀ (A B : primeLocalizationIndex) (p : PrimeSpectrum R)
      (hA : primeLocalizationSubmonoidOver R A.val ≤ p.asIdeal.primeCompl)
      (hB : primeLocalizationSubmonoidOver R B.val ≤ p.asIdeal.primeCompl),
      IsLocalizedModule.liftOfLE _ _ hA (LocalizedModule.mkLinearMap _ M)
        (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M) (s A) =
      IsLocalizedModule.liftOfLE _ _ hB (LocalizedModule.mkLinearMap _ M)
        (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M) (s B)) :
    ∃! m : M, ∀ A, LocalizedModule.mk m 1 = s A := by
  classical
  choose A hA using exists_index_submonoid_le_primeCompl (R := R)
  let v (p : PrimeSpectrum R) : LocalizedModule p.asIdeal.primeCompl M :=
    IsLocalizedModule.liftOfLE _ _ (hA p) (LocalizedModule.mkLinearMap _ M)
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M) (s (A p))
  have hv (B : primeLocalizationIndex) (p : PrimeSpectrum R)
      (hB : primeLocalizationSubmonoidOver R B.val ≤ p.asIdeal.primeCompl) :
      v p = IsLocalizedModule.liftOfLE _ _ hB (LocalizedModule.mkLinearMap _ M)
        (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M) (s B) := hs (A p) B p (hA p) hB
  obtain ⟨m, hm⟩ := exists_eq_mk_of_fraction_on_primeLocalizationOver v (by
    intro B
    obtain ⟨⟨b, t⟩, ht⟩ := IsLocalizedModule.mk'_surjective
      (primeLocalizationSubmonoidOver R B.val)
      (LocalizedModule.mkLinearMap (primeLocalizationSubmonoidOver R B.val) M) (s B)
    have ht' : LocalizedModule.mk b t = s B := by
      simpa only [Function.uncurry_apply_pair, ← IsLocalizedModule.mk_eq_mk'] using ht
    refine ⟨b, t.val, t.property, fun p hp => ?_⟩
    rw [hv B p hp, ← ht', liftOfLE_mk])
  have hmA (B : primeLocalizationIndex) : LocalizedModule.mk m 1 = s B := by
    apply localizedModule_ext_primes
    intro p hp
    rw [liftOfLE_mk, ← hv B p hp, hm]
    rfl
  refine ⟨m, hmA, fun m' hm' => ?_⟩
  apply (StructureSheaf.toOpenₗ_top_bijective (R := R) (M := M)).injective
  apply Subtype.ext
  funext p
  show LocalizedModule.mk m' (1 : p.val.asIdeal.primeCompl) = LocalizedModule.mk m 1
  have h := congrArg
    (IsLocalizedModule.liftOfLE _ _ (hA p.val) (LocalizedModule.mkLinearMap _ M)
      (LocalizedModule.mkLinearMap p.val.asIdeal.primeCompl M))
      ((hm' (A p.val)).trans (hmA (A p.val)).symm)
  simp only [liftOfLE_mk] at h
  convert! h using 1

private noncomputable def localizationMapOfLE {R : Type*} [CommRing R]
    (S T : Submonoid R) (h : S ≤ T) : Localization S →ₐ[R] Localization T where
  __ := IsLocalization.map (Localization T) (RingHom.id R) h
  commutes' r := IsLocalization.map_eq h r

private theorem localizationMapOfLE_algebraMap {R : Type*} [CommRing R]
    (S T : Submonoid R) (h : S ≤ T) (r : R) :
    localizationMapOfLE S T h (algebraMap R (Localization S) r) =
      algebraMap R (Localization T) r := (localizationMapOfLE S T h).commutes r

private noncomputable def localizedRingModuleEquiv {R : Type*} [CommRing R]
    (S : Submonoid R) : LocalizedModule S R ≃ₗ[R] Localization S :=
  IsLocalizedModule.iso S (Algebra.linearMap R (Localization S))

private theorem localizedRingModuleEquiv_mk_one {R : Type*} [CommRing R]
    (S : Submonoid R) (r : R) :
    localizedRingModuleEquiv S (LocalizedModule.mk r 1) =
      algebraMap R (Localization S) r := IsLocalizedModule.iso_mk_one _ _ _

private theorem localizedRingModuleEquiv_liftOfLE {R : Type*} [CommRing R]
    (S T : Submonoid R) (h : S ≤ T) (m : LocalizedModule S R) :
    localizedRingModuleEquiv T (LocalizedModule.liftOfLE S T h m) =
      localizationMapOfLE S T h (localizedRingModuleEquiv S m) := by
  have he : (localizedRingModuleEquiv T).toLinearMap.comp
      (LocalizedModule.liftOfLE S T h) =
      (localizationMapOfLE S T h).toLinearMap.comp
        (localizedRingModuleEquiv S).toLinearMap := by
    apply IsLocalizedModule.ext S (LocalizedModule.mkLinearMap S R)
      (fun s => IsLocalizedModule.map_units (Algebra.linearMap R (Localization T))
        ⟨s.val, h s.property⟩)
    apply LinearMap.ext
    intro r
    show localizedRingModuleEquiv T (LocalizedModule.liftOfLE S T h
      (LocalizedModule.mk r 1)) =
        localizationMapOfLE S T h (localizedRingModuleEquiv S (LocalizedModule.mk r 1))
    rw [liftOfLE_mk]
    show localizedRingModuleEquiv T (LocalizedModule.mk r 1) = _
    rw [localizedRingModuleEquiv_mk_one, localizedRingModuleEquiv_mk_one,
      localizationMapOfLE_algebraMap]
  exact LinearMap.congr_fun he m

private theorem primeLocalizationOver_ring_equalizer
    {R : Type u} [CommRing R] [Algebra ℤ R]
    (s : ∀ A : primeLocalizationIndex, primeLocalizationOver R A.val)
    (hs : ∀ (A B : primeLocalizationIndex) (p : PrimeSpectrum R)
      (hA : primeLocalizationSubmonoidOver R A.val ≤ p.asIdeal.primeCompl)
      (hB : primeLocalizationSubmonoidOver R B.val ≤ p.asIdeal.primeCompl),
      localizationMapOfLE _ _ hA (s A) = localizationMapOfLE _ _ hB (s B)) :
    ∃! r : R, ∀ A, algebraMap R (primeLocalizationOver R A.val) r = s A := by
  let t (A : primeLocalizationIndex) :
      LocalizedModule (primeLocalizationSubmonoidOver R A.val) R :=
    (localizedRingModuleEquiv (primeLocalizationSubmonoidOver R A.val)).symm (s A)
  have ht : ∀ (A B : primeLocalizationIndex) (p : PrimeSpectrum R)
      (hA : primeLocalizationSubmonoidOver R A.val ≤ p.asIdeal.primeCompl)
      (hB : primeLocalizationSubmonoidOver R B.val ≤ p.asIdeal.primeCompl),
      LocalizedModule.liftOfLE _ _ hA (t A) = LocalizedModule.liftOfLE _ _ hB (t B) := by
    intro A B p hA hB
    apply (localizedRingModuleEquiv p.asIdeal.primeCompl).injective
    simpa only [localizedRingModuleEquiv_liftOfLE, t, LinearEquiv.apply_symm_apply]
      using hs A B p hA hB
  obtain ⟨r, hr, huniq⟩ := primeLocalizationOver_module_equalizer t ht
  have iff_eq (x : R) (A : primeLocalizationIndex) :
      LocalizedModule.mk x 1 = t A ↔
        algebraMap R (primeLocalizationOver R A.val) x = s A := by
    rw [← (localizedRingModuleEquiv (primeLocalizationSubmonoidOver R A.val)).injective.eq_iff]
    simp only [localizedRingModuleEquiv_mk_one, t, LinearEquiv.apply_symm_apply]
  exact ⟨r, fun A => (iff_eq r A).mp (hr A),
    fun x hx => huniq x (fun A => (iff_eq x A).mpr (hx A))⟩

private theorem primeLocalizationOver_ring_ext {R : Type u} [CommRing R] [Algebra ℤ R]
    {r t : R} (h : ∀ A : primeLocalizationIndex,
      algebraMap R (primeLocalizationOver R A.val) r =
        algebraMap R (primeLocalizationOver R A.val) t) : r = t := by
  obtain ⟨x, hx, hu⟩ := primeLocalizationOver_ring_equalizer
    (fun A => algebraMap R (primeLocalizationOver R A.val) t) (by
      intros
      simp only [localizationMapOfLE_algebraMap])
  exact (hu r h).trans (hu t (fun _ => rfl)).symm

private theorem primeLocalizationOver_ringHom_equalizer
    {R B : Type u} [CommRing R] [Algebra ℤ R] [CommRing B]
    (s : ∀ A : primeLocalizationIndex, B →+* primeLocalizationOver R A.val)
    (hs : ∀ (A C : primeLocalizationIndex) (p : PrimeSpectrum R)
      (hA : primeLocalizationSubmonoidOver R A.val ≤ p.asIdeal.primeCompl)
      (hC : primeLocalizationSubmonoidOver R C.val ≤ p.asIdeal.primeCompl),
      (localizationMapOfLE _ _ hA).toRingHom.comp (s A) =
        (localizationMapOfLE _ _ hC).toRingHom.comp (s C)) :
    ∃! f : B →+* R, ∀ A, (algebraMap R (primeLocalizationOver R A.val)).comp f = s A := by
  classical
  have hex (b : B) := primeLocalizationOver_ring_equalizer (fun A => s A b)
    (fun A C p hA hC => RingHom.congr_fun (hs A C p hA hC) b)
  choose f hf hu using hex
  let g : B →+* R :=
    { toFun := f
      map_one' := primeLocalizationOver_ring_ext (fun A => by simp [hf])
      map_mul' a b := primeLocalizationOver_ring_ext (fun A => by simp [hf])
      map_zero' := primeLocalizationOver_ring_ext (fun A => by simp [hf])
      map_add' a b := primeLocalizationOver_ring_ext (fun A => by simp [hf]) }
  refine ⟨g, fun A => RingHom.ext (fun b => hf b A), ?_⟩
  intro g' hg'
  ext b
  exact hu b (g' b) (fun A => RingHom.congr_fun (hg' A) b)

private theorem primeLocalizationOver_affine_isEffectiveEpiFamily
    (R : Type) [CommRing R] [Algebra ℤ R] :
    StacksEffectiveEpi.IsEffectiveEpiFamily
      (fun A : primeLocalizationIndex =>
        AffineScheme.of (Spec (CommRingCat.of (primeLocalizationOver R A.val))))
      (fun A => AffineScheme.ofHom
        (Spec.map (CommRingCat.ofHom (algebraMap R (primeLocalizationOver R A.val))))) := by
  classical
  let X (A : primeLocalizationIndex) :=
    AffineScheme.of (Spec (CommRingCat.of (primeLocalizationOver R A.val)))
  let f (A : primeLocalizationIndex) : X A ⟶ AffineScheme.of (Spec (CommRingCat.of R)) :=
    AffineScheme.ofHom
      (Spec.map (CommRingCat.ofHom (algebraMap R (primeLocalizationOver R A.val))))
  have hrep : StacksEffectiveEpi.IsRepresentableFamily X f := fun _ _ => inferInstance
  refine ⟨hrep, fun Y g hg => ?_⟩
  have hcompat := (hrep.compatible_iff X f g).mp hg
  obtain ⟨T, ⟨eY⟩⟩ : ∃ T : CommRingCat,
      Nonempty (AffineScheme.forgetToScheme.obj Y ≅ Spec T) :=
    ⟨Γ(Y.obj, ⊤), ⟨Y.obj.isoSpec⟩⟩
  let gS (A : primeLocalizationIndex) :
      Spec (CommRingCat.of (primeLocalizationOver R A.val)) ⟶ Spec T :=
    AffineScheme.forgetToScheme.map (g A) ≫ eY.hom
  let s (A : primeLocalizationIndex) : T ⟶
      CommRingCat.of (primeLocalizationOver R A.val) :=
    (Scheme.Spec.preimage (gS A)).unop
  have hs (A : primeLocalizationIndex) : Spec.map (s A) = gS A :=
    Scheme.Spec.map_preimage _
  obtain ⟨r, hr, hu⟩ := primeLocalizationOver_ringHom_equalizer (fun A => (s A).hom) (by
    intro A B p hA hB
    let a : AffineScheme.of (Spec (CommRingCat.of (Localization p.asIdeal.primeCompl))) ⟶ X A :=
      AffineScheme.ofHom (Spec.map (CommRingCat.ofHom (localizationMapOfLE _ _ hA).toRingHom))
    let b : AffineScheme.of (Spec (CommRingCat.of (Localization p.asIdeal.primeCompl))) ⟶ X B :=
      AffineScheme.ofHom (Spec.map (CommRingCat.ofHom (localizationMapOfLE _ _ hB).toRingHom))
    have hab : a ≫ f A = b ≫ f B := by
      apply AffineScheme.forgetToScheme.map_injective
      show Spec.map (CommRingCat.ofHom (localizationMapOfLE _ _ hA).toRingHom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R (primeLocalizationOver R A.val))) =
        Spec.map (CommRingCat.ofHom (localizationMapOfLE _ _ hB).toRingHom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R (primeLocalizationOver R B.val)))
      rw [← Spec.map_comp, ← Spec.map_comp]
      congr 1
      ext x
      exact (localizationMapOfLE_algebraMap _ _ hA x).trans
        (localizationMapOfLE_algebraMap _ _ hB x).symm
    have hc : a ≫ g A = b ≫ g B := hcompat A B _ a b hab
    have key : Spec.map (CommRingCat.ofHom (localizationMapOfLE _ _ hA).toRingHom) ≫ gS A =
        Spec.map (CommRingCat.ofHom (localizationMapOfLE _ _ hB).toRingHom) ≫ gS B := by
      have h1 : AffineScheme.forgetToScheme.map (a ≫ g A) ≫ eY.hom =
          AffineScheme.forgetToScheme.map (b ≫ g B) ≫ eY.hom :=
        congrArg (fun k => AffineScheme.forgetToScheme.map k ≫ eY.hom) hc
      rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc] at h1
      exact h1
    show (s A ≫ CommRingCat.ofHom (localizationMapOfLE _ _ hA).toRingHom).hom =
      (s B ≫ CommRingCat.ofHom (localizationMapOfLE _ _ hB).toRingHom).hom
    apply congrArg CommRingCat.Hom.hom
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, hs, hs]
    exact key)
  let tS : Spec (CommRingCat.of R) ⟶ Spec T := Spec.map (CommRingCat.ofHom r)
  let tY : AffineScheme.forgetToScheme.obj (AffineScheme.of (Spec (CommRingCat.of R))) ⟶
      AffineScheme.forgetToScheme.obj Y := tS ≫ eY.inv
  let t : AffineScheme.of (Spec (CommRingCat.of R)) ⟶ Y :=
    AffineScheme.forgetToScheme.preimage tY
  have htmap : AffineScheme.forgetToScheme.map t = tY :=
    AffineScheme.forgetToScheme.map_preimage _
  have htY : tY ≫ eY.hom = tS := by
    show (tS ≫ eY.inv) ≫ eY.hom = tS
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have ht (A) : f A ≫ t = g A := by
    apply AffineScheme.forgetToScheme.map_injective
    rw [Functor.map_comp, htmap]
    apply (cancel_mono eY.hom).mp
    rw [Category.assoc, htY]
    show AffineScheme.forgetToScheme.map (f A) ≫ tS = gS A
    rw [← hs A]
    show Spec.map (CommRingCat.ofHom (algebraMap R (primeLocalizationOver R A.val))) ≫
      Spec.map (CommRingCat.ofHom r) = Spec.map (s A)
    rw [← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext (hr A))
  refine ⟨t, ht, fun t' ht' => ?_⟩
  let t'Y : Spec (CommRingCat.of R) ⟶ Spec T :=
    AffineScheme.forgetToScheme.map t' ≫ eY.hom
  let r' : T ⟶ CommRingCat.of R := (Scheme.Spec.preimage t'Y).unop
  have hr'map : Spec.map r' = t'Y := Scheme.Spec.map_preimage _
  have hr' : r'.hom = r := hu r'.hom (by
    intro A
    have key : Spec.map (CommRingCat.ofHom (algebraMap R (primeLocalizationOver R A.val))) ≫
        t'Y = gS A := by
      have h3 : AffineScheme.forgetToScheme.map (f A ≫ t') ≫ eY.hom =
          AffineScheme.forgetToScheme.map (g A) ≫ eY.hom :=
        congrArg (fun k => AffineScheme.forgetToScheme.map k ≫ eY.hom) (ht' A)
      rw [Functor.map_comp, Category.assoc] at h3
      exact h3
    apply congrArg CommRingCat.Hom.hom
    apply Spec.map_injective
    show Spec.map (r' ≫ CommRingCat.ofHom
      (algebraMap R (primeLocalizationOver R A.val))) = Spec.map (s A)
    rw [Spec.map_comp, hr'map, hs]
    exact key)
  apply AffineScheme.forgetToScheme.map_injective
  apply (cancel_mono eY.hom).mp
  rw [htmap, htY]
  show t'Y = tS
  rw [← hr'map]
  show Spec.map r' = Spec.map (CommRingCat.ofHom r)
  exact congrArg Spec.map (CommRingCat.hom_ext hr')

private noncomputable def primeLocalizationBaseChangeMap {R : Type} [CommRing R]
    [Algebra ℤ R] (A : Set Nat.Primes) : primeLocalization A →+* primeLocalizationOver R A :=
  IsLocalization.map (M := primeLocalizationSubmonoid A)
    (T := primeLocalizationSubmonoidOver R A)
    (primeLocalizationOver R A) (algebraMap ℤ R) (fun _ h => ⟨_, h, rfl⟩)

private theorem primeLocalizationBaseChange_isPullback {R : Type} [CommRing R]
    [Algebra ℤ R] (A : Set Nat.Primes) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (algebraMap R (primeLocalizationOver R A))))
      (Spec.map (CommRingCat.ofHom (primeLocalizationBaseChangeMap A)))
      (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))
      (primeLocalizationToSpecInt A) := by
  have hloc : IsLocalization ((primeLocalizationSubmonoid A).map (algebraMap ℤ R))
      (primeLocalizationOver R A) := by
    show IsLocalization (primeLocalizationSubmonoidOver R A)
      (Localization (primeLocalizationSubmonoidOver R A))
    infer_instance
  apply isPullback_SpecMap_of_isPushout
  apply CommRingCat.isPushout_of_isLocalization (algebraMap ℤ R)
    (primeLocalizationBaseChangeMap (R := R) A) _ (primeLocalizationSubmonoid A)
  ext z
  simp [primeLocalizationBaseChangeMap]

/-- The base change of the localization family along any scheme `Y` isomorphic to `Spec R`. -/
private theorem primeLocalizationBaseChange_isPullback_of_iso {R : Type} [CommRing R]
    [Algebra ℤ R] {Y : Scheme.{0}} (e : Y ≅ Spec (CommRingCat.of R))
    (g : Y ⟶ Spec (CommRingCat.of ℤ)) (A : Set Nat.Primes) :
    IsPullback (Spec.map (CommRingCat.ofHom (algebraMap R (primeLocalizationOver R A))) ≫ e.inv)
      (Spec.map (CommRingCat.ofHom (primeLocalizationBaseChangeMap A))) g
      (primeLocalizationToSpecInt A) := by
  apply (primeLocalizationBaseChange_isPullback (R := R) A).of_iso
    (Iso.refl _) e.symm (Iso.refl _) (Iso.refl _)
  · simp
  · simp
  · exact specZIsTerminal.hom_ext _ _
  · simp [primeLocalizationToSpecInt]

private theorem isEffectiveEpiFamily_of_iso
    {C : Type*} [Category C] [Limits.HasPullbacks C] {I : Type*}
    {B B' : C} {X X' : I → C} {f : ∀ i, X i ⟶ B} {f' : ∀ i, X' i ⟶ B'}
    (e : B ≅ B') (ei : ∀ i, X i ≅ X' i)
    (w : ∀ i, (ei i).hom ≫ f' i = f i ≫ e.hom)
    (h : StacksEffectiveEpi.IsEffectiveEpiFamily X f) :
    StacksEffectiveEpi.IsEffectiveEpiFamily X' f' := by
  have hrep' : StacksEffectiveEpi.IsRepresentableFamily X' f' := fun _ _ => inferInstance
  refine ⟨hrep', fun Y g hg => ?_⟩
  have hc := (hrep'.compatible_iff X' f' g).mp hg
  obtain ⟨t, ht, hu⟩ := h.2 Y (fun i => (ei i).hom ≫ g i)
    ((h.1.compatible_iff X f _).mpr (by
      intro i j Z a b hab
      have he : (a ≫ (ei i).hom) ≫ f' i = (b ≫ (ei j).hom) ≫ f' j := by
        rw [Category.assoc, w i, ← Category.assoc, hab, Category.assoc, ← w j,
          ← Category.assoc]
      simpa only [yoneda_obj_map, TypeCat.ofHom_apply, Quiver.Hom.unop_op, Category.assoc]
        using hc i j Z _ _ he))
  refine ⟨e.inv ≫ t, fun i => ?_, fun t' ht' => ?_⟩
  · apply (cancel_epi (ei i).hom).mp
    rw [← Category.assoc, w i]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    exact ht i
  · have ht'' : ∀ i, f i ≫ (e.hom ≫ t') = (ei i).hom ≫ g i := by
      intro i
      rw [← Category.assoc, ← w i, Category.assoc, ht' i]
    have heq := hu (e.hom ≫ t') ht''
    rw [← heq]
    simp

private theorem primeLocalization_affine_isUniversalEffectiveEpiFamily :
    StacksEffectiveEpi.IsUniversalEffectiveEpiFamily
      (fun A : primeLocalizationIndex => AffineScheme.of (primeLocalizationFamilySource A))
      (fun A => AffineScheme.ofHom (primeLocalizationFamilyMap A)) := by
  refine ⟨fun _ _ => inferInstance, fun V g X' f' p hp => ?_⟩
  obtain ⟨T, ⟨eV⟩⟩ : ∃ T : CommRingCat,
      Nonempty (AffineScheme.forgetToScheme.obj V ≅ Spec T) :=
    ⟨Γ(V.obj, ⊤), ⟨V.obj.isoSpec⟩⟩
  let f (A : primeLocalizationIndex) : Spec (CommRingCat.of (primeLocalizationOver T A.val)) ⟶
      AffineScheme.forgetToScheme.obj V :=
    Spec.map (CommRingCat.ofHom (algebraMap T (primeLocalizationOver T A.val))) ≫ eV.inv
  have hsq (A : primeLocalizationIndex) : IsPullback (f A)
      (Spec.map (CommRingCat.ofHom (primeLocalizationBaseChangeMap A.val)))
      (AffineScheme.forgetToScheme.map g) (primeLocalizationFamilyMap A) :=
    primeLocalizationBaseChange_isPullback_of_iso (R := T) eV _ A.val
  let eS : AffineScheme.forgetToScheme.obj (AffineScheme.of (Spec (CommRingCat.of T))) ≅
      AffineScheme.forgetToScheme.obj V := eV.symm
  let e : AffineScheme.of (Spec (CommRingCat.of T)) ≅ V :=
    AffineScheme.forgetToScheme.preimageIso eS
  let eiS (A : primeLocalizationIndex) :
      AffineScheme.forgetToScheme.obj
          (AffineScheme.of (Spec (CommRingCat.of (primeLocalizationOver T A.val)))) ≅
        AffineScheme.forgetToScheme.obj (X' A) :=
    (hsq A).isoIsPullback _ _ ((hp A).map AffineScheme.forgetToScheme)
  let ei (A : primeLocalizationIndex) :
      AffineScheme.of (Spec (CommRingCat.of (primeLocalizationOver T A.val))) ≅ X' A :=
    AffineScheme.forgetToScheme.preimageIso (eiS A)
  have hee : AffineScheme.forgetToScheme.map e.hom = eS.hom :=
    AffineScheme.forgetToScheme.map_preimage _
  have hei (A : primeLocalizationIndex) :
      AffineScheme.forgetToScheme.map (ei A).hom = (eiS A).hom :=
    AffineScheme.forgetToScheme.map_preimage _
  apply isEffectiveEpiFamily_of_iso e ei _ (primeLocalizationOver_affine_isEffectiveEpiFamily T)
  intro A
  apply AffineScheme.forgetToScheme.map_injective
  rw [Functor.map_comp, Functor.map_comp, hei, hee]
  exact (hsq A).isoIsPullback_hom_fst _ _ ((hp A).map AffineScheme.forgetToScheme)

private theorem primeLocalization_affineBaseChange_isQuotientMap
    (Y : Scheme.{0}) [IsAffine Y] (g : Y ⟶ Spec (CommRingCat.of ℤ)) :
    Topology.IsQuotientMap (fun p : Σ A : primeLocalizationIndex,
      (Limits.pullback (primeLocalizationFamilyMap A) g : Scheme.{0}) =>
        (Limits.pullback.snd (primeLocalizationFamilyMap p.1) g) p.2) := by
  let R := Γ(Y, ⊤)
  let f (A : primeLocalizationIndex) : Spec (CommRingCat.of (primeLocalizationOver R A.val)) ⟶ Y :=
    Spec.map (CommRingCat.ofHom (algebraMap R (primeLocalizationOver R A.val))) ≫ Y.isoSpec.inv
  have hsq (A : primeLocalizationIndex) : IsPullback (f A)
      (Spec.map (CommRingCat.ofHom (primeLocalizationBaseChangeMap A.val))) g
      (primeLocalizationFamilyMap A) :=
    primeLocalizationBaseChange_isPullback_of_iso (R := R) Y.isoSpec g A.val
  let e (A) := (hsq A).flip.isoPullback
  let j : (Σ A : primeLocalizationIndex, PrimeSpectrum (primeLocalizationOver R A.val)) →
      (Σ A : primeLocalizationIndex, (Limits.pullback (primeLocalizationFamilyMap A) g : Scheme)) :=
    fun p => ⟨p.1, (e p.1).hom p.2⟩
  have hj : Continuous j := continuous_sigma fun A =>
    continuous_sigmaMk.comp (e A).hom.continuous
  have hc : Topology.IsQuotientMap (fun p : Σ A : primeLocalizationIndex,
      PrimeSpectrum (primeLocalizationOver R A.val) =>
        Y.isoSpec.inv (PrimeSpectrum.comap
          (algebraMap R (primeLocalizationOver R p.1.val)) p.2)) :=
    Y.isoSpec.inv.homeomorph.isQuotientMap.comp isQuotientMap_primeLocalizationOver
  apply Topology.IsQuotientMap.of_comp hj
    (continuous_sigma fun A => (Limits.pullback.snd (primeLocalizationFamilyMap A) g).continuous)
  convert hc using 1
  funext p
  show ((e p.1).hom ≫ Limits.pullback.snd (primeLocalizationFamilyMap p.1) g) p.2 = _
  exact congrArg (fun k => k p.2) (hsq p.1).flip.isoPullback_hom_snd

private theorem isUniversalEffectiveEpiFamily_iff_mem_canonicalTopology
    {C : Type*} [Category C] [Limits.HasPullbacks C] {I : Type*}
    {X : C} (Y : I → C) (f : ∀ i, Y i ⟶ X) :
    StacksEffectiveEpi.IsUniversalEffectiveEpiFamily Y f ↔
      Sieve.ofArrows Y f ∈ Sheaf.canonicalTopology C X := by
  constructor
  · intro h
    apply Sheaf.mem_finestTopology_of_forall_isSheafFor
    rintro _ ⟨Z, rfl⟩ V g
    have hp i : IsPullback (Limits.pullback.snd (f i) g)
        (Limits.pullback.fst (f i) g) g (f i) :=
      (IsPullback.of_hasPullback (f i) g).flip
    rw [← Sieve.ofArrows_eq_pullback_of_isPullback f hp]
    apply (Presieve.isSheafFor_iff_generate _).mp
    apply (Presieve.EffectiveEpimorphic.iff_forall_isSheafFor_yoneda _).mp
    apply (Sieve.effectiveEpimorphic_family _ _).mpr
    exact ((h.2 g _ _ _ hp).1.isEffectiveEpiFamily_iff _ _).mp (h.2 g _ _ _ hp)
  · intro h
    refine ⟨fun _ _ => inferInstance, fun V g Y' f' p hp => ?_⟩
    have hcov : Sieve.ofArrows Y' f' ∈ Sheaf.canonicalTopology C V := by
      rw [Sieve.ofArrows_eq_pullback_of_isPullback f hp]
      exact (Sheaf.canonicalTopology C).pullback_stable g h
    have hrep : StacksEffectiveEpi.IsRepresentableFamily Y' f' :=
      fun _ _ => inferInstance
    apply (hrep.isEffectiveEpiFamily_iff _ _).mpr
    apply (Sieve.effectiveEpimorphic_family _ _).mp
    apply (Presieve.EffectiveEpimorphic.iff_forall_isSheafFor_yoneda _).mpr
    intro Z
    exact (Sheaf.isSheaf_yoneda_obj Z).isSheafFor _ hcov

private theorem jointlySurjective_of_mem_canonicalTopology
    {I : Type*} {X : Scheme.{0}} (Y : I → Scheme.{0}) (f : ∀ i, Y i ⟶ X)
    (h : Sieve.ofArrows Y f ∈ Sheaf.canonicalTopology Scheme.{0} X) :
    ∀ x : X, ∃ i, x ∈ Set.range (f i) :=
  AlgebraicGeometry.jointlySurjective_of_isUniversalEffectiveEpiFamily Y f
    ((isUniversalEffectiveEpiFamily_iff_mem_canonicalTopology Y f).mpr h)

private theorem primeLocalization_not_isQuasiCompactObject_of_cover
    (hcover : Sieve.ofArrows primeLocalizationFamilySource primeLocalizationFamilyMap ∈
      Sheaf.canonicalTopology Scheme.{0} (Spec (CommRingCat.of ℤ))) :
    ¬(Sheaf.canonicalTopology Scheme.{0}).IsQuasiCompactObject
      (Spec (CommRingCat.of ℤ)) := by
  intro hqc
  let E : PreZeroHypercover.{1} (Spec (CommRingCat.of ℤ)) :=
    { I₀ := ULift.{1} primeLocalizationIndex
      X := fun i => primeLocalizationFamilySource i.down
      f := fun i => primeLocalizationFamilyMap i.down }
  have hE : E.sieve₀ ∈ Sheaf.canonicalTopology Scheme.{0} _ := by
    apply (Sheaf.canonicalTopology Scheme.{0}).superset_covering _ hcover
    rw [Sieve.ofArrows, Sieve.generate_le_iff]
    rintro _ _ ⟨i⟩
    exact E.sieve₀_f ⟨i⟩
  obtain ⟨F, φ, hF, hfin⟩ := hqc E hE
  have hfin' : (Set.range fun j => (φ.s₀ j).down).Finite := by
    simpa only [← Set.range_comp, Function.comp_def] using hfin.image (fun i => i.down)
  obtain ⟨p, hp⟩ := primeLocalizationIndex_finite_range_avoids_closedPoint _ hfin'
  obtain ⟨j, y, hy⟩ := jointlySurjective_of_mem_canonicalTopology F.X F.f hF
    (closedPrimePoint p)
  apply hp (φ.s₀ j).down ⟨j, rfl⟩
  refine ⟨(φ.h₀ j) y, ?_⟩
  show (φ.h₀ j ≫ E.f (φ.s₀ j)) y = closedPrimePoint p
  rw [φ.w₀]
  exact hy

/-- The spectrum of the integers is not quasi-compact in the canonical topology
on the category of schemes. -/
@[stacks 0EUG]
public theorem specInt_not_isQuasiCompactObject_canonicalTopology :
    ¬(Sheaf.canonicalTopology Scheme.{0}).IsQuasiCompactObject
      (Spec (CommRingCat.of ℤ)) := by
  apply primeLocalization_not_isQuasiCompactObject_of_cover
  apply (isUniversalEffectiveEpiFamily_iff_mem_canonicalTopology _ _).mp
  apply AlgebraicGeometry.isUniversalEffectiveEpiFamily_of_affine_of_submersive
    (AffineScheme.of (Spec (CommRingCat.of ℤ)))
    (fun A : primeLocalizationIndex => AffineScheme.of (primeLocalizationFamilySource A))
    (fun A => AffineScheme.ofHom (primeLocalizationFamilyMap A))
  · exact primeLocalization_affine_isUniversalEffectiveEpiFamily
  · exact primeLocalization_affineBaseChange_isQuotientMap

end Stacks.AlgebraicGeometry.SpecIntQuasiCompactCounterexample
