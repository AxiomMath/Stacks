module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.Topology.Constructible

/-!
# Isolating a point of a discrete complement by one regular function

Let `U` be a retrocompact open subscheme of a scheme `X` whose complement is discrete, and
assume that the local ring at every point of the complement is Noetherian of Krull dimension at
most one. This file shows that each such point `x` has an affine open neighbourhood `V` on which
`x` is simultaneously the only point of the complement and the zero locus of a single regular
function `f ∈ Γ(X, V)`.

The proof is local commutative algebra transported to `X` through an affine chart. Discreteness
of the complement gives an affine open `V₀` meeting the complement only in `x`; retrocompactness
makes `U ⊓ V₀` quasi-compact, so finitely many basic opens of `V₀` contained in `U ⊓ V₀` already
cover it, and the corresponding finite set `s ⊆ Γ(X, V₀)` cuts out `x` among the primes of
`Γ(X, V₀)`. In the local ring at `x` — Noetherian of dimension at most one — some element
generates an ideal whose only prime is the maximal ideal, and clearing denominators turns that
element into a pair `(a, g)` with `a` vanishing exactly at `x` on the basic open `D(g)`. The
required affine neighbourhood is `V = X.basicOpen g` and the function is the restriction of `a`.

## Main results

* `AlgebraicGeometry.exists_isAffineOpen_isolating_point`: the affine neighbourhood and the
  regular function isolating a chosen point of the complement.

## Implementation notes

For an affine open `V`, its coordinate ring is represented canonically by `Γ(X, V)`, and the
zero locus in `V` of a section `f` is written as the relative complement of `X.basicOpen f`
in `V`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry

/-- In a Noetherian local ring of Krull dimension at most one there is an element of the maximal
ideal whose only prime divisor is the maximal ideal itself. If the maximal ideal is already
minimal, `0` will do; otherwise the maximal ideal is not contained in the union of the finitely
many minimal primes, and any element avoiding all of them works. -/
private lemma exists_mem_maximalIdeal_isUnique_prime
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [Ring.KrullDimLE 1 R] :
    ∃ r : R, r ∈ IsLocalRing.maximalIdeal R ∧
      ∀ q : Ideal R, q.IsPrime → r ∈ q → q = IsLocalRing.maximalIdeal R := by
  classical
  let m : Ideal R := IsLocalRing.maximalIdeal R
  have hdim := Ring.krullDimLE_one_iff.mp (inferInstance : Ring.KrullDimLE 1 R)
  by_cases hm : m ∈ minimalPrimes R
  · refine ⟨0, Ideal.zero_mem _, fun q hq _ => ?_⟩
    rcases hdim q hq with - | hmax
    · change IsMinimalPrime m at hm
      exact ((IsMinimalPrime.iff_minimal m).mp hm).eq_of_le hq
        (IsLocalRing.le_maximalIdeal_of_isPrime q)
    · exact IsLocalRing.eq_maximalIdeal hmax
  · let S : Set (Ideal R) := minimalPrimes R
    have hfin : S.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing R ⊥
    have hnot : ¬ (m : Set R) ⊆ ⋃ q ∈ S, (q : Set R) := by
      intro h
      obtain ⟨q, hq, hmq⟩ :=
        (Ideal.subset_union_prime_finite hfin (⊤ : Ideal R) ⊤
          (fun i hi _ _ => by
            change i ∈ minimalPrimes R at hi
            rw [minimalPrimes_eq_minimals] at hi
            exact hi.1) (I := m)).mp h
      change IsMinimalPrime q at hq
      have : q.IsPrime := hq.isPrime
      have hEq : q = m := le_antisymm (IsLocalRing.le_maximalIdeal_of_isPrime q) hmq
      exact hm (hEq ▸ hq)
    obtain ⟨r, hr, havoid⟩ := Set.not_subset.mp hnot
    refine ⟨r, hr, fun q hq hqr => ?_⟩
    rcases hdim q hq with hmin | hmax
    · exact (havoid (Set.mem_iUnion.mpr ⟨q, Set.mem_iUnion.mpr ⟨hmin, hqr⟩⟩)).elim
    · exact IsLocalRing.eq_maximalIdeal hmax

/-- A prime lies in `V(a) ∩ D(g)` exactly when it contains `a` and does not contain `g`. -/
private lemma mem_zeroLocus_singleton_inter_basicOpen_iff {A : Type*} [CommRing A] {a g : A}
    {q : PrimeSpectrum A} :
    q ∈ (PrimeSpectrum.zeroLocus ({a} : Set A) ∩ PrimeSpectrum.basicOpen g :
      Set (PrimeSpectrum A)) ↔ a ∈ q.asIdeal ∧ g ∉ q.asIdeal := by
  simp [PrimeSpectrum.mem_zeroLocus]

/-- If `p` is the only prime containing `a` and avoiding `g`, and `a ∈ p`, `g ∉ p`, then
`V(a) ∩ D(g)` is the single point `p`. -/
private lemma zeroLocus_inter_basicOpen_eq_singleton_of_unique {A : Type*} [CommRing A]
    {p : Ideal A} [p.IsPrime] {a g : A} (ha : a ∈ p) (hg : g ∉ p)
    (h : ∀ q : Ideal A, q.IsPrime → a ∈ q → g ∉ q → q = p) :
    (PrimeSpectrum.zeroLocus ({a} : Set A) ∩ PrimeSpectrum.basicOpen g : Set (PrimeSpectrum A)) =
      {⟨p, inferInstance⟩} := by
  ext q
  rw [mem_zeroLocus_singleton_inter_basicOpen_iff, Set.mem_singleton_iff]
  refine ⟨fun ⟨haq, hgq⟩ => PrimeSpectrum.ext (h _ q.2 haq hgq), ?_⟩
  rintro rfl
  exact ⟨ha, hg⟩

/-- Clearing denominators in the localization `R` of `A` at `p`: if the image of `b` lies in the
radical of the extension of `I`, then `t * b ^ n ∈ I` for some `n` and some `t ∉ p`. -/
private lemma exists_mul_pow_mem_of_algebraMap_mem_radical
    {A R : Type*} [CommRing A] [CommRing R] [Algebra A R]
    {p : Ideal A} [p.IsPrime] [IsLocalization.AtPrime R p] {I : Ideal A} {b : A}
    (hb : algebraMap A R b ∈ (I.map (algebraMap A R)).radical) :
    ∃ n : ℕ, ∃ t : A, t ∉ p ∧ t * b ^ n ∈ I := by
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hb
  obtain ⟨t, ht⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff p.primeCompl R I
    (b ^ n)).mp (by simpa only [map_pow] using hn)
  exact ⟨n, t, ht.1, ht.2⟩

/-- Descend the previous lemma along a localization at a prime `p` of `A`. If a finite set
`s ⊆ p` already cuts `p` out among the primes of `A`, then there are `a ∈ p` and `g ∉ p` such
that `p` is the only prime containing `a` and avoiding `g`. -/
private lemma exists_zeroLocus_inter_basicOpen_eq_singleton
    (A R : Type*) [CommRing A] [CommRing R] [Algebra A R]
    (p : Ideal A) [p.IsPrime] [IsLocalization.AtPrime R p] [IsLocalRing R]
    [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
    (s : Finset A) (hs : ∀ b ∈ s, b ∈ p)
    (hsep : ∀ q : Ideal A, q.IsPrime → (∀ b ∈ s, b ∈ q) → q = p) :
    ∃ a g : A, a ∈ p ∧ g ∉ p ∧
      (PrimeSpectrum.zeroLocus ({a} : Set A) ∩ PrimeSpectrum.basicOpen g : Set (PrimeSpectrum A)) =
        {⟨p, inferInstance⟩} := by
  classical
  obtain ⟨r, hr, hlocal⟩ := exists_mem_maximalIdeal_isUnique_prime R
  obtain ⟨a, d, hrepr⟩ := IsLocalization.exists_mk'_eq p.primeCompl r
  have hm : IsLocalRing.maximalIdeal R = Ideal.map (algebraMap A R) p :=
    (IsLocalization.AtPrime.map_eq_maximalIdeal p R).symm
  have hspec : r * algebraMap A R (d : A) = algebraMap A R a := by
    rw [← hrepr, IsLocalization.mk'_spec]
  have ha : a ∈ p := by
    rw [← Ideal.under_map_of_isLocalizationAtPrime (q := p) (p := p) (S := R) le_rfl,
      Ideal.mem_under, ← hspec]
    exact (Ideal.map (algebraMap A R) p).mul_mem_right _ (hm ▸ hr)
  have hzeroR : PrimeSpectrum.zeroLocus ({r} : Set R) =
      {⟨IsLocalRing.maximalIdeal R, inferInstance⟩} := by
    ext q
    simp only [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff, Set.mem_singleton_iff]
    refine ⟨fun hrq => PrimeSpectrum.ext (hlocal _ q.2 hrq), ?_⟩
    rintro rfl
    exact hr
  have hrad : (Ideal.span ({r} : Set R)).radical = IsLocalRing.maximalIdeal R := by
    rw [← PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical (Ideal.span ({r} : Set R)),
      PrimeSpectrum.zeroLocus_span, hzeroR, PrimeSpectrum.vanishingIdeal_singleton]
  have hspanle : Ideal.span ({r} : Set R) ≤
      Ideal.map (algebraMap A R) (Ideal.span ({a} : Set A)) :=
    (Ideal.span_singleton_le_iff_mem _).mpr ((IsLocalization.mem_map_algebraMap_iff p.primeCompl
      R).2 ⟨⟨⟨a, Ideal.mem_span_singleton_self a⟩, d⟩, hspec⟩)
  have hex : ∀ b ∈ s, ∃ n : ℕ, ∃ t : A, t ∉ p ∧ t * b ^ n ∈ Ideal.span ({a} : Set A) := by
    intro b hb
    have hbrad : algebraMap A R b ∈ (Ideal.span ({r} : Set R)).radical := by
      rw [hrad, hm]
      exact Ideal.mem_map_of_mem _ (hs b hb)
    exact exists_mul_pow_mem_of_algebraMap_mem_radical (p := p) (Ideal.radical_mono hspanle hbrad)
  choose n t htNot htRel using hex
  let td : A → A := fun b => if hb : b ∈ s then t b hb else 1
  let g : A := ∏ b ∈ s, td b
  have hg : g ∉ p := by
    intro hgp
    simp only [g, Ideal.IsPrime.prod_mem_iff] at hgp
    obtain ⟨b, hb, htb⟩ := hgp
    have heq : td b = t b hb := by simp [td, hb]
    exact htNot b hb (heq ▸ htb)
  have hsepAt : ∀ q : Ideal A, q.IsPrime → a ∈ q → g ∉ q → q = p := by
    intro q hq haq hgq
    refine hsep q hq fun b hb => hq.mem_of_pow_mem (n b hb) ?_
    have htb : td b ∉ q := fun htq =>
      hgq (Ideal.IsPrime.prod_mem_iff.mpr ⟨b, hb, htq⟩ : (∏ b ∈ s, td b) ∈ q)
    have hrel : td b * b ^ (n b hb) ∈ q :=
      (Ideal.span_singleton_le_iff_mem q).mpr haq (by simpa [td, hb] using htRel b hb)
    exact (hq.mul_mem_iff_mem_or_mem.mp hrel).resolve_left htb
  exact ⟨a, g, ha, hg, zeroLocus_inter_basicOpen_eq_singleton_of_unique ha hg hsepAt⟩

/-- Every subset of a closed subset carrying the discrete topology is closed. -/
private lemma isClosed_of_subset_of_discreteTopology {Y : Type*} [TopologicalSpace Y]
    {C S : Set Y} (hC : IsClosed C) [DiscreteTopology C] (hS : S ⊆ C) : IsClosed S := by
  have := hC.isClosedEmbedding_subtypeVal.isClosedMap _
    (isClosed_discrete (Subtype.val ⁻¹' S : Set C))
  rwa [Subtype.image_preimage_coe, Set.inter_eq_right.mpr hS] at this

/-- A point of a discrete closed complement has an affine open neighbourhood meeting the
complement only in that point, and the point is closed. -/
private lemma exists_isAffineOpen_inter_compl_eq_singleton
    (X : Scheme) (U : X.Opens) [DiscreteTopology (Uᶜ : Set X)]
    (x : X) (hx : x ∈ (U : Set X)ᶜ) :
    ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V ∧ (V : Set X) ∩ (U : Set X)ᶜ = {x} ∧
      IsClosed ({x} : Set X) := by
  have hC : IsClosed (U : Set X)ᶜ := U.2.isClosed_compl
  have hCx : IsClosed ((U : Set X)ᶜ \ {x}) :=
    isClosed_of_subset_of_discreteTopology hC fun _ h => h.1
  have hxO : x ∈ ((U : Set X)ᶜ \ {x})ᶜ := by simp
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVO⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxO hCx.isOpen_compl
  refine ⟨V, hV, hxV, Set.Subset.antisymm (fun y hy => ?_)
    (Set.singleton_subset_iff.mpr ⟨hxV, hx⟩),
    isClosed_of_subset_of_discreteTopology hC (Set.singleton_subset_iff.mpr hx)⟩
  by_contra hyx
  exact hVO hy.1 ⟨hy.2, hyx⟩

/-- On an affine open `V`, the point `hV.fromSpec q` lies in `X.basicOpen f` exactly when `f`
does not lie in the prime `q`. -/
lemma IsAffineOpen.fromSpec_mem_basicOpen_iff {X : Scheme.{u}} {V : X.Opens}
    (hV : IsAffineOpen V) (f : Γ(X, V)) (q : PrimeSpectrum Γ(X, V)) :
    hV.fromSpec q ∈ X.basicOpen f ↔ f ∉ q.asIdeal := by
  change q ∈ hV.fromSpec ⁻¹ᵁ X.basicOpen f ↔ _
  rw [hV.fromSpec_preimage_basicOpen f]
  exact PrimeSpectrum.mem_basicOpen f q

/-- If `U` is retrocompact and the affine open `V` meets the complement of `U` only in `x`, then
a finite set of sections over `V` cuts out the prime of `x` among the primes of `Γ(X, V)`. -/
lemma IsAffineOpen.exists_finset_isolating_primeIdealOf {X : Scheme.{u}} {U V : X.Opens}
    (hV : IsAffineOpen V) (hU : IsRetrocompact (U : Set X)) {x : X} (hxV : x ∈ V)
    (hVC : (V : Set X) ∩ (U : Set X)ᶜ = {x}) :
    ∃ s : Finset Γ(X, V), (∀ b ∈ s, b ∈ (hV.primeIdealOf ⟨x, hxV⟩).asIdeal) ∧
      ∀ q : Ideal Γ(X, V), q.IsPrime → (∀ b ∈ s, b ∈ q) →
        q = (hV.primeIdealOf ⟨x, hxV⟩).asIdeal := by
  classical
  have hx : x ∈ (V : Set X) ∩ (U : Set X)ᶜ := by
    rw [hVC]
    exact Set.mem_singleton x
  have hW : IsCompact ((U ⊓ V : X.Opens) : Set X) := by
    change IsCompact ((U : Set X) ∩ (V : Set X))
    simpa [Set.inter_comm] using hU hV.isCompact V.2
  have hcover : ((U ⊓ V : X.Opens) : Set X) ⊆
      ⋃ j : {b : Γ(X, V) // X.basicOpen b ≤ U ⊓ V}, (X.basicOpen j.1 : Set X) := by
    intro y hy
    obtain ⟨f, hle, hmem⟩ := hV.exists_basicOpen_le ⟨y, hy⟩ hy.2
    exact Set.mem_iUnion.mpr ⟨⟨f, hle⟩, hmem⟩
  obtain ⟨t, ht⟩ := hW.elim_finite_subcover
    (fun j : {b : Γ(X, V) // X.basicOpen b ≤ U ⊓ V} => (X.basicOpen j.1 : Set X))
    (fun j => (X.basicOpen j.1).2) hcover
  refine ⟨t.image Subtype.val, fun b hb => ?_, fun q hq hbs => ?_⟩
  · obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hb
    by_contra hbnot
    have hxj := (hV.fromSpec_mem_basicOpen_iff j.1 (hV.primeIdealOf ⟨x, hxV⟩)).mpr hbnot
    rw [hV.fromSpec_primeIdealOf] at hxj
    have hxW : x ∈ ((U ⊓ V : X.Opens) : Set X) := j.2 hxj
    exact hx.2 hxW.1
  · let y : PrimeSpectrum Γ(X, V) := ⟨q, hq⟩
    have hyV : hV.fromSpec y ∈ (V : Set X) := by
      rw [← hV.range_fromSpec]
      exact ⟨y, rfl⟩
    have hyU : hV.fromSpec y ∉ (U : Set X) := by
      intro hyU
      obtain ⟨j, hjD⟩ := Set.mem_iUnion.mp (ht (show hV.fromSpec y ∈ ((U ⊓ V : X.Opens) : Set X)
        from ⟨hyU, hyV⟩))
      obtain ⟨hjt, hjD⟩ := Set.mem_iUnion.mp hjD
      exact (hV.fromSpec_mem_basicOpen_iff _ y).mp hjD (hbs _ (Finset.mem_image_of_mem _ hjt))
    have hyx : hV.fromSpec y ∈ (V : Set X) ∩ (U : Set X)ᶜ := ⟨hyV, hyU⟩
    rw [hVC] at hyx
    exact congrArg PrimeSpectrum.asIdeal (hV.fromSpec.isOpenEmbedding.injective
      ((Set.mem_singleton_iff.mp hyx).trans (hV.fromSpec_primeIdealOf ⟨x, hxV⟩).symm))

/-- On an affine open `V`, if `p` is the only prime containing `a` and avoiding `g`, then the zero
locus of the restriction of `a` to `X.basicOpen g` is the single point `hV.fromSpec p`. -/
lemma IsAffineOpen.basicOpen_sdiff_basicOpen_map_eq_singleton {X : Scheme.{u}} {V : X.Opens}
    (hV : IsAffineOpen V) {a g : Γ(X, V)} {p : PrimeSpectrum Γ(X, V)}
    (h : (PrimeSpectrum.zeroLocus ({a} : Set Γ(X, V)) ∩ PrimeSpectrum.basicOpen g :
      Set (PrimeSpectrum Γ(X, V))) = {p}) :
    (X.basicOpen g : Set X) \
        X.basicOpen (X.presheaf.map (homOfLE (X.basicOpen_le g)).op a) = {hV.fromSpec p} := by
  rw [Scheme.basicOpen_res]
  ext y
  refine ⟨fun ⟨hyg, hya⟩ => ?_, ?_⟩
  · obtain ⟨q, rfl⟩ : ∃ q : PrimeSpectrum Γ(X, V), hV.fromSpec q = y :=
      ⟨_, hV.fromSpec_primeIdealOf ⟨y, X.basicOpen_le g hyg⟩⟩
    have hq : q ∈ (PrimeSpectrum.zeroLocus ({a} : Set Γ(X, V)) ∩ PrimeSpectrum.basicOpen g :
        Set (PrimeSpectrum Γ(X, V))) :=
      mem_zeroLocus_singleton_inter_basicOpen_iff.mpr
        ⟨by_contra fun ha => hya ⟨hyg, (hV.fromSpec_mem_basicOpen_iff a q).mpr ha⟩,
          (hV.fromSpec_mem_basicOpen_iff g q).mp hyg⟩
    rw [h, Set.mem_singleton_iff] at hq
    rw [hq]
    exact Set.mem_singleton _
  · rintro rfl
    have hp := mem_zeroLocus_singleton_inter_basicOpen_iff.mp (h ▸ Set.mem_singleton p)
    exact ⟨(hV.fromSpec_mem_basicOpen_iff g p).mpr hp.2,
      fun hpa => (hV.fromSpec_mem_basicOpen_iff a p).mp hpa.2 hp.1⟩

/-- A point of a discrete retrocompact complement whose local ring is Noetherian of Krull
dimension at most one can be isolated on an affine neighbourhood both from the rest of the
complement and as the zero locus of a single regular function. -/
lemma exists_isAffineOpen_isolating_point
    (X : Scheme.{u}) (U : X.Opens) (hU : IsRetrocompact (U : Set X))
    [DiscreteTopology (Uᶜ : Set X)]
    (h_noetherian : ∀ x : X, x ∈ (U : Set X)ᶜ → IsNoetherianRing (X.presheaf.stalk x))
    (h_dimension : ∀ x : X, x ∈ (U : Set X)ᶜ →
      Ring.KrullDimLE 1 (X.presheaf.stalk x))
    (x : X) (hx : x ∈ (U : Set X)ᶜ) :
    ∃ V : X.Opens,
      IsAffineOpen V ∧
        x ∈ V ∧
          (V : Set X) ∩ (U : Set X)ᶜ = {x} ∧
            ∃ f : Γ(X, V), (V : Set X) \ (X.basicOpen f : Set X) = {x} := by
  classical
  obtain ⟨V₀, hV₀, hxV₀, hV₀C, -⟩ := exists_isAffineOpen_inter_compl_eq_singleton X U x hx
  obtain ⟨s, hs, hsep⟩ := hV₀.exists_finset_isolating_primeIdealOf hU hxV₀ hV₀C
  let p : Ideal Γ(X, V₀) := (hV₀.primeIdealOf ⟨x, hxV₀⟩).asIdeal
  let R : Type _ := X.presheaf.stalk x
  let : Algebra Γ(X, V₀) R := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxV₀⟩
  have : IsLocalization.AtPrime R p := hV₀.isLocalization_stalk ⟨x, hxV₀⟩
  have : p.IsPrime := (hV₀.primeIdealOf ⟨x, hxV₀⟩).2
  have : IsNoetherianRing R := h_noetherian x hx
  have : Ring.KrullDimLE 1 R := h_dimension x hx
  obtain ⟨a, g, -, hg, hzero⟩ :=
    exists_zeroLocus_inter_basicOpen_eq_singleton Γ(X, V₀) R p s hs hsep
  have hP : hV₀.fromSpec ⟨p, inferInstance⟩ = x := hV₀.fromSpec_primeIdealOf ⟨x, hxV₀⟩
  have hxg : x ∈ X.basicOpen g := by
    rw [← hP]
    exact (hV₀.fromSpec_mem_basicOpen_iff g _).mpr hg
  refine ⟨X.basicOpen g, hV₀.basicOpen g, hxg, Set.Subset.antisymm ?_
    (Set.singleton_subset_iff.mpr ⟨hxg, hx⟩), X.presheaf.map (homOfLE (X.basicOpen_le g)).op a,
    by rw [hV₀.basicOpen_sdiff_basicOpen_map_eq_singleton hzero, hP]⟩
  exact (Set.inter_subset_inter_left _
    (X.basicOpen_le g : (X.basicOpen g : Set X) ⊆ V₀)).trans hV₀C.subset

end AlgebraicGeometry

end
