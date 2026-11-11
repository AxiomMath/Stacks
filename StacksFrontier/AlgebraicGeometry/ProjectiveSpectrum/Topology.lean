module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology
public import Mathlib.RingTheory.GradedAlgebra.Radical
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The topology of `Proj`

Let `A = ⨁_{d ≥ 0} 𝒜 d` be a graded ring. Its homogeneous spectrum `Proj 𝒜`
(`ProjectiveSpectrum 𝒜`) is the set of *relevant* homogeneous primes of `A`, that is, the
homogeneous primes not containing the irrelevant ideal `𝒜₊ = ⨁_{d > 0} 𝒜 d`, topologized by the
closed sets `V₊(I) = {p ∈ Proj 𝒜 | I ⊆ p}` for `I` a homogeneous ideal — in Mathlib,
`ProjectiveSpectrum.zeroLocus 𝒜 I`. For `f` homogeneous of positive degree, `D₊(f)` is the set of
`p ∈ Proj 𝒜` with `f ∉ p`, Mathlib's `ProjectiveSpectrum.basicOpen 𝒜 f`; for an arbitrary
`g ∈ A`, the same `basicOpen 𝒜 g` is the set `D(g) ∩ Proj 𝒜` of the source.

This file states the assertions of the source's lemma on the topology of `Proj` (Stacks 00JP)
other than (6) and (7): (1) the `D₊(f)` are open; (2) `D₊(ff') = D₊(f) ∩ D₊(f')`; (3) for
`g = ∑ gᵢ` with `gᵢ ∈ 𝒜 i`, `D(g) ∩ Proj 𝒜 = (D(g₀) ∩ Proj 𝒜) ∪ ⋃_{i ≥ 1} D₊(gᵢ)`; (4) for
`g₀ ∈ 𝒜 0`, `D(g₀) ∩ Proj 𝒜 = ⋃_{f ∈ 𝒜 d, d ≥ 1} D₊(g₀ f)`; (5) the `D₊(f)` form a basis of the
topology; (8) the `V₊(I)` are closed; (9) every closed set is some `V₊(I)`; and (10) the
emptiness criterion below. Assertion (6), the homeomorphisms
`D₊(f) ← {ℤ-graded primes of A_f} → Spec A₍f₎`, is in
`StacksFrontier.AlgebraicGeometry.ProjectiveSpectrum.AwayGradedPrimes`, and assertion (7), a graded
ring whose `Proj` is not quasi-compact, in
`StacksFrontier.AlgebraicGeometry.ProjectiveSpectrum.NotQuasiCompact`; both need imports this file
does not carry.

Assertion (10) is the criterion for a closed set to be empty: `V₊(I) = ∅` if and only if
`𝒜₊ ⊆ √I`. One direction is the definition of relevance: a prime containing `I` contains `√I`, so
if `𝒜₊ ⊆ √I` no prime containing `I` can be relevant. The other direction is the substance. If
`𝒜₊ ⊄ √I` then some homogeneous `f` of positive degree is not nilpotent modulo `I`, so the graded
ring `(A/I)_f` is nonzero, hence so is the ring `(A/I)₍f₎` of degree-zero elements of `(A/I)_f`;
a prime of the latter is a point of `Proj (A/I) ∩ D₊(f)`, and pulling it back along `A → A/I`
produces a relevant homogeneous prime containing `I`. The last step is the identification of
`D₊(f)` with `Spec A⁰_f` for `f` homogeneous of positive degree, which in Mathlib is
`AlgebraicGeometry.projIsoSpecTopComponent`.

Taking `I = ⊥` specializes the criterion to `Proj 𝒜 = ∅ ↔ 𝒜₊ ⊆ √(0)`, i.e. `Proj 𝒜` is empty
exactly when every element of positive degree is nilpotent. Passing to complements, it is the
converse of `AlgebraicGeometry.Proj.iSup_basicOpen_eq_top`: a family of homogeneous elements whose
basic opens cover `Proj 𝒜` is precisely a family whose span has `𝒜₊` inside its radical.

## Main results

* `ProjectiveSpectrum.isOpen_basicOpen_of_mem`, `ProjectiveSpectrum.basicOpen_mul_of_mem`,
  `ProjectiveSpectrum.basicOpen_eq_basicOpen_proj_zero_sup_iSup`,
  `ProjectiveSpectrum.basicOpen_eq_iSup_basicOpen_mul_of_mem_zero`,
  `ProjectiveSpectrum.isTopologicalBasis_basicOpen_of_pos`,
  `ProjectiveSpectrum.isClosed_zeroLocus_homogeneousIdeal`,
  `ProjectiveSpectrum.exists_homogeneousIdeal_eq_zeroLocus_of_isClosed`: assertions (1)–(5), (8)
  and (9) of Stacks 00JP.
* `ProjectiveSpectrum.zeroLocus_empty_iff_irrelevant_le_radical`: for a homogeneous ideal `I` of a
  graded ring `A`, the projective zero locus of `I` is empty if and only if the irrelevant ideal is
  contained in the radical of `I`.

## Implementation notes

Assertions (1), (2), (8) and (9) are Mathlib's `ProjectiveSpectrum.isOpen_basicOpen`,
`ProjectiveSpectrum.basicOpen_mul`, `ProjectiveSpectrum.isClosed_zeroLocus` and
`ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure` (a closed `T` is the zero locus of the
homogeneous ideal `ProjectiveSpectrum.vanishingIdeal T`), restated at the source's hypotheses: in
(1) and (2) the elements are homogeneous of positive degree, as the source defines `D₊(f)` only for
those, and in (8) the ideal is homogeneous. Assertion (3) is
`ProjectiveSpectrum.basicOpen_eq_union_of_projection`, `D(g) = ⋃_i D(gᵢ)`, with the degree-zero part
split off as the source does. Assertion (4) is proved directly: a relevant prime `p` misses some
homogeneous `f` of positive degree, and if also `g₀ ∉ p` then `g₀ f ∉ p`. Assertion (5) follows from
(3) and (4), since the `D(g)` form a basis (Mathlib's
`ProjectiveSpectrum.isTopologicalBasis_basic_opens`) and each `D(g)` is by (3) and (4) a union of
`D₊(f)` with `f` homogeneous of positive degree; Mathlib's
`AlgebraicGeometry.Proj.isBasis_basicOpen` lets `f` range over all of `A` and is therefore weaker.
The hypotheses `f ∈ 𝒜 d`, `0 < d` of (1), (2) and `g₀ ∈ 𝒜 0` of (4) are the source's and are not
used by the proofs.

The source proves the substantial direction by localization: from `𝒜₊ ⊄ √I` it extracts a
homogeneous `f` of positive degree that is not nilpotent modulo `I`, so `(A/I)_f ≠ 0`, hence the
subring `(A/I)₍f₎` of its degree-zero elements is nonzero, and a prime of that ring is a point of
`V₊(I) ∩ D₊(f)` via the homeomorphism `D₊(f) ≅ Spec A⁰_f` of assertion (6). The proof below
replaces that route by `Ideal.IsHomogeneous.radical_eq`: both sides of the criterion are readings
of one condition, that every homogeneous prime of `A` containing `I` contains `𝒜₊`. That
`V₊(I) = ∅` says this is the definition of `Proj 𝒜` and needs no homogeneity of `I`; that
`𝒜₊ ≤ √I` says this is `radical_eq`, the radical of a homogeneous ideal being the intersection of
the homogeneous primes above it. The two routes are the same mathematics organized differently,
but the second needs no graded localization, and in particular needs only
`AddSubmonoidClass σ A`, whereas the homeomorphism of assertion (6) requires
`AddSubgroupClass σ A`.

The ideal is taken bundled, as `I : HomogeneousIdeal 𝒜`, matching
`ProjectiveSpectrum.zeroLocus_sup_homogeneousIdeal` and its neighbours, and the right-hand side is
phrased with `HomogeneousIdeal.radical`, the radical of a homogeneous ideal again as a homogeneous
ideal, so that both sides of `≤` live in `HomogeneousIdeal 𝒜`.

Faithfulness of (10). (1) The one hypothesis, that `I` is homogeneous, is used: without it the
criterion fails in the direction `V₊(I) = ∅ → 𝒜₊ ≤ √I`, since for `A = k[x, y]` graded by degree and
`I = (x + y)` every homogeneous prime containing `x + y` contains both `x` and `y` and so is
irrelevant, giving `V₊(I) = ∅`, while `x ∉ √I`. (2) The base is the source's: `I` is an ideal of the
graded ring `A` itself, `𝒜₊` is the irrelevant ideal of that same grading, and the radical is taken
in `A`. (3) The two sides are pinned to the source's own sets rather than asserted to exist: `V₊(I)`
is `ProjectiveSpectrum.zeroLocus 𝒜 I`, the relevant homogeneous primes containing `I`, and `𝒜₊ ⊆ √I`
is an inclusion of ideals of `A`. (4) The instantiation is not degenerate, in both directions: for
`A = k[x, y]` graded by degree, `I = (x, y) = 𝒜₊` has `V₊(I) = ∅` and `𝒜₊ ≤ √I`, whereas `I = (x)`
has `V₊(I) = {(x)}` nonempty and `y ∉ √I`.

## References

* [StackProject 00JP](https://stacks.math.columbia.edu/tag/00JP)
-/

@[expose] public section

namespace ProjectiveSpectrum

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubmonoidClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- A standard open `D₊(f)`, for `f` homogeneous of positive degree, is open in `Proj 𝒜`. -/
@[stacks 00JP "Assertion (1): the sets `D₊(f)`, `f` homogeneous of positive degree, are open \
  (Mathlib's `ProjectiveSpectrum.isOpen_basicOpen`)."]
theorem isOpen_basicOpen_of_mem {f : A} {d : ℕ} (_hf : f ∈ 𝒜 d) (_hd : 0 < d) :
    IsOpen (basicOpen 𝒜 f : Set (ProjectiveSpectrum 𝒜)) :=
  isOpen_basicOpen 𝒜

/-- For `f`, `f'` homogeneous of positive degree, `D₊(ff') = D₊(f) ∩ D₊(f')`. -/
@[stacks 00JP "Assertion (2): `D₊(ff') = D₊(f) ∩ D₊(f')` (Mathlib's \
  `ProjectiveSpectrum.basicOpen_mul`)."]
theorem basicOpen_mul_of_mem {f f' : A} {d d' : ℕ} (_hf : f ∈ 𝒜 d) (_hd : 0 < d)
    (_hf' : f' ∈ 𝒜 d') (_hd' : 0 < d') :
    basicOpen 𝒜 (f * f') = basicOpen 𝒜 f ⊓ basicOpen 𝒜 f' :=
  basicOpen_mul 𝒜 f f'

/-- For `g ∈ A` with homogeneous components `gᵢ = proj i g`, the set `D(g) ∩ Proj 𝒜` of relevant
homogeneous primes not containing `g` is `(D(g₀) ∩ Proj 𝒜) ∪ ⋃_{i ≥ 1} D₊(gᵢ)`. -/
@[stacks 00JP "Assertion (3): `D(g) ∩ Proj(S) = (D(g₀) ∩ Proj(S)) ∪ ⋃_{i ≥ 1} D₊(gᵢ)` for \
  `g = ∑ gᵢ` with `gᵢ ∈ Sᵢ`; derived from Mathlib's \
  `ProjectiveSpectrum.basicOpen_eq_union_of_projection`."]
theorem basicOpen_eq_basicOpen_proj_zero_sup_iSup (g : A) :
    basicOpen 𝒜 g = basicOpen 𝒜 (GradedRing.proj 𝒜 0 g) ⊔
      ⨆ (i : ℕ) (_ : 0 < i), basicOpen 𝒜 (GradedRing.proj 𝒜 i g) := by
  have hle : ∀ i, basicOpen 𝒜 (GradedRing.proj 𝒜 i g) ≤ basicOpen 𝒜 g := fun i => by
    rw [basicOpen_eq_union_of_projection 𝒜 g]
    exact le_iSup (fun i => basicOpen 𝒜 (GradedRing.proj 𝒜 i g)) i
  refine le_antisymm ?_ (sup_le (hle 0) (iSup₂_le fun i _ => hle i))
  rw [basicOpen_eq_union_of_projection 𝒜 g]
  refine iSup_le fun i => ?_
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · exact le_sup_left
  · exact le_sup_of_le_right (le_iSup₂_of_le i hi le_rfl)

/-- For `g₀` homogeneous of degree `0`, `D(g₀) ∩ Proj 𝒜 = ⋃_{f ∈ 𝒜 d, d ≥ 1} D₊(g₀ f)`. -/
@[stacks 00JP "Assertion (4): `D(g₀) ∩ Proj(S) = ⋃_{f ∈ S_d, d ≥ 1} D₊(g₀ f)` for `g₀ ∈ S₀`."]
theorem basicOpen_eq_iSup_basicOpen_mul_of_mem_zero {g₀ : A} (_hg₀ : g₀ ∈ 𝒜 0) :
    basicOpen 𝒜 g₀ = ⨆ (d : ℕ) (_ : 0 < d) (f : A) (_ : f ∈ 𝒜 d), basicOpen 𝒜 (g₀ * f) := by
  refine le_antisymm (fun x hx => ?_)
    (iSup_le fun d => iSup_le fun _ => iSup_le fun f => iSup_le fun _ =>
      basicOpen_mul_le_left 𝒜 g₀ f)
  have hirr := x.not_irrelevant_le
  rw [HomogeneousIdeal.irrelevant_le] at hirr
  push Not at hirr
  obtain ⟨d, hd, hdx⟩ := hirr
  obtain ⟨f, hf, hfx⟩ := SetLike.not_le_iff_exists.mp hdx
  simp only [TopologicalSpace.Opens.mem_iSup]
  exact ⟨d, hd, f, hf, x.isPrime.mul_notMem hx hfx⟩

/-- The standard opens `D₊(f)`, for `f` homogeneous of positive degree, form a basis of the
topology of `Proj 𝒜`. -/
@[stacks 00JP "Assertion (5): the opens `D₊(f)`, `f` homogeneous of positive degree, form a \
  basis of the topology of `Proj(S)`."]
theorem isTopologicalBasis_basicOpen_of_pos :
    TopologicalSpace.IsTopologicalBasis
      {U : Set (ProjectiveSpectrum 𝒜) |
        ∃ (d : ℕ) (f : A), 0 < d ∧ f ∈ 𝒜 d ∧ U = basicOpen 𝒜 f} := by
  refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds ?_ fun x U hx hU => ?_
  · rintro _ ⟨d, f, -, -, rfl⟩
    exact isOpen_basicOpen 𝒜
  obtain ⟨_, ⟨g, rfl⟩, hxg, hgU⟩ :=
    (isTopologicalBasis_basic_opens 𝒜).exists_subset_of_mem_open hx hU
  have hxg' : x ∈ basicOpen 𝒜 g := hxg
  replace hgU : (basicOpen 𝒜 g : Set (ProjectiveSpectrum 𝒜)) ⊆ U := hgU
  rw [basicOpen_eq_basicOpen_proj_zero_sup_iSup 𝒜 g] at hxg'
  have hle : ∀ i, (basicOpen 𝒜 (GradedRing.proj 𝒜 i g) : Set (ProjectiveSpectrum 𝒜)) ⊆
      basicOpen 𝒜 g := fun i => by
    rw [basicOpen_eq_union_of_projection 𝒜 g]
    exact le_iSup (fun i => basicOpen 𝒜 (GradedRing.proj 𝒜 i g)) i
  have hproj : ∀ i, GradedRing.proj 𝒜 i g ∈ 𝒜 i := fun i => by
    rw [GradedRing.proj_apply]
    exact SetLike.coe_mem _
  rcases TopologicalSpace.Opens.mem_sup.mp hxg' with h0 | hpos
  · rw [basicOpen_eq_iSup_basicOpen_mul_of_mem_zero 𝒜 (hproj 0)] at h0
    simp only [TopologicalSpace.Opens.mem_iSup] at h0
    obtain ⟨d, hd, f, hf, hxf⟩ := h0
    refine ⟨_, ⟨d, _, hd, ?_, rfl⟩, hxf, ?_⟩
    · simpa using SetLike.mul_mem_graded (hproj 0) hf
    · exact ((SetLike.coe_subset_coe.mpr (basicOpen_mul_le_left 𝒜 _ f)).trans (hle 0)).trans hgU
  · simp only [TopologicalSpace.Opens.mem_iSup] at hpos
    obtain ⟨i, hi, hxi⟩ := hpos
    exact ⟨_, ⟨i, _, hi, hproj i, rfl⟩, hxi, (hle i).trans hgU⟩

/-- For a homogeneous ideal `I`, the set `V₊(I)` is closed in `Proj 𝒜`. -/
@[stacks 00JP "Assertion (8): the sets `V₊(I)`, `I` homogeneous, are closed (Mathlib's \
  `ProjectiveSpectrum.isClosed_zeroLocus`)."]
theorem isClosed_zeroLocus_homogeneousIdeal (I : HomogeneousIdeal 𝒜) :
    IsClosed (zeroLocus 𝒜 (I : Set A)) :=
  isClosed_zeroLocus 𝒜 _

/-- Every closed subset of `Proj 𝒜` is `V₊(I)` for some homogeneous ideal `I`. -/
@[stacks 00JP "Assertion (9): every closed `T ⊆ Proj(S)` is `V₊(I)` for a homogeneous ideal `I`, \
  namely `I = ProjectiveSpectrum.vanishingIdeal T` (Mathlib's \
  `ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure`)."]
theorem exists_homogeneousIdeal_eq_zeroLocus_of_isClosed {T : Set (ProjectiveSpectrum 𝒜)}
    (hT : IsClosed T) : ∃ I : HomogeneousIdeal 𝒜, T = zeroLocus 𝒜 (I : Set A) :=
  ⟨vanishingIdeal T, by rw [zeroLocus_vanishingIdeal_eq_closure, hT.closure_eq]⟩

/-- The projective zero locus of an ideal `I` of a graded ring `A` is empty exactly when every
homogeneous prime of `A` containing `I` contains the irrelevant ideal: a homogeneous prime that
does not is a point of `Proj 𝒜`, hence a point of `V₊(I)`. The ideal `I` need not be
homogeneous. -/
private theorem zeroLocus_eq_empty_iff_forall_isPrime (I : Ideal A) :
    zeroLocus 𝒜 (I : Set A) = ∅ ↔
      ∀ J : Ideal A, J.IsHomogeneous 𝒜 → I ≤ J → J.IsPrime →
        (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤ J := by
  rw [Set.eq_empty_iff_forall_notMem]
  exact ⟨fun h J hJ hIJ hJp => not_not.mp fun hirr => h ⟨⟨J, hJ⟩, hJp, hirr⟩ hIJ,
    fun h x hx => x.not_irrelevant_le
      (h _ x.asHomogeneousIdeal.isHomogeneous hx x.isPrime)⟩

/-- An ideal `K` of a graded ring is contained in the radical of a homogeneous ideal `I` exactly
when it is contained in every homogeneous prime containing `I`: the `le_sInf` reading of
`Ideal.IsHomogeneous.radical_eq`. -/
@[ega "II 2.3.9" "more general"]
private theorem le_radical_iff_of_isHomogeneous {I K : Ideal A} (hI : I.IsHomogeneous 𝒜) :
    K ≤ I.radical ↔ ∀ J : Ideal A, J.IsHomogeneous 𝒜 → I ≤ J → J.IsPrime → K ≤ J := by
  simp [hI.radical_eq, le_sInf_iff]

/-- The projective zero locus `V₊(I)` of a homogeneous ideal `I` of a graded ring `A` is empty if
and only if the irrelevant ideal `𝒜₊` is contained in the radical of `I`. -/
@[stacks 00JP "Assertion (10): for a homogeneous ideal `I`, `V₊(I) = ∅` if and only if \
  `S₊ ⊆ √I`.",
  ega "II 2.3.16",
  ega "II 2.3.13" "more general",
  ega "II 2.3.2" "V₊(S₊)=∅",
  ega "II 8.3.4" "partial"]
theorem zeroLocus_empty_iff_irrelevant_le_radical (I : HomogeneousIdeal 𝒜) :
    zeroLocus 𝒜 (I : Set A) = ∅ ↔ HomogeneousIdeal.irrelevant 𝒜 ≤ I.radical := by
  rw [← coe_toIdeal, zeroLocus_eq_empty_iff_forall_isPrime, ← toIdeal_le_toIdeal_iff,
    HomogeneousIdeal.coe_radical, le_radical_iff_of_isHomogeneous 𝒜 I.isHomogeneous]

end ProjectiveSpectrum
