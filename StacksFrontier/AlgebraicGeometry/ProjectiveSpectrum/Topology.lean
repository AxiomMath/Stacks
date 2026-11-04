module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology
public import Mathlib.RingTheory.GradedAlgebra.Radical
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Emptiness of a projective zero locus

Let `A = ⨁_{d ≥ 0} 𝒜 d` be a graded ring. Its homogeneous spectrum `Proj 𝒜`
(`ProjectiveSpectrum 𝒜`) is the set of *relevant* homogeneous primes of `A`, that is, the
homogeneous primes not containing the irrelevant ideal `𝒜₊ = ⨁_{d > 0} 𝒜 d`, topologized by the
closed sets `V₊(I) = {p ∈ Proj 𝒜 | I ⊆ p}` for `I` a homogeneous ideal — in Mathlib,
`ProjectiveSpectrum.zeroLocus 𝒜 I`.

This file records the criterion for such a closed set to be empty: `V₊(I) = ∅` if and only if
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

* `ProjectiveSpectrum.zeroLocus_empty_iff_irrelevant_le_radical`: for a homogeneous ideal `I` of a
  graded ring `A`, the projective zero locus of `I` is empty if and only if the irrelevant ideal is
  contained in the radical of `I`.

## Implementation notes

The source states ten assertions about the topology of `Proj 𝒜`, and all but four of them are
already available at hypotheses no stronger than the source's, so restating them here would
duplicate them; only the emptiness criterion, the source's assertion (10), is stated. Namely: (1)
`D₊(f)` is open is `ProjectiveSpectrum.isOpen_basicOpen`; (2) `D₊(ff') = D₊(f) ∩ D₊(f')` is
`ProjectiveSpectrum.basicOpen_mul`; (3) the decomposition of `D(g) ∩ Proj 𝒜` along the homogeneous
parts of `g` is `ProjectiveSpectrum.basicOpen_eq_union_of_projection`, in the equivalent form
`D₊(g) = ⨆_i D₊(gᵢ)` that treats the degree-zero part on the same footing as the others; (6) the
homeomorphism `D₊(f) ≅ Spec A⁰_f` for `f` homogeneous of positive degree is
`AlgebraicGeometry.projIsoSpecTopComponent` (the source's intermediate description of the same
space as the ℤ-graded primes of `A_f` is a device of its proof, not of its statement); (8)
`V₊(I)` is closed is `ProjectiveSpectrum.isClosed_zeroLocus`; and (9), that every closed subset is
some `V₊(I)` with `I` homogeneous, is `ProjectiveSpectrum.isClosed_iff_zeroLocus` together with
`ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure`, which exhibits a closed `T` as the zero
locus of the homogeneous ideal `ProjectiveSpectrum.vanishingIdeal T`. Of the source's remaining
assertions, (5) is available only in the weaker form `AlgebraicGeometry.Proj.isBasis_basicOpen`,
where `f` ranges over all of `A` rather than over the homogeneous elements of positive degree; and
(4), the sharp form of (5), and (7), the existence of a graded ring with non-quasi-compact `Proj`,
are not yet available. Each of those is a statement about basic opens rather than about zero loci,
and belongs with the `basicOpen` API.

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

Faithfulness. (1) The one hypothesis, that `I` is homogeneous, is used: without it the criterion
fails in the direction `V₊(I) = ∅ → 𝒜₊ ≤ √I`, since for `A = k[x, y]` graded by degree and
`I = (x + y)` every homogeneous prime containing `x + y` contains both `x` and `y` and so is
irrelevant, giving `V₊(I) = ∅`, while `x ∉ √I`. (2) The base is the source's: `I` is an ideal of
the graded ring `A` itself, `𝒜₊` is the irrelevant ideal of that same grading, and the radical is
taken in `A`. (3) The two sides are pinned to the source's own sets rather than asserted to exist:
`V₊(I)` is `ProjectiveSpectrum.zeroLocus 𝒜 I`, the relevant homogeneous primes containing `I`, and
`𝒜₊ ⊆ √I` is an inclusion of ideals of `A`. (4) The instantiation is not degenerate, in both
directions: for `A = k[x, y]` graded by degree, `I = (x, y) = 𝒜₊` has `V₊(I) = ∅` and
`𝒜₊ ≤ √I`, whereas `I = (x)` has `V₊(I) = {(x)}` nonempty and `y ∉ √I`.

## References

* [StackProject 00JP](https://stacks.math.columbia.edu/tag/00JP)
-/

@[expose] public section

namespace ProjectiveSpectrum

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubmonoidClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

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
@[stacks 00JP "Assertion (10); see the module docstring for the other nine.",
  ega "II 2.3.16",
  ega "II 2.3.13" "more general",
  ega "II 2.3.2" "V₊(S₊)=∅",
  ega "II 8.3.4" "partial"]
theorem zeroLocus_empty_iff_irrelevant_le_radical (I : HomogeneousIdeal 𝒜) :
    zeroLocus 𝒜 (I : Set A) = ∅ ↔ HomogeneousIdeal.irrelevant 𝒜 ≤ I.radical := by
  rw [← coe_toIdeal, zeroLocus_eq_empty_iff_forall_isPrime, ← toIdeal_le_toIdeal_iff,
    HomogeneousIdeal.coe_radical, le_radical_iff_of_isHomogeneous 𝒜 I.isHomogeneous]

end ProjectiveSpectrum
