module

public import StacksFrontier.RingTheory.GradedAlgebra.Proj.AwayGradedPrimesVertical

/-!
# The diagram of [Stacks, Tag 01M4] part (1)(f)

Let `A = ⨁_{i ≥ 0} 𝒜 i` be a nonnegatively graded ring and let `f ∈ 𝒜 d`, `g ∈ 𝒜 e` be
homogeneous of positive degree with `D₊(g) ⊆ D₊(f)`. The maps constructed in parts (1)(c) and
(1)(d) induce a diagram of topological spaces

    D₊(g)  ←  {ℤ-graded primes of A[1/g]}  →  Spec A₍g₎
      ↓                   ↓                      ↓
    D₊(f)  ←  {ℤ-graded primes of A[1/f]}  →  Spec A₍f₎

in which the horizontal maps are homeomorphisms and the vertical maps are open immersions.

The horizontal homeomorphisms and the middle vertical arrow are
`StacksFrontier.RingTheory.GradedAlgebra.Proj.AwayGradedPrimesChart`,
`...AwayGradedPrimes` and `...AwayGradedPrimesVertical`. This file supplies the two outer
vertical arrows — the inclusion `D₊(g) ⊆ D₊(f)` on the left, and the map of spectra induced by
`A₍f₎ → A₍g₎` on the right — proves each is an open immersion, and assembles the whole of part
(1)(f) into the single statement `Stacks.ProjStandardOpenBaseChange.topologicalDiagram`.

The right-hand vertical arrow is an open immersion because `A₍g₎` is a localization of `A₍f₎`
away from `g ^ d / f ^ e`, which is part (1)(e)
(`ProjectiveSpectrum.isLocalizationAway_degreeZeroRingMap`); the left-hand one because it is the
inclusion of one open subset of `Proj 𝒜` into another.

## Main results

* `Stacks.ProjStandardOpenBaseChange.isOpenEmbedding_basicOpenInclusion`: the left vertical
  arrow is an open immersion.
* `Stacks.ProjStandardOpenBaseChange.isOpenEmbedding_comap_degreeZeroRingMap`: the right
  vertical arrow is an open immersion.
* `Stacks.ProjStandardOpenBaseChange.topologicalDiagram`: part (1)(f) in one statement.

## References

* [Stacks Project, Tag 01M4](https://stacks.math.columbia.edu/tag/01M4)
-/

@[expose] public noncomputable section

namespace Stacks.ProjStandardOpenBaseChange

open AlgebraicGeometry.ProjectiveSpectrum.Proj
open HomogeneousLocalization

universe u v

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
variable (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] {f g : A} {d e : ℕ}

/-! ### The left vertical arrow -/

/-- **The left vertical arrow of the diagram of [Stacks, Tag 01M4] part (1)(f)**: the inclusion
of the standard open `D₊(g)` into the standard open `D₊(f)` containing it. -/
public def basicOpenInclusion
    (hfg : ProjectiveSpectrum.basicOpen 𝒜 g ≤ ProjectiveSpectrum.basicOpen 𝒜 f) :
    ↥(ProjectiveSpectrum.basicOpen 𝒜 g) → ↥(ProjectiveSpectrum.basicOpen 𝒜 f) :=
  Set.inclusion hfg

/-- The left vertical arrow does not move the point of `Proj 𝒜`. -/
@[simp]
public theorem basicOpenInclusion_coe
    (hfg : ProjectiveSpectrum.basicOpen 𝒜 g ≤ ProjectiveSpectrum.basicOpen 𝒜 f)
    (p : ↥(ProjectiveSpectrum.basicOpen 𝒜 g)) :
    (basicOpenInclusion 𝒜 hfg p : ProjectiveSpectrum 𝒜) = p := rfl

/-- **The left vertical arrow of the diagram of [Stacks, Tag 01M4] part (1)(f) is an open
immersion.** It is the inclusion of an open subset of `Proj 𝒜` into another. -/
public theorem isOpenEmbedding_basicOpenInclusion
    (hfg : ProjectiveSpectrum.basicOpen 𝒜 g ≤ ProjectiveSpectrum.basicOpen 𝒜 f) :
    Topology.IsOpenEmbedding (basicOpenInclusion 𝒜 hfg) :=
  (ProjectiveSpectrum.basicOpen 𝒜 g).isOpen.isOpenEmbedding_inclusion hfg

/-! ### The right vertical arrow -/

/-- **The right vertical arrow of the diagram of [Stacks, Tag 01M4] part (1)(f)**: the map of
spectra induced by the canonical map `A₍f₎ → A₍g₎` of degree-zero localizations. -/
public def specDegreeZeroVertical (f g : A) (d e : ℕ) (hd : 0 < d) (he : 0 < e)
    (hf : f ∈ 𝒜 d) (hg : g ∈ 𝒜 e)
    (hfg : ProjectiveSpectrum.basicOpen 𝒜 g ≤ ProjectiveSpectrum.basicOpen 𝒜 f) :
    PrimeSpectrum (Away 𝒜 g) → PrimeSpectrum (Away 𝒜 f) :=
  PrimeSpectrum.comap
    (ProjectiveSpectrum.degreeZeroRingMap 𝒜 f g ⟨d, hd, hf⟩ ⟨e, he, hg⟩ hfg).toRingHom

/-- **The right vertical arrow of the diagram of [Stacks, Tag 01M4] part (1)(f) is an open
immersion.** By part (1)(e) the ring `A₍g₎` is the localization of `A₍f₎` away from the element
`g ^ d / f ^ e`, and the spectrum of a localization away from an element is an open subspace. -/
public theorem isOpenEmbedding_comap_degreeZeroRingMap (f g : A) (d e : ℕ) (hd : 0 < d)
    (he : 0 < e) (hf : f ∈ 𝒜 d) (hg : g ∈ 𝒜 e)
    (hfg : ProjectiveSpectrum.basicOpen 𝒜 g ≤ ProjectiveSpectrum.basicOpen 𝒜 f) :
    Topology.IsOpenEmbedding (specDegreeZeroVertical 𝒜 f g d e hd he hf hg hfg) := by
  let : Algebra (Away 𝒜 f) (Away 𝒜 g) :=
    (ProjectiveSpectrum.degreeZeroRingMap 𝒜 f g ⟨d, hd, hf⟩ ⟨e, he, hg⟩ hfg).toRingHom.toAlgebra
  have := ProjectiveSpectrum.isLocalizationAway_degreeZeroRingMap 𝒜 f g d e hd he hf hg hfg
  have hmem : g ^ d ∈ 𝒜 (e • d) := by
    rw [smul_eq_mul, mul_comm]
    exact SetLike.pow_mem_graded d hg
  exact PrimeSpectrum.localization_away_isOpenEmbedding (Away 𝒜 g)
    (Away.mk 𝒜 hf e (g ^ d) hmem)

/-! ### The diagram -/

section Diagram

variable [GradedRing (twistAway 𝒜 f d)] [GradedRing (twistAway 𝒜 g e)]

/-- The upper left-hand horizontal arrow, as a map into `D₊(g)`. -/
public def gradedPrimeToBasicOpen (hge : g ∈ 𝒜 e) (he : 0 < e) :
    gradedPrimes (twistAway 𝒜 g e) → ↥(ProjectiveSpectrum.basicOpen 𝒜 g) :=
  fun q => ⟨gradedPrimeToProj 𝒜 hge he q, gradedPrimeToProj_mem_basicOpen 𝒜 hge he q⟩

/-- **[Stacks, Tag 01M4] part (1)(f).** For `f ∈ 𝒜 d` and `g ∈ 𝒜 e` homogeneous of positive
degree with `D₊(g) ⊆ D₊(f)`, the canonical maps induce a commutative diagram of topological
spaces

    D₊(g)  ←  {ℤ-graded primes of A[1/g]}  →  Spec A₍g₎
      ↓                   ↓                      ↓
    D₊(f)  ←  {ℤ-graded primes of A[1/f]}  →  Spec A₍f₎

whose four horizontal arrows are homeomorphisms and whose three vertical arrows are open
immersions. The conjuncts are, in order: the two horizontal arrows of the top row are
homeomorphisms; the two of the bottom row are homeomorphisms; the left, middle and right
vertical arrows are open immersions; the left square commutes; the right square commutes. -/
public theorem topologicalDiagram (hfd : f ∈ 𝒜 d) (hd : 0 < d) (hge : g ∈ 𝒜 e) (he : 0 < e)
    (hf : ∃ m : ℕ, 0 < m ∧ f ∈ 𝒜 m) (hg : ∃ m : ℕ, 0 < m ∧ g ∈ 𝒜 m)
    (hfg : ProjectiveSpectrum.basicOpen 𝒜 g ≤ ProjectiveSpectrum.basicOpen 𝒜 f) :
    IsHomeomorph (gradedPrimeToBasicOpen 𝒜 hge he) ∧
      IsHomeomorph (gradedPrimesAwayToSpec 𝒜 hge) ∧
      IsHomeomorph (gradedPrimeToBasicOpen 𝒜 hfd hd) ∧
      IsHomeomorph (gradedPrimesAwayToSpec 𝒜 hfd) ∧
      Topology.IsOpenEmbedding (basicOpenInclusion 𝒜 hfg) ∧
      Topology.IsOpenEmbedding (gradedPrimesVertical 𝒜 hfd hge hf hg hfg) ∧
      Topology.IsOpenEmbedding (specDegreeZeroVertical 𝒜 f g d e hd he hfd hge hfg) ∧
      (∀ q : gradedPrimes (twistAway 𝒜 g e),
        basicOpenInclusion 𝒜 hfg (gradedPrimeToBasicOpen 𝒜 hge he q) =
          gradedPrimeToBasicOpen 𝒜 hfd hd (gradedPrimesVertical 𝒜 hfd hge hf hg hfg q)) ∧
      (∀ q : gradedPrimes (twistAway 𝒜 g e),
        specDegreeZeroVertical 𝒜 f g d e hd he hfd hge hfg (gradedPrimesAwayToSpec 𝒜 hge q) =
          gradedPrimesAwayToSpec 𝒜 hfd (gradedPrimesVertical 𝒜 hfd hge hf hg hfg q)) :=
  ⟨isHomeomorph_gradedPrimeToProj 𝒜 hge he, isHomeomorph_gradedPrimesAwayToSpec 𝒜 hge he,
    isHomeomorph_gradedPrimeToProj 𝒜 hfd hd, isHomeomorph_gradedPrimesAwayToSpec 𝒜 hfd hd,
    isOpenEmbedding_basicOpenInclusion 𝒜 hfg,
    isOpenEmbedding_gradedPrimesVertical 𝒜 hfd hd hge he hf hg hfg,
    isOpenEmbedding_comap_degreeZeroRingMap 𝒜 f g d e hd he hfd hge hfg,
    fun q => Subtype.ext
      (gradedPrimeToProj_gradedPrimesVertical 𝒜 hfd hd hge he hf hg hfg q).symm,
    fun q => comap_degreeZeroRingMap_gradedPrimesAwayToSpec 𝒜 hfd hge hf hg hfg q⟩

end Diagram

end Stacks.ProjStandardOpenBaseChange

end
