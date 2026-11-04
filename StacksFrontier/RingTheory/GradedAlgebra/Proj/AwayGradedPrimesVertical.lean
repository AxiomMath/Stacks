module

public import StacksFrontier.RingTheory.GradedAlgebra.Proj.AwayGradedPrimesChart
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjLocalizedRingMap

/-!
# The middle column of the diagram of [Stacks, Tag 01M4] part (1)(f)

Let `A = ⨁_{i ≥ 0} 𝒜 i` be a nonnegatively graded ring and let `f ∈ 𝒜 d`, `g ∈ 𝒜 e` be
homogeneous of positive degree with `D₊(g) ⊆ D₊(f)`. Contraction along the canonical map
`A[1/f] → A[1/g]` carries `ℤ`-graded primes to `ℤ`-graded primes; this is the vertical arrow of
the middle column of the diagram

    D₊(g)  ←  {ℤ-graded primes of A[1/g]}  →  Spec A₍g₎
      ↓                   ↓                      ↓
    D₊(f)  ←  {ℤ-graded primes of A[1/f]}  →  Spec A₍f₎

and this file proves that both squares commute and that the middle vertical arrow is an open
immersion.

## Main results

* `Stacks.ProjStandardOpenBaseChange.gradedPrimesVertical`: the middle vertical arrow.
* `Stacks.ProjStandardOpenBaseChange.gradedPrimeToProj_gradedPrimesVertical`: the left square
  commutes.
* `Stacks.ProjStandardOpenBaseChange.comap_degreeZeroRingMap_gradedPrimesAwayToSpec`: the right
  square commutes.
* `Stacks.ProjStandardOpenBaseChange.isOpenEmbedding_gradedPrimesVertical`: the middle vertical
  arrow is an open immersion.

## Implementation notes

Homogeneity of the contracted ideal is not proved by a degree computation on `A[1/f] → A[1/g]`.
The map is an `A`-algebra map, so contracting all the way to `A` gives the same ideal whichever
route is taken, and an ideal of `A[1/f]` is the extension of its own contraction to `A`
(`IsLocalization.map_comap`); so homogeneity follows from homogeneity in `A` together with
`Stacks.ProjStandardOpenBaseChange.isHomogeneous_map`. The same identity of contractions is the
commutativity of the left square.

## References

* [Stacks Project, Tag 01M4](https://stacks.math.columbia.edu/tag/01M4)
-/

@[expose] public noncomputable section

/-- **The inclusion of an open subset into a larger set is an open embedding.** Its range is the
preimage of `U` under the inclusion of `V`, which is open in the subspace `V` because `U` is open
in `X`; openness of `V` is not needed. -/
public theorem IsOpen.isOpenEmbedding_inclusion {X : Type*} [TopologicalSpace X] {U V : Set X}
    (hU : IsOpen U) (h : U ⊆ V) : Topology.IsOpenEmbedding (Set.inclusion h) where
  __ := Topology.IsEmbedding.inclusion h
  isOpen_range := by
    have hrange : Set.range (Set.inclusion h) = (Subtype.val : V → X) ⁻¹' U := by
      ext ⟨x, hx⟩
      simp [Set.inclusion, Set.range, Subtype.ext_iff]
    rw [hrange]
    exact hU.preimage continuous_subtype_val

namespace Stacks.ProjStandardOpenBaseChange

open AlgebraicGeometry.ProjectiveSpectrum.Proj
open HomogeneousLocalization

universe u v

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
variable (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] {f g : A} {d e : ℕ}

/-- The canonical map `A[1/f] → A[1/g]` is an `A`-algebra map, so it fixes the image of `A`. -/
public theorem localizedRingMap_algebraMap
    (hf : ∃ m : ℕ, 0 < m ∧ f ∈ 𝒜 m) (hg : ∃ m : ℕ, 0 < m ∧ g ∈ 𝒜 m)
    (hfg : ProjectiveSpectrum.basicOpen 𝒜 g ≤ ProjectiveSpectrum.basicOpen 𝒜 f) (a : A) :
    ProjectiveSpectrum.localizedRingMap 𝒜 f g hf hg hfg
        (algebraMap A (Localization.Away f) a) = algebraMap A (Localization.Away g) a :=
  AlgHom.commutes _ a

/-- **Contracting to `A` does not see which of the two localizations the prime came from.** The
contraction to `A` of the contraction of an ideal of `A[1/g]` along `A[1/f] → A[1/g]` is its
contraction to `A`. -/
public theorem comap_comap_localizedRingMap
    (hf : ∃ m : ℕ, 0 < m ∧ f ∈ 𝒜 m) (hg : ∃ m : ℕ, 0 < m ∧ g ∈ 𝒜 m)
    (hfg : ProjectiveSpectrum.basicOpen 𝒜 g ≤ ProjectiveSpectrum.basicOpen 𝒜 f)
    (J : Ideal (Localization.Away g)) :
    (J.comap (ProjectiveSpectrum.localizedRingMap 𝒜 f g hf hg hfg).toRingHom).comap
        (algebraMap A (Localization.Away f)) =
      J.comap (algebraMap A (Localization.Away g)) := by
  rw [Ideal.comap_comap]
  congr 1
  exact RingHom.ext fun a => localizedRingMap_algebraMap 𝒜 hf hg hfg a

section Vertical

variable [GradedRing (twistAway 𝒜 f d)] [GradedRing (twistAway 𝒜 g e)]

/-- Contraction along `A[1/f] → A[1/g]` preserves homogeneity: the contracted ideal is the
extension of its own contraction to `A`, which is homogeneous. -/
public theorem isHomogeneous_comap_localizedRingMap (hfd : f ∈ 𝒜 d) (hge : g ∈ 𝒜 e)
    (hf : ∃ m : ℕ, 0 < m ∧ f ∈ 𝒜 m) (hg : ∃ m : ℕ, 0 < m ∧ g ∈ 𝒜 m)
    (hfg : ProjectiveSpectrum.basicOpen 𝒜 g ≤ ProjectiveSpectrum.basicOpen 𝒜 f)
    {J : Ideal (Localization.Away g)} (hJ : J.IsHomogeneous (twistAway 𝒜 g e)) :
    (J.comap (ProjectiveSpectrum.localizedRingMap 𝒜 f g hf hg hfg).toRingHom).IsHomogeneous
      (twistAway 𝒜 f d) := by
  set K := J.comap (ProjectiveSpectrum.localizedRingMap 𝒜 f g hf hg hfg).toRingHom with hK
  have hrec : Ideal.map (algebraMap A (Localization.Away f))
      (K.comap (algebraMap A (Localization.Away f))) = K := by
    have h := IsLocalization.map_under (Submonoid.powers f) (Localization.Away f) K
    rwa [Ideal.under_def] at h
  rw [← hrec, comap_comap_localizedRingMap 𝒜 hf hg hfg J]
  exact isHomogeneous_map 𝒜 hfd (isHomogeneous_comap 𝒜 hge hJ)

/-- **The middle vertical arrow of the diagram of [Stacks, Tag 01M4] part (1)(f)**: contraction
along the canonical map `A[1/f] → A[1/g]`, which carries `ℤ`-graded primes of `A[1/g]` to
`ℤ`-graded primes of `A[1/f]`. -/
public def gradedPrimesVertical (hfd : f ∈ 𝒜 d) (hge : g ∈ 𝒜 e)
    (hf : ∃ m : ℕ, 0 < m ∧ f ∈ 𝒜 m) (hg : ∃ m : ℕ, 0 < m ∧ g ∈ 𝒜 m)
    (hfg : ProjectiveSpectrum.basicOpen 𝒜 g ≤ ProjectiveSpectrum.basicOpen 𝒜 f) :
    gradedPrimes (twistAway 𝒜 g e) → gradedPrimes (twistAway 𝒜 f d) :=
  fun q =>
    ⟨PrimeSpectrum.comap (ProjectiveSpectrum.localizedRingMap 𝒜 f g hf hg hfg).toRingHom q.val,
      isHomogeneous_comap_localizedRingMap 𝒜 hfd hge hf hg hfg q.property⟩

/-- The middle vertical arrow contracts ideals along `A[1/f] → A[1/g]`. -/
@[simp]
public theorem gradedPrimesVertical_asIdeal (hfd : f ∈ 𝒜 d) (hge : g ∈ 𝒜 e)
    (hf : ∃ m : ℕ, 0 < m ∧ f ∈ 𝒜 m) (hg : ∃ m : ℕ, 0 < m ∧ g ∈ 𝒜 m)
    (hfg : ProjectiveSpectrum.basicOpen 𝒜 g ≤ ProjectiveSpectrum.basicOpen 𝒜 f)
    (q : gradedPrimes (twistAway 𝒜 g e)) :
    (gradedPrimesVertical 𝒜 hfd hge hf hg hfg q).val.asIdeal =
      q.val.asIdeal.comap
        (ProjectiveSpectrum.localizedRingMap 𝒜 f g hf hg hfg).toRingHom :=
  rfl

/-- **The left square of the diagram of [Stacks, Tag 01M4] part (1)(f) commutes.** A `ℤ`-graded
prime of `A[1/g]` has the same image in `Proj 𝒜` whether it is first carried to a `ℤ`-graded
prime of `A[1/f]` and then contracted to `A`, or contracted to `A` directly; that is, the point
of `D₊(g)` it determines, read inside `D₊(f)`, is the point its image in the `ℤ`-graded primes
of `A[1/f]` determines. -/
public theorem gradedPrimeToProj_gradedPrimesVertical (hfd : f ∈ 𝒜 d) (hd : 0 < d)
    (hge : g ∈ 𝒜 e) (he : 0 < e)
    (hf : ∃ m : ℕ, 0 < m ∧ f ∈ 𝒜 m) (hg : ∃ m : ℕ, 0 < m ∧ g ∈ 𝒜 m)
    (hfg : ProjectiveSpectrum.basicOpen 𝒜 g ≤ ProjectiveSpectrum.basicOpen 𝒜 f)
    (q : gradedPrimes (twistAway 𝒜 g e)) :
    gradedPrimeToProj 𝒜 hfd hd (gradedPrimesVertical 𝒜 hfd hge hf hg hfg q) =
      gradedPrimeToProj 𝒜 hge he q :=
  ProjectiveSpectrum.ext (HomogeneousIdeal.toIdeal_injective
    (comap_comap_localizedRingMap 𝒜 hf hg hfg q.val.asIdeal))

/-- The right-hand horizontal arrow is contraction along `A₍f₎ → A[1/f]`. -/
public theorem gradedPrimesAwayToSpec_asIdeal (hfd : f ∈ 𝒜 d)
    (q : gradedPrimes (twistAway 𝒜 f d)) :
    (gradedPrimesAwayToSpec 𝒜 hfd q).asIdeal =
      q.val.asIdeal.comap (algebraMap (Away 𝒜 f) (Localization.Away f)) := by
  have hhom : (gradeZeroSubring (twistAway 𝒜 f d)).subtype.comp
      (gradeZeroSubringEquivAway 𝒜 hfd).toRingHom =
      algebraMap (Away 𝒜 f) (Localization.Away f) :=
    RingHom.ext fun c => (coe_gradeZeroSubringEquivAway 𝒜 hfd c).trans
      (HomogeneousLocalization.algebraMap_apply c).symm
  rw [gradedPrimesAwayToSpec, Function.comp_apply, PrimeSpectrum.comap_asIdeal,
    gradedPrimesComparison, PrimeSpectrum.comap_asIdeal, Ideal.comap_comap, hhom]

/-- **The right square of the diagram of [Stacks, Tag 01M4] part (1)(f) commutes.** Contracting
a `ℤ`-graded prime of `A[1/g]` to `A₍g₎` and then to `A₍f₎` gives the same prime of `A₍f₎` as
carrying it to a `ℤ`-graded prime of `A[1/f]` and contracting that to `A₍f₎`. -/
public theorem comap_degreeZeroRingMap_gradedPrimesAwayToSpec (hfd : f ∈ 𝒜 d) (hge : g ∈ 𝒜 e)
    (hf : ∃ m : ℕ, 0 < m ∧ f ∈ 𝒜 m) (hg : ∃ m : ℕ, 0 < m ∧ g ∈ 𝒜 m)
    (hfg : ProjectiveSpectrum.basicOpen 𝒜 g ≤ ProjectiveSpectrum.basicOpen 𝒜 f)
    (q : gradedPrimes (twistAway 𝒜 g e)) :
    PrimeSpectrum.comap (ProjectiveSpectrum.degreeZeroRingMap 𝒜 f g hf hg hfg).toRingHom
        (gradedPrimesAwayToSpec 𝒜 hge q) =
      gradedPrimesAwayToSpec 𝒜 hfd (gradedPrimesVertical 𝒜 hfd hge hf hg hfg q) := by
  refine PrimeSpectrum.ext ?_
  rw [PrimeSpectrum.comap_asIdeal, gradedPrimesAwayToSpec_asIdeal 𝒜 hge q,
    gradedPrimesAwayToSpec_asIdeal 𝒜 hfd,
    gradedPrimesVertical_asIdeal 𝒜 hfd hge hf hg hfg q, Ideal.comap_comap, Ideal.comap_comap]
  congr 1
  refine RingHom.ext fun x => ?_
  rw [RingHom.comp_apply, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply]
  exact ProjectiveSpectrum.val_degreeZeroRingMap 𝒜 f g hf hg hfg x

/-- **The middle vertical arrow of the diagram of [Stacks, Tag 01M4] part (1)(f) is an open
immersion.** Under the two left-hand horizontal homeomorphisms it is the inclusion of the open
`D₊(g)` into `D₊(f)`, so it is an open embedding of the space of `ℤ`-graded primes of `A[1/g]`
into the space of `ℤ`-graded primes of `A[1/f]`. -/
public theorem isOpenEmbedding_gradedPrimesVertical (hfd : f ∈ 𝒜 d) (hd : 0 < d)
    (hge : g ∈ 𝒜 e) (he : 0 < e)
    (hf : ∃ m : ℕ, 0 < m ∧ f ∈ 𝒜 m) (hg : ∃ m : ℕ, 0 < m ∧ g ∈ 𝒜 m)
    (hfg : ProjectiveSpectrum.basicOpen 𝒜 g ≤ ProjectiveSpectrum.basicOpen 𝒜 f) :
    Topology.IsOpenEmbedding (gradedPrimesVertical 𝒜 hfd hge hf hg hfg) := by
  have hsub : (ProjectiveSpectrum.basicOpen 𝒜 g : Set (ProjectiveSpectrum 𝒜)) ⊆
      (ProjectiveSpectrum.basicOpen 𝒜 f : Set (ProjectiveSpectrum 𝒜)) := hfg
  have hfact : gradedPrimesVertical 𝒜 hfd hge hf hg hfg =
      (gradedPrimesHomeoBasicOpen 𝒜 hfd hd).symm ∘ Set.inclusion hsub ∘
        (gradedPrimesHomeoBasicOpen 𝒜 hge he) := by
    funext q
    have h1 : (gradedPrimesHomeoBasicOpen 𝒜 hfd hd)
          (gradedPrimesVertical 𝒜 hfd hge hf hg hfg q) =
        Set.inclusion hsub ((gradedPrimesHomeoBasicOpen 𝒜 hge he) q) :=
      Subtype.ext (gradedPrimeToProj_gradedPrimesVertical 𝒜 hfd hd hge he hf hg hfg q)
    simp only [Function.comp_apply, ← h1, Homeomorph.symm_apply_apply]
  rw [hfact]
  exact (gradedPrimesHomeoBasicOpen 𝒜 hfd hd).symm.isOpenEmbedding.comp
    (((ProjectiveSpectrum.basicOpen 𝒜 g).isOpen.isOpenEmbedding_inclusion hsub).comp
      (gradedPrimesHomeoBasicOpen 𝒜 hge he).isOpenEmbedding)

end Vertical

end Stacks.ProjStandardOpenBaseChange

end
