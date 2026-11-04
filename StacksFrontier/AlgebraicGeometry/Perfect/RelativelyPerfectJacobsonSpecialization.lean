module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
import StacksCore.Tactic.StacksAttribute

/-!
# Points specialize into the closed fibre over a Jacobson-radical ideal

Let `R` be a ring, let `I ⊆ R` be an ideal contained in the Jacobson radical of `R`, write
`S = Spec R` and `S₀ = Spec (R/I)`, and let `f : X ⟶ S` be universally closed. Then every point
of `X` specializes to a point of `X₀ = S₀ ×_S X`.

## Main results

* `AlgebraicGeometry.exists_specializes_mem_zeroLocus_of_universallyClosed`: every point of `X`
  specializes to a point whose image prime contains `I`.
* `AlgebraicGeometry.range_specMap_quotientMk_base`: the image of `Spec (R/I) ⟶ Spec R` is the
  zero locus of `I`.
* `AlgebraicGeometry.exists_specializes_mem_range_pullback_snd_quotientMk`: the previous two
  combined, in the form `x ⤳ x₀` with `x₀` in the image of `X₀ ⟶ X`.

## Implementation notes

The argument is the one the source gives. The closure `Z` of a point `x` of `X` is closed, so its
image in `Spec R` is closed because `f` is universally closed, hence is the zero locus of an
ideal `J`; it is nonempty, so `J ≠ R` and `J` is contained in a maximal ideal `m`. The Jacobson
radical is the infimum of the maximal ideals, so `I ⊆ m`, and `m` lies in the image of `Z`: any
preimage of `m` in `Z` is the required specialization.

Universal closedness is the only part of properness used, and it is taken as the hypothesis
rather than `IsProper` so that separatedness and finite type are not asked for. Both hypotheses
are satisfiable with no further conditions: `I = ⊥` lies in every Jacobson radical, and `I` may
be taken to be the maximal ideal of a local ring.

## References

* [The Stacks Project, Lemma 37.71.3 (0DJZ)](https://stacks.math.columbia.edu/tag/0DJZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A nonempty closed subset of `Spec R` contains a point whose prime contains every ideal
inside the Jacobson radical of `R`: the subset is the zero locus of a proper ideal, which lies
in some maximal ideal. -/
private lemma exists_mem_of_isClosed_of_jacobson_le {R : Type u} [CommRing R]
    {Z : Set (PrimeSpectrum R)} (hZ : IsClosed Z) (hne : Z.Nonempty)
    {I : Ideal R} (hI : I ≤ (⊥ : Ideal R).jacobson) :
    ∃ p ∈ Z, (I : Set R) ⊆ p.asIdeal := by
  obtain ⟨J, hJ⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal Z).mp hZ
  obtain ⟨q, hq⟩ := hne
  have hqJ : (J : Set R) ⊆ q.asIdeal := (PrimeSpectrum.mem_zeroLocus _ _).mp (hJ ▸ hq)
  have hJne : J ≠ ⊤ := fun h =>
    q.isPrime.ne_top (top_le_iff.mp (h ▸ hqJ))
  obtain ⟨m, hm, hJm⟩ := Ideal.exists_le_maximal J hJne
  have hIm : I ≤ m := hI.trans (by rw [Ideal.jacobson]; exact sInf_le ⟨bot_le, hm⟩)
  exact ⟨⟨m, hm.isPrime⟩, hJ ▸ (PrimeSpectrum.mem_zeroLocus _ _).mpr hJm, hIm⟩

/-- **Stacks 0DJZ, the specialization step.** Let `I` be an ideal of `R` contained in the
Jacobson radical and let `f : X ⟶ Spec R` be universally closed. Then every point of `X`
specializes to a point whose image prime contains `I`. -/
public theorem exists_specializes_mem_zeroLocus_of_universallyClosed
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [UniversallyClosed f] {I : Ideal R} (hI : I ≤ (⊥ : Ideal R).jacobson) (x : X) :
    ∃ x₀ : X, x ⤳ x₀ ∧ (I : Set R) ⊆ (f.base x₀).asIdeal := by
  obtain ⟨p, hp, hIp⟩ := exists_mem_of_isClosed_of_jacobson_le
    (Z := f.base '' closure {x}) (f.isClosedMap _ isClosed_closure)
    ⟨f.base x, x, subset_closure rfl, rfl⟩ hI
  obtain ⟨x₀, hx₀, hfx₀⟩ := hp
  exact ⟨x₀, specializes_iff_mem_closure.mpr hx₀, hfx₀ ▸ hIp⟩

/-- The image of the morphism `Spec (R/I) ⟶ Spec R` is the zero locus of `I`. -/
public theorem range_specMap_quotientMk_base {R : Type u} [CommRing R] (I : Ideal R) :
    Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).base =
      PrimeSpectrum.zeroLocus (I : Set R) := by
  have key : Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)) =
      PrimeSpectrum.zeroLocus (I : Set R) := by
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective]
    simp
  exact key

/-- **Stacks 0DJZ, the specialization step, for an arbitrary model of the closed fibre.** If the
zero locus of `I` is covered by the image of `i : S₀ ⟶ Spec R`, every point of `X` specializes
into the image of the projection `S₀ ×_{Spec R} X ⟶ X`. -/
public theorem exists_specializes_mem_range_of_universallyClosed
    {R : Type u} [CommRing R] {X S₀ : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [UniversallyClosed f] (i : S₀ ⟶ Spec (CommRingCat.of R)) {I : Ideal R}
    (hI : I ≤ (⊥ : Ideal R).jacobson)
    (hi : PrimeSpectrum.zeroLocus (I : Set R) ⊆ Set.range i.base) (x : X) :
    ∃ x₀ : X, x ⤳ x₀ ∧ x₀ ∈ Set.range (pullback.snd i f).base := by
  obtain ⟨x₀, hspec, hmem⟩ := exists_specializes_mem_zeroLocus_of_universallyClosed f hI x
  refine ⟨x₀, hspec, ?_⟩
  rw [Scheme.Pullback.range_snd]
  exact hi ((PrimeSpectrum.mem_zeroLocus _ _).mpr hmem)

/-- **Stacks 0DJZ, the specialization step.** Let `I` be an ideal of `R` contained in the
Jacobson radical, let `f : X ⟶ Spec R` be universally closed and let
`X₀ = Spec (R/I) ×_{Spec R} X`. Then every point of `X` specializes to a point lying in the
image of `X₀ ⟶ X`. -/
@[stacks 0DJZ "the specialization step of the proof: universal closedness of `f` and `I` \
inside the Jacobson radical force every point of `X` to specialize to a point of \
`X₀ = Spec (R/I) ×_{Spec R} X`"]
public theorem exists_specializes_mem_range_pullback_snd_quotientMk
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [UniversallyClosed f] {I : Ideal R} (hI : I ≤ (⊥ : Ideal R).jacobson) (x : X) :
    ∃ x₀ : X, x ⤳ x₀ ∧ x₀ ∈
      Set.range (pullback.snd (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) f).base :=
  exists_specializes_mem_range_of_universallyClosed f _ hI
    (range_specMap_quotientMk_base I).ge x

end AlgebraicGeometry

end
