module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.FiniteChart
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.GroupStructure
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.SpecializationCriterion
public import StacksFrontier.AlgebraicGeometry.Properties.DiscreteValuation
public import StacksCore.Tactic.StacksAttribute

/-!
# Checking the weighting condition over discrete valuation rings

Being a weighting is a condition about every finite open piece of every étale base change, and
it can be verified after base change to the spectra of discrete valuation rings alone. This is
the converse of the base-change stability of weightings: a function on the source of a locally
quasi-finite morphism locally of finite type over a locally Noetherian base is a weighting as
soon as its pullback to each finite open piece of each base change along a morphism from the
spectrum of a discrete valuation ring is one.

## Main results

* `AlgebraicGeometry.IsWeighting.isLocallyConstant_of_isFinite`: a weighting of a finite
  morphism has locally constant weighted fibre sum, the morphism itself being a chart.
* `AlgebraicGeometry.isWeighting_of_forall_isFinite_over_isDiscreteValuationRing`: the weighting
  condition can be checked after base change to the spectra of discrete valuation rings.

## Implementation notes

The base of a chart is locally Noetherian, the chart morphism to the base being étale, so by
`AlgebraicGeometry.isLocallyConstant_of_specializes_eq_of_isLocallyNoetherian` the local
constancy required of the weighted fibre sum of a chart reduces to its invariance along
specializations in that base. A specialization is realized by a morphism `q` from the spectrum
of a discrete valuation ring, by `AlgebraicGeometry.exists_dvr_morphism_of_specializes`, and
base changing the chart along `q` produces, via `AlgebraicGeometry.baseChangedChartMap`, a
finite open piece of the base change of the given morphism along `q` composed with the chart
morphism. The hypothesis applies to that piece, and the spectrum of a domain being irreducible,
hence preconnected, the resulting locally constant function takes the same value at the generic
and at the closed point. Tag 0F39, the compatibility of weighted fibre sums with cartesian base
change, identifies that common value with the two values to be compared.

The two auxiliary facts that the chart morphism `π` is locally quasi-finite and that `h` is
étale are `AlgebraicGeometry.locallyQuasiFinite_of_isWeighting_data` and
`AlgebraicGeometry.etale_of_openImmersion_pullback_lift`; they already exist in
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.GroupStructure` and are reused rather
than restated here.

## References

* [Stacks Project, Tag 0F3A](https://stacks.math.columbia.edu/tag/0F3A)
* [Stacks Project, Tag 0F3B](https://stacks.math.columbia.edu/tag/0F3B)
* [Stacks Project, Tag 0H5P](https://stacks.math.columbia.edu/tag/0H5P)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The projection to the first factor of a fibre product along an identity morphism is an
isomorphism: the square with both horizontal edges the identity is cartesian, so the projection
is a base change of an isomorphism. -/
theorem isIso_pullback_fst_of_id {W T : Scheme.{u}} (F : W ⟶ T) :
    IsIso (pullback.fst F (𝟙 T)) :=
  (IsPullback.of_hasPullback F (𝟙 T)).isIso_fst_of_isIso

/-- An open immersion into the first factor of a fibre product along an identity morphism
induces an open immersion into that fibre product, the first projection being an isomorphism. -/
theorem isOpenImmersion_pullback_lift_id {P W T : Scheme.{u}} {F : W ⟶ T} (k : P ⟶ W)
    (e : P ⟶ T) (comm : k ≫ F = e ≫ 𝟙 T) [IsOpenImmersion k] :
    IsOpenImmersion (pullback.lift k e comm) := by
  have := isIso_pullback_fst_of_id F
  have hlift : pullback.lift k e comm = k ≫ inv (pullback.fst F (𝟙 T)) := by
    rw [IsIso.eq_comp_inv]
    exact pullback.lift_fst k e comm
  rw [hlift]
  infer_instance

/-- A weighting of a finite morphism has locally constant weighted fibre sum: the morphism is
itself a chart for the weighting condition, over the identity of its target. -/
theorem IsWeighting.isLocallyConstant_of_isFinite {P T : Scheme.{u}} {p : P ⟶ T} {v : P → ℤ}
    (hw : IsWeighting p v) (hp : IsFinite p) :
    IsLocallyConstant (separableDegreeWeightedFiberSum p v) := by
  have := hp
  have comm : 𝟙 P ≫ p = p ≫ 𝟙 T := by simp
  have hlift : IsOpenImmersion (pullback.lift (𝟙 P) p comm) :=
    isOpenImmersion_pullback_lift_id (𝟙 P) p comm
  simpa using hw (𝟙 P) p (𝟙 T) comm inferInstance hlift hp

/-- **Stacks Project, Lemma 0H5P**, the converse of Tag 0F3B. For a locally quasi-finite
morphism locally of finite type over a locally Noetherian base, an integer-valued function on
the source is a weighting as soon as, for every discrete valuation ring `R` and every morphism
`c` from `Spec R` to the base, the pulled-back function is a weighting of every finite open
piece of the base change of `f` along `c`. -/
theorem isWeighting_of_forall_isFinite_over_isDiscreteValuationRing {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f] [LocallyQuasiFinite f] [IsLocallyNoetherian S]
    (w : X → ℤ)
    (H : ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
      (c : Spec (CommRingCat.of R) ⟶ S) {W : Scheme.{u}} (ι : W ⟶ pullback f c),
      IsOpenImmersion ι → IsFinite (ι ≫ pullback.snd f c) →
      IsWeighting (ι ≫ pullback.snd f c) (w ∘ pullback.fst f c ∘ ι)) :
    IsWeighting f w := by
  intro U V h π g comm hg hU hπ
  have := hg
  have := hU
  have := hπ
  have : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian g
  have : LocallyQuasiFinite π := locallyQuasiFinite_of_isWeighting_data h π g comm hU
  have hfin : ∀ v : V, (π ⁻¹' {v}).Finite := fun v ↦ π.finite_preimage_singleton v
  refine isLocallyConstant_of_specializes_eq_of_isLocallyNoetherian ?_
  intro v v' hspec
  obtain ⟨R, _, _, _, q, hη, hs⟩ := exists_dvr_morphism_of_specializes V hspec
  have : IsOpenImmersion (baseChangedChartMap f g q h π comm) :=
    baseChangedChartMap_isOpenImmersion f g q h π comm
  have hsnd : baseChangedChartMap f g q h π comm ≫ pullback.snd f (q ≫ g) =
      pullback.snd π q := baseChangedChartMap_snd f g q h π comm
  have hfinR : IsFinite (baseChangedChartMap f g q h π comm ≫ pullback.snd f (q ≫ g)) := by
    rw [hsnd]; infer_instance
  have hW : IsWeighting (baseChangedChartMap f g q h π comm ≫ pullback.snd f (q ≫ g))
      (w ∘ pullback.fst f (q ≫ g) ∘ baseChangedChartMap f g q h π comm) :=
    H R (q ≫ g) (baseChangedChartMap f g q h π comm) inferInstance hfinR
  rw [hsnd] at hW
  have hlc := hW.isLocallyConstant_of_isFinite inferInstance
  have hfun : w ∘ pullback.fst f (q ≫ g) ∘ baseChangedChartMap f g q h π comm =
      (w ∘ h) ∘ pullback.fst π q := by
    funext z
    simp only [Function.comp_apply]
    rw [← Scheme.Hom.comp_apply, baseChangedChartMap_fst, Scheme.Hom.comp_apply]
  rw [hfun, ← separableDegreeWeightedFiberSum_comp_of_isPullback π (pullback.fst π q)
    (pullback.snd π q) q (IsPullback.of_hasPullback π q) hfin (w ∘ h)] at hlc
  have hvalue : separableDegreeWeightedFiberSum π (w ∘ h)
        (q (genericPoint (Spec (CommRingCat.of R)))) =
      separableDegreeWeightedFiberSum π (w ∘ h) (q (IsLocalRing.closedPoint R)) :=
    hlc.apply_eq_of_preconnectedSpace _ _
  rw [hη, hs] at hvalue
  exact hvalue

end AlgebraicGeometry
