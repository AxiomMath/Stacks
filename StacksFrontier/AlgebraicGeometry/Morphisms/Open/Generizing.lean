module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Spectrum.Prime.Specialization
public import StacksFrontier.Topology.Specialization.Lifting

/-!
# Open morphisms are generizing

An open morphism of schemes lifts generalizations of points: if a point of the target
generalizes the image of a point of the source, that generalization is itself the image of a
generalization. Affine-locally this is the going-down property for the corresponding ring map,
which openness of the map on spectra supplies. Consequently a universally open morphism lifts
generalizations after every base change.

## Main results

* `AlgebraicGeometry.liftsGeneralizations_of_isOpenMap`: an open morphism of schemes lifts
  generalizations.
* `AlgebraicGeometry.universally_liftsGeneralizations_of_universallyOpen`: a universally open
  morphism lifts generalizations after every base change.

## Implementation notes

The generizing condition is expressed by `LiftsGeneralizations`. Its universal version is the
universal closure of the corresponding topological morphism property, matching Mathlib's
formulation of `UniversallyOpen`. The proof of the first result reduces to the affine case twice,
once at the target and once at the source, since both `topologically GeneralizingMap` and
`topologically IsOpenMap` are Zariski-local on each side.

## References

* [EGA IV, Corollary 1.10.4]
* [Stacks Project, Tag 040F](https://stacks.math.columbia.edu/tag/040F)
-/

@[expose] public section

open CategoryTheory CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry

/-- An open morphism of schemes lifts generalizations of points. -/
@[stacks 040F "open morphisms", ega "IV 1.10.3" "a) ⇒ b)", ega "IV 2.3.5" "partial"]
public lemma liftsGeneralizations_of_isOpenMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : IsOpenMap f) : LiftsGeneralizations f := by
  rw [liftsGeneralizations_iff_generalizingMap]
  wlog hY : ∃ R, Y = Spec R
  · show (topologically GeneralizingMap) f
    rw [IsZariskiLocalAtTarget.iff_of_openCover (P := topologically GeneralizingMap)
      Y.affineCover]
    intro i
    dsimp only [Scheme.Cover.pullbackHom]
    exact this _ (IsZariskiLocalAtTarget.of_isPullback (P := topologically IsOpenMap)
      (iY := Y.affineCover.f i) (IsPullback.of_hasPullback ..) hf) ⟨_, rfl⟩
  obtain ⟨R, rfl⟩ := hY
  wlog hX : ∃ S, X = Spec S
  · show (topologically GeneralizingMap) f
    rw [IsZariskiLocalAtSource.iff_of_openCover (P := topologically GeneralizingMap)
      X.affineCover]
    intro i
    refine this R (X.affineCover.f i ≫ f) ?_ ⟨_, rfl⟩
    exact IsZariskiLocalAtSource.comp (P := topologically IsOpenMap) hf _
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  have hgd : φ.hom.SatisfiesGoingDown := isOpenMap_comap_satisfiesGoingDown φ.hom hf
  intro x y hyx
  obtain ⟨q, hqle, hover⟩ := hgd y (PrimeSpectrum.comap φ.hom x)
    ((PrimeSpectrum.le_iff_specializes _ _).mpr hyx) x rfl
  exact ⟨q, (PrimeSpectrum.le_iff_specializes _ _).mp hqle, hover⟩

/-- A universally open morphism of schemes lifts generalizations after every base change. -/
@[stacks 040F "universally open morphisms", ega "IV 2.3.5" "special case"]
public lemma universally_liftsGeneralizations_of_universallyOpen {X Y : Scheme.{u}} (f : X ⟶ Y)
    [UniversallyOpen f] : universally (topologically @LiftsGeneralizations) f := by
  intro X' Y' i₁ i₂ f' hpb
  exact liftsGeneralizations_of_isOpenMap f'
    (UniversallyOpen.universally_isOpenMap (f := f) i₁ i₂ f' hpb)

end AlgebraicGeometry
