module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.UniversallyBounded

/-!
# Bounds on fibre degrees and base change

An arbitrary base change of a morphism of schemes preserves every bound on the degrees of its
fibres.  In particular a morphism with universally bounded fibres stays universally bounded
after base change.  Conversely the base changes to spectra of fields already detect such a bound,
and a finite locally free morphism of a given degree has that degree as a bound.

## Main results

* `AlgebraicGeometry.boundsFiberDegrees_isStableUnderBaseChange`: for each integer `n`, having
  all fibre degrees bounded by `n` is stable under arbitrary base change.
* `AlgebraicGeometry.boundsFiberDegrees_of_isPullback` and
  `AlgebraicGeometry.hasUniversallyBoundedFibers_of_isPullback`: that stability read off a
  cartesian square, for a fixed bound and for the existence of a bound.
* `AlgebraicGeometry.boundsFiberDegrees_iff_field_baseChange`: an integer bounds the degrees of
  the fibres exactly when every base change to the spectrum of a field is finite locally free of
  a rank bounded by that integer.
* `AlgebraicGeometry.boundsFiberDegrees_of_isFiniteLocallyFreeOfRank`: the degree of a finite
  locally free morphism bounds the degrees of its fibres.

## Implementation notes

The stability statement is the stability under base change of the morphism property with a *fixed*
bound `n`, so the same integer, and not merely some new integer, bounds the fibres after base
change; being categorical it applies to every pullback square and is independent of a chosen
pullback object.

The characterisation by field-valued base changes omits the nonnegativity condition on the integer
in the Stacks statement, since the condition on each fibre already produces a nonnegative rank
bounded by it.

## References

* [Stacks Project, Tag 03J5](https://stacks.math.columbia.edu/tag/03J5)
* [Stacks Project, Tag 03J7](https://stacks.math.columbia.edu/tag/03J7)
* [Stacks Project, Tag 0CC2](https://stacks.math.columbia.edu/tag/0CC2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Every integer bound on the degrees of the fibres of a morphism
of schemes is preserved by arbitrary base change. -/
@[stacks 03J7]
instance boundsFiberDegrees_isStableUnderBaseChange (n : ℤ) :
    MorphismProperty.IsStableUnderBaseChange
      (fun {X Y : Scheme.{u}} (f : X ⟶ Y) ↦ BoundsFiberDegrees f n) := by
  constructor
  intro X Y Y' S f g f' g' sq hg y
  obtain ⟨r, hr, hrank⟩ := hg (f y)
  exact ⟨r, hr, MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} r)
    (isPullback_fiberToSpecResidueField_of_isPullback sq y) hrank⟩

/-- Around a cartesian square: if `n` bounds the degrees of the fibres of `g`, it
also bounds the degrees of the fibres of its base change `g'`. -/
theorem boundsFiberDegrees_of_isPullback {X Y Y' S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    {f' : Y' ⟶ Y} {g' : Y' ⟶ X} (sq : IsPullback f' g' g f) {n : ℤ}
    (hg : BoundsFiberDegrees g n) : BoundsFiberDegrees g' n :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := fun {X Y : Scheme.{u}} (f : X ⟶ Y) ↦ BoundsFiberDegrees f n) sq hg

/-- A base change of a morphism with universally bounded fibres has universally
bounded fibres. -/
theorem hasUniversallyBoundedFibers_of_isPullback {X Y Y' S : Scheme.{u}} {f : X ⟶ S}
    {g : Y ⟶ S} {f' : Y' ⟶ Y} {g' : Y' ⟶ X} (sq : IsPullback f' g' g f)
    (hg : HasUniversallyBoundedFibers g) : HasUniversallyBoundedFibers g' :=
  ⟨hg.choose, boundsFiberDegrees_of_isPullback sq hg.choose_spec⟩

/-- Over the spectrum of a field, the canonical morphism from the spectrum of the residue field at
the closed point is an isomorphism. -/
lemma isIso_fromSpecResidueField_closedPoint (k : Type u) [Field k] :
    IsIso ((Spec (.of k)).fromSpecResidueField (IsLocalRing.closedPoint k : Spec (.of k))) := by
  let p : Spec (.of k) := IsLocalRing.closedPoint k
  have : IsIso (CommRingCat.ofHom (algebraMap k p.asIdeal.ResidueField)) :=
    p.asIdeal.algEquivResidueFieldOfField.toRingEquiv.toCommRingCatIso.isIso_hom
  show IsIso ((Spec (.of k)).fromSpecResidueField p)
  rw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField]
  infer_instance

/-- An integer bounds the degrees of the fibres of a morphism of schemes exactly when each of its
base changes to the spectrum of a field is finite locally free of a rank bounded by that
integer. -/
@[stacks 03J5 "bounded_degree_iff_field_base_changes"]
theorem boundsFiberDegrees_iff_field_baseChange {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℤ) :
    BoundsFiberDegrees f n ↔
      ∀ (k : Type u) [Field k] (g : Spec (.of k) ⟶ Y),
        ∃ r : ℕ, (r : ℤ) ≤ n ∧
          Stacks.Morphisms.IsFiniteLocallyFreeOfRank (pullback.fst g f) r := by
  constructor
  · intro h k _ g
    obtain ⟨r, hr, hrank⟩ := boundsFiberDegrees_of_isPullback (IsPullback.of_hasPullback g f).flip
      h (IsLocalRing.closedPoint k)
    refine ⟨r, hr, ?_⟩
    have := isIso_fromSpecResidueField_closedPoint k
    have hι : IsIso ((pullback.fst g f).fiberι (IsLocalRing.closedPoint k)) :=
      (IsPullback.of_hasPullback (pullback.fst g f) ((Spec (.of k)).fromSpecResidueField
        (IsLocalRing.closedPoint k : Spec (.of k)))).isIso_fst_of_isIso
    have h1 : Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} r
        ((pullback.fst g f).fiberToSpecResidueField (IsLocalRing.closedPoint k) ≫
          (Spec (.of k)).fromSpecResidueField (IsLocalRing.closedPoint k)) :=
      MorphismProperty.RespectsIso.postcomp _ _ _ hrank
    rw [← Scheme.Hom.fiber_fac (pullback.fst g f) (IsLocalRing.closedPoint k)] at h1
    exact (MorphismProperty.cancel_left_of_respectsIso _
      ((pullback.fst g f).fiberι (IsLocalRing.closedPoint k)) (pullback.fst g f)).mp h1
  · intro h y
    obtain ⟨r, hr, hrank⟩ := h (Y.residueField y) (Y.fromSpecResidueField y)
    refine ⟨r, hr, ?_⟩
    have h1 : Stacks.Morphisms.IsFiniteLocallyFreeOfRank.property.{u} r
        ((pullbackSymmetry f (Y.fromSpecResidueField y)).hom ≫
          pullback.fst (Y.fromSpecResidueField y) f) :=
      MorphismProperty.RespectsIso.precomp _ _ _ hrank
    rwa [pullbackSymmetry_hom_comp_fst] at h1

/-- The degree of a finite locally free morphism bounds the degrees of all of its fibres. -/
@[stacks 0CC2]
theorem boundsFiberDegrees_of_isFiniteLocallyFreeOfRank {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ)
    [Stacks.Morphisms.IsFiniteLocallyFreeOfRank f d] : BoundsFiberDegrees f (d : ℤ) := fun y ↦
  ⟨d, le_rfl, Stacks.Morphisms.IsFiniteLocallyFreeOfRank.of_isPullback
    (IsPullback.of_hasPullback f (Y.fromSpecResidueField y))⟩

end AlgebraicGeometry

end
