module

public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.LocalRing
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.LocalCompleteIntersection
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Properties
public import StacksFrontier.AlgebraicGeometry.Properties.CohenMacaulayCharacterization
public import StacksFrontier.RingTheory.CompleteIntersection.Local
public import StacksCore.Tactic.StacksAttribute

/-!
# Syntomic morphisms are Cohen–Macaulay

A scheme syntomic over a field is Cohen–Macaulay, because its local rings are complete
intersections over that field and a complete intersection is Cohen–Macaulay. Base changing to the
residue field of a point of the target, it follows that the fibres of a syntomic morphism are
Cohen–Macaulay schemes, and hence that a syntomic morphism is a Cohen–Macaulay morphism.

## Main results

* `AlgebraicGeometry.isCohenMacaulay_of_syntomic_over_field`: a scheme syntomic over a field is
  Cohen–Macaulay.
* `AlgebraicGeometry.isCohenMacaulay_fiber_of_syntomic`: the fibres of a syntomic morphism are
  Cohen–Macaulay.
* `AlgebraicGeometry.isCohenMacaulay_of_syntomic`: a syntomic morphism is a Cohen–Macaulay
  morphism.

## Implementation notes

Over a field, being syntomic is exactly being a local complete intersection, so the local rings
are complete intersections over the field by Tag 01UG, and Tag 00SB turns each of them into a
Cohen–Macaulay local ring. Cohen–Macaulayness of the scheme is then the stalkwise
characterization `AlgebraicGeometry.isCohenMacaulay_tfae_stalk`, whose locally Noetherian half
holds because a scheme locally of finite type over a field is locally Noetherian.

The fibre of `f : X ⟶ Y` at `y` is the base change of `f` along
`AlgebraicGeometry.Scheme.fromSpecResidueField`, and
`AlgebraicGeometry.Scheme.Hom.fiberToSpecResidueField` is the second projection of that pullback,
so it is syntomic whenever `f` is. The residue field `Y.residueField y` is a `CommRingCat` whose
carrier is a field, and `CommRingCat.of ↥(Y.residueField y)` is the object itself, so the fibre is
a scheme over the spectrum of a field with no further comparison.

Cohen–Macaulayness of a morphism takes a witness of locally Noetherian fibres as an explicit
argument, so the last result is stated for an arbitrary such witness; one always exists by
`AlgebraicGeometry.isLocallyNoetherian_fiber`.

## References

* [Stacks Project, Tag 01UG](https://stacks.math.columbia.edu/tag/01UG)
* [Stacks Project, Tag 00SB](https://stacks.math.columbia.edu/tag/00SB)
* [Stacks Project, Tag 045R](https://stacks.math.columbia.edu/tag/045R)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A scheme syntomic over a field is Cohen–Macaulay. -/
public theorem isCohenMacaulay_of_syntomic_over_field {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (hf : Syntomic f) : IsCohenMacaulay X := by
  have _ : LocallyOfFinitePresentation f := locallyOfFinitePresentation hf
  have _ : LocallyOfFiniteType f := inferInstance
  have _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  refine ((isCohenMacaulay_tfae_stalk X).out 2 1 rfl rfl).mp ⟨inferInstance, fun x => ?_⟩
  have hci := ((localCompleteIntersection_tfae k X f).out 1 3 rfl rfl).mp hf x
  refine ⟨inferInstance, ?_⟩
  let _ : Algebra k (X.presheaf.stalk x) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
      X.presheaf.germ ⊤ x (by simp)).hom.toAlgebra
  exact (isCohenMacaulayLocalRing_iff_isMaximalCohenMacaulay (X.presheaf.stalk x)).mpr
    (IsCompleteIntersection.isMaximalCohenMacaulay hci)

/-- The fibres of a syntomic morphism of schemes are Cohen–Macaulay. -/
public theorem isCohenMacaulay_fiber_of_syntomic {X Y : Scheme.{u}} {f : X ⟶ Y}
    (hf : Syntomic f) (y : Y) : IsCohenMacaulay (f.fiber y) := by
  have hsyn : Syntomic (f.fiberToSpecResidueField y) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := (@Syntomic : MorphismProperty Scheme.{u}))
      (IsPullback.of_hasPullback f (Y.fromSpecResidueField y)) hf
  exact isCohenMacaulay_of_syntomic_over_field (k := ↥(Y.residueField y))
    (f.fiberToSpecResidueField y) hsyn

/-- **Stacks Project, Tag 045R.** A syntomic morphism of schemes is a Cohen–Macaulay morphism. -/
public theorem isCohenMacaulay_of_syntomic {X Y : Scheme.{u}} {f : X ⟶ Y} (hf : Syntomic f)
    (hfib : ∀ y : Y, IsLocallyNoetherian (f.fiber y)) : f.IsCohenMacaulay hfib := by
  intro x
  have _ : IsLocallyNoetherian (f.fiber (f x)) := hfib (f x)
  have _ : Flat f := flat hf
  refine ⟨?_, ?_⟩
  · change (f.stalkMap x).hom.Flat
    exact Flat.stalkMap f x
  · obtain ⟨-, hstalk⟩ :=
      ((isCohenMacaulay_tfae_stalk (f.fiber (f x))).out 1 2 rfl rfl).mp
        (isCohenMacaulay_fiber_of_syntomic hf (f x))
    obtain ⟨_, hCM⟩ := hstalk (f.asFiber x)
    exact hCM

end AlgebraicGeometry
