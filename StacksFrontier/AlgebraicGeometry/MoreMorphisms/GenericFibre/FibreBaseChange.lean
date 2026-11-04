module

public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.IrreducibleBaseChange

/-!
# Geometric irreducibility of a fibre is unchanged by a base change of the target

Let `f : X ⟶ Y` be a morphism of schemes, let `a : Y' ⟶ Y` and let `y' : Y'`. The fibre of the
base change `pullback.fst a f : Y' ×_Y X ⟶ Y'` at `y'` is the base change of the fibre of `f` at
`a y'` along the residue field extension `κ(a y') ⟶ κ(y')`. Geometric irreducibility over a
field is insensitive to a field extension by Stacks Tag 054P, so the fibre of the base change is
geometrically irreducible if and only if the fibre of `f` is.

The forward implication is the stability of `AlgebraicGeometry.GeometricallyIrreducible` under
base change; the reverse one is Tag 054P, applied to the algebra structure that the residue
field map carries.

## Main results

* `AlgebraicGeometry.geometricallyIrreducible_fiber_pullbackFst_iff`

## References

* [Stacks Project, Tag 054P](https://stacks.math.columbia.edu/tag/054P)
* [Stacks Project, Tag 0559](https://stacks.math.columbia.edu/tag/0559)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A morphism which is presented as the base change of a geometrically irreducible morphism by
a pullback square is geometrically irreducible, in the chosen pullback. -/
private theorem geometricallyIrreducible_pullbackSnd_of_isPullback
    {P A B C : Scheme.{u}} {m : P ⟶ A} {n : P ⟶ B} {p : A ⟶ C} {q : B ⟶ C}
    (hsq : IsPullback m n p q) (h : GeometricallyIrreducible n) :
    GeometricallyIrreducible (pullback.snd p q) := by
  have : MorphismProperty.RespectsIso @GeometricallyIrreducible.{u} :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have key := MorphismProperty.cancel_left_of_respectsIso (P := @GeometricallyIrreducible)
    hsq.isoPullback.hom (pullback.snd p q)
  rw [hsq.isoPullback_hom_snd] at key
  exact key.mp h

/-- The fibre of the base change of `f` along `a` at `y'` is the base change of the fibre of `f`
at `a y'` along the residue field extension at `y'`. -/
theorem isPullback_fiberToSpecResidueField_pullbackFst {X Y Y' : Scheme.{u}} (f : X ⟶ Y)
    (a : Y' ⟶ Y) (y' : Y') :
    IsPullback
      (pullback.map _ _ _ _ (pullback.snd a f) (Spec.map (a.residueFieldMap y')) a
        (IsPullback.of_hasPullback a f).flip.w.symm (by simp))
      ((pullback.fst a f).fiberToSpecResidueField y')
      (f.fiberToSpecResidueField (a y'))
      (Spec.map (a.residueFieldMap y')) :=
  isPullback_fiberToSpecResidueField_of_isPullback (IsPullback.of_hasPullback a f).flip y'

/-- Geometric irreducibility of the fibre at `y'` of a base change of `f` along `a` is
equivalent to geometric irreducibility of the fibre of `f` at the image point. -/
theorem geometricallyIrreducible_fiber_pullbackFst_iff {X Y Y' : Scheme.{u}} (f : X ⟶ Y)
    (a : Y' ⟶ Y) (y' : Y') {y : Y} (hy : a y' = y) :
    GeometricallyIrreducible ((pullback.fst a f).fiberToSpecResidueField y') ↔
      GeometricallyIrreducible (f.fiberToSpecResidueField y) := by
  subst hy
  have hsq := isPullback_fiberToSpecResidueField_pullbackFst f a y'
  refine ⟨fun h ↦ ?_, fun h ↦ MorphismProperty.of_isPullback hsq h⟩
  let : Algebra ↥(Y.residueField (a y')) ↥(Y'.residueField y') :=
    (a.residueFieldMap y').hom.toAlgebra
  exact (geometricallyIrreducible_iff_baseChange_fieldExtension
    ↥(Y.residueField (a y')) ↥(Y'.residueField y')
    (f.fiberToSpecResidueField (a y'))).mpr
    (geometricallyIrreducible_pullbackSnd_of_isPullback hsq h)

end AlgebraicGeometry

end
