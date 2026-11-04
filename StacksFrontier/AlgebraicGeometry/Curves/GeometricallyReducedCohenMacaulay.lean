module

public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Properties.CohenMacaulayCharacterization

/-!
# Geometrically reduced curves are Cohen–Macaulay

A reduced locally Noetherian scheme of dimension at most one is Cohen–Macaulay: reducedness is
Serre's condition `(S₁)` together with `(R₀)`, and in dimension at most one `(S₁)` already gives
the equality of depth and dimension at every local ring.

Applied to a curve — a scheme of dimension at most one which is proper over a field — this says
that a geometrically reduced curve is Cohen–Macaulay, and applied to the fibres of a family of
curves it says that a fibre which is geometrically reduced is Cohen–Macaulay. These are the two
readings of the inclusion `Curves^{geomred} ⊂ Curves^{CM}` of open substacks of the stack of
curves: the first on the curves parametrized by a field-valued point, the second on the fibres
of an arbitrary family.

## Main results

* `AlgebraicGeometry.isCohenMacaulay_of_isReduced_of_topologicalKrullDim_le_one`: a reduced
  locally Noetherian scheme of dimension at most one is Cohen–Macaulay.
* `AlgebraicGeometry.isCohenMacaulay_of_geometricallyReduced_of_topologicalKrullDim_le_one`: a
  geometrically reduced scheme of dimension at most one over a field is Cohen–Macaulay.
* `AlgebraicGeometry.isCohenMacaulay_fiber_of_geometricallyReduced_of_topologicalKrullDim_le_one`:
  a fibre of dimension at most one of a morphism with geometrically reduced fibres is
  Cohen–Macaulay.

## Implementation notes

The dimension hypothesis is `TopologicalSpace.topologicalKrullDim`, which bounds the Krull
dimension of every local ring; this is the same shape as the dimension hypothesis of Tag 0B3D,
the normal analogue in dimension at most two.

Geometric reducedness is `AlgebraicGeometry.GeometricallyReduced`, reducedness of every
field-valued base change. Over a field it yields reducedness of the scheme itself by taking the
base change along the identity, so no flatness hypothesis is needed; for a fibre it yields
reducedness of that fibre.

## References

* [Stacks Project, Tag 0E1G](https://stacks.math.columbia.edu/tag/0E1G)
* [Stacks Project, Tag 031R](https://stacks.math.columbia.edu/tag/031R)
* [Stacks Project, Tag 0344](https://stacks.math.columbia.edu/tag/0344)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A reduced locally Noetherian scheme of dimension at most one is Cohen–Macaulay. Reducedness
gives Serre's condition `(S₁)`, which in dimension at most one forces the depth of every local
ring to equal its dimension. -/
@[ega "IV 5.7.8" "more general", ega "IV 6.11.9" "partial"]
theorem isCohenMacaulay_of_isReduced_of_topologicalKrullDim_le_one (X : Scheme.{u})
    [IsLocallyNoetherian X] [IsReduced X] (hX : topologicalKrullDim X ≤ 1) :
    IsCohenMacaulay X := by
  rw [topologicalKrullDim_eq_iSup_krullDimOfRing_stalk] at hX
  refine (isCohenMacaulay_iff_forall_hasPropertySk X).2 fun k =>
    (hasPropertySk_iff X k).mpr fun x => ?_
  have hdim : ringKrullDim (X.presheaf.stalk x) ≤ (1 : WithBot ℕ∞) :=
    (le_iSup (fun y : X => ringKrullDim (X.presheaf.stalk y)) x).trans hX
  have hS₁ := (hasPropertySk_iff X 1).mp
    ((isReduced_iff_hasPropertyS1_and_isRegularInCodimension_zero X).mp inferInstance).1 x
  rw [Nat.cast_one, min_eq_right hdim] at hS₁
  exact (min_le_right _ _).trans hS₁

/-- A scheme which is geometrically reduced over a field is reduced: it is its own base change
along the identity of the base. -/
@[ega "IV 4.6.1" "(b) ⇒ (e)", ega "IV 7.3.9" "more general"]
theorem isReduced_of_geometricallyReduced {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [GeometricallyReduced f] : IsReduced X :=
  GeometricallyReduced.geometrically_isReduced (𝟙 (Spec (.of k))) (𝟙 X) f (.id_horiz f)

/-- **A geometrically reduced curve is Cohen–Macaulay.** A scheme of dimension at most one which
is locally of finite type and geometrically reduced over a field is Cohen–Macaulay. -/
@[stacks 0E1G "the inclusion read on a curve over a field, the curves being the objects of the \
  stack parametrized by a field-valued point", ega "IV 5.7.8" "special case"]
theorem isCohenMacaulay_of_geometricallyReduced_of_topologicalKrullDim_le_one {k : Type u}
    [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [GeometricallyReduced f]
    [LocallyOfFiniteType f] (hX : topologicalKrullDim X ≤ 1) :
    IsCohenMacaulay X :=
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsReduced X := isReduced_of_geometricallyReduced f
  isCohenMacaulay_of_isReduced_of_topologicalKrullDim_le_one X hX

/-- **A geometrically reduced fibre of dimension at most one is Cohen–Macaulay.** For a morphism
of schemes which is locally of finite type with geometrically reduced fibres, every fibre of
dimension at most one is Cohen–Macaulay. -/
@[stacks 0E1G "the inclusion read fibrewise on a family of curves", ega "IV 5.7.8" "special case"]
theorem isCohenMacaulay_fiber_of_geometricallyReduced_of_topologicalKrullDim_le_one
    {X S : Scheme.{u}} (f : X ⟶ S) [GeometricallyReduced f] [LocallyOfFiniteType f] (s : S)
    (hX : topologicalKrullDim (f.fiber s) ≤ 1) :
    IsCohenMacaulay (f.fiber s) := by
  have : IsLocallyNoetherian (f.fiber s) :=
    inferInstanceAs (IsLocallyNoetherian (Limits.pullback f (S.fromSpecResidueField s)))
  exact isCohenMacaulay_of_isReduced_of_topologicalKrullDim_le_one (f.fiber s) hX

end AlgebraicGeometry

end
