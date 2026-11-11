module

public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.SpaceRelativeWeakAssassinTFAE

/-!
# Associated points of a module on a locally Noetherian algebraic space

On a locally Noetherian algebraic space `X` the source calls a point *associated* to a
quasi-coherent `𝒪_X`-module `F` exactly when it is weakly associated to `F`, sets
`Ass(F) = WeakAss(F)`, and calls a point an *associated point of `X`* exactly when it is a
weakly associated point of `X`. This file completes the formalization of Stacks 0CTX with those
locally Noetherian clauses.

## Main definitions

* `AlgebraicGeometry.Space.associatedPoints` is the set `Ass(F)` of points associated to an
  `𝒪_X`-module `F`.
* `AlgebraicGeometry.Space.associatedPointsOfSpace` is the set of associated points of `X`.

## Main results

* `AlgebraicGeometry.Space.associatedPoints_eq_weaklyAssociatedPoints`: the whole of
  Stacks 0CTX — on a locally Noetherian algebraic space, association of a point to a module is
  weak association, `Ass(F) = WeakAss(F)`, and the associated points of `X` are its weakly
  associated points.

## Implementation notes

The pointwise predicate is `AlgebraicGeometry.Space.IsAssociatedPoint`, which asks that `X` be
locally Noetherian — the property `AlgebraicGeometry.IsLocallyNoetherian` of schemes holding
étale-locally on `X` — and that the point be weakly associated in the sense of
`AlgebraicGeometry.Space.IsWeaklyAssociatedPoint`. Off the locally Noetherian case, where the
source does not define association, the predicate is false. Parts (1), (2) and (3) of the
source are `AlgebraicGeometry.Space.IsWeaklyAssociatedPoint`,
`AlgebraicGeometry.Space.weaklyAssociatedPoints` and
`AlgebraicGeometry.Space.weaklyAssociatedPointsOfSpace`.

## References

* [Stacks Project, Tag 0CTX](https://stacks.math.columbia.edu/tag/0CTX)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : AlgebraicSpaces B S hS)

/-- The set `Ass(F)` of points of an algebraic space `X` associated to an `𝒪_X`-module `F`: the
points weakly associated to `F`, when `X` is locally Noetherian. -/
@[stacks 0CTX "set of associated points on a locally Noetherian space"]
noncomputable abbrev associatedPoints (F : Modules.{u, u} B S hS X.1 X.2) :
    Set (points B S hS X.1) :=
  {x | IsAssociatedPoint B S hS X F x}

/-- The associated points of an algebraic space `X`: the points associated to its structure
sheaf, that is, its weakly associated points when `X` is locally Noetherian. -/
@[stacks 0CTX "associated points of a locally Noetherian space"]
noncomputable abbrev associatedPointsOfSpace : Set (points B S hS X.1) :=
  associatedPoints B S hS X
    (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)))

/-- **Stacks 0CTX**, the locally Noetherian clauses. On a locally Noetherian algebraic space `X`,
a point is associated to an `𝒪_X`-module `F` if and only if it is weakly associated to `F`;
`Ass(F) = WeakAss(F)`; and the associated points of `X` are its weakly associated points. -/
@[stacks 0CTX "associated points on a locally Noetherian space"]
theorem associatedPoints_eq_weaklyAssociatedPoints
    (hX : HasEtaleLocalProperty B S hS X.1
      (fun T : Scheme.{u} ↦ _root_.AlgebraicGeometry.IsLocallyNoetherian T)) :
    (∀ (F : Modules.{u, u} B S hS X.1 X.2) (x : points B S hS X.1),
        IsAssociatedPoint B S hS X F x ↔ IsWeaklyAssociatedPoint B S hS X F x) ∧
      (∀ F : Modules.{u, u} B S hS X.1 X.2,
        associatedPoints B S hS X F = weaklyAssociatedPoints B S hS X F) ∧
      associatedPointsOfSpace B S hS X = weaklyAssociatedPointsOfSpace B S hS X :=
  have h : ∀ (F : Modules.{u, u} B S hS X.1 X.2) (x : points B S hS X.1),
      IsAssociatedPoint B S hS X F x ↔ IsWeaklyAssociatedPoint B S hS X F x :=
    fun _ _ ↦ and_iff_right hX
  ⟨h, fun F ↦ Set.ext (h F), Set.ext (h _)⟩

end AlgebraicGeometry.Space

end
