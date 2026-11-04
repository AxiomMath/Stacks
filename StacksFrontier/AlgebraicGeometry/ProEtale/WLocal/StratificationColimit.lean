module

public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.StratificationTransition
public import Mathlib.Algebra.Colimit.Ring
public import StacksCore.Tactic.StacksAttribute

/-!
# The colimit ring of finite vanishing stratifications

For a commutative ring `A`, the finite subsets of `A`, ordered by inclusion, form a directed
set. The rings attached to their vanishing stratifications and the canonical transition maps
form a directed system of `A`-algebras. Its colimit is the ring `A_w`.

## Main definitions

* `AlgebraicGeometry.ProEtale.stratificationColimitRing` is `A_w`, the directed colimit of the
  rings `A_E`.
* `AlgebraicGeometry.ProEtale.stratificationColimitMap` is the canonical map `A_E → A_w`.
* `AlgebraicGeometry.ProEtale.stratificationColimitAlgebraMap` is the canonical map `A → A_w`.

## Main results

* `AlgebraicGeometry.ProEtale.stratificationColimitMap_comp_algebraMap` says that the maps
  `A → A_E → A_w` agree with the canonical map `A → A_w`.

## Implementation notes

The displayed equality defining `A_w` is represented by a direct-limit type abbreviation. The
transition maps are those of the finite stratifications, and `Ring.DirectLimit` supplies the
colimit construction. The structure map from `A` is obtained at the empty finite subset;
compatibility with the other stages follows from the compatibility of the transition maps with
their `A`-algebra maps.

## References

* [Stacks Project, Tag 0973](https://stacks.math.columbia.edu/tag/0973)
-/

@[expose] public noncomputable section

universe u

namespace AlgebraicGeometry.ProEtale

variable {A : Type u} [CommRing A]

/-- The rings attached to the finite vanishing stratifications of `Spec A` form a directed
system along the transition maps for inclusion. -/
instance stratificationDirectedSystem :
    DirectedSystem (fun E : Finset A => stratificationRing E)
      (fun _ _ h => stratificationRingMap _ _ h) where
  map_self := by intro E x; rw [stratificationRingMap_id]; rfl
  map_map := by
    intro E₃ E₂ E₁ h₁₂ h₂₃ x
    exact congrArg (fun f => f x) (stratificationRingMap_comp E₁ E₂ E₃ h₁₂ h₂₃)

/-- The colimit of the rings attached to all finite vanishing stratifications
of `Spec A`, with the canonical transition maps for inclusion. -/
@[stacks 0973]
abbrev stratificationColimitRing : Type u := Ring.DirectLimit
    (fun E : Finset A => stratificationRing E)
    (fun E₁ E₂ h => stratificationRingMap E₁ E₂ h)

/-- The canonical map from a finite stratification ring to their colimit. -/
def stratificationColimitMap (E : Finset A) :
    stratificationRing E →+* stratificationColimitRing (A := A) :=
  Ring.DirectLimit.of (fun E : Finset A => stratificationRing E)
    (fun E₁ E₂ h => stratificationRingMap E₁ E₂ h) E

/-- The canonical structure map from `A` to its stratification colimit. -/
def stratificationColimitAlgebraMap : A →+* stratificationColimitRing (A := A) :=
  (stratificationColimitMap (A := A) ∅).comp (stratificationAlgebraMap ∅)

/-- The stratification colimit is an `A`-algebra via its canonical structure map. -/
noncomputable instance : Algebra A (stratificationColimitRing (A := A)) :=
  stratificationColimitAlgebraMap.toAlgebra

/-- The structure map from `A` agrees with the map through any finite stage. -/
@[stacks 0973 "compatibility with the finite stages"]
theorem stratificationColimitMap_comp_algebraMap (E : Finset A) :
    (stratificationColimitMap (A := A) E).comp (stratificationAlgebraMap E) =
      stratificationColimitAlgebraMap (A := A) := by
  rw [← stratificationRingMap_comp_algebraMap ∅ E (Finset.empty_subset E)]
  rw [← RingHom.comp_assoc]
  congr 1; ext x; simp [stratificationColimitMap, Ring.DirectLimit.of_f]

end AlgebraicGeometry.ProEtale

end
