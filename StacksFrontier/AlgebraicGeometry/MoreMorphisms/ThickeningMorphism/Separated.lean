module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.Diagonal
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.Topological

/-!
# Separatedness and quasi-separatedness across a morphism of thickenings

For a morphism of thickenings — a commutative square whose horizontal arrows are thickenings —
the morphism of closed subschemes is separated, respectively quasi-separated, exactly when the
morphism of ambient schemes is.

Both statements are the corresponding statement for the relative diagonals. The two diagonals
themselves form a morphism of thickenings, over the map
`Stacks.Thickenings.diagonalTargetMap` on their targets, so separatedness reduces to universal
closedness and quasi-separatedness to quasi-compactness, each for that new morphism of
thickenings.

## Main results

* `Stacks.Thickenings.isSeparated_left_iff_right`
* `Stacks.Thickenings.quasiSeparated_left_iff_right`

## Implementation notes

Separatedness of a morphism of schemes is a closed-immersion condition on its relative
diagonal, while the statement available for a morphism of thickenings is about universal
closedness; the two agree for the diagonal because it is always an immersion, which is the
content of the private lemma used here.

## References

* [Stacks Project, Tag 09ZV](https://stacks.math.columbia.edu/tag/09ZV)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Stacks.Thickenings

universe u

/-- An immersion is a closed immersion exactly when it is universally closed. -/
private theorem isClosedImmersion_iff_universallyClosed_of_isImmersion
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsImmersion f] :
    IsClosedImmersion f ↔ UniversallyClosed f := by
  constructor <;> intro h <;> have _ := h
  · infer_instance
  · exact IsClosedImmersion.of_isPreimmersion f f.isClosedMap.isClosed_range

/-- The relative diagonals of a morphism of thickenings form a morphism of thickenings. -/
private noncomputable def diagonalHom {X S : Arrow (Scheme.{u})} (φ : X ⟶ S) :
    Arrow.mk X.hom ⟶ Arrow.mk (diagonalTargetMap X.hom φ.left φ.right S.hom (Arrow.w φ).symm) :=
  Arrow.homMk (pullback.diagonal φ.left) (pullback.diagonal φ.right)
    (diagonal_comp_diagonalTargetMap X.hom φ.left φ.right S.hom (Arrow.w φ).symm)

/-- Separatedness is invariant under a morphism of thickenings. -/
@[stacks 09ZV "separated"]
theorem isSeparated_left_iff_right
    {X X' S S' : Scheme.{u}} {i : X ⟶ X'} {j : S ⟶ S'}
    (hi : IsThickening i) (hj : IsThickening j)
    (φ : Arrow.mk i ⟶ Arrow.mk j) :
    IsSeparated φ.left ↔ IsSeparated φ.right := by
  simpa only [isSeparated_iff, isClosedImmersion_iff_universallyClosed_of_isImmersion,
    diagonalHom, Arrow.homMk_left, Arrow.homMk_right]
    using universallyClosed_left_iff_right (diagonalHom φ) hi
      (isThickening_diagonalTargetMap i φ.left φ.right j φ.w.symm hi hj)

/-- Quasi-separatedness of a morphism of schemes is unchanged by passing between the closed
subschemes and the ambient schemes of a morphism of thickenings. -/
@[stacks 09ZV "quasi_separated"]
theorem quasiSeparated_left_iff_right {X S : Arrow (Scheme.{u})}
    (φ : X ⟶ S) (hX : IsThickening X.hom)
    (hS : IsThickening S.hom) :
    QuasiSeparated φ.left ↔ QuasiSeparated φ.right := by
  rw [quasiSeparated_iff, quasiSeparated_iff]
  exact quasiCompact_left_iff_right (diagonalHom φ) hX
    (isThickening_diagonalTargetMap X.hom φ.left φ.right S.hom (Arrow.w φ).symm hX hS)

end Stacks.Thickenings

end
