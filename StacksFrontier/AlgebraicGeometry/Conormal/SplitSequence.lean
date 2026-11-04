module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import StacksFrontier.AlgebraicGeometry.Conormal.ConormalSequence

/-!
# Immersions with an exact and locally split conormal sequence

For immersions `i : Z ⟶ Y` and `j : Y ⟶ X` the conormal sequence of [Stacks Project, Tag 062S]
is `i^* 𝒞_{Y/X} ⟶ 𝒞_{Z/X} ⟶ 𝒞_{Z/Y} ⟶ 0`.  This file constructs its left-hand map and records
what it means for the sequence to be exact and locally split.

## Main definitions

* `Stacks.AlgebraicGeometry.conormalSequenceLeftMap`: the left-hand map `i^* 𝒞_{Y/X} ⟶ 𝒞_{Z/X}`,
  the canonical map of [Stacks Project, Tag 01R4] for the square with horizontal maps `i ≫ j`
  and `j`, vertical maps `i` and `𝟙 X`.
* `Stacks.AlgebraicGeometry.IsSplitExactConormalSequence`: the conormal sequence is a short exact
  sequence and its left-hand map admits a retraction on a neighbourhood of every point.

## References

* [Stacks Project, Tag 062S](https://stacks.math.columbia.edu/tag/062S)
* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.AlgebraicGeometry

variable {Z Y X : Scheme.{u}}

/-- **The left-hand map `i^* 𝒞_{Y/X} ⟶ 𝒞_{Z/X}` of the conormal sequence of
[Stacks Project, Tag 062S].** It is the canonical map of [Stacks Project, Tag 01R4] attached to
the square with horizontal maps `i ≫ j` and `j` and vertical maps `i` and `𝟙 X`. -/
@[stacks 062S "the first arrow i^* 𝒞_{Y/X} ⟶ 𝒞_{Z/X}"]
def conormalSequenceLeftMap (i : Z ⟶ Y) (j : Y ⟶ X) [IsImmersion i] [IsImmersion j] :
    (modulePullback i.toLRSHom.toShHom).obj
        (Stacks.ClosedImmersion.conormalSheaf j.liftCoborder.toLRSHom.toShHom) ⟶
      Stacks.ClosedImmersion.conormalSheaf (i ≫ j).liftCoborder.toLRSHom.toShHom :=
  Stacks.Immersion.immersionConormalSheafMap (i ≫ j) j i (𝟙 X)
    (Stacks.Immersion.toShHom_square (by simp))

/-- **The conormal sequence of a pair of immersions is exact and locally split.**

The two maps are those of [Stacks Project, Tag 062S]: the composite vanishes, the resulting short
complex `0 ⟶ i^* 𝒞_{Y/X} ⟶ 𝒞_{Z/X} ⟶ 𝒞_{Z/Y} ⟶ 0` is short exact, and every point of `Z` has a
neighbourhood on which the left-hand map admits a retraction, which for a short exact sequence is
the same as a splitting. -/
structure IsSplitExactConormalSequence (i : Z ⟶ Y) (j : Y ⟶ X)
    [IsImmersion i] [IsImmersion j] : Prop where
  /-- The composite of the two maps of the conormal sequence vanishes. -/
  comp_eq_zero :
    conormalSequenceLeftMap i j ≫ Stacks.Immersion.conormalSequenceRightMap i j = 0
  /-- The conormal sequence is a short exact sequence. -/
  shortExact : (ShortComplex.mk _ _ comp_eq_zero).ShortExact
  /-- On a neighbourhood of every point the left-hand map admits a retraction. -/
  locallySplit : ∀ z : Z, ∃ V : Z.Opens, z ∈ V ∧
    ∃ r : (Scheme.Modules.restrictFunctor V.ι).obj
        (Stacks.ClosedImmersion.conormalSheaf (i ≫ j).liftCoborder.toLRSHom.toShHom) ⟶
      (Scheme.Modules.restrictFunctor V.ι).obj
        ((modulePullback i.toLRSHom.toShHom).obj
          (Stacks.ClosedImmersion.conormalSheaf j.liftCoborder.toLRSHom.toShHom)),
      (Scheme.Modules.restrictFunctor V.ι).map (conormalSequenceLeftMap i j) ≫ r = 𝟙 _

end Stacks.AlgebraicGeometry

end
