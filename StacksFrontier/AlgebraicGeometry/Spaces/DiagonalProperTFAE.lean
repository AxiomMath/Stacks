module

public import Mathlib.Tactic.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.DiagonalProper
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDiagonalProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedRepresentable

/-!
# Separatedness and properness of the relative diagonal

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. The following are equivalent: `f` is separated; the relative
diagonal `Δ_f : X ⟶ X ×_Y X` is universally closed; the relative diagonal is proper.

## Main results

* `AlgebraicGeometry.Space.isSeparated_tfae_diagonal`: for a morphism `f` of algebraic spaces,
  separatedness of `f`, universal closedness of `Δ_f` and properness of `Δ_f` are equivalent.

## Implementation notes

The name carries the qualifier `diagonal` because `AlgebraicGeometry.Space.isSeparated_tfae` is a
different equivalence, the local criteria for separatedness of [Stacks, Tag 03KM].

## References

* [Stacks Project, Tag 04Y0](https://stacks.math.columbia.edu/tag/04Y0)
* [Stacks Project, Tag 04XZ](https://stacks.math.columbia.edu/tag/04XZ)
* [Stacks Project, Tag 04XV](https://stacks.math.columbia.edu/tag/04XV)
* [Stacks Project, Tag 03HK](https://stacks.math.columbia.edu/tag/03HK)
* [Stacks Project, Tag 03XD](https://stacks.math.columbia.edu/tag/03XD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- For a morphism of algebraic spaces over `S` the following are equivalent: it is separated;
its relative diagonal is universally closed; its relative diagonal is proper. -/
@[stacks 04Y0]
theorem isSeparated_tfae_diagonal (f : X ⟶ Y) (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) :
    List.TFAE [IsSeparated B S hS f,
      UniversallyClosed B S hS (pullback.diagonal f),
      IsProper B S hS (pullback.diagonal f)] := by
  tfae_have 1 → 3 := isProper_diagonal_of_isSeparated B S hS hX hY f
  tfae_have 3 → 2 := fun h => h.2.2
  tfae_have 2 → 1 := fun h =>
    isSeparated_of_diagonal_charts B S hS f
      (presheaf_locallyOfFiniteType_pullbackDiagonal B S hS f hX)
      (presheaf_universallyClosed_of_universallyClosed B S hS
        (relativelyRepresentable_pullbackDiagonal B S hS f hX) h)
  tfae_finish

end AlgebraicGeometry.Space

end
