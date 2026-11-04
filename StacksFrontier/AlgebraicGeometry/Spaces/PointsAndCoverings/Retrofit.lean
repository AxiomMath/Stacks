module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnSource.Defs
public import StacksFrontier.AlgebraicGeometry.Spaces.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.RelativeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Diagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Sheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentableAtlasTest

/-!
# Algebraic spaces relative to an algebraic space

This module has no declarations of its own. It imports the statements that let the definition of an
algebraic space be used relative to a given algebraic space instead of the base scheme: the source
of a representable morphism to an algebraic space is an algebraic space
(`AlgebraicGeometry.isAlgebraicSpace_of_relativelyRepresentable`), and a property of scheme
morphisms which is stable under base change and fppf local on the target may be tested on a
representable morphism after pullback to a single surjective étale scheme atlas
(`AlgebraicGeometry.presheaf_inverseImage_iff_atlas_snd`).

## References

* [Stacks Project, Tag 02WY](https://stacks.math.columbia.edu/tag/02WY)
* [Stacks Project, Tag 02WZ](https://stacks.math.columbia.edu/tag/02WZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

end AlgebraicGeometry.Space

end
