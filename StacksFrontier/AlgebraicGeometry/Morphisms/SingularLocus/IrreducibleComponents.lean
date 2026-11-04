module

public import Mathlib.AlgebraicGeometry.Fiber
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.FlatCodimensionZero
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import StacksCore.Tactic.StacksAttribute

/-!
# Local finiteness of irreducible components along a smooth morphism

For a smooth morphism of schemes, local finiteness of the set of irreducible components passes
from the target to the source.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.finite_irreducibleComponents_of_flat_locallyOfFiniteType` shows that if
  every quasi-compact open of the target has finitely many irreducible components, then so does
  every quasi-compact open of the source of a flat morphism locally of finite type.
* `AlgebraicGeometry.finite_irreducibleComponents_of_smooth` is its instance at a smooth
  morphism, which is Tag 07TD.

## Implementation notes

Irreducible components of a scheme correspond to its generic points, so the statement is proved
by counting generic points. A flat morphism is generalizing, so it carries generic points of the
source to generic points of the target; over a generic point of the target, the generic points of
the source lying above it are the generic points of the fibre, and the fibre of a morphism locally
of finite type over a field is a Noetherian scheme and so has finitely many of them. This bounds
the generic points of an affine piece by a sigma type over the generic points of the target, and a
quasi-compact open is covered by finitely many such pieces.

The hypothesis and conclusion quantify over quasi-compact opens rather than assuming the schemes
themselves quasi-compact, which is what makes the statement local and lets it be applied to the
affine pieces of the covering during its own proof. Smoothness enters only through flatness and
local finite type.

## References

* [Stacks Project, Tag 07TD](https://stacks.math.columbia.edu/tag/07TD)
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 07TD.** Local finiteness of irreducible components ascends along a
smooth morphism. -/
@[stacks 07TD "finiteness of irreducible components"]
public theorem finite_irreducibleComponents_of_smooth {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Smooth f]
    (hY : ∀ U : Y.Opens, IsCompact (U : Set Y) → (irreducibleComponents U).Finite) :
    ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite := by
  have : Flat f := inferInstance
  have : LocallyOfFiniteType f := inferInstance
  exact finite_irreducibleComponents_of_flat_locallyOfFiniteType f hY

end AlgebraicGeometry
