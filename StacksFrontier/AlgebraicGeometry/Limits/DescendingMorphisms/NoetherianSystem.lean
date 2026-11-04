module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksCore.Tactic.StacksAttribute

/-!
# Limits of directed systems of Noetherian schemes

A limit-Noetherian situation is a nonempty directed preorder together with an inverse system of
Noetherian schemes indexed by it whose transition morphisms are affine, and a chosen limit of
that system. It is the standing setup for descending a scheme of finite type over the limit to a
finite stage.

## Main definitions

* `AlgebraicGeometry.LimitNoetherianSituation` bundles the directed inverse system and its chosen
  limiting cone.
* `AlgebraicGeometry.LimitNoetherianSituation.limitScheme` is the limit of the system.

## Implementation notes

The transition morphism `S_{i'} ⟶ S_i` for `i ≤ i'` is represented by the image under a functor
from the opposite of the indexing preorder. The limiting scheme and all its canonical projections,
including their naturality, are packaged as a cone, and `CategoryTheory.Limits.IsLimit` records
its universal property. Noetherian means `AlgebraicGeometry.IsNoetherian`, hence includes both
local Noetherianity and quasi-compactness.

## References

* [Stacks Project, Tag 0CNM](https://stacks.math.columbia.edu/tag/0CNM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 0CNM.** A directed inverse system of Noetherian schemes with affine
transition morphisms, equipped with a chosen limiting cone. -/
@[stacks 0CNM]
structure LimitNoetherianSituation (I : Type v) [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] where
  /-- The inverse system `(S_i)`. -/
  system : Iᵒᵖ ⥤ Scheme.{u}
  /-- Every scheme in the system is Noetherian. -/
  noetherian : ∀ i : I, IsNoetherian (system.obj (op i))
  /-- Every transition morphism in the system is affine. -/
  transition_affine : ∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (system.map f)
  /-- The chosen cone whose point is the scheme `S`. -/
  limitCone : Cone system
  /-- The chosen cone is a limit cone. -/
  isLimit : IsLimit limitCone

namespace LimitNoetherianSituation

/-- The limit scheme `S` of a limit-Noetherian situation. -/
abbrev limitScheme {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : LimitNoetherianSituation.{v, u} I) : Scheme.{u} :=
  D.limitCone.pt

end LimitNoetherianSituation

end AlgebraicGeometry
