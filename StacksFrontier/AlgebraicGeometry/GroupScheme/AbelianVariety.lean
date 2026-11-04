module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.Topology.KrullDimension
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Abelian varieties

An abelian variety over a field `k` is a group scheme over `k` whose underlying scheme is a
proper, geometrically integral variety over `k`.

## Main definitions

* `Stacks.Groupoids.IsAbelianVariety` is the property of being an abelian variety.
* `Stacks.Groupoids.abelianVarietyDimension` is the dimension of an abelian variety, as a
  natural number.

## Main results

* `Stacks.Groupoids.isAbelianVariety_iff` unfolds the class into a conjunction.

## Implementation notes

A group scheme over `k` is a group object `A` in schemes over `Spec k`. Both conditions are
stated for its structure morphism `A.hom`, as `AlgebraicGeometry.IsProperVariety` and
`AlgebraicGeometry.GeometricallyIntegral`, and the class extends both.

Scheme dimension is valued in `WithBot ℕ∞`; `abelianVarietyDimension` reads it as a natural
number by `unbotD 0` followed by `ENat.toNat`. For an abelian variety the scheme is nonempty and
its dimension finite, so this loses nothing.

## References

* [Stacks Project, Tag 03RO](https://stacks.math.columbia.edu/tag/03RO)
* [Stacks Project, Tag 04L1](https://stacks.math.columbia.edu/tag/04L1)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Groupoids

/-- A group scheme over a field is an abelian variety if its structure morphism makes its
underlying scheme a proper, geometrically integral variety. -/
@[stacks 03RO]
class IsAbelianVariety (k : Type u) [Field k] (A : Over (Spec (.of k))) [GrpObj A] : Prop
    extends IsProperVariety k A.hom, GeometricallyIntegral A.hom

/-- Being an abelian variety is being a proper variety and being geometrically integral. -/
theorem isAbelianVariety_iff (k : Type u) [Field k] (A : Over (Spec (.of k))) [GrpObj A] :
    IsAbelianVariety k A ↔ IsProperVariety k A.hom ∧ GeometricallyIntegral A.hom :=
  ⟨fun h ↦ ⟨h.toIsProperVariety, h.toGeometricallyIntegral⟩, fun ⟨h₁, h₂⟩ ↦
    .mk (toIsProperVariety := h₁) (toGeometricallyIntegral := h₂)⟩

/-- The dimension of an abelian variety, as a natural number. -/
@[sga "7 IX 2.1.5" "α = dim B_o in (2.1.9)"]
noncomputable abbrev abelianVarietyDimension {k : Type u} [Field k]
    (A : Over (Spec (.of k))) : ℕ :=
  (topologicalKrullDim A.left).unbotD 0 |>.toNat

end Stacks.Groupoids

end
