module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.Dimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.IsolatedFibrePoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PropertyGammaPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.RelativeConditions
public import StacksFrontier.Topology.Dimension.IsolatedPoint

/-!
# The topological dimension of a field fibre at a point

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` which is locally of finite
type, let `p` be a field-valued point of `Y` with field of definition `k`, and let
`X_k = X ×_Y Spec k` be the field fibre. Among the eight conditions on a point `x̃` of `|X_k|`
compared by Stacks 0ACB, two are the ones this file is about:

* (4) the point space `|X_k|` has local Krull dimension zero at `x̃`;
* (5) `x̃` is isolated in `|X_k|`.

Condition (5) always implies condition (4), because an isolated point has a one-point open
neighbourhood. The converse is the one implication of Stacks 0ACB that needs a decency
hypothesis: it holds when `f` is a decent morphism, and therefore also when the source `X` is
a decent algebraic space.

## Main results

* `AlgebraicGeometry.Space.isDecent_of_isDecentSpace_source`: the decent case of Stacks 0ABX,
  a morphism whose source is a decent algebraic space is a decent morphism.
* `AlgebraicGeometry.Space.isDecentSpace_fieldFibre`: the field fibre of a decent morphism is
  a decent algebraic space.
* `AlgebraicGeometry.Space.isIsolatedPoint_fieldFibre_of_topologicalKrullDimAt_eq_zero`:
  condition (4) implies condition (5) for a decent morphism.
* `AlgebraicGeometry.Space.topologicalKrullDimAt_points_fieldFibre_eq_zero_iff_isIsolatedPoint`:
  conditions (4) and (5) are equivalent when the source is a decent algebraic space.

## Implementation notes

The field fibre `X_k` is the pullback of `f` along the morphism `Spec k ⟶ Y` presenting the
field-valued point, so it is a base change of `f` along a morphism out of a representable
presheaf and decency of `f` applies to it directly — up to the symmetry of the fibre product,
since `AlgebraicGeometry.Space.IsDecent` is stated for the pullback taken in the other order.

With `X_k` decent, Stacks 0A4J identifies the local Krull dimension of `|X_k|` at `x̃` with
the dimension of the algebraic space `X_k` at `x̃`, which is condition (7) of Stacks 0ACB;
conditions (7), (6) and (5) are already known to be equivalent, in
`StacksFrontier.AlgebraicGeometry.Spaces.Decent.IsolatedFibrePoint`. So condition (4) is
condition (7) for a decent morphism, and the implication (4) ⟹ (5) is a transport along that
identification rather than a new argument. The reverse implication is purely topological and
needs no hypothesis at all.

The decent case of Stacks 0ABX is proved here because it is the input the equivalence needs
and the repository carries only the weaker condition-(4)-of-Stacks-03JU forms of Stacks 0ABX,
in `StacksFrontier.AlgebraicGeometry.Spaces.Decent.RelativeConditions`. It is the source's own
argument: a morphism from a representable presheaf into an algebraic space is representable,
so the projection of a base change of `f` along it to the source `X` is representable, and
decency passes from the target of a representable morphism to its source by Stacks 0ABT.

## References

* [Stacks Project, Tag 0ACB](https://stacks.math.columbia.edu/tag/0ACB)
* [Stacks Project, Tag 0A4J](https://stacks.math.columbia.edu/tag/0A4J)
* [Stacks Project, Tag 0ABT](https://stacks.math.columbia.edu/tag/0ABT)
* [Stacks Project, Tag 0ABX](https://stacks.math.columbia.edu/tag/0ABX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/- Instance search for pullbacks of presheaves on `BigFppfOver B S hS` times out under Lean
v4.35.0; supply the functor-category instance. -/
local instance (priority := high) : HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  functorCategoryHasLimitsOfShape

local instance (priority := high) {Y Z W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : Y ⟶ W)
    (g : Z ⟶ W) : HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit (cospan f g)

/-! ### Decency of the field fibre -/

/-- **Stacks 0ABX, the decent case.** A morphism of algebraic spaces over `S` whose source is
a decent algebraic space is a decent morphism.

A morphism `g : h_T ⟶ Y` out of a representable presheaf into an algebraic space is
representable, because the diagonal of `Y` is; hence so is the projection
`T ×_Y X ⟶ X` of its base change, and decency passes from the target of a representable
morphism to its source by Stacks 0ABT. -/
@[stacks 0ABX "decent: a morphism whose source is decent is decent"]
theorem isDecent_of_isDecentSpace_source (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hdec : IsDecentSpace B S hS X) :
    IsDecent B S hS f := by
  intro T g
  have : HasBinaryProducts (BigFppfOver B S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  have hg : yoneda.relativelyRepresentable g :=
    Functor.relativelyRepresentable.of_diag hY.diagonal_representable g
  exact isDecentSpace_of_relativelyRepresentable B S hS
    (isAlgebraicSpace_pullback B S hS g f (isAlgebraicSpace_yoneda B S hS T) hX hY)
    (pullback.snd g f)
    (MorphismProperty.of_isPullback (IsPullback.of_hasPullback g f) hg) hdec

/-- The field fibre `X_k = X ×_Y Spec k` of a decent morphism of algebraic spaces over `S`
along a field-valued point of its target is a decent algebraic space.

It is a base change of the morphism along the morphism `Spec k ⟶ Y` presenting the point,
which comes out of a representable presheaf; the fibre product is taken in the other order
from the one in `AlgebraicGeometry.Space.IsDecent`, whence the symmetry. -/
theorem isDecentSpace_fieldFibre (f : X ⟶ Y) (hd : IsDecent B S hS f)
    (p : FieldValuedPoint B S hS Y) :
    IsDecentSpace B S hS (fieldFibre B S hS f p) :=
  isDecentSpace_of_iso B S hS (pullbackSymmetry (yonedaEquiv.symm p.value) f)
    (hd (p.siteObject B S hS Y) (yonedaEquiv.symm p.value))

/-! ### The comparison of conditions (4) and (5) -/

/-- **Stacks 0ACB, condition (4) implies condition (5) for a decent morphism.** If the point
space of the field fibre of a decent morphism of algebraic spaces locally of finite type has
local Krull dimension zero at a point, then that point is isolated in it.

For a decent morphism the field fibre is a decent algebraic space, so Stacks 0A4J identifies
the local Krull dimension of its point space with its dimension as an algebraic space, which
is condition (7); conditions (7), (6) and (5) are equivalent. -/
@[stacks 0ACB "condition (4) implies (5) for decent morphisms"]
theorem isIsolatedPoint_fieldFibre_of_topologicalKrullDimAt_eq_zero
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hf : IsLocallyOfFiniteType B S hS f) (hd : IsDecent B S hS f)
    (p : FieldValuedPoint B S hS Y) (z : points B S hS (fieldFibre B S hS f p))
    (h : topologicalKrullDimAt (points B S hS (fieldFibre B S hS f p)) z = 0) :
    IsIsolatedPoint z :=
  (isIsolatedPoint_fieldFibre_iff_isClosedNoGeneralization hX hY f hf p z).mpr
    ((isClosedNoGeneralization_fieldFibre_iff_dimensionAtPoint_eq_zero hX hY f hf p z).mpr
      ((topologicalKrullDimAt_points_eq_dimensionAtPoint_of_isDecentSpace B S hS
        (isAlgebraicSpace_fieldFibre hX hY f p)
        (isDecentSpace_fieldFibre B S hS f hd p) z).symm.trans h))

/-- **Stacks 0ACB, conditions (4) and (5) for decent spaces.** A point of the point space of
the field fibre of a morphism of algebraic spaces locally of finite type with decent source is
isolated exactly when that point space has local Krull dimension zero there.

A morphism out of a decent algebraic space is a decent morphism, Stacks 0ABX, which gives the
implication from dimension zero to isolation. The converse holds for any topological space:
an isolated point has a one-point open neighbourhood. -/
@[stacks 0ACB "conditions (4) and (5) for decent spaces"]
theorem topologicalKrullDimAt_points_fieldFibre_eq_zero_iff_isIsolatedPoint
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hf : IsLocallyOfFiniteType B S hS f) (hdec : IsDecentSpace B S hS X)
    (p : FieldValuedPoint B S hS Y) (z : points B S hS (fieldFibre B S hS f p)) :
    topologicalKrullDimAt (points B S hS (fieldFibre B S hS f p)) z = 0 ↔
      IsIsolatedPoint z :=
  ⟨isIsolatedPoint_fieldFibre_of_topologicalKrullDimAt_eq_zero B S hS hX hY f hf
      (isDecent_of_isDecentSpace_source B S hS hX hY f hdec) p z,
    topologicalKrullDimAt_eq_zero_of_isIsolatedPoint z⟩

end AlgebraicGeometry.Space

end
