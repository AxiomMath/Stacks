module

public import StacksFrontier.AlgebraicGeometry.NagataExtensionClosed.Basic
public import StacksFrontier.AlgebraicGeometry.General.Basic

/-!
# Tag 0GWV, unconditionally

Tag `0GWV` states the equivalence, over a Nagata base `S` and for a quasi-compact `f : X ⟶ Y`
between schemes locally of finite type over `S`, of

1. `f` is universally closed,
2. every finite-dimensional affine-space base change of `f` is closed,
3. `f` satisfies the essentially-finite-type one-dimensional extension test.

The implications `1 ⇒ 2`, `1 ⇒ 3` and `3 ⇒ 2` are proved in
`StacksFrontier/AlgebraicGeometry/NagataValuativeCriterion/Basic.lean` and
`StacksFrontier/AlgebraicGeometry/NagataExtensionClosed/Basic.lean`, which reduce the tag to the
single named hypothesis `ClosedAffineSpaceBaseChangeImpliesUniversallyClosed` — the edge
`2 ⇒ 1`, which is Stacks `05JX`, implication (3) ⇒ (1).

`Basic.lean` of this directory proves that edge for an arbitrary quasi-compact morphism, so this
file discharges the named hypothesis and states tag `0GWV` with no hypothesis beyond the
source's own.  In particular `f` is not assumed affine.

## Main results

* `closedAffineSpaceBaseChangeImpliesUniversallyClosed`: the named hypothesis, discharged.
* `universallyClosed_tfae_essentiallyFiniteType`: tag `0GWV`.

## References

* [Stacks Project, Tag 0GWV](https://stacks.math.columbia.edu/tag/0GWV)
* [Stacks Project, Tag 05JX](https://stacks.math.columbia.edu/tag/05JX)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.AlgebraicGeometry.Tag05JXGeneral

open Stacks.AlgebraicGeometry.NagataValuativeCriterion
open Stacks.AlgebraicGeometry.NagataExtensionClosed

/-- Stacks `05JX`, implication (3) ⇒ (1), in the packaged form that the reduction of tag `0GWV`
leaves as a named hypothesis.  This discharges
`NagataValuativeCriterion.ClosedAffineSpaceBaseChangeImpliesUniversallyClosed`. -/
theorem closedAffineSpaceBaseChangeImpliesUniversallyClosed :
    ClosedAffineSpaceBaseChangeImpliesUniversallyClosed.{u} := fun f hqc h =>
  have := hqc
  universallyClosed_of_forall_isClosedMap_affineSpaceMap f h

/-- **Stacks Project, Tag 0GWV.**  Over a Nagata base `S`, for a quasi-compact `f : X ⟶ Y` with
`X` and `Y` locally of finite type over `S`, universal closedness, closedness of every
finite-dimensional affine-space base change, and the essentially-finite-type one-dimensional
extension test are equivalent.

Three of the four edges come from the Nagata files; the fourth, `2 ⇒ 1`, is Stacks `05JX`
(3) ⇒ (1), proved in `Basic.lean` for an arbitrary quasi-compact morphism. -/
@[stacks 0GWV]
theorem universallyClosed_tfae_essentiallyFiniteType
    {S X Y : Scheme.{u}} (hX : X ⟶ S) (hY : Y ⟶ S) (f : X ⟶ Y)
    (hf : f ≫ hY = hX) (hS : IsNagataScheme S)
    [LocallyOfFiniteType hX] [LocallyOfFiniteType hY] [QuasiCompact f] :
    List.TFAE
      [UniversallyClosed f,
       ∀ n : ℕ, IsClosedMap (AffineSpace.map (ULift.{u} (Fin n)) f),
       HasEssentiallyFiniteTypeValuativeExtension f hY] :=
  universallyClosed_tfae_essentiallyFiniteType_of_closedAffineSpaceBaseChange hX hY f hf hS
    closedAffineSpaceBaseChangeImpliesUniversallyClosed

end Stacks.AlgebraicGeometry.Tag05JXGeneral
