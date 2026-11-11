module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionSituation
public import StacksFrontier.AlgebraicGeometry.FormalSpace.GeneralReduction

/-!
# The situation of Artin's theorem on contractions, with the reduction constructed

Let `S` be a scheme contained in a big fppf site `B`. **Stacks 0GH8** fixes the standing data
for Artin's theorem on contractions: `S` is a locally Noetherian scheme, `X'` is an algebraic
space locally of finite type over `S`, `T' ⊆ |X'|` is a closed subset, `U' ⊆ X'` is the open
subspace with `|U'| = |X'| ∖ T'`, `W` is a locally Noetherian formal algebraic space over `S`
with `W_red` locally of finite type over `S`, and `g : X'_{/T'} ⟶ W` is a formal modification
in the sense of Stacks 0GDK, where `X'_{/T'}` is the formal completion of `X'` along `T'` of
Stacks 0AIX.

This file records that situation with exactly those data. `U'` is constructed from `T'` by the
correspondence of Stacks 03BZ, and `W_red` is the reduction of `W` constructed by Stacks 0AIN,
`AlgebraicGeometry.FormalSpace.reduction`: the source's condition on `W_red` is a condition on
that reduction, and no reduction is supplied by hand.

## Main definitions

* `AlgebraicGeometry.Artin.ContractionSetting`: **Stacks 0GH8**, the standing data.
* `AlgebraicGeometry.Artin.ContractionSetting.Wred`: the reduction `W_red` of `W`, by Stacks
  0AIN.
* `AlgebraicGeometry.Artin.ContractionSetting.U'`: **Stacks 0GH8**, the open subspace
  `U' ⊆ X'` with `|U'| = |X'| ∖ T'`.
* `AlgebraicGeometry.Artin.ContractionSetting.toContractionSituation`: the same data in the
  shape of `AlgebraicGeometry.Artin.ContractionSituation`, which the rest of the contraction
  development consumes.

## Main results

* `AlgebraicGeometry.Artin.ContractionSetting.isReduction_Wred`: the inclusion `W_red ⟶ W` is
  a reduction in the sense of Stacks 0AIN.
* `AlgebraicGeometry.Artin.ContractionSetting.toContractionSituation_U'`: `U'` is the open
  subspace of `AlgebraicGeometry.Artin.ContractionSituation`, so it is an open subspace of `X'`
  whose point set is the complement of `T'`
  (`AlgebraicGeometry.Artin.ContractionSituation.isOpenSubspace_U'` and
  `AlgebraicGeometry.Artin.ContractionSituation.range_pointsMap_ι_U'`).

## Implementation notes

The conventions are those of `AlgebraicGeometry.Artin.ContractionSituation`: `X'` is a presheaf
on the big fppf site of `S`, so "over `S`" is carried by the ambient category, and "locally of
finite type over `S`" is local finite type of the morphism to the terminal presheaf, which is
`S`. The reduction of Stacks 0AIN is an algebraic space with values in `Type u`; it is viewed
as an fppf sheaf of `Type (u + 1)`, the value universe of `W`, through
`AlgebraicGeometry.FormalSpace.liftSheaf`, and its local finite type over `S` is accordingly
`AlgebraicGeometry.Space.IsLocallyOfFiniteTypeULift`.

`AlgebraicGeometry.FormalSpace.reduction` is a choice of reduction; any two reductions of `W`
are identified by the unique isomorphism `AlgebraicGeometry.FormalSpace.Reduction.iso` over
`W`, which is the sense in which the source speaks of *the* reduction `W_red`.

`X'_{/T'}` is `AlgebraicGeometry.Space.completionSheaf` of Stacks 0AMC; that it is a locally
Noetherian formal algebraic space is part of the hypothesis that `g` is a formal modification
(the field `isLocallyNoetherian_source` of
`AlgebraicGeometry.FormalSpace.IsFormalModification`). The field `isLocallyNoetherian_W` is the
source's standing hypothesis on `W`; it is also what makes the reduction of `W` available.

## References

* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 0AIN](https://stacks.math.columbia.edu/tag/0AIN)
* [Stacks Project, Tag 0AIX](https://stacks.math.columbia.edu/tag/0AIX)
* [Stacks Project, Tag 0AMC](https://stacks.math.columbia.edu/tag/0AMC)
* [Stacks Project, Tag 0GDK](https://stacks.math.columbia.edu/tag/0GDK)
* [Stacks Project, Tag 0GH8](https://stacks.math.columbia.edu/tag/0GH8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Artin

attribute [local instance] Space.pointTopology

/-- **Stacks 0GH8.** The standing situation of Artin's theorem on contractions: a locally
Noetherian scheme `S` contained in a big fppf site `B`, an algebraic space `X'` locally of finite
type over `S`, a closed subset `T' ⊆ |X'|`, a locally Noetherian formal algebraic space `W` over
`S` whose reduction `W_red` (constructed by Stacks 0AIN) is locally of finite type over `S`, and
a formal modification `g : X'_{/T'} ⟶ W` from the formal completion of `X'` along `T'` to `W`.

The open subspace `U' ⊆ X'` with `|U'| = |X'| ∖ T'` is constructed from `T'` as
`AlgebraicGeometry.Artin.ContractionSetting.U'`, and `W_red` as
`AlgebraicGeometry.Artin.ContractionSetting.Wred`. -/
@[stacks 0GH8 "the standing data S, X', T', W and g, with W_red the reduction of W constructed \
by Stacks 0AIN"]
structure ContractionSetting (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) where
  /-- The base scheme `S` is locally Noetherian. -/
  isLocallyNoetherian_base : _root_.AlgebraicGeometry.IsLocallyNoetherian S
  /-- The algebraic space `X'`, as a presheaf on the big fppf site of `S`. -/
  X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u
  /-- `X'` is an algebraic space over `S`, in the sense of Stacks 025Y. -/
  isAlgebraicSpace_X' : IsAlgebraicSpace B S hS X'
  /-- `X'` is locally of finite type over `S`: its structure morphism to the base, the
  terminal presheaf on the big fppf site of `S`, is locally of finite type. -/
  isLocallyOfFiniteType_X' : Space.IsLocallyOfFiniteType B S hS (terminal.from X')
  /-- The subset `T' ⊆ |X'|` of the point space of Stacks 03BU. -/
  T' : Set (Space.points B S hS X')
  /-- `T'` is closed in the point space `|X'|` of Stacks 03BY. -/
  isClosed_T' : IsClosed T'
  /-- The formal algebraic space `W`, as an fppf sheaf of `Type (u + 1)` on the big fppf site
  of `S`. -/
  W : FormalSpace.FppfSheaf B S hS
  /-- `W` is a locally Noetherian formal algebraic space over `S`, in the sense of Stacks
  0AKY. -/
  isLocallyNoetherian_W : FormalSpace.IsLocallyNoetherian B S hS W
  /-- The reduction `W_red` of `W`, constructed by Stacks 0AIN, is locally of finite type over
  `S`: its structure morphism to the terminal sheaf on the big fppf site of `S` is locally of
  finite type. -/
  isLocallyOfFiniteType_Wred : Space.IsLocallyOfFiniteTypeULift.{u + 1} B S hS
    (terminal.from (FormalSpace.liftSheaf B S hS
      (FormalSpace.reduction B S hS W isLocallyNoetherian_W.1).space).obj)
  /-- The morphism `g : X'_{/T'} ⟶ W` out of the formal completion of `X'` along `T'`
  (Stacks 0AIX, 0AMC). -/
  g : Space.completionSheaf B S hS X' T' ⟶ W
  /-- `g` is a formal modification in the sense of Stacks 0GDK. -/
  isFormalModification_g : FormalSpace.IsFormalModification B S hS g

namespace ContractionSetting

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (c : ContractionSetting B S hS)

/-- The reduction `W_red` of `W`, constructed by Stacks 0AIN, as an fppf sheaf of
`Type (u + 1)`. -/
noncomputable def Wred : FormalSpace.FppfSheaf B S hS :=
  FormalSpace.liftSheaf B S hS (FormalSpace.reduction B S hS c.W c.isLocallyNoetherian_W.1).space

/-- The inclusion `W_red ⟶ W` of the reduction. -/
noncomputable def WredInclusion : c.Wred ⟶ c.W :=
  (FormalSpace.reduction B S hS c.W c.isLocallyNoetherian_W.1).inclusion

/-- The inclusion `W_red ⟶ W` exhibits `W_red` as the reduction of `W`, by Stacks 0AIN. -/
theorem isReduction_Wred : FormalSpace.IsReduction B S hS c.W c.Wred c.WredInclusion :=
  (FormalSpace.reduction B S hS c.W c.isLocallyNoetherian_W.1).isReduction

/-- The situation in the shape of `AlgebraicGeometry.Artin.ContractionSituation`, with the
reduction of `W` constructed by Stacks 0AIN. -/
noncomputable def toContractionSituation : ContractionSituation B S hS where
  isLocallyNoetherian_base := c.isLocallyNoetherian_base
  X' := c.X'
  isAlgebraicSpace_X' := c.isAlgebraicSpace_X'
  isLocallyOfFiniteType_X' := c.isLocallyOfFiniteType_X'
  T' := c.T'
  isClosed_T' := c.isClosed_T'
  W := c.W
  isLocallyNoetherian_W := c.isLocallyNoetherian_W
  Wred := c.Wred
  WredInclusion := c.WredInclusion
  isReduction_WredInclusion := c.isReduction_Wred
  isLocallyOfFiniteType_Wred := c.isLocallyOfFiniteType_Wred
  g := c.g
  isFormalModification_g := c.isFormalModification_g

/-- **Stacks 0GH8.** The open subspace `U' ⊆ X'` with `|U'| = |X'| ∖ T'`: the subfunctor of
`X'` cut out by the complement of `T'` under the correspondence of Stacks 03BZ. It agrees with the
open subspace of `AlgebraicGeometry.Artin.ContractionSituation`
(`AlgebraicGeometry.Artin.ContractionSetting.toContractionSituation_U'`), whose two defining
properties are `AlgebraicGeometry.Artin.ContractionSituation.isOpenSubspace_U'` and
`AlgebraicGeometry.Artin.ContractionSituation.range_pointsMap_ι_U'`. -/
@[stacks 0GH8 "the open subspace U' ⊆ X' with |U'| = |X'| ∖ T', constructed from T'"]
def U' : Subfunctor c.X' :=
  Space.openSubspaceOfPoints B S hS c.X' c.T'ᶜ

/-- The open subspace `U'` of the situation agrees with the one of
`AlgebraicGeometry.Artin.ContractionSituation`. -/
theorem toContractionSituation_U' : c.toContractionSituation.U' = c.U' :=
  rfl

end ContractionSetting

end AlgebraicGeometry.Artin

end
