module

public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Completion
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Proper
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Reduction
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence

/-!
# The situation of Artin's theorem on contractions

Let `S` be a scheme contained in a big fppf site `B`. Stacks 0GH8 fixes the standing data
for Artin's theorem on contractions: `S` is locally Noetherian, `X'` is an algebraic space
locally of finite type over `S`, `T' ⊆ |X'|` is a closed subset with open complement the open
subspace `U' ⊆ X'`, `W` is a locally Noetherian formal algebraic space over `S` whose
reduction `W_red` is locally of finite type over `S`, and `g : X'_{/T'} ⟶ W` is a formal
modification in the sense of Stacks 0GDK from the completion of `X'` along `T'` of Stacks
0AIX to `W`.

This is a setting rather than an assertion, so it is recorded as a structure bundling those
data, with the reduction `W_red` of `W` carried as a datum. Stacks 0GH8 itself, with `W_red` the
reduction of `W` constructed by Stacks 0AIN, is registered at
`AlgebraicGeometry.Artin.ContractionSetting`
(`StacksFrontier/AlgebraicGeometry/Artin/ContractionSetting.lean`), which produces this structure
through `AlgebraicGeometry.Artin.ContractionSetting.toContractionSituation`.

## Main definitions

* `AlgebraicGeometry.Artin.ContractionSituation`: the standing data of Stacks 0GH8, with the
  reduction of `W` carried as a datum.
* `AlgebraicGeometry.Artin.ContractionSituation.U'`: the open subspace `U' ⊆ X'` with
  `|U'| = |X'| ∖ T'`.

## Main results

* `AlgebraicGeometry.Artin.ContractionSituation.isOpenSubspace_U'` and
  `AlgebraicGeometry.Artin.ContractionSituation.range_pointsMap_ι_U'`: the two defining
  properties of `U'`, namely that it is an open subspace of `X'` and that its point set is
  the complement of `T'`.

## What is assumed

Nothing beyond the source's own hypotheses. The reduction `W_red` is carried as the three
fields `Wred`, `WredInclusion` and `isReduction_WredInclusion` rather than constructed from
`W`. This costs no generality: Stacks 0AIN —
`AlgebraicGeometry.FormalSpace.exists_isReduction_of_isFormalAlgebraicSpace` — supplies such
a datum for every formal algebraic space, so no locally Noetherian formal algebraic
space `W` is excluded; and a reduction is unique up to unique isomorphism by the universal
property in `AlgebraicGeometry.FormalSpace.IsReduction.universal`, so the requirement that
`W_red` be locally of finite type over `S` does not depend on which reduction is supplied.

Nothing else is assumed. In particular `U'` is a construction and not a field: the
correspondence of Stacks 03BZ between open subsets of `|X'|` and open subspaces of `X'` is
available as `AlgebraicGeometry.Space.openSubspaceOfPoints`, together with the proofs that it
is an open subspace and that its point set is the given open set, so `U'` is defined from `T'`
and its two defining properties are theorems.

## Implementation notes

An algebraic space over `S` is a presheaf on the big fppf site of `S` in the sense of Stacks
025Y, so `X'` is an object of `(BigFppfOver B S hS)ᵒᵖ ⥤ Type u` and "over `S`" is carried by
the ambient category rather than by a morphism. Accordingly "locally of finite type over `S`"
is local finite type of the structure morphism `terminal.from X'`. Its target, the terminal
presheaf, *is* `S`: it is the Yoneda presheaf of the terminal object of the site by
`AlgebraicGeometry.Space.yonedaTerminalIso`, and that object has underlying scheme `S` by
`AlgebraicGeometry.Space.toSchemeTerminalIso`, its structure morphism being the identity
(`StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFppfDescent`). The étale-chart condition of
`AlgebraicGeometry.Space.IsLocallyOfFiniteType` therefore says that for every étale scheme
chart `U` of `X'` and every scheme `V` étale over `S` in the site, every morphism `U ⟶ V` over
`S` is locally of finite type; taking `V = S` gives that every étale chart of `X'` is locally
of finite type over `S`, and conversely that condition gives the others by Stacks 01T8, so the
two agree. The same device is used for `W_red` through
`AlgebraicGeometry.Space.IsLocallyOfFiniteTypeULift`, the value universe of a formal algebraic
space being `Type (u + 1)` rather than `Type u`.

`W` is an object of `AlgebraicGeometry.FormalSpace.FppfSheaf`, the fppf sheaves of
`Type (u + 1)`, and `X'_{/T'}` is `AlgebraicGeometry.Space.completionSheaf` of Stacks 0AMC,
the sheafification of the subfunctor of sections whose point-set image lies in `T'`. That
`X'_{/T'}` is a formal algebraic space is Stacks 0AIZ
(`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_completionSheaf_of_isClosed`); it is not
needed as a separate field, because the source's own hypothesis on `g` already contains it: the
field `isLocallyNoetherian_source` of `AlgebraicGeometry.FormalSpace.IsFormalModification`
asserts that the source of a formal modification is a locally Noetherian formal algebraic
space.

The field `isLocallyNoetherian_W` is implied by `isFormalModification_g`, whose
`isLocallyNoetherian_target` field is the same assertion. It is kept because the source states
it as a standing hypothesis on `W` on its own, before `g` is introduced.

The topology on `|X'|` is the one of Stacks 03BY, `AlgebraicGeometry.Space.pointTopology`,
which is a plain definition rather than an instance and is made a local instance here, as
elsewhere in this library.

## References

* [Stacks Project, Tag 01T8](https://stacks.math.columbia.edu/tag/01T8)
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

/-- The standing situation of Artin's theorem on contractions (Stacks 0GH8): a locally
Noetherian base scheme `S` contained in a big fppf site `B`, an algebraic space `X'` locally
of finite type over `S`, a closed subset `T' ⊆ |X'|`, a locally Noetherian formal algebraic
space `W` over `S` with reduction `W_red` locally of finite type over `S`, and a formal
modification `g : X'_{/T'} ⟶ W` from the completion of `X'` along `T'` to `W`.

The open subspace `U' ⊆ X'` with `|U'| = |X'| ∖ T'` is not a field: it is constructed from
`T'` as `AlgebraicGeometry.Artin.ContractionSituation.U'`.

The reduction of `W` is carried as data, which is the shape the rest of the contraction
development consumes. Stacks 0GH8 itself, with `W_red` the reduction constructed by Stacks 0AIN,
is `AlgebraicGeometry.Artin.ContractionSetting`, and
`AlgebraicGeometry.Artin.ContractionSetting.toContractionSituation` produces this structure from
it. -/
structure ContractionSituation (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    where
  /-- The base scheme `S` is locally Noetherian. -/
  isLocallyNoetherian_base : _root_.AlgebraicGeometry.IsLocallyNoetherian S
  /-- The algebraic space `X'`, as a presheaf on the big fppf site of `S`. -/
  X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u
  /-- `X'` is an algebraic space over `S`, in the sense of Stacks 025Y. -/
  isAlgebraicSpace_X' : IsAlgebraicSpace B S hS X'
  /-- `X'` is locally of finite type over `S`: its structure morphism to the base, the
  terminal presheaf on the big fppf site of `S`, is locally of finite type. -/
  isLocallyOfFiniteType_X' : Space.IsLocallyOfFiniteType B S hS (terminal.from X')
  /-- The subset `T' ⊆ |X'|` of the point space of Stacks 03BU along which `X'` is
  completed. -/
  T' : Set (Space.points B S hS X')
  /-- `T'` is closed in the point space `|X'|` of Stacks 03BY. -/
  isClosed_T' : IsClosed T'
  /-- The formal algebraic space `W`, as an fppf sheaf of `Type (u + 1)` on the big fppf site
  of `S`. -/
  W : FormalSpace.FppfSheaf B S hS
  /-- `W` is a locally Noetherian formal algebraic space over `S`, in the sense of Stacks
  0AKY. -/
  isLocallyNoetherian_W : FormalSpace.IsLocallyNoetherian B S hS W
  /-- The reduction `W_red` of `W`, supplied as data rather than produced by Stacks 0AIN. -/
  Wred : FormalSpace.FppfSheaf B S hS
  /-- The inclusion `W_red ⟶ W` of the reduction. -/
  WredInclusion : Wred ⟶ W
  /-- The inclusion exhibits `W_red` as the reduction of `W`: `W_red` is a reduced algebraic
  space, the inclusion is a representable thickening, and every morphism to `W` from a reduced
  algebraic space factors uniquely through it. -/
  isReduction_WredInclusion : FormalSpace.IsReduction B S hS W Wred WredInclusion
  /-- `W_red` is locally of finite type over `S`: its structure morphism to the terminal
  sheaf of `Type (u + 1)` on the big fppf site of `S` is locally of finite type. -/
  isLocallyOfFiniteType_Wred :
    Space.IsLocallyOfFiniteTypeULift.{u + 1} B S hS (terminal.from Wred.obj)
  /-- The morphism `g : X'_{/T'} ⟶ W` out of the completion of `X'` along `T'` of Stacks
  0AMC. -/
  g : Space.completionSheaf B S hS X' T' ⟶ W
  /-- `g` is a formal modification in the sense of Stacks 0GDK: a proper, rig-étale and
  rig-surjective morphism of locally Noetherian formal algebraic spaces whose relative
  diagonal is rig-surjective. -/
  isFormalModification_g : FormalSpace.IsFormalModification B S hS g

namespace ContractionSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (c : ContractionSituation B S hS)

/-- The open subspace `U' ⊆ X'` of the situation of Stacks 0GH8, the one with
`|U'| = |X'| ∖ T'`: the subfunctor of `X'` cut out by the complement of `T'` under the
correspondence of Stacks 03BZ. Its two defining properties are
`AlgebraicGeometry.Artin.ContractionSituation.isOpenSubspace_U'` and
`AlgebraicGeometry.Artin.ContractionSituation.range_pointsMap_ι_U'`. -/
def U' : Subfunctor c.X' :=
  Space.openSubspaceOfPoints B S hS c.X' c.T'ᶜ

/-- `U'` is an open subspace of `X'`, by Stacks 03BZ: the complement of the closed set `T'`
is open. -/
theorem isOpenSubspace_U' : Space.IsOpenSubspace B S hS c.U' :=
  Space.isOpenSubspace_openSubspaceOfPoints B S hS c.isAlgebraicSpace_X' c.T'ᶜ
    c.isClosed_T'.isOpen_compl

/-- The point set of `U'` is the complement of `T'`, that is `|U'| = |X'| ∖ T'`, by Stacks
03BZ. -/
theorem range_pointsMap_ι_U' :
    Set.range (Space.pointsMap B S hS c.U'.toFunctor c.U'.ι) = c.T'ᶜ :=
  Space.range_pointsMap_ι_openSubspaceOfPoints B S hS c.T'ᶜ

end ContractionSituation

end AlgebraicGeometry.Artin

end
