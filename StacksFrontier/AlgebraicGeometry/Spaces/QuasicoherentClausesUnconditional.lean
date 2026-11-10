module

public import StacksFrontier.AlgebraicGeometry.Spaces.CokernelAffineSurjectivityFromCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCokernelsUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentColimitsEssSurj
public import StacksFrontier.AlgebraicGeometry.Spaces.ShortExactQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartCechVanishingUnconditional

/-!
# The short-exact and colimit clauses of Stacks 03M1, with nothing assumed

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B`.  Three files in
this tree state clauses of Stacks 03M1 for the small étale site of `F` conditionally, on two
propositions of Descent, Chapter 35 written out at every use:

* `hEss`, the essential-surjectivity clause of Descent, Proposition 03DX (2) at an affine chart;
* `h03DW`, surjectivity on the sections over an affine chart of every epimorphism of
  `𝒪_F`-modules whose kernel is cartesian on affine charts — the uniform form of Descent,
  Proposition 03DW, carried byte-identically at eleven binder sites.

**Both are now discharged, and this file states those clauses with nothing assumed.**

* The residue of `hEss` was always only the implication "quasi-coherent ⟹ cartesian on affine
  charts", and that is proved unconditionally as `@[stacks 03DX "quasi-coherent implies
  cartesian"] AlgebraicGeometry.Space.isCartesianOnAffineCharts_of_isQuasicoherentOnSite`.  `hEss`
  itself is *not* proved anywhere, and the statements below do not need it: each of the three
  conditional files uses its `hEss` only to form that implication.  Other `hEss` binders in the
  tree, in `StacksFrontier.AlgebraicGeometry.Spaces.SliceAssociatedModuleEssSurj`, are not claimed
  to be reducible to it.
* `h03DW` is proved unconditionally as
  `AlgebraicGeometry.Space.surjective_val_app_of_epi_of_kernel_isCartesianOnAffineCharts`
  (`StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartCechVanishingUnconditional`).

## Which of the eleven binder sites this actually needed

Five of the eleven, the cokernel-side ones in
`StacksFrontier.AlgebraicGeometry.Spaces.CokernelAffineSurjectivity`, were **already** discharged
unconditionally by
`StacksFrontier.AlgebraicGeometry.Spaces.CokernelAffineSurjectivityFromCartesian`,
which replaces the uniform hypothesis by
`AlgebraicGeometry.Space.surjective_val_app_of_epi_of_cartesian` — available there because the
source of each of those three epimorphisms is already cartesian.  That file records that the one
site it could *not* reach is
`AlgebraicGeometry.Space.surjective_g_val_app_of_shortExact_of_h03DW`, whose epimorphism is the
right-hand map `T.g` of a short exact sequence, with `T.X₂` not known to be cartesian.

So what the uniform form of 03DW genuinely adds is that one site, and the clauses downstream of
it: `AlgebraicGeometry.Space.surjective_g_val_app_of_shortExact_of_isCartesian` below is the first
statement here that needs the uniform form of 03DW, and clause (4) is the first clause.

## Main results

* `AlgebraicGeometry.Space.surjective_g_val_app_of_shortExact_of_isCartesian`: **the right-hand map
  of a short exact sequence of `𝒪_F`-modules whose left term is cartesian on affine charts is
  surjective on the sections over an affine chart**, with nothing assumed.
* `AlgebraicGeometry.Space.isQuasicoherent_left_of_shortExact'`,
  `AlgebraicGeometry.Space.isQuasicoherent_middle_of_shortExact'` and
  `AlgebraicGeometry.Space.isQuasicoherent_right_of_shortExact'`: clause (4), the
  two-out-of-three property of a short exact sequence.
* `AlgebraicGeometry.Space.isQuasicoherent_colimit'`: clause (2), **still carrying the added
  coproduct hypothesis** — see the implementation notes.  The closure statement it rests on is
  `AlgebraicGeometry.Space.isClosedUnderColimitsOfShape_quasicoherentSheaves_schemeUniverse` of
  `StacksFrontier/AlgebraicGeometry/Spaces/QuasicoherentCoherator.lean`.

## Implementation notes

The primed names are this tree's existing mark for the unconditional form of a statement whose
hypothesis-carrying version keeps the unprimed name; compare
`AlgebraicGeometry.SmallEtale.isSheaf_associatedPresheaf'`,
`AlgebraicGeometry.SmallEtale.full_associatedModuleQcoh'` and
`AlgebraicGeometry.SmallEtale.isEquivalence_associatedModuleQcohOnSite'`.  The conditional
statements are kept, not deleted: their hypotheses are general and they are how the rest of the
tree cites these clauses.  The `_of_h03DW` and `_of_essSurj_of_h03DW` suffixes on those
statements now name a discharged hypothesis rather than an owed one, which is a naming debt this
file does not pay off — renaming them touches eight files and six of the eleven target names are
taken by the general theorems the statements are built from.

The hypotheses were not removed in place, in the three files that carry them.  Adding the import
of the uniform form of 03DW to
`StacksFrontier/AlgebraicGeometry/Spaces/CokernelAffineSurjectivity.lean` makes that file stop
compiling: its statements leave the module universe of
`CategoryTheory.Limits.kernel` and `CategoryTheory.Abelian.image` to be inferred, and the wider
import surface brings a second `CategoryTheory.Abelian` instance into range, so elaboration ends
at `stuck at solving universe constraint u + 1 =?= max (u + 1) ?u`.  Stating the unconditional
forms downstream, in a file that pins `Modules.{u, u}` in every statement, is also what
`CokernelAffineSurjectivityFromCartesian` does and for the same reason.

## Why clause (2) carries no attribute

`AlgebraicGeometry.Space.isQuasicoherent_colimit'` keeps
`CategoryTheory.Limits.HasCoproducts.{max w w'}` on the category of `𝒪_F`-modules, which clause
(2) of Stacks 03M1 does not carry; it comes from presenting a colimit as a cokernel of a map
between two coproducts.  That is an added hypothesis, so those two statements are not
registrations of the tag however unconditional they are otherwise, and they carry no attribute.
The implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentColimitsEssSurj` record why the hypothesis is
there and why it is expected to hold for `max w w' ≤ u`.

## The cokernel half of clause (3) is not restated here

It is already proved, unconditionally and by a different route, as
`AlgebraicGeometry.Space.isQuasicoherentOnSite_cokernel_unconditional` and
`AlgebraicGeometry.Space.isClosedUnderCokernels_quasicoherentSheaves`
(`StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCokernelsUnconditional`), which presents the
cokernel of sheaves of modules as a sheafification and discharges the local step directly — it
needs no instance of Stacks 03DW at all.  The closure statements below consume that declaration
rather than a copy of it, and this file adds no second spelling of the cokernel clause.  No
`@[stacks 03M1]` attribute is added to it either: that is the other file's declaration to
register, and it declines the attribute deliberately.

## What is registered, and what is still open

All three terms of clause (4) are registered below, at module universe `u`; the universe is
forced because the statements name `CategoryTheory.ShortComplex.ShortExact`, so the modules have
to form an abelian category, which at this site holds at `m := u`.  Clause (5) is already
registered, on `AlgebraicGeometry.Space.isQuasicoherentOnSite_tensorModule`.  Clause (1) (direct
sums), clause (2) (arbitrary colimits), clause (3) and clause (6) (internal hom) are not
registered here.

## References

* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w w' u

namespace AlgebraicGeometry.Space

section Implicit

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}

/-! ### The one binder site that only the uniform form of 03DW could reach -/

/-- **The right-hand map of a short exact sequence of `𝒪_F`-modules whose left term is cartesian
on affine charts is surjective on the sections over an affine chart**, with nothing assumed.

This is `AlgebraicGeometry.Space.surjective_g_val_app_of_shortExact_of_h03DW` with its uniform
hypothesis supplied by
`AlgebraicGeometry.Space.surjective_val_app_of_epi_of_kernel_isCartesianOnAffineCharts`.  It is
the one of the eleven binder sites that
`StacksFrontier.AlgebraicGeometry.Spaces.CokernelAffineSurjectivityFromCartesian` could not reach:
the epimorphism is `T.g`, whose source `T.X₂` is not known to be cartesian on affine charts, so
`AlgebraicGeometry.Space.surjective_val_app_of_epi_of_cartesian` does not apply to it. -/
theorem surjective_g_val_app_of_shortExact_of_isCartesian
    (T : ShortComplex (Modules.{u, u} B S hS F hF)) (hT : T.ShortExact)
    (h₁ : IsCartesianOnAffineCharts T.X₁) (U : SmallEtale B S hS F)
    (hU : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U)) :
    Function.Surjective (T.g.val.app (op U)) :=
  surjective_g_val_app_of_shortExact_of_h03DW T hT
    surjective_val_app_of_epi_of_kernel_isCartesianOnAffineCharts h₁ U hU

/-! ### Clause (4), the two-out-of-three property -/

/-- **Stacks 03M1 for short exact sequences, left term, at `m := u`, with nothing assumed.**  The
kernel term of a short exact sequence of `𝒪_F`-modules on an algebraic space is quasi-coherent if
the other two terms are.

No instance of Stacks 03DW occurs, because sections of a short exact sequence are left exact;
this is `AlgebraicGeometry.Space.isQuasicoherent_left_of_shortExact` with its `h03DX` supplied by
`AlgebraicGeometry.Space.isCartesianOnAffineCharts_of_isQuasicoherentOnSite`. -/
@[stacks 03M1 "clause (4), left term, for the small étale site of an algebraic space, at module \
universe u"]
theorem isQuasicoherent_left_of_shortExact'
    (T : ShortComplex (Modules.{u, u} B S hS F hF)) (hT : T.ShortExact)
    [T.X₂.IsQuasicoherentOnSite] [T.X₃.IsQuasicoherentOnSite] :
    T.X₁.IsQuasicoherentOnSite :=
  isQuasicoherent_left_of_shortExact T hT
    (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS F hF)

/-- **Stacks 03M1 for short exact sequences, middle term, at `m := u`, with nothing assumed.**  An
extension of quasi-coherent `𝒪_F`-modules on an algebraic space is quasi-coherent.

This is `AlgebraicGeometry.Space.isQuasicoherent_middle_of_shortExact` with its `h03DX` supplied
by `AlgebraicGeometry.Space.isCartesianOnAffineCharts_of_isQuasicoherentOnSite` and its
`T.g`-specific instance of Stacks 03DW by
`AlgebraicGeometry.Space.surjective_g_val_app_of_shortExact_of_isCartesian`. -/
@[stacks 03M1 "clause (4), middle term, for the small étale site of an algebraic space, at \
module universe u"]
theorem isQuasicoherent_middle_of_shortExact'
    (T : ShortComplex (Modules.{u, u} B S hS F hF)) (hT : T.ShortExact)
    [T.X₁.IsQuasicoherentOnSite] [T.X₃.IsQuasicoherentOnSite] :
    T.X₂.IsQuasicoherentOnSite :=
  isQuasicoherent_middle_of_shortExact T hT
    (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS F hF)
    (fun U hU => surjective_g_val_app_of_shortExact_of_isCartesian T hT
      (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS F hF T.X₁
        ‹T.X₁.IsQuasicoherentOnSite›) U hU)

/-- **Stacks 03M1 for short exact sequences, right term, at `m := u`, with nothing assumed.**  The
quotient term of a short exact sequence of `𝒪_F`-modules on an algebraic space is quasi-coherent
if the other two terms are.

Its two hypotheses are supplied as in
`AlgebraicGeometry.Space.isQuasicoherent_middle_of_shortExact'`. -/
@[stacks 03M1 "clause (4), right term, for the small étale site of an algebraic space, at module \
universe u"]
theorem isQuasicoherent_right_of_shortExact'
    (T : ShortComplex (Modules.{u, u} B S hS F hF)) (hT : T.ShortExact)
    [T.X₁.IsQuasicoherentOnSite] [T.X₂.IsQuasicoherentOnSite] :
    T.X₃.IsQuasicoherentOnSite :=
  isQuasicoherent_right_of_shortExact T hT
    (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS F hF)
    (fun U hU => surjective_g_val_app_of_shortExact_of_isCartesian T hT
      (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS F hF T.X₁
        ‹T.X₁.IsQuasicoherentOnSite›) U hU)

end Implicit

/-! ### The closure properties -/

section Explicit

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- **Clause (2) of Stacks 03M1, with nothing assumed beyond the coproduct hypothesis.**  A
colimit of quasi-coherent `𝒪_F`-modules on an algebraic space is quasi-coherent.

`CategoryTheory.Limits.HasCoproducts.{max w w'}` is an added hypothesis which the source does not
carry, so no attribute is claimed; see the module documentation. -/
theorem isQuasicoherent_colimit' {K : Type w} [Category.{w'} K]
    [HasCoproducts.{max w w'} (Modules.{u, u} B S hS F hF)]
    (D : K ⥤ Modules.{u, u} B S hS F hF) [HasColimit D]
    (hD : ∀ k, (D.obj k).IsQuasicoherentOnSite) :
    (Limits.colimit D).IsQuasicoherentOnSite :=
  isQuasicoherent_colimit_of_h03DX B S hS F hF
    (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS F hF)
    (isClosedUnderCokernels_quasicoherentSheaves B S hS F hF) D hD

end Explicit

end AlgebraicGeometry.Space

end
