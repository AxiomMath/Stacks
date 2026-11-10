module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackGradedAlgebra
import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.ZeroTwist
public import StacksFrontier.AlgebraicGeometry.RelativeProjTwistQcoh.Basic
import StacksFrontier.AlgebraicGeometry.ThetaMultiplicative.Basic

/-!
# The degree-zero twist on a relative projective spectrum is the structure sheaf

Let `S` be a scheme, `A` a commutative, nonnegatively graded, quasi-coherent graded
`𝒪_S`-algebra, and `D` a `Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData` for `A` — the
structure Tag 01NR produces: the integer-graded sheaf of algebras of twists on the relative
Proj of `A`, together with its identifications with the absolute twists on every affine chart.

This file proves that the **unit of that graded algebra is an isomorphism**: the degree-zero
piece of the algebra of twists is the structure sheaf of the relative Proj, by the map carrying
a local section `r` to `r` times the algebra unit.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjTwistUnit.pieceZeroIsoUnit`: the degree-zero piece of
  the graded algebra of twists, identified with the structure sheaf of the relative Proj.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjTwistUnit.isIso_oneHom`: **the unit
  `𝒪 ⟶ (D.algebra).piece 0` of the graded algebra of twists on a relative Proj is invertible**,
  for an arbitrary `TwistData` — no hypothesis on the base scheme and none on the graded
  algebra beyond the chart identifications the twist datum already carries.
* `Stacks.AlgebraicGeometry.RelativeProjTwistUnit.pieceZeroIsoUnit` and
  `pieceZeroIsoUnit_one`: that invertibility as the isomorphism
  `(D.algebra).piece 0 ≅ 𝒪` together with its normalisation — it carries the algebra unit to
  `1` — which is the pair of hypotheses
  `SheafOfModules.GradedAlgebra.isIso_unitalHom_app_zero` and
  `bijective_smul_one_of_pieceZeroIsoUnit` are stated on.
* `Stacks.AlgebraicGeometry.RelativeProjTwistUnit.chart_oneHom_eq_twistUnitMap`: the
  identification behind it. Restricted to a chart and read through the chart identification in
  degree zero, the unit of the glued algebra *is* the unit
  `Stacks.AlgebraicGeometry.ProjTwistCompare.twistUnitMap` of the absolute graded twisting
  algebra on that chart.
* `Stacks.AlgebraicGeometry.RelativeProjTwistUnit.absoluteTwistUnit_eq_unitSection`: the unit
  section of the degree-zero absolute twist, as the chart identifications of a twist datum see
  it, is the image of `1` under that absolute unit. Both have the value `1` at every point.

## The route

Invertibility is local on the relative Proj
(`Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_restrict`), and the inverse images
of the affine opens of the base cover it
(`Stacks.AlgebraicGeometry.RelativeProjTwistGlue.iSup_toBase_preimage_eq_top`). This is the
only available route: the chart identifications of a `TwistData` carry **no cocycle
condition**, so they cannot be glued into a global isomorphism; invertibility has to be checked
chartwise and descended.

Over the inverse image of one affine open `U` the glued degree-zero piece restricts, along the
chart, to the absolute twist `𝒪_{Proj Γ(A, U)}(0)`, which is the structure sheaf of that
absolute Proj by `Stacks.AlgebraicGeometry.ProjEulerSequence.isIso_twistUnitMap`. What has to
be checked is that the restriction of the glued *unit* is the absolute unit under that
identification, and that is the `isGradedChartIso` field of the twist datum, in the form
`Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData.chartIso_one`: both morphisms go out of
the unit sheaf of modules, so by `LinearMap.ext_ring` they agree as soon as they agree on the
section `1`, and there the glued unit is `1 • D.algebra.one`, which `chartIso_one` identifies
with `Stacks.AlgebraicGeometry.RelativeProjTwists.absoluteTwistUnit`.

## Implementation notes

The chart identification compares the restriction along the **chart**, while the locality
criterion is stated for the restriction along the inclusion of an open subscheme. The two are
compared exactly as in `Stacks.AlgebraicGeometry.RelativeProjTwistQcoh.isQuasicoherent_piece`:
`RelativeProjTwistQcoh.chartIsoPreimage` identifies the inverse image of `U` with
`Proj Γ(A, U)` over the relative Proj, so `Scheme.Modules.restrictFunctorCongr` and
`Scheme.Modules.restrictFunctorComp` exhibit the restriction functor along the inclusion as the
restriction along the chart followed by a restriction along an isomorphism, and
`CategoryTheory.NatIso.isIso_map_iff` transports invertibility across that natural
isomorphism. The transport is done with `NatIso.isIso_map_iff` applied as a term rather than
rewritten with: `rw` rejects the equation as not type-correct, because the source of the unit
morphism is written in `CategoryTheory.SheafOfModules` while the restriction functor is written
in `AlgebraicGeometry.Scheme.Modules`, and those are two spellings of one category.

For the same reason the two cancellations of isomorphisms are
`CategoryTheory.IsIso.of_isIso_comp_left` and `of_isIso_comp_right` applied with their instance
arguments **passed explicitly**: instance
search does not find an `IsIso` hypothesis whose statement was produced by rewriting inside the
other spelling. This is the hazard the implementation notes of
`StacksFrontier/AlgebraicGeometry/AffineBaseChange/Basic.lean` record.

## What is not done here

No `TwistData` is constructed; this is a theorem about an arbitrary one, as every result about
the relative twists in this library is. Nothing is proved about the pieces in nonzero degree,
and no comparison of the graded algebra of twists with the absolute graded twisting algebra is
made beyond degree zero. No `stacks` attribute is attached: Tag 01NR asserts the existence and
uniqueness of the twist data, and this file asserts neither — it is the degree-zero
normalisation that the consumers of
`SheafOfModules.GradedAlgebra.isIso_unitalHom_app_zero` require of a graded algebra, supplied
here for the relative Proj.

## References

* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01MP](https://stacks.math.columbia.edu/tag/01MP)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjTwistSections
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjTwists

namespace Stacks.AlgebraicGeometry.RelativeProjTwistUnit

universe u

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

section Absolute

variable {R : Type u} {σ : Type u} [CommRing R] [SetLike σ R] [AddSubgroupClass σ R]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- **The unit section of the degree-zero absolute twist is the image of `1` under the unit of
the absolute graded twisting algebra.** The left-hand side is the section the chart
identifications of a twist datum are tested against, the right-hand side is the one the
comparison `𝒪_{Proj 𝒜} ⟶ 𝒪_{Proj 𝒜}(0)` produces; both have the value `1` at every point. -/
theorem absoluteTwistUnit_eq_unitSection (W : (AlgebraicGeometry.Proj 𝒜).Opens) :
    absoluteTwistUnit 𝒜 W = ProjTwistCompare.unitSection 𝒜 W 1 :=
  Subtype.ext (funext fun x => (ThetaMultiplicative.absoluteTwistUnit_apply 𝒜 W x).trans
    HomogeneousLocalization.val_one.symm)

end Absolute

section Relative

variable {S : Scheme.{u}} {A : SheafGradedAlgebra S}

/-- An isomorphism of sheaves of modules sends the value of its inverse back to the original
local section. -/
private theorem hom_app_inv_app {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat} {X Y : SheafOfModules R} (e : X ≅ Y) (V : Cᵒᵖ) (y : Y.val.obj V) :
    e.hom.val.app V (e.inv.val.app V y) = y :=
  congrFun (congrArg (fun g => ⇑(ConcreteCategory.hom ((SheafOfModules.Hom.val g).app V)))
    e.inv_hom_id) y

/-- **On a chart, the unit of the glued graded algebra is the unit of the absolute graded
twisting algebra.** Restrict the unit `𝒪 ⟶ (D.algebra).piece 0` along the chart over an affine
open `U` of the base, identify its source with the structure sheaf of `Proj Γ(A, U)` and its
target with the absolute twist `𝒪(0)` by the chart identification of the twist datum; the
result is `Stacks.AlgebraicGeometry.ProjTwistCompare.twistUnitMap`.

Both sides go out of the unit sheaf of modules, so they agree as soon as they agree on the
section `1`; there the left-hand side is the algebra unit, which the `chartIso_one` field of
the twist datum identifies with the absolute unit section. -/
theorem chart_oneHom_eq_twistUnitMap (D : TwistData A) (U : S.Opens) (hU : IsAffineOpen U) :
    letI := D.chartData.chart_isOpenImmersion U hU
    (Scheme.Modules.restrictUnitIso ((relativeProj A).chart U hU)).inv ≫
      (Scheme.Modules.restrictFunctor ((relativeProj A).chart U hU)).map
        (SheafOfModules.GradedAlgebra.oneHom D.algebra) ≫
          (D.chartData.chartIso U hU 0).hom =
      ProjTwistCompare.twistUnitMap (A.grading U) := by
  let := D.chartData.chart_isOpenImmersion U hU
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V => ModuleCat.hom_ext
    (LinearMap.ext_ring ?_))
  change (D.chartData.chartIso U hU 0).hom.val.app V
      (((Scheme.Modules.restrictFunctor ((relativeProj A).chart U hU)).map
        (SheafOfModules.GradedAlgebra.oneHom D.algebra)).val.app V
          ((Scheme.Modules.restrictUnitIso ((relativeProj A).chart U hU)).inv.val.app V
            (1 : Γ(AlgebraicGeometry.Proj (A.grading U), V.unop)))) =
    ProjTwistCompare.unitSection (A.grading U) V.unop 1
  have h1 : ((Scheme.Modules.restrictUnitIso ((relativeProj A).chart U hU)).inv.val.app V)
      (1 : Γ(AlgebraicGeometry.Proj (A.grading U), V.unop)) =
      (1 : Γ((relativeProj A).scheme, ((relativeProj A).chart U hU) ''ᵁ V.unop)) :=
    map_one (ConcreteCategory.hom (((relativeProj A).chart U hU).appIso V.unop).inv)
  rw [h1]
  have h2 : (((Scheme.Modules.restrictFunctor ((relativeProj A).chart U hU)).map
      (SheafOfModules.GradedAlgebra.oneHom D.algebra)).val.app V)
      (1 : Γ((relativeProj A).scheme, ((relativeProj A).chart U hU) ''ᵁ V.unop)) =
      D.algebra.one.eval (op (((relativeProj A).chart U hU) ''ᵁ V.unop)) :=
    (SheafOfModules.GradedAlgebra.oneHom_val_app D.algebra
      (op (((relativeProj A).chart U hU) ''ᵁ V.unop)) 1).trans (one_smul _ _)
  rw [h2, ← D.chartIso_one U hU V.unop]
  refine Eq.trans ?_ (absoluteTwistUnit_eq_unitSection (A.grading U) V.unop)
  exact hom_app_inv_app _ _ _

/-- **The unit of the glued graded algebra is invertible on every chart.** It is the absolute
unit `𝒪_{Proj Γ(A, U)} ⟶ 𝒪(0)` up to two isomorphisms, and that absolute unit is invertible by
`Stacks.AlgebraicGeometry.ProjEulerSequence.isIso_twistUnitMap`. -/
theorem isIso_restrict_chart_oneHom (D : TwistData A) (U : S.Opens) (hU : IsAffineOpen U) :
    letI := D.chartData.chart_isOpenImmersion U hU
    IsIso ((Scheme.Modules.restrictFunctor ((relativeProj A).chart U hU)).map
      (SheafOfModules.GradedAlgebra.oneHom D.algebra)) := by
  let := D.chartData.chart_isOpenImmersion U hU
  have hiso : IsIso (ProjTwistCompare.twistUnitMap (A.grading U)) :=
    ProjEulerSequence.isIso_twistUnitMap (A.grading U)
  rw [← chart_oneHom_eq_twistUnitMap D U hU] at hiso
  have hi1 : IsIso (Scheme.Modules.restrictUnitIso ((relativeProj A).chart U hU)).inv :=
    (Scheme.Modules.restrictUnitIso ((relativeProj A).chart U hU)).isIso_inv
  have hi2 : IsIso (D.chartData.chartIso U hU 0).hom :=
    (D.chartData.chartIso U hU 0).isIso_hom
  have h2 : IsIso ((Scheme.Modules.restrictFunctor ((relativeProj A).chart U hU)).map
      (SheafOfModules.GradedAlgebra.oneHom D.algebra) ≫
        (D.chartData.chartIso U hU 0).hom) :=
    @IsIso.of_isIso_comp_left _ _ _ _ _
      (Scheme.Modules.restrictUnitIso ((relativeProj A).chart U hU)).inv
      ((Scheme.Modules.restrictFunctor ((relativeProj A).chart U hU)).map
        (SheafOfModules.GradedAlgebra.oneHom D.algebra) ≫
          (D.chartData.chartIso U hU 0).hom) hi1 hiso
  exact @IsIso.of_isIso_comp_right _ _ _ _ _
    ((Scheme.Modules.restrictFunctor ((relativeProj A).chart U hU)).map
      (SheafOfModules.GradedAlgebra.oneHom D.algebra))
    (D.chartData.chartIso U hU 0).hom hi2 h2

/-- **The unit of the glued graded algebra is invertible on the inverse image of an affine open
of the base.** The chart over `U` is an open immersion with that inverse image as its range, so
restricting along the inclusion of the inverse image is restricting along the chart followed by
a restriction along an isomorphism. -/
theorem isIso_restrict_preimage_oneHom (D : TwistData A) (U : S.Opens) (hU : IsAffineOpen U) :
    IsIso ((Scheme.Modules.restrictFunctor
      ((relativeProj A).toBase ⁻¹ᵁ U).ι).map
        (SheafOfModules.GradedAlgebra.oneHom D.algebra)) := by
  let := D.chartData.chart_isOpenImmersion U hU
  have e : Scheme.Modules.restrictFunctor (((relativeProj A).toBase ⁻¹ᵁ U).ι) ≅
      Scheme.Modules.restrictFunctor ((relativeProj A).chart U hU) ⋙
        Scheme.Modules.restrictFunctor
          (RelativeProjTwistQcoh.chartIsoPreimage (A := A) U hU).hom :=
    (Scheme.Modules.restrictFunctorCongr
      (RelativeProjTwistQcoh.chartIsoPreimage_hom_comp U hU)).symm ≪≫
        Scheme.Modules.restrictFunctorComp _ _
  have := isIso_restrict_chart_oneHom D U hU
  refine (NatIso.isIso_map_iff e (SheafOfModules.GradedAlgebra.oneHom D.algebra)).mpr ?_
  exact Functor.map_isIso (Scheme.Modules.restrictFunctor
    (RelativeProjTwistQcoh.chartIsoPreimage (A := A) U hU).hom) _

/-- **The degree-zero piece of the graded algebra of twists on a relative Proj is the structure
sheaf.** The unit `𝒪 ⟶ (D.algebra).piece 0`, which carries a local section `r` to `r` times the
algebra unit, is an isomorphism — for an arbitrary twist datum, with no hypothesis on the base
scheme and none on the graded algebra of the base.

Invertibility is local, the inverse images of the affine opens of the base cover the relative
Proj, and over one of them the unit is the unit of the absolute graded twisting algebra, which
is invertible because the zeroth twist on an absolute Proj is its structure sheaf. -/
theorem isIso_oneHom (D : TwistData A) :
    IsIso (SheafOfModules.GradedAlgebra.oneHom D.algebra) :=
  Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_restrict _
    (fun U : S.affineOpens => (relativeProj A).toBase ⁻¹ᵁ (U.1 : S.Opens))
    (RelativeProjTwistGlue.iSup_toBase_preimage_eq_top (relativeProj A))
    (fun i => isIso_restrict_preimage_oneHom D i.1 i.2)

/-- **The degree-zero piece of the graded algebra of twists is the structure sheaf**, as an
isomorphism: the inverse of the unit. This is the shape the degree-zero machinery of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GradedAlgebraDegreeZeroIso.lean` takes as a
hypothesis. -/
def pieceZeroIsoUnit (D : TwistData A) :
    D.algebra.piece 0 ≅ SheafOfModules.unit
      (Stacks.CategoryTheory.RingedSite.ofScheme (relativeProj A).scheme).ringSheaf :=
  let := isIso_oneHom D
  (asIso (SheafOfModules.GradedAlgebra.oneHom D.algebra)).symm

/-- The identification of degree zero with the structure sheaf is normalised: it carries the
algebra unit to `1`. -/
theorem pieceZeroIsoUnit_one (D : TwistData A)
    (V : (relativeProj A).scheme.Opensᵒᵖ) :
    (pieceZeroIsoUnit D).hom.val.app V (D.algebra.one.eval V) =
      (1 : Γ((relativeProj A).scheme, V.unop)) := by
  have h : (pieceZeroIsoUnit D).inv.val.app V (1 : Γ((relativeProj A).scheme, V.unop)) =
      D.algebra.one.eval V :=
    (SheafOfModules.GradedAlgebra.oneHom_val_app D.algebra V 1).trans (one_smul _ _)
  rw [← h]
  exact hom_app_inv_app _ _ _

end Relative

end Stacks.AlgebraicGeometry.RelativeProjTwistUnit

end
