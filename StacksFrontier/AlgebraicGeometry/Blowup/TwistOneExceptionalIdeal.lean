module

public import StacksFrontier.AlgebraicGeometry.Blowup.TwistOneChartCompare
import StacksCore.Tactic.EgaSgaAttribute

/-!
# `𝒪_{X'}(1)` is the ideal sheaf of the exceptional divisor (Stacks 02OS (3))

Let `X` be a scheme and `ℐ ⊆ 𝒪_X` a quasi-coherent sheaf of ideals, with blowup
`b : X' ⟶ X`. Part (3) of [Stacks, Tag 02OS] says that the twisting sheaf `𝒪_{X'}(1)` of the
blowup is the ideal sheaf of the exceptional divisor, the inverse image `ℐ·𝒪_{X'}` of the centre.
This file proves it, for an arbitrary scheme `X` and an arbitrary quasi-coherent sheaf of ideals.

The comparison is local on the standard affine charts of [Stacks, Tag 0804]: over the chart at a
section `a ∈ ℐ(U)` both sheaves are trivial, and the comparison is "divide by the trivializing
section of the degree-one generator `a⁽¹⁾`, then multiply by the pullback of `a`"
(`AlgebraicGeometry.chartEquiv`). Two charts give the same comparison. When they lie over the
same affine open of the base that is an identity inside a single `Proj`
(`AlgebraicGeometry.chartEquiv_agree_of_eq_base`); in general the two base opens `U`, `U'` only
meet in an open which need not be affine, so there is no chart over `U ⊓ U'` through which the
two could be compared. The identity is therefore checked on the cover of the overlap by the parts
lying over the affine opens inside `U ⊓ U'`, where
`AlgebraicGeometry.chartEquiv_agree_of_le` applies twice, and propagated by the sheaf condition.

## Main definitions

* `AlgebraicGeometry.twistOneLocalEquiv`: the chartwise comparisons, as a glueing datum of
  comparison isomorphisms over the standard affine charts of the blowup.

## Main results

* `AlgebraicGeometry.iSup_chartOpen_eq_top`: the standard affine charts, indexed by pairs
  `(U, a)`, cover the blowup.
* `AlgebraicGeometry.chartEquiv_agree`: **any two chartwise comparisons agree** wherever both are
  defined.
* `AlgebraicGeometry.twistOneIsoExceptionalIdealModule`: **[Stacks, Tag 02OS] part (3)** —
  `𝒪_{X'}(1) ≅ ℐ·𝒪_{X'}`, for an arbitrary scheme and an arbitrary quasi-coherent sheaf of
  ideals.

## References

* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
* [Stacks Project, Tag 0804](https://stacks.math.columbia.edu/tag/0804)
* [Stacks Project, Tag 01MS](https://stacks.math.columbia.edu/tag/01MS)
* [Stacks Project, Tag 00AM](https://stacks.math.columbia.edu/tag/00AM)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Stacks.SheafOfModules Stacks.RelativeProj

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- **The standard affine charts of the blowup cover it**, indexed by an affine open `U` of the
base together with a section of the centre over `U`. This is
`Stacks.BlowUpChartCover.iSup_opensRange_chart_eq_top` with the two indices packed into one. -/
theorem iSup_chartOpen_eq_top :
    (⨆ k : (U : X.affineOpens) × I.ideal U,
      (Stacks.BlowUpChartCover.chartOpen I k.1 k.2).1) = ⊤ := by
  rw [iSup_sigma]
  exact Stacks.BlowUpChartCover.iSup_opensRange_chart_eq_top I

/-- **An open lying in two charts of the blowup is covered by its parts lying over the affine
opens of the base contained in both base opens.** This is what replaces a chart over `U ⊓ U'`,
which does not exist because `U ⊓ U'` need not be affine. -/
theorem le_iSup_inf_opensRange_relativeProjChart
    (k l : (U : X.affineOpens) × I.ideal U) {V : (blowUp I).Opens}
    (hk : V ≤ (Stacks.BlowUpChartCover.chartOpen I k.1 k.2).1)
    (hl : V ≤ (Stacks.BlowUpChartCover.chartOpen I l.1 l.2).1) :
    V ≤ ⨆ T : {T : X.affineOpens // T.1 ≤ k.1.1 ⊓ l.1.1},
      V ⊓ (Situation.relativeProjChart (reesSituation I) T.1).opensRange := by
  intro x hx
  have hxk : blowUpToBase I x ∈ k.1.1 :=
    Stacks.BlowUpChartCover.chartOpen_le I k.1 k.2 (hk hx)
  have hxl : blowUpToBase I x ∈ l.1.1 :=
    Stacks.BlowUpChartCover.chartOpen_le I l.1 l.2 (hl hx)
  obtain ⟨T, hxT, hTle⟩ := Stacks.CartierAffineLocal.exists_affineOpens_le
    (k.1.1 ⊓ l.1.1) (show blowUpToBase I x ∈ k.1.1 ⊓ l.1.1 from ⟨hxk, hxl⟩)
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨T, hTle⟩, hx,
    (Situation.mem_opensRange_relativeProjChart (reesSituation I) T x).mpr hxT⟩

/-- **Any two chartwise comparisons of `𝒪_{X'}(1)` with the exceptional ideal sheaf agree**
wherever both are defined. The two charts lie over two affine opens `U`, `U'` of the base, whose
intersection need not be affine, so the identity cannot be checked inside one `Proj`: it is
checked on the cover of the overlap by the parts lying over the affine opens inside `U ⊓ U'`,
where the two comparisons both agree with a comparison over that smaller affine open
(`AlgebraicGeometry.chartEquiv_agree_of_le`), and those agree with each other because they lie
over the same affine open (`AlgebraicGeometry.chartEquiv_agree_of_eq_base`). The sheaf condition
for the exceptional ideal sheaf propagates the identity back to the overlap. -/
theorem chartEquiv_agree (k l : (U : X.affineOpens) × I.ideal U) {V : (blowUp I).Opens}
    (hk : V ≤ (Stacks.BlowUpChartCover.chartOpen I k.1 k.2).1)
    (hl : V ≤ (Stacks.BlowUpChartCover.chartOpen I l.1 l.2).1)
    (t : ToType ((blowUpTwist I 1).val.obj (op V))) :
    chartEquiv I k.1 k.2 hk t = chartEquiv I l.1 l.2 hl t := by
  refine (OModuleLocalPresheaf.isSheaf_ofSheafOfModules (exceptionalIdealModule I)
      (⊤ : (blowUp I).Opens)).eq_of_locally_eq (hV := le_top)
    (fun T : {T : X.affineOpens // T.1 ≤ k.1.1 ⊓ l.1.1} =>
      V ⊓ (Situation.relativeProjChart (reesSituation I) T.1).opensRange)
    (fun _ => inf_le_left) (le_iSup_inf_opensRange_relativeProjChart I k l hk hl) fun T => ?_
  have side : ∀ (m : (U : X.affineOpens) × I.ideal U) (hTm : T.1 ≤ m.1)
      (hm : V ≤ (Stacks.BlowUpChartCover.chartOpen I m.1 m.2).1)
      (hZ : V ⊓ (Situation.relativeProjChart (reesSituation I) T.1).opensRange
        ≤ (Stacks.BlowUpChartCover.chartOpen I T.1 (restrictIdeal I hTm m.2)).1),
      (exceptionalIdealModule I).val.restrictₛₗ
          (homOfLE (inf_le_left : V ⊓ (Situation.relativeProjChart (reesSituation I)
            T.1).opensRange ≤ V)).op (chartEquiv I m.1 m.2 hm t)
        = chartEquiv I T.1 (restrictIdeal I hTm m.2) hZ
          ((blowUpTwist I 1).val.restrictₛₗ
            (homOfLE (inf_le_left : V ⊓ (Situation.relativeProjChart (reesSituation I)
              T.1).opensRange ≤ V)).op t) := fun m hTm hm hZ =>
    (chartEquiv_map I m.1 m.2 hm inf_le_left t).symm.trans
      (chartEquiv_agree_of_le I hTm m.2 (inf_le_left.trans hm) hZ _)
  have hZ : ∀ (m : (U : X.affineOpens) × I.ideal U) (hTm : T.1 ≤ m.1)
      (hm : V ≤ (Stacks.BlowUpChartCover.chartOpen I m.1 m.2).1),
      V ⊓ (Situation.relativeProjChart (reesSituation I) T.1).opensRange
        ≤ (Stacks.BlowUpChartCover.chartOpen I T.1 (restrictIdeal I hTm m.2)).1 :=
    fun m hTm hm => by
      rw [chartOpen_restrictIdeal_eq I hTm m.2]
      exact le_inf inf_le_right (inf_le_left.trans hm)
  have hTk : T.1 ≤ k.1 := T.2.trans inf_le_left
  have hTl : T.1 ≤ l.1 := T.2.trans inf_le_right
  exact (side k hTk hk (hZ k hTk hk)).trans
    ((chartEquiv_agree_of_eq_base I T.1 (restrictIdeal I hTk k.2)
      (restrictIdeal I hTl l.2) _ _ _).trans (side l hTl hl (hZ l hTl hl)).symm)

/-- **The glueing datum of the comparison of `𝒪_{X'}(1)` with the exceptional ideal sheaf**: the
chartwise comparisons over the standard affine charts of the blowup, which cover it and on which
any two agree. -/
def twistOneLocalEquiv :
    OModuleLocalPresheaf.LocalEquiv
      (OModuleLocalPresheaf.ofSheafOfModules (blowUpTwist I 1) ⊤)
      (OModuleLocalPresheaf.ofSheafOfModules (exceptionalIdealModule I) ⊤)
      ((U : X.affineOpens) × I.ideal U) where
  cover k := (Stacks.BlowUpChartCover.chartOpen I k.1 k.2).1
  cover_le _ := le_top
  le_iSup_cover := (iSup_chartOpen_eq_top I).ge
  equiv k _ hV := chartEquiv I k.1 k.2 hV
  equiv_map k _ _ hV hWV t := chartEquiv_map I k.1 k.2 hV hWV t
  equiv_agree k l _ hk hl t := chartEquiv_agree I k l hk hl t

/-- **[Stacks, Tag 02OS] part (3).** For a scheme `X` and a quasi-coherent sheaf of ideals `ℐ` on
it, the twisting sheaf `𝒪_{X'}(1)` of the blowup `b : X' ⟶ X` of `X` in `ℐ` is the ideal sheaf
of the exceptional divisor, the inverse image `ℐ·𝒪_{X'}` of the centre.

No hypothesis is carried: `X` is an arbitrary scheme and `ℐ` an arbitrary quasi-coherent sheaf of
ideals. Parts (1) and (2) of the tag are
`AlgebraicGeometry.isIso_blowUp_restrict_compl_support` and
`Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal`. -/
@[stacks 02OS "part (3)", ega "IV 19.4.1" "(1)"]
def twistOneIsoExceptionalIdealModule : blowUpTwist I 1 ≅ exceptionalIdealModule I :=
  (twistOneLocalEquiv I).gluedIso

end AlgebraicGeometry

end
