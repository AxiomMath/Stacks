module

public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.Proper
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesSituationComparison
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionFinitePresentation.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupEquivalenceRelationTransitivity
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartIdealSheafPreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ResidualSpaceExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSplitQuasiFiniteReduction
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The relative `Proj`s of the blowup along a finitely presented centre lie in the site

The blowup `AlgebraicGeometry.Space.blowUpAlong'` of an algebraic space `X` along a closed
subspace `K` (Stacks 085Q) is glued from three relative `Proj`s of Rees algebras: the one on the
presenting scheme `U` of an étale presentation of `X`, the one on its relation scheme `R` and the
one on the scheme `R ×_U R` of composable pairs.  The construction asks that the big fppf site
contain these three schemes.  This file proves that it does, for every étale presentation, as
soon as the inclusion of `K` is of finite presentation; and that every algebraic space has an
étale presentation.

The argument is the source's: on each of the three charts the ideal which `K` cuts out is the
kernel ideal of the base change of the closed immersion of `K` along an étale chart, which is a
closed immersion locally of finite presentation, so that ideal is finitely generated over every
affine open (Stacks 01TV).  The blowup of a scheme in an ideal which is finitely generated over
every affine open is proper over its base, so it is quasi-compact and locally of finite type
over a scheme of the site, and is therefore itself of size below the cutoff of the site
(Stacks 000R).

## Main results

* `AlgebraicGeometry.Space.contains_relativeProj_reesSituation_of_fg`: the blowup of a scheme of
  the site in an ideal finitely generated over every affine open lies in the site.
* `AlgebraicGeometry.Space.fg_ideal_idealSheafDataOfChart_centreIdeal`: the ideal which a
  finitely presented closed subspace cuts out on any étale chart is finitely generated over
  every affine open of the chart.
* `AlgebraicGeometry.Space.contains_reesProj_of_isFinitePresentation`: the three relative
  `Proj`s of the construction of Stacks 085Q along a finitely presented centre lie in the site,
  for every étale presentation.

## References

* [Stacks Project, Tag 085Q](https://stacks.math.columbia.edu/tag/085Q)
* [Stacks Project, Tag 01TV](https://stacks.math.columbia.edu/tag/01TV)
* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The blowup of a scheme of the site in an ideal of finite type lies in the site.**  If the
ideal sheaf `I` on the scheme underlying an object `Y₀` of the big fppf site is finitely
generated over every affine open, the relative `Proj` of its Rees algebra is isomorphic over
`Y₀` to the blowup (`Stacks.Blowup.reesSituationBlowUpIso`), which is proper over `Y₀`
(`AlgebraicGeometry.isProper_blowUpToBase_of_fg`); it is therefore quasi-compact and locally of
finite type over it, so its size is below the cutoff of the site
(`AlgebraicGeometry.Space.contains_of_locallyOfFiniteType_of_quasiCompact`). -/
theorem contains_relativeProj_reesSituation_of_fg {Y₀ : BigFppfOver B S hS}
    (I : ((BigFppfOver.toScheme B S hS).obj Y₀).IdealSheafData)
    (hfg : ∀ V : ((BigFppfOver.toScheme B S hS).obj Y₀).affineOpens, (I.ideal V).FG) :
    B.Contains (Stacks.Blowup.reesSituation I).relativeProj := by
  have := _root_.AlgebraicGeometry.isProper_blowUpToBase_of_fg I hfg
  exact contains_of_locallyOfFiniteType_of_quasiCompact B S hS
    ((Stacks.Blowup.reesSituationBlowUpIso I).hom ≫ _root_.AlgebraicGeometry.blowUpToBase I)

/-- **A finitely presented closed subspace cuts out an ideal of finite type on every étale
chart.**  For a closed subspace `K` of an algebraic space `X` whose inclusion is of finite
presentation, and for any étale chart `A` of `X`, the ideal sheaf which the defining ideal
sheaf of `K` induces on the scheme of `A` is finitely generated over every affine open.

That ideal sheaf is the kernel of the base change `K ×_X A ⟶ A` of the inclusion of `K`
(`AlgebraicGeometry.Space.ker_rep_snd_eq_idealSheafDataOfChart`), which is a closed immersion
locally of finite presentation because the inclusion of `K` is so on every étale chart; and a
closed immersion of schemes is locally of finite presentation exactly when its kernel is
finitely generated over every affine open (Stacks 01TV,
`AlgebraicGeometry.locallyOfFinitePresentation_iff_fg_ker`).  Unlike
`AlgebraicGeometry.Space.isFinitePresentation_iff_fg_ker_of_surjectiveEtaleChart`, the chart
need not be surjective. -/
@[ega "IV 8.6.1" "partial", sga "3 XI 6.4" "partial"]
theorem fg_ideal_idealSheafDataOfChart_centreIdeal {X : AlgebraicSpaces B S hS}
    (K : ClosedSubspaces B S hS X.obj) (hK : IsFinitePresentation B S hS K.1.ι)
    (A : SmallEtale B S hS X.obj)
    (V : ((BigFppfOver.toScheme B S hS).obj A.1.left).affineOpens) :
    ((idealSheafDataOfChart B S hS X (centreIdeal K) (isCartesianOnAffineCharts_centreIdeal K)
      A).ideal V).FG := by
  have hker := (ker_rep_snd_eq_idealSheafDataOfChart B S hS X K A).symm
  show ((idealSheafDataOfChart B S hS X (definingIdealSheaf B S hS X K)
    (definingIdealSheaf_isCartesianOnAffineCharts B S hS X K) A).ideal V).FG
  rw [hker]
  have hclosed : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (K.2.2.rep.snd A.1.hom)) := K.2.2.property_snd A.1.hom
  have ha : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (K.2.2.rep.fst A.1.hom) :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
      (K.2.2.rep.isPullback A.1.hom).flip A.2
  refine (_root_.AlgebraicGeometry.locallyOfFinitePresentation_iff_fg_ker _).mp ?_ V
  exact hK.1 _ A.1.left (K.2.2.rep.fst A.1.hom) A.1.hom (K.2.2.rep.snd A.1.hom) ha A.2
    ((K.2.2.rep.isPullback A.1.hom).w).symm

/-- **The three relative `Proj`s of the blowup along a finitely presented centre lie in the
site.**  Let `K` be a closed subspace of an algebraic space `X` whose inclusion is of finite
presentation and let `P` be any étale presentation of `X`.  Then the relative `Proj`s of the
Rees algebras of the ideals `K` cuts out on the presenting scheme, on the relation scheme and
on the scheme of composable pairs of `P` are all contained in the big fppf site: these are
exactly the three containment side conditions of the construction of Stacks 085Q,
`AlgebraicGeometry.Space.blowUpAlong'`.

Each of the three ideals is finitely generated over every affine open by
`AlgebraicGeometry.Space.fg_ideal_idealSheafDataOfChart_centreIdeal`, at the étale charts
`AlgebraicGeometry.Space.presentationChart`, `AlgebraicGeometry.Space.presentationRelationChart`
and `AlgebraicGeometry.Space.presentationDoubleChart`, so
`AlgebraicGeometry.Space.contains_relativeProj_reesSituation_of_fg` applies. -/
theorem contains_reesProj_of_isFinitePresentation {X : AlgebraicSpaces B S hS}
    (K : ClosedSubspaces B S hS X.obj) (hK : IsFinitePresentation B S hS K.1.ι)
    (P : Presentation B S hS X.obj X.property) :
    B.Contains (reesChartSituation (centreIdeal K)
        (isCartesianOnAffineCharts_centreIdeal K) P).relativeProj ∧
      B.Contains (reesRelationSituation (centreIdeal K)
        (isCartesianOnAffineCharts_centreIdeal K) P).relativeProj ∧
        B.Contains (reesDoubleSituation (centreIdeal K)
          (isCartesianOnAffineCharts_centreIdeal K) P).relativeProj :=
  ⟨contains_relativeProj_reesSituation_of_fg (Y₀ := P.U) _
      (fg_ideal_idealSheafDataOfChart_centreIdeal K hK (presentationChart P)),
    contains_relativeProj_reesSituation_of_fg (Y₀ := P.R) _
      (fg_ideal_idealSheafDataOfChart_centreIdeal K hK (presentationRelationChart P)),
    contains_relativeProj_reesSituation_of_fg (Y₀ := presentationDouble P) _
      (fg_ideal_idealSheafDataOfChart_centreIdeal K hK (presentationDoubleChart P))⟩

end AlgebraicGeometry.Space

end
