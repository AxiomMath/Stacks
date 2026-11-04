module

public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.Proper
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.ObjectRestriction
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupEquivalenceRelationTransitivity
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupFinality
public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSite
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartIdealSheafPreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ResidualSpaceExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersionFinitePresentation
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The blowup of an algebraic space in a finitely presented closed subspace exists

Let `S` be a scheme and let `X` be an algebraic space over `S`.  The blowup of `X` along a
closed subspace `Z ⊆ X` is constructed in
`StacksFrontier/AlgebraicGeometry/Spaces/BlowupEquivalenceRelationClosed.lean` as
`AlgebraicGeometry.Space.blowUpAlongHom'` (Tag 085Q), and
`AlgebraicGeometry.Space.isBlowupAlong_blowUpAlongHom'` (Tag 085U) proves that it satisfies the
universal property `AlgebraicGeometry.Space.IsBlowupAlong`.  Both take four inputs beyond `Z`:
an étale presentation `P` of `X`, the universe choice `HasSheafify` for the quotient presheaf,
and three `B.Contains` conditions asking that the relative `Proj`s the construction glues from
— on the presenting scheme, on the relation scheme and on the scheme of composable pairs — be
objects of the big fppf site.

**This file discharges all four**, for a centre whose closed immersion is of finite
presentation, and so proves the plain existence statement

`∃ (X' : AlgebraicSpaces B S hS) (f : X' ⟶ X), IsBlowupAlong B S hS Z f`

with no hypothesis on `X`, on `B` or on `S` beyond `Z` being finitely presented.

## Main results

* `AlgebraicGeometry.Space.fg_ideal_idealSheafDataOfChart_definingIdealSheaf`: the sheaf of
  ideals that the defining ideal sheaf of a finitely presented closed subspace induces on an
  étale scheme chart is finitely generated over every affine open of that chart.
* `AlgebraicGeometry.Space.contains_relativeProj_reesSituation`: the relative `Proj` of the Rees
  algebra of a finitely generated sheaf of ideals on the scheme of an object of the big fppf
  site is again an object of that site.
* `AlgebraicGeometry.Space.contains_reesChartSituation_centreIdeal`,
  `AlgebraicGeometry.Space.contains_reesRelationSituation_centreIdeal` and
  `AlgebraicGeometry.Space.contains_reesDoubleSituation_centreIdeal`: the three `B.Contains`
  conditions of the construction, for a finitely presented centre.
* `AlgebraicGeometry.Space.exists_isBlowupAlong_of_isFinitePresentation`: **the blowup of `X` in
  a finitely presented closed subspace exists.**

## Implementation notes

**Why finite presentation of the centre is what makes the smallness conditions provable.**  A
`B.Contains` condition is the size bound `size < B.cutoff` of the site's set-theoretic
conventions, and the route to it is Stacks 000R (5): the source of a morphism that is locally of
finite type and quasi-compact is no larger than its target.  For the blowup of a *scheme* in a
sheaf of ideals that is finitely generated over every affine open, the structure morphism is
proper by `AlgebraicGeometry.isProper_blowUpToBase_of_fg`, hence locally of finite type and
quasi-compact; the base of each of the three relative `Proj`s is the scheme of an object of the
site, which is contained by `AlgebraicGeometry.BigFppfOver.contains_objScheme`.  So the whole
question is finite generation of the three induced sheaves of ideals, and that is exactly what
finite presentation of `Z ⟶ X` says, read on a chart.

**The two Rees situations.**  `AlgebraicGeometry.isProper_blowUpToBase_of_fg` is proved for
`AlgebraicGeometry.blowUpToBase`, the relative `Proj` of the *chosen* Rees algebra datum, while
the three situations of the construction are built from `Stacks.Blowup.reesSituation`, the
situation of the *explicit* Rees algebra sheaf.  `Stacks.Blowup.reesSituationBlowUpIso`
identifies the two, and `AlgebraicGeometry.Scheme.size_congr` transports the size bound across
it; no geometry is needed for that step.

**Finite generation on a chart.**  `AlgebraicGeometry.Space.ker_rep_snd_eq_idealSheafDataOfChart`
identifies the sheaf of ideals induced on a chart by the defining ideal sheaf of `Z` with the
kernel ideal of the base change `Z ×_X A ⟶ A` of the closed immersion, and
`AlgebraicGeometry.Space.fg_ideal_ker_rep_snd_of_isFinitePresentation` — the forward direction
of Tag 084Q, which needs no surjectivity of the chart — gives finite generation of that kernel
over the affine opens.  Surjectivity is not available for free here: of the three charts only
the presenting scheme is the atlas, so the chart-general form is what this file needs.

**No `@[stacks]` attribute.**  Tag 085Q is a *definition* and is already registered on the
objects it defines; Tag 085U is registered on
`AlgebraicGeometry.Space.isBlowupAlong_blowUpAlongHom'`, of which the existence statement here
is a consequence restricted to a finitely presented centre, hence a special case.  Nothing here
claims a tag.

## References

* [Stacks Project, Tag 085Q](https://stacks.math.columbia.edu/tag/085Q)
* [Stacks Project, Tag 085U](https://stacks.math.columbia.edu/tag/085U)
* [Stacks Project, Tag 084Q](https://stacks.math.columbia.edu/tag/084Q)
* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
* [Stacks Project, Tag 0263](https://stacks.math.columbia.edu/tag/0263)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Finite generation of the chart ideal of a finitely presented centre -/

/-- **The sheaf of ideals that the defining ideal sheaf of a finitely presented closed subspace
induces on an étale scheme chart is finitely generated over every affine open of the chart.**

By `AlgebraicGeometry.Space.ker_rep_snd_eq_idealSheafDataOfChart` that sheaf of ideals is the
kernel ideal of the base change `Z ×_X A ⟶ A` of the closed immersion `Z ⟶ X` along the chart,
and finite generation of that kernel over the affine opens of the chart is the forward direction
of Tag 084Q, `AlgebraicGeometry.Space.fg_ideal_ker_rep_snd_of_isFinitePresentation`. -/
@[sga "3 XI 6.4" "partial"]
theorem fg_ideal_idealSheafDataOfChart_definingIdealSheaf (X : AlgebraicSpaces B S hS)
    (Z : ClosedSubspaces B S hS X.1) (hZ : IsFinitePresentation B S hS Z.1.ι)
    (A : SmallEtale B S hS X.1)
    (V : ((BigFppfOver.toScheme B S hS).obj A.1.left).affineOpens) :
    ((idealSheafDataOfChart B S hS X (definingIdealSheaf B S hS X Z)
      (definingIdealSheaf_isCartesianOnAffineCharts B S hS X Z) A).ideal V).FG := by
  rw [← ker_rep_snd_eq_idealSheafDataOfChart B S hS X Z A]
  exact fg_ideal_ker_rep_snd_of_isFinitePresentation B S hS
    (Z := (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)) (X := X)
    (ObjectProperty.homMk Z.1.ι) Z.2.2 hZ A.2 V

/-! ### The relative Proj of a Rees algebra as an object of the site -/

/-- **The relative `Proj` of the Rees algebra of a finitely generated sheaf of ideals on the
scheme of an object of the big fppf site is again an object of that site.**

The blowup of a scheme in such a sheaf of ideals is proper over it
(`AlgebraicGeometry.isProper_blowUpToBase_of_fg`), hence locally of finite type and
quasi-compact, so Stacks 000R (5) bounds its size by that of the base, which is below the
site's cutoff by `AlgebraicGeometry.BigFppfOver.contains_objScheme`.  The relative `Proj` of the
explicit Rees algebra sheaf is isomorphic to that blowup by
`Stacks.Blowup.reesSituationBlowUpIso`, and size is an isomorphism invariant. -/
theorem contains_relativeProj_reesSituation (T : BigFppfOver B S hS)
    (I : ((BigFppfOver.toScheme B S hS).obj T).IdealSheafData)
    (hfg : ∀ V : ((BigFppfOver.toScheme B S hS).obj T).affineOpens, (I.ideal V).FG) :
    B.Contains (Stacks.Blowup.reesSituation I).relativeProj := by
  have hp : _root_.AlgebraicGeometry.IsProper
      (_root_.AlgebraicGeometry.blowUpToBase I) :=
    _root_.AlgebraicGeometry.isProper_blowUpToBase_of_fg I hfg
  have hb : (_root_.AlgebraicGeometry.blowUp I).size < B.cutoff :=
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact
      (_root_.AlgebraicGeometry.blowUpToBase I)
      (BigFppfOver.contains_objScheme B S hS T)
  show (Stacks.Blowup.reesSituation I).relativeProj.size < B.cutoff
  rw [Scheme.size_congr (Stacks.Blowup.reesSituationBlowUpIso I)]
  exact hb

/-! ### The three smallness conditions of the construction -/

variable {X : AlgebraicSpaces B S hS}

/-- **The relative `Proj` on the presenting scheme of a presentation is an object of the site**,
for a centre whose closed immersion is of finite presentation. -/
theorem contains_reesChartSituation_centreIdeal (Z : ClosedSubspaces B S hS X.1)
    (hZ : IsFinitePresentation B S hS Z.1.ι)
    (P : Presentation B S hS X.obj X.property) :
    B.Contains (reesChartSituation (centreIdeal Z)
      (isCartesianOnAffineCharts_centreIdeal Z) P).relativeProj :=
  contains_relativeProj_reesSituation _ _
    (fg_ideal_idealSheafDataOfChart_definingIdealSheaf X Z hZ (presentationChart P))

/-- **The relative `Proj` on the relation scheme of a presentation is an object of the site**,
for a centre whose closed immersion is of finite presentation. -/
theorem contains_reesRelationSituation_centreIdeal (Z : ClosedSubspaces B S hS X.1)
    (hZ : IsFinitePresentation B S hS Z.1.ι)
    (P : Presentation B S hS X.obj X.property) :
    B.Contains (reesRelationSituation (centreIdeal Z)
      (isCartesianOnAffineCharts_centreIdeal Z) P).relativeProj :=
  contains_relativeProj_reesSituation _ _
    (fg_ideal_idealSheafDataOfChart_definingIdealSheaf X Z hZ (presentationRelationChart P))

/-- **The relative `Proj` on the scheme of composable pairs of a presentation is an object of the
site**, for a centre whose closed immersion is of finite presentation. -/
theorem contains_reesDoubleSituation_centreIdeal (Z : ClosedSubspaces B S hS X.1)
    (hZ : IsFinitePresentation B S hS Z.1.ι)
    (P : Presentation B S hS X.obj X.property) :
    B.Contains (reesDoubleSituation (centreIdeal Z)
      (isCartesianOnAffineCharts_centreIdeal Z) P).relativeProj :=
  contains_relativeProj_reesSituation _ _
    (fg_ideal_idealSheafDataOfChart_definingIdealSheaf X Z hZ (presentationDoubleChart P))

/-! ### Existence of the blowup -/

/-- **The blowup of an algebraic space in a finitely presented closed subspace exists.**  There
are an algebraic space `X'` over `S` and a morphism `f : X' ⟶ X` which is the blowup of `X` in
`Z`, in the sense of the universal property of Tag 085U.

Nothing is assumed beyond finite presentation of the closed immersion `Z ⟶ X`.  The étale
presentation the construction of Tag 085Q needs comes from
`AlgebraicGeometry.Space.presentationOfIsAlgebraicSpace`, the universe choice from
`AlgebraicGeometry.hasSheafify_bigFppfOver`, and the three smallness conditions from the three
`contains_rees…_centreIdeal` results above; being the blowup is then Tag 085U,
`AlgebraicGeometry.Space.isBlowupAlong_blowUpAlongHom'`. -/
theorem exists_isBlowupAlong_of_isFinitePresentation (Z : ClosedSubspaces B S hS X.1)
    (hZ : IsFinitePresentation B S hS Z.1.ι) :
    ∃ (X' : AlgebraicSpaces B S hS) (f : X' ⟶ X), IsBlowupAlong B S hS Z f := by
  let : HasSheafify (BigFppfOver.topology B S hS) (Type u) :=
    AlgebraicGeometry.hasSheafify_bigFppfOver B S hS
  let P : Presentation B S hS X.obj X.property :=
    presentationOfIsAlgebraicSpace B S hS X.obj X.property
  exact ⟨_, _, isBlowupAlong_blowUpAlongHom' Z P
    (contains_reesChartSituation_centreIdeal Z hZ P)
    (contains_reesRelationSituation_centreIdeal Z hZ P)
    (contains_reesDoubleSituation_centreIdeal Z hZ P)⟩

end AlgebraicGeometry.Space

end
