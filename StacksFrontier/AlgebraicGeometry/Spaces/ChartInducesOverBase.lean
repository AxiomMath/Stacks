module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRecoveryOverBase

/-!
# A chart morphism inducing `ψ` over a chart

Let `X` and `Y` be algebraic spaces over a scheme `S` contained in a big fppf site `B`, let `ψ`
be a locally ringed morphism of their small étale ringed topoi which is 2-compatible with the
structure morphisms to `AlgebraicGeometry.Space.baseSpace`, let `T` be an étale scheme chart of
`X`, `V` one of `Y` with affine underlying scheme, and `s : h_T ⟶ ψ⁻¹h_V` a section.

`AlgebraicGeometry.Space.exists_chartHom_twoIso_chartRelocalized` produces from these a morphism
of the site `T ⟶ V` whose morphism of small étale ringed topoi is 2-isomorphic to the
*relocalized* morphism of [Stacks Project, Tag 04J8].  This file rewrites that conclusion into
the form the gluing of steps 5 and 6 of the proof of [Stacks Project, Tag 04KL] consumes: the
composite `T ⟶ V ⟶ Y`, as a morphism of algebraic spaces out of the chart space of `T`, induces
`ψ` restricted to the chart.

The rewriting consumes `AlgebraicGeometry.Space.chartRelocalizedRestrictionTwoIso`, the chartwise
comparison square, and otherwise only the composition law of Stacks 03G8
(`AlgebraicGeometry.Space.smallEtaleRingedToposHom_compTwoIso`) and the identity 2-isomorphism
between the two presentations of the morphism of ringed topoi of an étale morphism
(`AlgebraicGeometry.Space.twoIsoSmallEtaleRestrictionRingedToposHom`).

This single statement is what *both* remaining hypotheses of the gluing need.  Step 5's
refinement coherence compares the morphisms chosen over a chart and over a refinement of it;
both are 2-isomorphic to `ψ` after the same chart by the statement below, so the comparison is
obtained by composing one with the inverse of the other.  Step 6's chartwise hypothesis is the
statement below verbatim, once the glued morphism is known to agree with the chosen one over
the chart.

## Main definitions

* `AlgebraicGeometry.Space.chartToSpaceRepresented` — the structure morphism of an étale chart,
  with its source presented as the representable algebraic space of the chart's object of the
  site.
* `AlgebraicGeometry.Space.chartRelocalizedChartRepresentedTwoIso` — the chartwise comparison
  square in that same presentation.

## Main results

* `AlgebraicGeometry.Space.exists_chartHom_induces` — the chart morphism of
  [Stacks Project, Tag 04KL] induces `ψ` over the chart.
* `AlgebraicGeometry.Space.exists_chartHom_induces_of_hasSomeChartSection` — the same, with the
  chart of `Y` and the section read off the predicate the gluing of step 5 selects its charts
  by.

## Implementation notes

As in `StacksFrontier/AlgebraicGeometry/Spaces/ChartRecoveryOverBase.lean`, the chart space
`AlgebraicGeometry.Space.chartSpace` and the representable algebraic space
`AlgebraicGeometry.Space.yonedaSpace` of the chart's object of the site are the same algebraic
space definitionally, but reconciling the two spellings through a metavariable exhausts the
heartbeat budget.  So the chart's structure morphism and the chartwise comparison square are
each restated once, directedly, in the representable spelling, and the 2-isomorphism is then
assembled with nothing left to guess.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 04J8](https://stacks.math.columbia.edu/tag/04J8)
* [Stacks Project, Tag 04KL](https://stacks.math.columbia.edu/tag/04KL)
-/

@[expose] public section

open CategoryTheory

universe w' u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The structure morphism of an étale chart, with its source presented as the representable
algebraic space of the chart's object of the site.**  It is
`AlgebraicGeometry.Space.chartToSpace`; the two presentations of the source are the same
algebraic space by `AlgebraicGeometry.Space.chartSpace_eq_yoneda`, and this is the one in which
the recovery over the base and the composition law are applied. -/
noncomputable def chartToSpaceRepresented (X : AlgebraicSpaces B S hS)
    (T : SmallEtale B S hS X.1) :
    schemeSpace (chartFppfObject B S hS X T) ⟶ X :=
  chartToSpace B S hS X T

/-- An étale chart's structure morphism is étale, in the representable presentation of its
source. -/
theorem isEtale_chartToSpaceRepresented (X : AlgebraicSpaces B S hS)
    (T : SmallEtale B S hS X.1) :
    IsEtale B S hS (chartToSpaceRepresented B S hS X T).hom :=
  isEtale_chartToSpace B S hS X T

variable (X Y : AlgebraicSpaces B S hS)
    (ψ : RingedToposHom (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y))
    (T : SmallEtale B S hS X.1) (V : SmallEtale B S hS Y.1)
    (s : smallEtaleChartSheaf B S hS X T ⟶
      ψ.toToposHom.inverseImage.obj (smallEtaleChartSheaf B S hS Y V))

/-- `AlgebraicGeometry.Space.chartRelocalizedChartTwoIso`, the chartwise comparison square, with
both chart spaces presented as the representable algebraic spaces of the charts' objects of the
site.  The two presentations are the same algebraic space; this is the one the conclusion of
`AlgebraicGeometry.Space.exists_chartHom_twoIso_chartRelocalized` is stated in. -/
noncomputable def chartRelocalizedChartRepresentedTwoIso :
    RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u}
      (RingedToposHom.comp.{u, u + 1, u, u, u + 1, u, u, u + 1, u}
        (smallEtaleRingedToposHom B S hS (chartToSpaceRepresented B S hS Y V))
        (chartRelocalizedRepresented B S hS X Y ψ T V s))
      (RingedToposHom.comp.{u, u + 1, u, u, u + 1, u, u, u + 1, u} ψ
        (smallEtaleRingedToposHom B S hS (chartToSpaceRepresented B S hS X T))) :=
  chartRelocalizedChartTwoIso B S hS X Y ψ T V s

include s in
/-- **The chart morphism of [Stacks Project, Tag 04KL] induces `ψ` over the chart.**

Let `ψ` be a locally ringed morphism of the small étale ringed topoi of `X` and `Y` which is
2-compatible with the structure morphisms to `AlgebraicGeometry.Space.baseSpace`, let `T` be an
étale scheme chart of `X`, let `V` be one of `Y` whose underlying scheme is affine, and let
`s : h_T ⟶ ψ⁻¹h_V` be a section.  Then there is a morphism of algebraic spaces from the chart
space of `T` to `Y` whose morphism of small étale ringed topoi is 2-isomorphic to `ψ` composed
with the morphism of small étale ringed topoi of the chart.

This is the chartwise datum of steps 5 and 6 of the proof of [Stacks Project, Tag 04KL].  The
morphism produced is the one of
`AlgebraicGeometry.Space.exists_chartHom_twoIso_chartRelocalized`, followed by the chart of
`Y`. -/
theorem exists_chartHom_induces (hψ : ψ.IsLocallyRinged)
    (hV : IsAffineOver B S hS (chartFppfObject B S hS Y V))
    (hc : RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u}
      (RingedToposHom.comp.{u, u + 1, u, u, u + 1, u, u, u + 1, u}
        (smallEtaleRingedToposHom B S hS (toBaseSpace B S hS Y)) ψ)
      (smallEtaleRingedToposHom B S hS (toBaseSpace B S hS X))) :
    ∃ m : schemeSpace (chartFppfObject B S hS X T) ⟶ Y,
      Nonempty (RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u}
        (smallEtaleRingedToposHom B S hS m)
        (RingedToposHom.comp.{u, u + 1, u, u, u + 1, u, u, u + 1, u} ψ
          (smallEtaleRingedToposHom B S hS (chartToSpaceRepresented B S hS X T)))) := by
  obtain ⟨g, ⟨c⟩⟩ := exists_chartHom_twoIso_chartRelocalized B S hS X Y ψ T V s hψ hV hc
  refine ⟨schemeSpaceMap g ≫ chartToSpaceRepresented B S hS Y V, ⟨?_⟩⟩
  have c1 := (smallEtaleRingedToposHom_compTwoIso B S hS (schemeSpaceMap g)
    (chartToSpaceRepresented B S hS Y V)).symm
  have c2 := (RingedToposHom.TwoIso.whiskerRight c
    (smallEtaleRingedToposHom B S hS (chartToSpaceRepresented B S hS Y V))).symm
  have c3 := chartRelocalizedChartRepresentedTwoIso B S hS X Y ψ T V s
  exact c1.trans (c2.trans c3)

/-! ### Comparing two morphisms which induce `ψ` after the same chart

The refinement coherence of step 5 of the proof of [Stacks Project, Tag 04KL] compares the
morphism chosen over a chart, restricted to a refinement of it, with the morphism chosen over
the refinement.  Both induce `ψ` after the refined chart — the first because restriction along
the refinement is 2-isomorphic to the refined chart by the composition law of Stacks 03G8 — so
the comparison is obtained by composing one 2-isomorphism with the inverse of the other.  The
step uses nothing about charts, so it is stated for arbitrary morphisms of algebraic spaces. -/

/-- **Two morphisms of algebraic spaces which induce `ψ` after the same morphism are
2-isomorphic.**  Let `cQ : Q ⟶ X'` and `cP : P ⟶ X'` be morphisms with `ρ ≫ cQ = cP` for some
`ρ : P ⟶ Q`, and let `mQ : Q ⟶ Y'` and `mP : P ⟶ Y'` be morphisms of small étale ringed topoi
2-isomorphic to `ψ` after `cQ` and after `cP` respectively.  Then `ρ ≫ mQ` and `mP` have
2-isomorphic morphisms of small étale ringed topoi.

This is the refinement coherence that the gluing of step 5 of the proof of
[Stacks Project, Tag 04KL] assumes, with `ρ` the refinement; it is assembled from the
composition law of Stacks 03G8 and a reassociation. -/
noncomputable def twoIso_of_induces_of_induces {P Q X' Y' : AlgebraicSpaces B S hS}
    (χ : RingedToposHom (smallEtaleRingedTopos B S hS X') (smallEtaleRingedTopos B S hS Y'))
    (ρ : P ⟶ Q) (cQ : Q ⟶ X') (cP : P ⟶ X') (hρ : ρ ≫ cQ = cP)
    (mQ : Q ⟶ Y') (mP : P ⟶ Y')
    (tQ : SmallEtaleTwoIso B S hS (smallEtaleRingedToposHom B S hS mQ)
      (smallEtaleComp B S hS χ (smallEtaleRingedToposHom B S hS cQ)))
    (tP : SmallEtaleTwoIso B S hS (smallEtaleRingedToposHom B S hS mP)
      (smallEtaleComp B S hS χ (smallEtaleRingedToposHom B S hS cP))) :
    SmallEtaleTwoIso B S hS (smallEtaleRingedToposHom B S hS (ρ ≫ mQ))
      (smallEtaleRingedToposHom B S hS mP) := by
  subst hρ
  have c1 := (smallEtaleRingedToposHom_compTwoIso B S hS ρ mQ).symm
  have c2 := RingedToposHom.TwoIso.whiskerLeft (C := smallEtaleRingedTopos B S hS Y')
    (smallEtaleRingedToposHom B S hS ρ) tQ
  have c3 := (RingedToposHom.TwoIso.associator (smallEtaleRingedToposHom B S hS ρ)
    (smallEtaleRingedToposHom B S hS cQ) χ).symm
  have c4 := RingedToposHom.TwoIso.whiskerRight
    (smallEtaleRingedToposHom_compTwoIso B S hS ρ cQ) χ
  have c5 := tP.symm
  exact c1.trans (c2.trans (c3.trans (c4.trans c5)))

/-- **Precomposing a morphism out of a representable algebraic space with the morphism
represented by a morphism of the site.**  Both sides are the morphism of algebraic spaces on the
composite of the underlying presheaf maps; the statement names the two spellings so that the
gluing's hypothesis, which is stated in the second, can be rewritten into the first. -/
theorem representedSpaceMap_comp_eq_homMk {R R' : BigFppfOver B S hS} (r : R ⟶ R')
    (m : schemeSpace R' ⟶ Y) :
    schemeSpaceMap r ≫ m =
      (ObjectProperty.homMk (yoneda.map r ≫ m.hom) : schemeSpace R ⟶ Y) :=
  rfl

/-- A morphism out of a representable algebraic space is the morphism of algebraic spaces on its
own underlying presheaf map. -/
theorem homMk_hom_self {R : BigFppfOver B S hS} (m : schemeSpace R ⟶ Y) :
    (ObjectProperty.homMk m.hom : schemeSpace R ⟶ Y) = m :=
  rfl

/-- **The refinement coherence of step 5 of the proof of [Stacks Project, Tag 04KL].**  Given a
family of morphisms `m R c` indexed by the selected charts of `X`, each inducing `ψ` after its
own chart, the morphism chosen over a chart `c` restricted along a refinement `r` and the
morphism chosen over the refined chart `r ≫ c` have 2-isomorphic morphisms of small étale ringed
topoi.

This is `AlgebraicGeometry.Space.twoIso_of_induces_of_induces` at the two chosen morphisms, in
the spelling the gluing's hypothesis uses.  The selecting predicate is arbitrary: the coherence
uses only that both morphisms induce `ψ` after the refined chart. -/
theorem nonempty_twoIso_chartHoms_of_induces
    {P : ∀ R : BigFppfOver B S hS, (yoneda.obj R ⟶ X.1) → Prop}
    (m : ∀ (R : BigFppfOver B S hS) (c : yoneda.obj R ⟶ X.1), P R c →
      (schemeSpace R ⟶ Y))
    (hm : ∀ (R : BigFppfOver B S hS) (c : yoneda.obj R ⟶ X.1) (hP : P R c),
      Nonempty (RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u}
        (smallEtaleRingedToposHom B S hS (m R c hP))
        (RingedToposHom.comp.{u, u + 1, u, u, u + 1, u, u, u + 1, u} ψ
          (smallEtaleRingedToposHom B S hS (etaleChartToSpace B S hS c)))))
    (R R' : BigFppfOver B S hS) (r : R ⟶ R') (c : yoneda.obj R' ⟶ X.1)
    (hPc : P R' c) (hPrc : P R (yoneda.map r ≫ c)) :
    Nonempty (RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u}
      (smallEtaleRingedToposHom B S hS
        (ObjectProperty.homMk (yoneda.map r ≫ (m R' c hPc).hom) :
          schemeSpace R ⟶ Y))
      (smallEtaleRingedToposHom B S hS
        (ObjectProperty.homMk (m R (yoneda.map r ≫ c) hPrc).hom :
          schemeSpace R ⟶ Y))) := by
  rw [← representedSpaceMap_comp_eq_homMk B S hS Y r (m R' c hPc),
    homMk_hom_self B S hS Y (m R (yoneda.map r ≫ c) hPrc)]
  exact ⟨twoIso_of_induces_of_induces B S hS ψ (schemeSpaceMap r)
    (etaleChartToSpace B S hS c) (etaleChartToSpace B S hS (yoneda.map r ≫ c))
    (ObjectProperty.hom_ext _ rfl) (m R' c hPc) (m R (yoneda.map r ≫ c) hPrc)
    (hm R' c hPc).some (hm R (yoneda.map r ≫ c) hPrc).some⟩

/-! ### The chart-choice function of step 5 -/

/-- **The chartwise morphism attached to a chart selected by a covering family of affine charts
of `Y`.**  This is `AlgebraicGeometry.Space.exists_chartHom_induces` with the chart of `Y` and
the section read off the predicate
`AlgebraicGeometry.Space.HasSomeChartSection` which the gluing of step 5 of the proof of
[Stacks Project, Tag 04KL] selects its charts by: a selected chart carries a section of
`ψ⁻¹h_{W i}` for some `i`, and a section of a sheaf over an object of the small étale site is a
morphism out of the sheaf represented by that object.

Choosing a value of the existential for every selected chart is the chart-choice function the
gluing consumes. -/
theorem exists_chartHom_induces_of_hasSomeChartSection {I : Type w'}
    (hψ : ψ.IsLocallyRinged)
    (hc : RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u}
      (RingedToposHom.comp.{u, u + 1, u, u, u + 1, u, u, u + 1, u}
        (smallEtaleRingedToposHom B S hS (toBaseSpace B S hS Y)) ψ)
      (smallEtaleRingedToposHom B S hS (toBaseSpace B S hS X)))
    (W : I → SmallEtale B S hS Y.1)
    (hW : ∀ i, IsAffineOver B S hS (chartFppfObject B S hS Y (W i)))
    (R : BigFppfOver B S hS) (b : yoneda.obj R ⟶ X.1)
    (hPb : HasSomeChartSection B S hS X.1
      (fun i => ψ.toToposHom.inverseImage.obj (smallEtaleChartSheaf B S hS Y (W i))) R b) :
    ∃ m : schemeSpace R ⟶ Y,
      Nonempty (RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u}
        (smallEtaleRingedToposHom B S hS m)
        (RingedToposHom.comp.{u, u + 1, u, u, u + 1, u, u, u + 1, u} ψ
          (smallEtaleRingedToposHom B S hS (etaleChartToSpace B S hS b)))) := by
  obtain ⟨hbchart, i, ⟨x⟩⟩ := hPb
  exact exists_chartHom_induces B S hS X Y ψ ⟨CostructuredArrow.mk b, hbchart⟩ (W i)
    ⟨yonedaEquiv.symm x⟩ hψ (hW i) hc

end AlgebraicGeometry.Space

end
