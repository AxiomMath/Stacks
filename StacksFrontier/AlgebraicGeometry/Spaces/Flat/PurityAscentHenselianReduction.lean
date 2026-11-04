module

public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.ImpurityFlatAscent
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.PurityHenselianReductionAffineLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.SpecStalkAffineNhdsSystem

/-!
# Stacks 0CW4 with the ascent of purity to the local base discharged

The reduction carried by this development's Stacks 0CW4,
`AlgebraicGeometry.Space.PurityStrictlyHenselianReduction`, asks for four things of a pointed
base change `(Y₁, y₁) ⟶ (Y, y)` — intended to be `Spec 𝒪_{Y, ȳ} ⟶ Y`. One of the four,
affine locality of the new base, was removed by
`AlgebraicGeometry.Space.PurityReductionAtSpecStalk`, which pins the base change to
`AlgebraicGeometry.Space.PrePureSituation.specStalkPointedOver` and so gets that conjunct from
`AlgebraicGeometry.Space.PrePureSituation.isAffineLocalAt_specStalkPointedOver`. Three were
left: the impurity ascent data of Stacks 0CVA, purity of the base change above its closed
point, and the étale cover of Stacks 0CVW along which the base change is universally pure.

This file removes the second of those three. Purity of the base change above the closed point
of `Spec 𝒪_{V, v}` — the ascent along `Spec 𝒪_{V, v} ⟶ V ⟶ Y` that the source performs
silently — is never needed in the strength in which it was asked for: the only use made of it,
here and in the source, is to put the relative assassin of the base change inside the image of
the étale cover, which is clause (2) of Stacks 0CW3, and over `Spec 𝒪_{V, v}` that containment
follows from purity above `y` *on the original base* together with étaleness of the chart. That
is `relativeWeaklyAssociatedPoints_subset_range_specStalkBaseChange_of_isEtale'`, proved from the
limit presentation of `Spec 𝒪_{V, v}` over the affine open neighbourhoods of `v`, which Stacks
0CV9 turns into the implication (1) ⟹ (4) of Stacks 0CVB.

## Main results

* `AlgebraicGeometry.Space.isUniversallyPureAbove_of_isPureAbove_of_isEtale`: **Stacks 0CW4
  with the ascent discharged.** Purity above `y`, an étale chart of the base through a point
  above `y`, the ascent data of Stacks 0CVA at the base change to the local ring of that chart,
  and an étale cover of the base-changed source along which the module is universally pure,
  give universal purity above `y`. No purity of the base change is assumed.
* `AlgebraicGeometry.Space.isUniversallyPureRelative_of_isPureRelative_of_forall_isEtale`:
  the same at every point of the base, which is the shape Stacks 0CW5 consumes.

## What is and is not achieved

The flatness hypothesis of Stacks 0CW4 is not used by either statement, and neither is
`AlgebraicGeometry.Space.PrePureSituation.IsAffineLocalAt`: the specialization step over the
local base is supplied by the limit presentation instead of by an affine local base with purity.
Both statements are therefore strictly stronger than
`AlgebraicGeometry.Space.isUniversallyPureAbove_of_isPureAbove_of_purityReductionAtSpecStalk`
and than `AlgebraicGeometry.Space.isUniversallyPureAbove_of_isPureAbove`.

What is still assumed is *data*: the chart, the ascent data of Stacks 0CVA, and the cover of
Stacks 0CVW with the universal purity Stacks 05K6 gives along it. Those are the two conjuncts of
`AlgebraicGeometry.Space.PurityReductionAtSpecStalk` that remain open, and this file does not
close either. What it does is remove the third, which is the one the attribute notes of this
development's Stacks 0CWC name as its single missing input.

**The hypotheses are not the conclusion.** `hpure` is purity above `y`, which is strictly weaker
than the universal purity concluded — the two differ exactly by the impurities whose structure
morphism is not quasi-finite, and
`AlgebraicGeometry.Space.isPureAbove_baseChange_iff_forall_exists_isImpurity_isQuasiFiniteAt`
records which reformulations of the gap between them are circular and why these are not among
them. `huniv` is universal purity of the *pullback along the cover* of the base change, a
statement about a different situation on a different space; the conclusion does not give it,
since nothing recovers the module on `X'` from universal purity on `X`. The ascent data of
Stacks 0CVA mentions no purity at all.

## References

* [Stacks Project, Tag 0CW4](https://stacks.math.columbia.edu/tag/0CW4)
* [Stacks Project, Tag 0CW5](https://stacks.math.columbia.edu/tag/0CW5)
* [Stacks Project, Tag 0CW3](https://stacks.math.columbia.edu/tag/0CW3)
* [Stacks Project, Tag 0CVB](https://stacks.math.columbia.edu/tag/0CVB)
* [Stacks Project, Tag 0CVG](https://stacks.math.columbia.edu/tag/0CVG)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] pointTopology

/-- **Stacks 0CW4 with the ascent of purity to the local base discharged.** Let `ℱ` be pure
above `y`, let `a : V ⟶ Y` be an étale chart of the base through a point `v` above `y`, let the
base change of the situation to `Spec 𝒪_{V, v}` admit the impurity ascent data of Stacks 0CVA,
and let `e` be an étale morphism into the base-changed source whose image on points contains the
fibre over the closed point and along which the module pulls back to one universally pure above
that point. Then `ℱ` is universally pure above `y`.

Clause (2) of Stacks 0CW3 over the local base is
`relativeWeaklyAssociatedPoints_subset_range_specStalkBaseChange_of_isEtale'`, which gets the
assassin containment from `hpure` and `hetale` alone; clause (1) carries universal purity along
`e` down to the base change; and part (2) of Stacks 0CVG descends it to `ℱ`.

This is `AlgebraicGeometry.Space.isUniversallyPureAbove_of_isPureAbove` with the conjunct
`IsPureAbove c.baseChange` of its carried reduction removed, and with the flatness hypothesis
and the affine locality of the local base unused. -/
theorem isUniversallyPureAbove_of_isPureAbove_of_isEtale (P : PrePureSituation.{u, u} B S hS)
    (hpure : IsPureAbove P) (V : BigFppfOver B S hS) (a : yoneda.obj V ⟶ P.Y)
    (v : points B S hS (yoneda.obj V)) (hv : pointsMap B S hS (yoneda.obj V) a v = P.y)
    (hetale : IsEtale B S hS a)
    (hascent : HasFlatImpurityAscentData (P.specStalkPointedOver V a v hv))
    (e : EtaleOverSource (P.specStalkPointedOver V a v hv).baseChange)
    (hfibre : pointsMap B S hS (P.specStalkPointedOver V a v hv).baseChange.X
          (P.specStalkPointedOver V a v hv).baseChange.f ⁻¹'
        {(P.specStalkPointedOver V a v hv).baseChange.y} ⊆
      Set.range (pointsMap B S hS e.X'.1 e.g.hom))
    (huniv : IsUniversallyPureAbove e.situation) :
    IsUniversallyPureAbove P :=
  isUniversallyPureAbove_of_isFlatAt P _ hascent.1
    (e.isUniversallyPureAbove_of_isUniversallyPureAbove_situation
      (relativeWeaklyAssociatedPoints_subset_range_specStalkBaseChange_of_isEtale' P V a v hv e
        hpure hetale hfibre)
      huniv)

/-- **Stacks 0CW5, the substantive implication, with the ascent of purity to the local base
discharged.** For a module pure relative to `Y`, if at every point of `Y` there is an étale chart
through a point above it carrying the ascent data of Stacks 0CVA and an étale cover of the
base-changed source with the universal purity of Stacks 05K6, then the module is universally pure
relative to `Y`.

Both notions of Stacks 0CVD quantify over the points of `Y`, so this is
`AlgebraicGeometry.Space.isUniversallyPureAbove_of_isPureAbove_of_isEtale` at each point. The
flatness hypothesis of Stacks 0CW5 is not needed, nor is any purity of a base change. -/
theorem isUniversallyPureRelative_of_isPureRelative_of_forall_isEtale
    (P : PrePureSituation.{u, u} B S hS) (hpure : IsPureRelative P)
    (hred : ∀ y : points B S hS P.Y,
      ∃ (V : BigFppfOver B S hS) (a : yoneda.obj V ⟶ ({ P with y := y } :
            PrePureSituation.{u, u} B S hS).Y) (v : points B S hS (yoneda.obj V))
        (hv : pointsMap B S hS (yoneda.obj V) a v =
          ({ P with y := y } : PrePureSituation.{u, u} B S hS).y),
        IsEtale B S hS a ∧
          HasFlatImpurityAscentData
            (({ P with y := y } : PrePureSituation.{u, u} B S hS).specStalkPointedOver V a v hv) ∧
          ∃ e : EtaleOverSource
              (({ P with y := y } : PrePureSituation.{u, u} B S hS).specStalkPointedOver
                V a v hv).baseChange,
            pointsMap B S hS
                  (({ P with y := y } : PrePureSituation.{u, u} B S hS).specStalkPointedOver
                    V a v hv).baseChange.X
                  (({ P with y := y } : PrePureSituation.{u, u} B S hS).specStalkPointedOver
                    V a v hv).baseChange.f ⁻¹'
                {(({ P with y := y } : PrePureSituation.{u, u} B S hS).specStalkPointedOver
                  V a v hv).baseChange.y} ⊆
                Set.range (pointsMap B S hS e.X'.1 e.g.hom) ∧
              IsUniversallyPureAbove e.situation) :
    IsUniversallyPureRelative P := by
  intro y
  obtain ⟨V, a, v, hv, hetale, hascent, e, hfibre, huniv⟩ := hred y
  exact isUniversallyPureAbove_of_isPureAbove_of_isEtale _ (hpure y) V a v hv hetale hascent e
    hfibre huniv

end AlgebraicGeometry.Space

end
