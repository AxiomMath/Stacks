module

public import StacksFrontier.AlgebraicGeometry.Examples.ProjectivityNotLocalOnBase
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.Composition
public import StacksFrontier.AlgebraicGeometry.Examples.HironakaNotProjective
public import StacksFrontier.AlgebraicGeometry.Examples.HironakaLocalModel.OriginFibre

/-!
# Being projective is not local on the base: Hironaka's example

This file proves [Stacks, Tag 08J1] outright: neither projectivity nor quasi-projectivity is
Zariski local on the base, and a fortiori neither is fpqc local on the base.

`StacksFrontier/AlgebraicGeometry/Examples/ProjectivityNotLocalOnBase.lean` reduces both assertions
to the existence of a proper, Zariski-locally projective, non-projective morphism; here that
morphism is constructed, and the reduction is run with the comparisons of Tags 07RL and 0BCL
proved rather than carried.

## The witness

`Stacks.Examples.ProjectivityNotLocalOnBase.ProperLocallyProjectiveNotProjectiveOverQcqs` is the
existence of a proper, Zariski-locally projective, non-projective morphism to a quasi-compact and
quasi-separated scheme. The base is asked to be quasi-compact and quasi-separated because the
quasi-projective half of the tag passes through clause (1) of [Stacks, Tag 0BCL]
(`AlgebraicGeometry.isProjective_iff_isQuasiProjective_and_isProper`), whose setting it is.

`Stacks.Examples.ProjectivityNotLocalOnBase.properLocallyProjectiveNotProjective` proves it with
Hironaka's example ([H, Example B.3.4.1]). Let `Y = ℙ³_k` and let `C`, `D` be the conics
`{xy = z², w = 0}` and `{xy = w², z = 0}`, meeting in `P = [1:0:0:0]` and `Q = [0:1:0:0]`. Over
`Y - Q` blow up `C` and then the strict transform of `D`; over `Y - P` blow up `D` and then the
strict transform of `C`; glue over `Y - {P, Q}`
(`StacksFrontier/AlgebraicGeometry/Examples/HironakaThreefold.lean`). The glued morphism is proper
and locally projective (Divisors, Tag 02NS). It is not projective: the source argues with
`1`-cycles on the fibres over `P` and `Q`; here the same argument is run with Euler
characteristics of invertible modules on those fibres, every fact being computed on one local
model over `𝔸³_k` (`StacksFrontier/AlgebraicGeometry/Examples/HironakaConicChart.lean`,
`StacksFrontier/AlgebraicGeometry/Examples/HironakaLocalModel/`,
`StacksFrontier/AlgebraicGeometry/Examples/HironakaNotProjective.lean`).

## Main results

Both are in the namespace `Stacks.Examples.ProjectivityNotLocalOnBase`.

* `properLocallyProjectiveNotProjective`: Hironaka's example.
* `not_isZariskiLocalAtTarget_and_not_isLocalAtTarget_fpqc`: [Stacks, Tag 08J1].

## References

* [Stacks Project, Tag 08J1](https://stacks.math.columbia.edu/tag/08J1)
* [Stacks Project, Tag 07RL](https://stacks.math.columbia.edu/tag/07RL)
* [Stacks Project, Tag 0BCL](https://stacks.math.columbia.edu/tag/0BCL)
* [H, Example B.3.4.1]
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.Examples.ProjectivityNotLocalOnBase

/-! ### The witness -/

/-- **The witness of [Stacks, Tag 08J1], over a quasi-compact quasi-separated base.** There is a
proper morphism of schemes, to a quasi-compact and quasi-separated scheme, which is
Zariski-locally projective and not projective.

The base is asked to be quasi-compact and quasi-separated because the quasi-projective half of
[Stacks, Tag 08J1] deduces non-quasi-projectivity from properness and non-projectivity by clause
(1) of [Stacks, Tag 0BCL], whose setting it is; the base of Hironaka's example is projective
`3`-space, which is both. -/
def ProperLocallyProjectiveNotProjectiveOverQcqs : Prop :=
  ∃ (V Y : Scheme.{u}) (f : V ⟶ Y), CompactSpace Y ∧ QuasiSeparatedSpace Y ∧
    IsProper f ∧ IsLocallyProjective f ∧ ¬ IsProjective f

/-- A witness over a quasi-compact quasi-separated base is in particular a witness in the sense
of `Stacks.Examples.ProjectivityNotLocalOnBase.ProperLocallyProjectiveNotProjective`. -/
theorem ProperLocallyProjectiveNotProjectiveOverQcqs.properLocallyProjectiveNotProjective
    (hH : ProperLocallyProjectiveNotProjectiveOverQcqs.{u}) :
    ProperLocallyProjectiveNotProjective.{u} := by
  obtain ⟨V, Y, f, -, -, hfproper, hfloc, hfnot⟩ := hH
  exact ⟨V, Y, f, hfproper, hfloc, hfnot⟩

/-- **Hironaka's example** ([H, Example B.3.4.1]; the source of [Stacks, Tag 08J1]). The
morphism `Stacks.Examples.HironakaThreefold.hironakaMorphism` to `ℙ³_k`, for `k = ULift (ZMod 2)`,
is proper and locally projective (`Stacks.Examples.HironakaThreefold.isProper_hironakaMorphism`,
`Stacks.Examples.HironakaThreefold.isLocallyProjective_hironakaMorphism`) and not projective
(`Stacks.Examples.HironakaNotProjective.not_isProjective_hironakaMorphism_of_modelFacts` with
`Stacks.Examples.HironakaLocalModel.modelFacts`). -/
theorem properLocallyProjectiveNotProjective :
    ProperLocallyProjectiveNotProjectiveOverQcqs.{u} :=
  open Stacks.Examples.HironakaNotProjective in
  exists_proper_locallyProjective_not_projective_of_forall_modelFacts
    fun k _ ↦ Stacks.Examples.HironakaLocalModel.modelFacts k

/-! ### The quasi-projective clauses -/

/-- **Quasi-projectivity is not Zariski local on the base, from a witness over a quasi-compact
quasi-separated base.** The second clause of [Stacks, Tag 08J1].

This is the source's argument. Over each member of the covering the morphism is projective, hence
quasi-projective by [Stacks, Tag 07RL] (`AlgebraicGeometry.IsProjective.isQuasiProjective`); so
Zariski-locality would make it quasi-projective, and being proper over a quasi-compact and
quasi-separated base it would then be projective by clause (1) of [Stacks, Tag 0BCL]
(`AlgebraicGeometry.isProjective_iff_isQuasiProjective_and_isProper`), which it is not. -/
theorem not_isZariskiLocalAtTarget_quasiProjectiveProperty_of_overQcqs
    (hH : ProperLocallyProjectiveNotProjectiveOverQcqs.{u}) :
    ¬ IsZariskiLocalAtTarget quasiProjectiveProperty.{u} := by
  obtain ⟨V, Y, f, hYc, hYqs, hfproper, hfloc, hfnot⟩ := hH
  obtain ⟨ι, U, hU, hUf⟩ := hfloc
  refine fun hloc ↦ hfnot ((isProjective_iff_isQuasiProjective_and_isProper f).mpr
    ⟨?_, hfproper⟩)
  exact isQuasiProjective_of_iSup_eq_top hloc U hU fun i ↦ (hUf i).isQuasiProjective

/-- **Quasi-projectivity is not fpqc local on the base, from a witness over a quasi-compact
quasi-separated base.** -/
theorem not_isLocalAtTarget_fpqc_quasiProjectiveProperty_of_overQcqs
    (hH : ProperLocallyProjectiveNotProjectiveOverQcqs.{u}) :
    ¬ quasiProjectiveProperty.{u}.IsLocalAtTarget Scheme.fpqcPrecoverage :=
  fun h ↦ not_isZariskiLocalAtTarget_quasiProjectiveProperty_of_overQcqs hH
    (isZariskiLocalAtTarget_of_isLocalAtTarget_fpqc _ h)

/-! ### Tag 08J1 -/

/-- The properties "`f` is projective" and "`f` is quasi-projective" are not Zariski local on
the base; a fortiori, they are not fpqc local on the base.

The witness is Hironaka's example,
`Stacks.Examples.ProjectivityNotLocalOnBase.properLocallyProjectiveNotProjective`. -/
@[stacks 08J1]
theorem not_isZariskiLocalAtTarget_and_not_isLocalAtTarget_fpqc :
    (¬ IsZariskiLocalAtTarget projectiveProperty.{u} ∧
      ¬ IsZariskiLocalAtTarget quasiProjectiveProperty.{u}) ∧
    (¬ projectiveProperty.{u}.IsLocalAtTarget Scheme.fpqcPrecoverage ∧
      ¬ quasiProjectiveProperty.{u}.IsLocalAtTarget Scheme.fpqcPrecoverage) :=
  have hH := properLocallyProjectiveNotProjective.{u}
  ⟨⟨not_isZariskiLocalAtTarget_projectiveProperty hH.properLocallyProjectiveNotProjective,
      not_isZariskiLocalAtTarget_quasiProjectiveProperty_of_overQcqs hH⟩,
    ⟨not_isLocalAtTarget_fpqc_projectiveProperty hH.properLocallyProjectiveNotProjective,
      not_isLocalAtTarget_fpqc_quasiProjectiveProperty_of_overQcqs hH⟩⟩

end Stacks.Examples.ProjectivityNotLocalOnBase

end
