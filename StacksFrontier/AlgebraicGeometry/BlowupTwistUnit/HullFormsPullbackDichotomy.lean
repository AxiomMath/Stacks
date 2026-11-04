module

public import StacksFrontier.AlgebraicGeometry.BlowupTwistUnit.PointBlowupDichotomyUnconditional
public import StacksFrontier.AlgebraicGeometry.BlowupTwistUnit.PullbackHullComparison

/-!
# The twist dichotomy with the top forms upstairs read as a pullback from the base

Let `W` be an integral regular Noetherian scheme of dimension two over `S`, let `w ∈ W` be a
closed point and let `b : W' ⟶ W` be the blowing up of `W` in the reduced point `{w}`. Write
`L = (Ω^r_{W/S₀})^{**}` for the determinant line bundle of the relative differentials, which is
`Stacks.BlowupTwistUnit.hullForms p r h`. The dichotomy of [Stacks, Tag 0B3T] delivers

`Ω^r_{W'/S₀} ^{**} ≅ 𝒪_{W'}(E) ⊗ (⋀^r b^*Ω_{W/S₀})^{**}`  or  `≅ (⋀^r b^*Ω_{W/S₀})^{**}`,

with the reflexive hull of the top exterior power of the *pullback* on the right. The induction
of [Stacks, Tag 0B4T] needs the pullback of the *hull*, `b^*L`, because that is the module whose
derived direct image the projection formula computes. This file replaces the one by the other,
using the comparison `Stacks.BlowupTwistUnit.reflexiveHullExteriorPowerPullbackIso`.

## Main results

The elided prefix is `Stacks.BlowupTwistUnit`.

* `nonempty_tensorIso_or_nonempty_iso_pullbackHullForms_vanishingIdeal_singleton`: **the
  dichotomy with `(⋀^r b^*Ω)^{**}` replaced by `b^*((Ω^r_{W/S₀})^{**})`**, under the reflexivity
  of `⋀^r Ω_{W/S₀}` that the replacement costs.
* `nonempty_tensorIso_or_nonempty_iso_pullbackHullForms_of_isFiniteLocallyFree`: the same with
  that reflexivity replaced by finite local freeness of `⋀^r Ω_{W/S₀}`, under which it holds
  automatically — the shape the base of the induction of [Stacks, Tag 0B4T] has, where
  `Ω_{A/A₀}` is free of rank `r`.

## Implementation notes

*Why two opens appear.* The dichotomy reads the generic rank of the differentials on a nonempty
open of the blowup, and the comparison reads it on a nonempty open of `W`; neither statement
produces the other's open, so both are arguments. On an integral scheme any nonempty open would
do, and `Stacks.BlowupTwistUnit.exists_open_isFiniteLocallyFreeOfRank_over_pointBlowup` derives
the upstairs open from the downstairs one; it is not used here, so that nothing is assumed about
the two beyond nonemptiness.

*The hypothesis on `⋀^r Ω_{W/S₀}` is not removable*, and is exactly the hypothesis of
`Stacks.BlowupTwistUnit.reflexiveHullExteriorPowerPullbackIso`. Without it the identity fails:
if `⋀^r Ω_{W/S₀}` is not reflexive at `w`, then `b^*` of the canonical map
`⋀^r Ω_{W/S₀} ⟶ (Ω^r_{W/S₀})^{**}` fails to be an isomorphism along the whole exceptional
divisor. The two alternatives differ by that divisor, and the hull does not forget a divisor's
worth of discrepancy.

**No `@[stacks]` attribute is placed.** What is below is [Stacks, Tag 0B3T] in a different
spelling of one of its two sides, and that tag is registered where it is proved; the spelling
change is an input of the inductive step of [Stacks, Tag 0B4T] and is not asserted by the source.

## References

* [Stacks Project, Tag 0B3T](https://stacks.math.columbia.edu/tag/0B3T)
* [Stacks Project, Tag 0B4L](https://stacks.math.columbia.edu/tag/0B4L)
* [Stacks Project, Tag 0B4T](https://stacks.math.columbia.edu/tag/0B4T)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace Stacks.BlowupTwistUnit

variable {S₀ S W : Scheme.{u}} [IsNoetherian W] [AlgebraicGeometry.IsIntegral W]

/-- **The twist dichotomy at a blowup in a closed point of a regular surface, with the top forms
upstairs compared to the pullback of the determinant line bundle downstairs.**

Either `(Ω^r_{W'/S₀})^{**} ≅ 𝒪_{W'}(E) ⊗ b^*((Ω^r_{W/S₀})^{**})` or
`(Ω^r_{W'/S₀})^{**} ≅ b^*((Ω^r_{W/S₀})^{**})`.

This is
`Stacks.BlowupTwistUnit.nonempty_tensorIso_or_nonempty_iso_hullForms_vanishingIdeal_singleton'`
with the reflexive hull of the top exterior power of `b^*Ω_{W/S₀}` rewritten by
`Stacks.BlowupTwistUnit.pullbackHullForms_iso` as the pullback of
`Stacks.BlowupTwistUnit.hullForms`, inside the tensor product in the first alternative and
directly in the second. -/
theorem nonempty_tensorIso_or_nonempty_iso_pullbackHullForms_vanishingIdeal_singleton
    (hreg : AlgebraicGeometry.IsRegular W) (hdim : topologicalKrullDim W = 2)
    (w : W) (hw : IsClosed ({w} : Set W))
    (hstalkdim : ringKrullDim (W.presheaf.stalk w) = 2) (p : S ⟶ S₀) (h : W ⟶ S) (r : ℕ)
    [(Scheme.Hom.relativeDifferentials (h ≫ p)).IsCoherent]
    [((Scheme.Modules.pullback (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))).obj
        (Scheme.Hom.relativeDifferentials (h ≫ p))).IsCoherent]
    [(Scheme.Hom.relativeDifferentials
        (AlgebraicGeometry.blowUpToBase (pointIdeal w hw) ≫ (h ≫ p))).IsCoherent]
    (U : (AlgebraicGeometry.blowUp (pointIdeal w hw)).Opens)
    (hU : ∃ x : AlgebraicGeometry.blowUp (pointIdeal w hw), x ∈ U)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (((Scheme.Modules.pullback (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))).obj
        (Scheme.Hom.relativeDifferentials (h ≫ p))).over U) r]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Hom.relativeDifferentials
        (AlgebraicGeometry.blowUpToBase (pointIdeal w hw) ≫ (h ≫ p))).over U) r]
    (V : W.Opens) (hV : ∃ x : W, x ∈ V)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Hom.relativeDifferentials (h ≫ p)).over V) r]
    (hrefl : IsReflexive (Scheme.Modules.exteriorPower
      (Scheme.Hom.relativeDifferentials (h ≫ p)) (r : ℤ))) :
    Nonempty
      (((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨(AlgebraicGeometry.blowUp (pointIdeal w hw)).sheaf.obj,
              Presheaf.isSheaf_of_isSheaf_comp _
                (AlgebraicGeometry.blowUp (pointIdeal w hw)).sheaf.obj
                (forget₂ CommRingCat RingCat)
                (AlgebraicGeometry.blowUp (pointIdeal w hw)).ringCatSheaf.property⟩).obj
          (Stacks.Divisors.invertibleSheaf'
            (AlgebraicGeometry.exceptionalIdeal (pointIdeal w hw)))).obj
        ((Scheme.Modules.pullback (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))).obj
          (hullForms p (r : ℤ) h)) ≅
      hullForms p (r : ℤ) (AlgebraicGeometry.blowUpToBase (pointIdeal w hw) ≫ h)) ∨
    Nonempty
      ((Scheme.Modules.pullback (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))).obj
          (hullForms p (r : ℤ) h) ≅
        hullForms p (r : ℤ) (AlgebraicGeometry.blowUpToBase (pointIdeal w hw) ≫ h)) := by
  have e := pullbackHullForms_iso p h hreg hdim w hw r V hV hrefl
  rcases nonempty_tensorIso_or_nonempty_iso_hullForms_vanishingIdeal_singleton'
    hreg hdim w hw hstalkdim p h r U hU with hd | hd
  · exact Or.inl (hd.elim fun d => ⟨((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨(AlgebraicGeometry.blowUp (pointIdeal w hw)).sheaf.obj,
          Presheaf.isSheaf_of_isSheaf_comp _
            (AlgebraicGeometry.blowUp (pointIdeal w hw)).sheaf.obj
            (forget₂ CommRingCat RingCat)
            (AlgebraicGeometry.blowUp (pointIdeal w hw)).ringCatSheaf.property⟩).obj
        (Stacks.Divisors.invertibleSheaf'
          (AlgebraicGeometry.exceptionalIdeal (pointIdeal w hw)))).mapIso e.symm ≪≫ d⟩)
  · exact Or.inr (hd.elim fun d => ⟨e.symm ≪≫ d⟩)

/-- **The dichotomy with the reflexivity hypothesis replaced by finite local freeness of
`⋀^r Ω_{W/S₀}`**, under which it holds automatically. This is the shape the base of the induction
of [Stacks, Tag 0B4T] has: there `Ω_{A/A₀}` is free of rank `r`, so its top exterior power is the
determinant line bundle and is finite locally free. -/
theorem nonempty_tensorIso_or_nonempty_iso_pullbackHullForms_of_isFiniteLocallyFree
    (hreg : AlgebraicGeometry.IsRegular W) (hdim : topologicalKrullDim W = 2)
    (w : W) (hw : IsClosed ({w} : Set W))
    (hstalkdim : ringKrullDim (W.presheaf.stalk w) = 2) (p : S ⟶ S₀) (h : W ⟶ S) (r : ℕ)
    [(Scheme.Hom.relativeDifferentials (h ≫ p)).IsCoherent]
    [((Scheme.Modules.pullback (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))).obj
        (Scheme.Hom.relativeDifferentials (h ≫ p))).IsCoherent]
    [(Scheme.Hom.relativeDifferentials
        (AlgebraicGeometry.blowUpToBase (pointIdeal w hw) ≫ (h ≫ p))).IsCoherent]
    (U : (AlgebraicGeometry.blowUp (pointIdeal w hw)).Opens)
    (hU : ∃ x : AlgebraicGeometry.blowUp (pointIdeal w hw), x ∈ U)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (((Scheme.Modules.pullback (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))).obj
        (Scheme.Hom.relativeDifferentials (h ≫ p))).over U) r]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Hom.relativeDifferentials
        (AlgebraicGeometry.blowUpToBase (pointIdeal w hw) ≫ (h ≫ p))).over U) r]
    (V : W.Opens) (hV : ∃ x : W, x ∈ V)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Hom.relativeDifferentials (h ≫ p)).over V) r]
    (hfree : Scheme.Modules.IsFiniteLocallyFree
      (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials (h ≫ p)) (r : ℤ))) :
    Nonempty
      (((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨(AlgebraicGeometry.blowUp (pointIdeal w hw)).sheaf.obj,
              Presheaf.isSheaf_of_isSheaf_comp _
                (AlgebraicGeometry.blowUp (pointIdeal w hw)).sheaf.obj
                (forget₂ CommRingCat RingCat)
                (AlgebraicGeometry.blowUp (pointIdeal w hw)).ringCatSheaf.property⟩).obj
          (Stacks.Divisors.invertibleSheaf'
            (AlgebraicGeometry.exceptionalIdeal (pointIdeal w hw)))).obj
        ((Scheme.Modules.pullback (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))).obj
          (hullForms p (r : ℤ) h)) ≅
      hullForms p (r : ℤ) (AlgebraicGeometry.blowUpToBase (pointIdeal w hw) ≫ h)) ∨
    Nonempty
      ((Scheme.Modules.pullback (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))).obj
          (hullForms p (r : ℤ) h) ≅
        hullForms p (r : ℤ) (AlgebraicGeometry.blowUpToBase (pointIdeal w hw) ≫ h)) :=
  nonempty_tensorIso_or_nonempty_iso_pullbackHullForms_vanishingIdeal_singleton
    hreg hdim w hw hstalkdim p h r U hU V hV
    (Stacks.FundamentalGroup.ExtendedEtale.isReflexive_of_isFiniteLocallyFree' _ hfree)

end Stacks.BlowupTwistUnit

end
