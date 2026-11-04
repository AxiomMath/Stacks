module

public import StacksFrontier.AlgebraicGeometry.Blowup.GlobalExceptionalCurveDifferentials
public import StacksFrontier.AlgebraicGeometry.BlowupTwistUnit.PointBlowupDichotomyTransport

/-!
# The twist dichotomy at a closed point of a regular surface, with no hypothesis on `Ω_{E/Z}`

`Stacks.BlowupTwistUnit.nonempty_tensorIso_or_nonempty_iso_hullForms_vanishingIdeal_singleton`
carries one substantial hypothesis, `hE`: that the relative differentials of the exceptional
divisor over the centre are finite locally free of rank one. That hypothesis holds by
`Blowup.isFiniteLocallyFreeOfRank_one_relativeDifferentials_exceptionalToCentre_vanishingIdeal`,
and this file discharges it, leaving the dichotomy with only the hypotheses on `W`, on the point
`w` and the coherence and rank side conditions on the forms.

## Main results

The elided prefix is `Stacks.BlowupTwistUnit`.

* `nonempty_tensorIso_or_nonempty_iso_reflexiveHull_exteriorPower_vanishingIdeal_singleton'`
* `nonempty_tensorIso_or_nonempty_iso_hullForms_vanishingIdeal_singleton'`: the dichotomy in the
  `Stacks.BlowupTwistUnit.hullForms` spelling that the `pushforwardIso` field of
  `Stacks.BlowupTwistUnit.NormalizedTopFormData` consumes.

## Implementation notes

The regularity of the local ring at `w`, which the globalized statement about `Ω_{E/Z}` needs, is
read off the regularity of `W` by `AlgebraicGeometry.IsRegular.isRegularLocalRing_stalk`; the
dimension of that local ring stays a hypothesis, as it must — a closed point of a
two-dimensional scheme may have a local ring of dimension `0`, `1` or `2`, and the dichotomy
itself case-splits on it.

**No `@[stacks]` attribute is placed.** [Stacks, Tag 0B4T] asserts the existence of the map
`φ_X : (Ω^r_{X/S₀})^{**} ⟶ ω_X` along a sequence of blowups in closed points; what is proved here
is the single-blowup computation that the induction consumes, which is the content of
[Stacks, Tag 0B4L] and [Stacks, Tag 0B3T] combined and already registered there.

## References

* [Stacks Project, Tag 0B3T](https://stacks.math.columbia.edu/tag/0B3T)
* [Stacks Project, Tag 0B4L](https://stacks.math.columbia.edu/tag/0B4L)
* [Stacks Project, Tag 0B4T](https://stacks.math.columbia.edu/tag/0B4T)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.AlgebraicGeometry.ReflexiveModules
open Scheme.Modules Stacks.SheafOfModules

universe u

namespace Stacks.BlowupTwistUnit

variable {S₀ S W : Scheme.{u}} [IsNoetherian W] [AlgebraicGeometry.IsIntegral W]

/-- **The twist dichotomy at a blowup in a closed point of a regular surface**, with the
hypothesis on the differentials of the exceptional divisor discharged. -/
theorem nonempty_tensorIso_or_nonempty_iso_reflexiveHull_exteriorPower_vanishingIdeal_singleton'
    (hreg : AlgebraicGeometry.IsRegular W) (hdim : topologicalKrullDim W = 2)
    (w : W) (hw : IsClosed ({w} : Set W))
    (hstalkdim : ringKrullDim (W.presheaf.stalk w) = 2) (q : W ⟶ S₀) (r : ℕ)
    [((Scheme.Modules.pullback (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))).obj
        (Scheme.Hom.relativeDifferentials q)).IsCoherent]
    [(Scheme.Hom.relativeDifferentials
        (AlgebraicGeometry.blowUpToBase (pointIdeal w hw) ≫ q)).IsCoherent]
    (U : (AlgebraicGeometry.blowUp (pointIdeal w hw)).Opens)
    (hU : ∃ x : AlgebraicGeometry.blowUp (pointIdeal w hw), x ∈ U)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (((Scheme.Modules.pullback (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))).obj
        (Scheme.Hom.relativeDifferentials q)).over U) r]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Hom.relativeDifferentials
        (AlgebraicGeometry.blowUpToBase (pointIdeal w hw) ≫ q)).over U) r] :
    Nonempty
      (((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨(AlgebraicGeometry.blowUp (pointIdeal w hw)).sheaf.obj,
              Presheaf.isSheaf_of_isSheaf_comp _
                (AlgebraicGeometry.blowUp (pointIdeal w hw)).sheaf.obj
                (forget₂ CommRingCat RingCat)
                (AlgebraicGeometry.blowUp (pointIdeal w hw)).ringCatSheaf.property⟩).obj
          (Stacks.Divisors.invertibleSheaf'
            (AlgebraicGeometry.exceptionalIdeal (pointIdeal w hw)))).obj
        (reflexiveHull (exteriorPower ((Scheme.Modules.pullback
          (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))).obj
            (Scheme.Hom.relativeDifferentials q)) (r : ℤ))) ≅
      reflexiveHull (exteriorPower (Scheme.Hom.relativeDifferentials
        (AlgebraicGeometry.blowUpToBase (pointIdeal w hw) ≫ q)) (r : ℤ))) ∨
    Nonempty
      (reflexiveHull (exteriorPower ((Scheme.Modules.pullback
          (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))).obj
            (Scheme.Hom.relativeDifferentials q)) (r : ℤ)) ≅
      reflexiveHull (exteriorPower (Scheme.Hom.relativeDifferentials
        (AlgebraicGeometry.blowUpToBase (pointIdeal w hw) ≫ q)) (r : ℤ))) :=
  nonempty_tensorIso_or_nonempty_iso_reflexiveHull_exteriorPower_vanishingIdeal_singleton
    hreg hdim w hw hstalkdim q
    (Blowup.isFiniteLocallyFreeOfRank_one_relativeDifferentials_exceptionalToCentre_vanishingIdeal
      w hw (hreg.isRegularLocalRing_stalk w) hstalkdim) r U hU

/-- **The twist dichotomy at a blowup in a closed point of a regular surface, in the
`Stacks.BlowupTwistUnit.hullForms` spelling**, with the hypothesis on the differentials of the
exceptional divisor discharged.

The right-hand side of each alternative is `hullForms p r (b ≫ h)`, the module the
`pushforwardIso` field of `Stacks.BlowupTwistUnit.NormalizedTopFormData` takes the direct image
of. -/
theorem nonempty_tensorIso_or_nonempty_iso_hullForms_vanishingIdeal_singleton'
    (hreg : AlgebraicGeometry.IsRegular W) (hdim : topologicalKrullDim W = 2)
    (w : W) (hw : IsClosed ({w} : Set W))
    (hstalkdim : ringKrullDim (W.presheaf.stalk w) = 2) (p : S ⟶ S₀) (h : W ⟶ S) (r : ℕ)
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
        (AlgebraicGeometry.blowUpToBase (pointIdeal w hw) ≫ (h ≫ p))).over U) r] :
    Nonempty
      (((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨(AlgebraicGeometry.blowUp (pointIdeal w hw)).sheaf.obj,
              Presheaf.isSheaf_of_isSheaf_comp _
                (AlgebraicGeometry.blowUp (pointIdeal w hw)).sheaf.obj
                (forget₂ CommRingCat RingCat)
                (AlgebraicGeometry.blowUp (pointIdeal w hw)).ringCatSheaf.property⟩).obj
          (Stacks.Divisors.invertibleSheaf'
            (AlgebraicGeometry.exceptionalIdeal (pointIdeal w hw)))).obj
        (reflexiveHull (exteriorPower ((Scheme.Modules.pullback
          (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))).obj
            (Scheme.Hom.relativeDifferentials (h ≫ p))) (r : ℤ))) ≅
      hullForms p (r : ℤ) (AlgebraicGeometry.blowUpToBase (pointIdeal w hw) ≫ h)) ∨
    Nonempty
      (reflexiveHull (exteriorPower ((Scheme.Modules.pullback
          (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))).obj
            (Scheme.Hom.relativeDifferentials (h ≫ p))) (r : ℤ)) ≅
      hullForms p (r : ℤ) (AlgebraicGeometry.blowUpToBase (pointIdeal w hw) ≫ h)) :=
  nonempty_tensorIso_or_nonempty_iso_hullForms_vanishingIdeal_singleton
    hreg hdim w hw hstalkdim p h
    (Blowup.isFiniteLocallyFreeOfRank_one_relativeDifferentials_exceptionalToCentre_vanishingIdeal
      w hw (hreg.isRegularLocalRing_stalk w) hstalkdim) r U hU

end Stacks.BlowupTwistUnit

end
