module

public import StacksFrontier.AlgebraicGeometry.BlowupTwistUnit.HullFormsPullbackDichotomy
public import StacksFrontier.AlgebraicGeometry.BlowupTwistUnit.PointBlowupFirstDirectImageBranches
public import StacksFrontier.AlgebraicGeometry.BlowupTwistUnit.PointBlowupPushforwardPullback

/-!
# The derived direct image of the reflexive top forms on the untwisted branch

Let `W` be an integral regular Noetherian scheme of dimension two over `S ⟶ S₀`, let `w ∈ W` be
a closed point whose local ring is regular of dimension two, let `b : W' ⟶ W` be the blowing up
of `W` in the reduced point `{w}` and let `L = (Ω^r_{W/S₀})^{**}`. Given an isomorphism
`b^*L ≅ (Ω^r_{W'/S₀})^{**}` (one branch of the dichotomy of [Stacks, Tag 0B3T]), this file
constructs an isomorphism

`Rb_*((Ω^r_{W'/S₀})^{**}[0]) ≅ (Ω^r_{W/S₀})^{**}[0]`  in `D_QCoh(𝒪_W)`,

the conclusion asked for by `Stacks.BlowupTwistUnit.NormalizedTopFormData.pushforwardIso` in
[Stacks, Tag 0B4T].

## Main results

The elided prefix is `Stacks.BlowupTwistUnit`.

* `isInvertible_hullForms`: `(Ω^r_{W/S₀})^{**}` is invertible, [Stacks, Tag 0B3T].
* `pushforwardIsoOfPullbackBranch`: the isomorphism
  `Rb_*((Ω^r_{W'/S₀})^{**}[0]) ≅ (Ω^r_{W/S₀})^{**}[0]` given `b^*L ≅ (Ω^r_{W'/S₀})^{**}`.

## References

* [Stacks Project, Tag 0B4T](https://stacks.math.columbia.edu/tag/0B4T)
* [Stacks Project, Tag 0B3T](https://stacks.math.columbia.edu/tag/0B3T)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Duality
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace Stacks.BlowupTwistUnit

variable {S₀ S W : Scheme.{u}} [IsNoetherian W] [AlgebraicGeometry.IsIntegral W]

omit [AlgebraicGeometry.IsNoetherian W] in
/-- `(Ω^r_{W/S₀})^{**}` is invertible on an integral regular scheme of dimension at most two,
for `Ω_{W/S₀}` coherent and locally free of rank `r` on a nonempty open ([Stacks, Tag 0B3T]). -/
theorem isInvertible_hullForms (hreg : AlgebraicGeometry.IsRegular W)
    (hdim : topologicalKrullDim W ≤ 2) (p : S ⟶ S₀) (h : W ⟶ S) (r : ℕ)
    [(Scheme.Hom.relativeDifferentials (h ≫ p)).IsCoherent]
    (U : W.Opens) (hU : ∃ x : W, x ∈ U)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Hom.relativeDifferentials (h ≫ p)).over U) r] :
    Stacks.SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 (hullForms p (r : ℤ) h) :=
  AlgebraicGeometry.isInvertible_reflexiveHull_exteriorPower_of_genericRank W hreg hdim
    (Scheme.Hom.relativeDifferentials (h ≫ p)) r U hU

/-- For `b : W' ⟶ W` the blowing up of an integral regular Noetherian surface at a closed point
`w` whose local ring is regular of dimension two, an isomorphism
`d : b^*((Ω^r_{W/S₀})^{**}) ≅ (Ω^r_{W'/S₀})^{**}` induces

`Rb_*((Ω^r_{W'/S₀})^{**}[0]) ≅ (Ω^r_{W/S₀})^{**}[0]`  in `D_QCoh(𝒪_W)`. -/
def pushforwardIsoOfPullbackBranch (hreg : AlgebraicGeometry.IsRegular W)
    (hdim : topologicalKrullDim W = 2) (w : W) (hw : IsClosed ({w} : Set W))
    [IsRegularLocalRing (W.presheaf.stalk w)]
    (hstalkdim : ringKrullDim (W.presheaf.stalk w) = 2) (p : S ⟶ S₀) (h : W ⟶ S) (r : ℕ)
    [(Scheme.Hom.relativeDifferentials (h ≫ p)).IsCoherent]
    (U : W.Opens) (hU : ∃ x : W, x ∈ U)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Hom.relativeDifferentials (h ≫ p)).over U) r]
    (hqcohUp : (hullForms p (r : ℤ)
      (AlgebraicGeometry.blowUpToBase (pointIdeal w hw) ≫ h)).IsQuasicoherent)
    (hqcoh : (hullForms p (r : ℤ) h).IsQuasicoherent)
    (d : (Scheme.Modules.pullback (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))).obj
        (hullForms p (r : ℤ) h) ≅
      hullForms p (r : ℤ) (AlgebraicGeometry.blowUpToBase (pointIdeal w hw) ≫ h)) :
    (quasiCoherentDerivedPushforward (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))
        (isQuasicoherent_homology_derivedPushforward_of_qcqs
          (AlgebraicGeometry.blowUpToBase (pointIdeal w hw)))).obj
      (singleQuasiCoherent (hullForms p (r : ℤ)
        (AlgebraicGeometry.blowUpToBase (pointIdeal w hw) ≫ h)) hqcohUp 0) ≅
      singleQuasiCoherent (hullForms p (r : ℤ) h) hqcoh 0 :=
  haveI := isInvertible_hullForms hreg hdim.le p h r U hU
  quasiCoherentDerivedPushforwardSingleIso hdim w hw _ hqcohUp
    (isZeroFirstDirectImageBlowUp_of_iso w hw
      (isZeroFirstDirectImageBlowUp_pullback w hw hstalkdim (hullForms p (r : ℤ) h)) d.symm)
    (hullForms p (r : ℤ) h) hqcoh
    ((Scheme.Modules.pushforward
          (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))).mapIso d.symm ≪≫
      pushforwardPullbackIso hreg hdim w hw (hullForms p (r : ℤ) h))

end Stacks.BlowupTwistUnit

end
