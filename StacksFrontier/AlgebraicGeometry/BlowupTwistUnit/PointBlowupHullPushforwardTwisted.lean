module

public import StacksFrontier.AlgebraicGeometry.BlowupTwistUnit.PointBlowupExceptionalTwistGlobal
public import StacksFrontier.AlgebraicGeometry.BlowupTwistUnit.PointBlowupHullPushforwardUntwisted

/-!
# The direct-image computation of the 0B4T induction, on the twisted branch, and unconditionally

Let `W` be an integral regular Noetherian scheme of dimension two over `S ⟶ S₀`, let `w ∈ W` be
a closed point whose local ring is regular of dimension two and let `b : W' ⟶ W` be the blowing
up of `W` in the reduced point `{w}`. The field
`Stacks.BlowupTwistUnit.NormalizedTopFormData.pushforwardIso` of the induction of
[Stacks, Tag 0B4T] asks for

`Rb_*((Ω^r_{W'/S₀})^{**}[0]) ≅ (Ω^r_{W/S₀})^{**}[0]`  in `D_QCoh(𝒪_W)`.

The dichotomy of [Stacks, Tag 0B3T], in the form
`BlowupTwistUnit.nonempty_tensorIso_or_nonempty_iso_pullbackHullForms_vanishingIdeal_singleton`,
presents the module upstairs as `𝒪_{W'}(E) ⊗ b^*L` or as `b^*L`, with `L = (Ω^r_{W/S₀})^{**}`.
`Stacks.BlowupTwistUnit.pushforwardIsoOfPullbackBranch` closes the second branch; **this file
closes the first**, and then closes `pushforwardIso` itself, with no branch hypothesis left.

## The three steps of the twisted branch

They are the three of the untwisted branch, with `𝒪_{W'}(E) ⊗ b^*L` in place of `b^*L`:

* `R^1b_*(𝒪_{W'}(E) ⊗ b^*L) = 0` —
  `Stacks.BlowupTwistUnit.isZeroFirstDirectImageBlowUp_exceptionalTwistPullback`;
* `b_*(𝒪_{W'}(E) ⊗ b^*L) ≅ L` — the projection formula of [Stacks, Tag 0FZE] in degree zero
  applied to `b_*𝒪_{W'}(E) ≅ 𝒪_W`, which is
  `Stacks.BlowupTwistUnit.isIso_exceptionalTwistComparison_pointIdeal`;
* the passage to the derived statement —
  `Stacks.BlowupTwistUnit.quasiCoherentDerivedPushforwardSingleIso`.

The first and the third are shared with the untwisted branch verbatim. The second is the one
place where the two branches differ, and `b_*𝒪_{W'}(E) ≅ 𝒪_W` at a closed point of a *global*
regular surface was the last input of the whole computation; it is part (4) of
[Stacks, Tag 0AGS] at `n = -1`, relativized.

## Main definitions

The elided prefix is `Stacks.BlowupTwistUnit`.

* `pushforwardExceptionalTwistPullbackIso`: **`b_*(𝒪_{W'}(E) ⊗ b^*L) ≅ L`** for `L` invertible.
* `pushforwardIsoOfTensorBranch`: **the `pushforwardIso` conclusion on the twisted branch.**

## Main results

* `nonempty_pushforwardIso_hullForms`: **the `pushforwardIso` conclusion, with no branch
  hypothesis** — the dichotomy of [Stacks, Tag 0B3T] supplies one branch or the other and each is
  closed.

## Implementation notes

**The conclusion is `Nonempty` of an isomorphism**, not an isomorphism: the dichotomy it consumes
is a disjunction of `Nonempty`s, which carries no data, so no isomorphism can be chosen from it
without `Classical.choice`. The field `pushforwardIso` of
`Stacks.BlowupTwistUnit.NormalizedTopFormData` asks for data, and a consumer inhabiting that
structure takes it from here with `Nonempty.some`.

**No `@[stacks]` attribute is placed.** [Stacks, Tag 0B4T] asserts the existence of
`φ_X : (Ω^r_{X/S₀})^{**} ⟶ ω_X` along a *sequence* of blowups in closed points; what is below is
one input of that induction at one blowup. The tag is registered on
`Stacks.BlowupTwistUnit.exists_extendsIdentification_hullForms_chainDualizingOfTopForms`, which
runs the induction through `Stacks.BlowupTwistUnit.ChainTopFormData` rather than through
`Stacks.BlowupTwistUnit.NormalizedTopFormData`; see the module docstring of
`StacksFrontier/AlgebraicGeometry/BlowupTwistUnit/ChainTopFormsDualizing.lean` for why.

## References

* [Stacks Project, Tag 0B4T](https://stacks.math.columbia.edu/tag/0B4T)
* [Stacks Project, Tag 0B3T](https://stacks.math.columbia.edu/tag/0B3T)
* [Stacks Project, Tag 0AGS](https://stacks.math.columbia.edu/tag/0AGS)
* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
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

/-! ### The degree-zero computation on the twisted branch -/

/-- **`b_*(𝒪_{W'}(E) ⊗ b^*L) ≅ L`** for the blowing up `b : W' ⟶ W` of a scheme at a closed point
whose local ring is regular of dimension two and `L` an invertible `𝒪_W`-module.

The projection formula of [Stacks, Tag 0FZE] in degree zero
(`Stacks.ProjectionFormula.pushforwardTensorRightNatIso`, which has no hypothesis on the
morphism) turns the direct image into `(b_*𝒪_{W'}(E)) ⊗ L`;
`Stacks.BlowupTwistUnit.isIso_exceptionalTwistComparison_pointIdeal` identifies `b_*𝒪_{W'}(E)`
with `𝒪_W` — part (4) of [Stacks, Tag 0AGS] at `n = -1`, relativized — and the left unitor of
[Stacks, Tag 01CA] gives `L`.

This is the twisted counterpart of `Stacks.BlowupTwistUnit.pushforwardPullbackIso`, which runs
the same three steps with `b_*𝒪_{W'} ≅ 𝒪_W` in place of `b_*𝒪_{W'}(E) ≅ 𝒪_W`. -/
def pushforwardExceptionalTwistPullbackIso (w : W) (hw : IsClosed ({w} : Set W))
    [IsRegularLocalRing (W.presheaf.stalk w)]
    (hstalkdim : ringKrullDim (W.presheaf.stalk w) = 2)
    (L : W.Modules) [Stacks.SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2 L] :
    (Scheme.Modules.pushforward (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))).obj
        ((Stacks.ProjectionFormula.tensorRightInvertible
            (AlgebraicGeometry.blowUp (pointIdeal w hw))
            ((Scheme.Modules.pullback
              (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))).obj L)).obj
          (Stacks.Divisors.invertibleSheaf'
            (AlgebraicGeometry.exceptionalIdeal (pointIdeal w hw)))) ≅ L :=
  haveI := isIso_exceptionalTwistComparison_pointIdeal w hw hstalkdim
  (Stacks.ProjectionFormula.pushforwardTensorRightNatIso
        (AlgebraicGeometry.blowUpToBase (pointIdeal w hw)) L).app
      (Stacks.Divisors.invertibleSheaf'
        (AlgebraicGeometry.exceptionalIdeal (pointIdeal w hw))) ≪≫
    (Stacks.ProjectionFormula.tensorRightInvertible W L).mapIso
      (asIso (exceptionalTwistComparison (pointIdeal w hw))).symm ≪≫
    Stacks.RingedSpace.tensorSheafUnitLeftIso W.toRingedSpace L

/-! ### The twisted branch -/

/-- **The `pushforwardIso` conclusion of [Stacks, Tag 0B4T] on the twisted branch of the
dichotomy of [Stacks, Tag 0B3T]**:

`Rb_*((Ω^r_{W'/S₀})^{**}[0]) ≅ (Ω^r_{W/S₀})^{**}[0]`  in `D_QCoh(𝒪_W)`,

for `b : W' ⟶ W` the blowing up of an integral regular Noetherian surface at a closed point `w`
whose local ring is regular of dimension two, given the identification
`d : 𝒪_{W'}(E) ⊗ b^*((Ω^r_{W/S₀})^{**}) ≅ (Ω^r_{W'/S₀})^{**}` that the twisted branch supplies.

`R^1b_*` vanishes on the module upstairs by
`Stacks.BlowupTwistUnit.isZeroFirstDirectImageBlowUp_exceptionalTwistPullback` transported along
`d`, the determinant line bundle downstairs being invertible by [Stacks, Tag 0B3T]; its direct
image is `(Ω^r_{W/S₀})^{**}` by
`Stacks.BlowupTwistUnit.pushforwardExceptionalTwistPullbackIso`, again transported along `d`; and
`Stacks.BlowupTwistUnit.quasiCoherentDerivedPushforwardSingleIso` turns the pair into the derived
statement. -/
def pushforwardIsoOfTensorBranch [CompactSpace W] (hreg : AlgebraicGeometry.IsRegular W)
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
    (d : (Stacks.ProjectionFormula.tensorRightInvertible
          (AlgebraicGeometry.blowUp (pointIdeal w hw))
          ((Scheme.Modules.pullback
            (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))).obj
              (hullForms p (r : ℤ) h))).obj
        (Stacks.Divisors.invertibleSheaf'
          (AlgebraicGeometry.exceptionalIdeal (pointIdeal w hw))) ≅
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
      (isZeroFirstDirectImageBlowUp_exceptionalTwistPullback w hw hstalkdim
        (hullForms p (r : ℤ) h)) d.symm)
    (hullForms p (r : ℤ) h) hqcoh
    ((Scheme.Modules.pushforward
          (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))).mapIso d.symm ≪≫
      pushforwardExceptionalTwistPullbackIso w hw hstalkdim (hullForms p (r : ℤ) h))

/-! ### `pushforwardIso`, with no branch hypothesis -/

/-- **The `pushforwardIso` computation of the induction of [Stacks, Tag 0B4T] at one blowup**:

`Rb_*((Ω^r_{W'/S₀})^{**}[0]) ≅ (Ω^r_{W/S₀})^{**}[0]`  in `D_QCoh(𝒪_W)`,

for `b : W' ⟶ W` the blowing up of an integral regular Noetherian surface at a closed point `w`
whose local ring is regular of dimension two.

The dichotomy of [Stacks, Tag 0B3T],
`BlowupTwistUnit.nonempty_tensorIso_or_nonempty_iso_pullbackHullForms_vanishingIdeal_singleton`,
presents the top forms upstairs as `𝒪_{W'}(E) ⊗ b^*((Ω^r_{W/S₀})^{**})` or as
`b^*((Ω^r_{W/S₀})^{**})`, and the two branches are closed by
`Stacks.BlowupTwistUnit.pushforwardIsoOfTensorBranch` and by
`Stacks.BlowupTwistUnit.pushforwardIsoOfPullbackBranch`. No hypothesis beyond the ones the
dichotomy itself carries survives. -/
theorem nonempty_pushforwardIso_hullForms [CompactSpace W] (hreg : AlgebraicGeometry.IsRegular W)
    (hdim : topologicalKrullDim W = 2) (w : W) (hw : IsClosed ({w} : Set W))
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
      (Scheme.Hom.relativeDifferentials (h ≫ p)) (r : ℤ)))
    (hqcohUp : (hullForms p (r : ℤ)
      (AlgebraicGeometry.blowUpToBase (pointIdeal w hw) ≫ h)).IsQuasicoherent)
    (hqcoh : (hullForms p (r : ℤ) h).IsQuasicoherent) :
    Nonempty
      ((quasiCoherentDerivedPushforward (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))
            (isQuasicoherent_homology_derivedPushforward_of_qcqs
              (AlgebraicGeometry.blowUpToBase (pointIdeal w hw)))).obj
          (singleQuasiCoherent (hullForms p (r : ℤ)
            (AlgebraicGeometry.blowUpToBase (pointIdeal w hw) ≫ h)) hqcohUp 0) ≅
        singleQuasiCoherent (hullForms p (r : ℤ) h) hqcoh 0) := by
  have : IsRegularLocalRing (W.presheaf.stalk w) := hreg.isRegularLocalRing_stalk w
  exact (nonempty_tensorIso_or_nonempty_iso_pullbackHullForms_vanishingIdeal_singleton
    hreg hdim w hw hstalkdim p h r U hU V hV hrefl).elim
    (.map <| pushforwardIsoOfTensorBranch hreg hdim w hw hstalkdim p h r V hV hqcohUp hqcoh)
    (.map <| pushforwardIsoOfPullbackBranch hreg hdim w hw hstalkdim p h r V hV hqcohUp hqcoh)

end Stacks.BlowupTwistUnit

end
