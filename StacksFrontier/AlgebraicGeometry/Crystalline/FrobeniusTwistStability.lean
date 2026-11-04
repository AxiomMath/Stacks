module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.ChangeBaseCrystals
public import StacksFrontier.AlgebraicGeometry.Crystalline.FrobeniusRelativeTwist

/-!
# The hypotheses of [Stacks, Tag 07N5] hold again for `X^{(1)}` and `E^{(1)}`

Let `X^{(1)} = X ×_{S₀, F_{S₀}} S₀` be the Frobenius twist and `E^{(1)}` the base change of `E` by
`Spec(σ)`.  This file proves that the pair `(X^{(1)}, E^{(1)})` satisfies the hypotheses of
[Stacks, Tag 07N5] whenever `(X, E)` does.

* `X^{(1)} ⟶ S₀` is the base change of `X ⟶ S₀` along the absolute Frobenius of `S₀`: the defining
  square of the fibre product is a pullback square
  (`Crystalline.FCrystalSituation.isPullback_frobeniusTwist`).  Properness and smoothness are
  stable under base change, so `X^{(1)} ⟶ S₀` is proper, resp. smooth, when `X ⟶ S₀` is.
* `E^{(1)}` is the pullback of `E` along change of divided power base, which carries crystals in
  finite locally free modules to crystals in finite locally free modules
  (`...IsFiniteLocallyFreeQuasicoherentCrystal.changeBaseModulePullback`).
* The divided power base of `X^{(1)}/S` is that of `X/S`, so the Noetherian and `p`-adic
  completeness hypotheses on its ring of global sections are the same hypotheses.

## Main results

* `Crystalline.FCrystalSituation.isPullback_frobeniusTwist` — the defining square of `X^{(1)}`.
* `Crystalline.FCrystalSituation.isProper_frobeniusTwist_toClosedFiber` and
  `Crystalline.FCrystalSituation.smooth_frobeniusTwist_toClosedFiber` — `X^{(1)} ⟶ S₀` is proper,
  resp. smooth, when `X ⟶ S₀` is.
* `Crystalline.FCrystalSituation.isFiniteLocallyFreeQuasicoherentCrystal_sigmaModulePullback` and
  `Crystalline.FCrystal.isFiniteLocallyFreeQuasicoherentCrystal_sigmaModulePullback` — `E^{(1)}` is
  a crystal in finite locally free modules.
* `Crystalline.FCrystalSituation.frobeniusTwistSituation_baseRing` — the ring of global sections of
  the divided power base of `X^{(1)}/S` is that of `X/S`.

## References

* [Stacks Project, Tag 07N5](https://stacks.math.columbia.edu/tag/07N5)
* [Stacks Project, Tag 07IU](https://stacks.math.columbia.edu/tag/07IU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Frobenius

universe u

namespace Crystalline.FCrystalSituation

open GlobalCrystallineSituation

variable (T : FCrystalSituation.{u})

/-- **The defining square of the Frobenius twist is a pullback square**: `X^{(1)}` is the fibre
product of `X ⟶ S₀` and the absolute Frobenius `F_{S₀} : S₀ ⟶ S₀`, with projections
`X^{(1)} ⟶ X` and `X^{(1)} ⟶ S₀`. -/
theorem isPullback_frobeniusTwist :
    IsPullback T.twistProjection T.frobeniusTwistSituation.toClosedFiber T.global.toClosedFiber
      (absoluteFrobenius (DividedPowerScheme.closedFiber T.global.S) T.global.p
        T.isInCharacteristic_closedFiber) :=
  IsPullback.of_hasPullback _ _

/-- **`X^{(1)} ⟶ S₀` is proper when `X ⟶ S₀` is**: it is the base change of `X ⟶ S₀` along the
absolute Frobenius of `S₀`. -/
theorem isProper_frobeniusTwist_toClosedFiber (h : IsProper T.global.toClosedFiber) :
    IsProper T.frobeniusTwistSituation.toClosedFiber :=
  MorphismProperty.of_isPullback (P := @IsProper) T.isPullback_frobeniusTwist h

/-- **`X^{(1)} ⟶ S₀` is smooth when `X ⟶ S₀` is**: it is the base change of `X ⟶ S₀` along the
absolute Frobenius of `S₀`. -/
theorem smooth_frobeniusTwist_toClosedFiber (h : Smooth T.global.toClosedFiber) :
    Smooth T.frobeniusTwistSituation.toClosedFiber :=
  MorphismProperty.of_isPullback (P := @Smooth) T.isPullback_frobeniusTwist h

/-- **`E^{(1)}` is a crystal in finite locally free modules when `E` is**, [Stacks, Tag 07IU]:
`E^{(1)}` is the pullback of `E` along change of divided power base. -/
theorem isFiniteLocallyFreeQuasicoherentCrystal_sigmaModulePullback
    {E : SheafOfModules.{u} (crystallineStructureSheaf T.global)}
    (hE : IsFiniteLocallyFreeQuasicoherentCrystal E) :
    IsFiniteLocallyFreeQuasicoherentCrystal (T.sigmaModulePullback.obj E) :=
  hE.changeBaseModulePullback

/-- **The base change `E^{(1)}` of an F-crystal is a crystal in finite locally free modules.** -/
theorem _root_.Crystalline.FCrystal.isFiniteLocallyFreeQuasicoherentCrystal_sigmaModulePullback
    {T : FCrystalSituation.{u}} (E : Crystalline.FCrystal T) :
    IsFiniteLocallyFreeQuasicoherentCrystal (T.sigmaModulePullback.obj E.crystal) :=
  T.isFiniteLocallyFreeQuasicoherentCrystal_sigmaModulePullback
    E.isFiniteLocallyFreeQuasicoherentCrystal

/-- **The value of `E^{(1)}` at an object of `CRIS(X^{(1)}/S)` is the value of `E` at its image
under change of base along `Spec(σ)` and `X^{(1)} ⟶ X`.** -/
theorem sigmaModulePullback_obj_val_obj
    (E : SheafOfModules.{u} (crystallineStructureSheaf T.global))
    (A : Thickening T.frobeniusTwistSituation) :
    (T.sigmaModulePullback.obj E).val.obj (op A) = E.val.obj (op (T.sigmaChangeBase.obj A)) :=
  rfl

/-- **The divided power base of `X^{(1)}/S` is affine**, being that of `X/S`. -/
instance isAffine_frobeniusTwistSituation_S : IsAffine T.frobeniusTwistSituation.S.scheme :=
  T.affine

/-- **The ring of global sections of the divided power base of `X^{(1)}/S` is that of `X/S`.** -/
theorem frobeniusTwistSituation_baseRing :
    Γ(T.frobeniusTwistSituation.S.scheme, ⊤) = Γ(T.global.S.scheme, ⊤) := rfl

/-- **The prime of `X^{(1)}/S` is that of `X/S`.** -/
theorem frobeniusTwistSituation_p : T.frobeniusTwistSituation.p = T.global.p := rfl

/-- **The Noetherian hypothesis of [Stacks, Tag 07N5] for `X^{(1)}/S` is that for `X/S`.** -/
theorem isNoetherianRing_frobeniusTwistSituation_iff :
    IsNoetherianRing Γ(T.frobeniusTwistSituation.S.scheme, ⊤) ↔
      IsNoetherianRing Γ(T.global.S.scheme, ⊤) :=
  Iff.rfl

/-- **The `p`-adic completeness hypothesis of [Stacks, Tag 07N5] for `X^{(1)}/S` is that for
`X/S`.** -/
theorem isAdicComplete_frobeniusTwistSituation_iff :
    IsAdicComplete (Ideal.span {(T.frobeniusTwistSituation.p :
        Γ(T.frobeniusTwistSituation.S.scheme, ⊤))}) Γ(T.frobeniusTwistSituation.S.scheme, ⊤) ↔
      IsAdicComplete (Ideal.span {(T.global.p : Γ(T.global.S.scheme, ⊤))})
        Γ(T.global.S.scheme, ⊤) :=
  Iff.rfl

end Crystalline.FCrystalSituation
