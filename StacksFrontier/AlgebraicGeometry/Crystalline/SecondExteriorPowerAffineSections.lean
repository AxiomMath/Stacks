module

public import StacksFrontier.AlgebraicGeometry.AffineChartLocalization.Basic
public import StacksFrontier.AlgebraicGeometry.Crystalline.SecondExteriorPowerQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.FormsRestrictionLocalizes

/-!
# The sections of `Ω²_{T/Y,δ}` over an affine open are `⋀²` of the sections of `Ω_{T/Y,δ}`

Let `(T, J, δ)` be a divided power scheme over a scheme `Y` and let `W` be an affine open of `T`.
`Crystalline.dpSecondExteriorPower` is the sheafification of the presheaf of sectionwise second
exterior powers `W ↦ ⋀²_{Γ(T, W)} Γ(W, Ω_{T/Y,δ})` of the sheaf of divided power differentials.
Over an affine open the sheafification unit is bijective: the sections of `Ω²_{T/Y,δ}` over `W`
are `⋀²_{Γ(T, W)} Γ(W, Ω_{T/Y,δ})`, the exterior product of two sections being their wedge.

## Main definitions

* `Crystalline.dpChartPresheaf`: a presheaf of modules over `X.sheaf.obj ⋙ forget₂ CommRingCat
  RingCat`, viewed as a presheaf of modules over `X.ringCatSheaf.obj`.
* `Crystalline.dpDifferentialsChart`: the sheaf `Ω_{T/Y,δ}`, viewed in this way.
* `Crystalline.dpSecondExteriorPresheafChart`: the presheaf of sectionwise second exterior powers
  of `Ω_{T/Y,δ}`, viewed in this way.

## Main results

* `Crystalline.isLocalizedModule_dpDifferentialsChart`: the sections of `Ω_{T/Y,δ}` localize on
  the basic opens of an affine open.
* `Crystalline.isLocalizedModule_dpSecondExteriorPresheaf`: the sectionwise second exterior
  power localizes on the basic opens of an affine open.
* `Crystalline.bijective_dpSecondExteriorToSheaf_app`: the sheafification unit
  `⋀² Γ(W, Ω_{T/Y,δ}) ⟶ Γ(W, Ω²_{T/Y,δ})` is bijective over an affine open `W`.

## References

* [Stacks Project, Tag 07IY](https://stacks.math.columbia.edu/tag/07IY)
* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open Stacks.AlgebraicGeometry
open Stacks.AlgebraicGeometry.AffineChartLocalization (bijective_sheafifyUnit_app_of_isAffineOpen)
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange (isLocalizedModule_restrictₗ)

universe u

attribute [local instance] Stacks.AlgebraicGeometry.AffineChartLocalization.sectionsModule

namespace Crystalline

variable (T : DividedPowerScheme.{u}) (Y : Scheme.{u}) (f : T.scheme ⟶ Y)

/-- A presheaf of modules over the structure sheaf `X.sheaf.obj ⋙ forget₂ CommRingCat RingCat` of
a scheme, viewed as a presheaf of modules over `X.ringCatSheaf.obj`. -/
abbrev dpChartPresheaf {X : Scheme.{u}}
    (P : PresheafOfModules.{u} (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)) :
    PresheafOfModules.{u} X.ringCatSheaf.obj :=
  P

/-- The sheaf of divided power differentials, viewed as a presheaf of modules over
`T.scheme.ringCatSheaf.obj`. -/
abbrev dpDifferentialsChart : PresheafOfModules.{u} T.scheme.ringCatSheaf.obj :=
  dpChartPresheaf (dpDifferentialsModules T Y f)

/-- The presheaf of sectionwise second exterior powers of `Ω_{T/Y,δ}`, viewed as a presheaf of
modules over `T.scheme.ringCatSheaf.obj`. -/
abbrev dpSecondExteriorPresheafChart : PresheafOfModules.{u} T.scheme.ringCatSheaf.obj :=
  dpChartPresheaf (dpSecondExteriorPresheaf T Y f)

/-- **The sections of `Ω_{T/Y,δ}` localize on the basic opens of an affine open**: over
`T.basicOpen g ⊆ W` its sections are the localization away from `g` of its sections over `W`. -/
theorem isLocalizedModule_dpDifferentialsChart {W : T.scheme.Opens} (hW : IsAffineOpen W)
    (g : Γ(T.scheme, W)) {U : T.scheme.Opens} (hU : U = T.scheme.basicOpen g) (hUW : U ≤ W) :
    letI := AffineChartLocalization.presheafModuleOfLE (dpDifferentialsChart T Y f) hUW
    IsLocalizedModule (Submonoid.powers g)
      (AffineChartLocalization.presheafRestrictₗ (dpDifferentialsChart T Y f) hUW) :=
  isLocalizedModule_restrictₗ (dpDifferentialsSheaf T Y f) hW g hU hUW

/-- **The presheaf of sectionwise second exterior powers of `Ω_{T/Y,δ}` localizes on the basic
opens of an affine open**: over `T.basicOpen g ⊆ W` its sections are the localization away from
`g` of its sections over `W`. -/
theorem isLocalizedModule_dpSecondExteriorPresheaf {W : T.scheme.Opens} (hW : IsAffineOpen W)
    (g : Γ(T.scheme, W)) {U : T.scheme.Opens} (hU : U = T.scheme.basicOpen g) (hUW : U ≤ W) :
    letI := AffineChartLocalization.presheafModuleOfLE (dpSecondExteriorPresheafChart T Y f) hUW
    IsLocalizedModule (Submonoid.powers g)
      (AffineChartLocalization.presheafRestrictₗ (dpSecondExteriorPresheafChart T Y f) hUW) := by
  subst hU
  have h1 := isLocalizedModule_dpDifferentialsChart T Y f hW g rfl hUW
  have h0 := hW.isLocalization_basicOpen g
  have h2 := PresheafOfModules.isLocalizedModule_restrictAlongₗ_extPow (O := T.scheme.sheaf.obj)
    (F := dpDifferentialsModules T Y f) (f := (homOfLE hUW).op) 2 (Submonoid.powers g) h0 h1
  exact h2

/-- **The sections of `Ω²_{T/Y,δ}` over an affine open are the second exterior power of the
sections of `Ω_{T/Y,δ}`**: the sheafification unit `dpSecondExteriorToSheaf` is bijective there. -/
theorem bijective_dpSecondExteriorToSheaf_app {W : T.scheme.Opens} (hW : IsAffineOpen W) :
    Function.Bijective ((dpSecondExteriorToSheaf T Y f).app (op W)) :=
  bijective_sheafifyUnit_app_of_isAffineOpen (dpSecondExteriorPresheafChart T Y f) hW
    (fun g _ hU hUW ↦ isLocalizedModule_dpSecondExteriorPresheaf T Y f hW g hU hUW)

end Crystalline

end
