module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackChartThickeningLifts
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackDeformationBridge.Obstruction
public import StacksFrontier.AlgebraicGeometry.Quot.QuotientFunctorRelativeSquareIdeal
public import StacksFrontier.Deformation.ToposThickening.Helpers.ExtDescentAlongThickening

/-!
# The obstruction to lifting an object of `Coh_{X/B}` over a chart, on `X_A`

Let `x` be an object of `Coh_{X/Y}` over `Spec A`, with `Y` final and `f : X ⟶ Y` flat, and let
`A' → A` be a square-zero thickening of `Spec A`. The obstruction of Stacks 08VW, part (1), to
lifting `x` to `A'` lives in `Ext²` of modules over `i_*𝒪_{X_A}` on the small étale site of
`X_{A'}` (`AlgebraicGeometry.Space.CoherentSituation.thickeningLiftObstruction`). This file reads
it on `X_A` itself, in `Ext²_{X_A}(ℱ, f̃^*t̃^*𝒥̃ ⊗ ℱ)`, through the equivalence `i_*` of modules
along the first order thickening `X_A ⊂ X_{A'}`
(`Deformation.ToposThickening.extDescentAddEquiv`), and records that it vanishes exactly when
`x` lifts across `A' → A`.

## Main definitions

* `AlgebraicGeometry.Space.CoherentSituation.chartObstruction`.

## Main results

* `AlgebraicGeometry.Space.CoherentSituation.nonempty_fiber_iff_chartObstruction_eq_zero`.

This module is a helper and carries no `@[stacks]` attribute.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor pushforwardModuleFunctor)
open Deformation.ToposThickening

attribute [local instance 2000] CategoryTheory.instHasWeakSheafifyOfHasSheafify
attribute [local instance 6000] IsIso.epi_of_iso IsIso.mono_of_iso
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 5000] Abelian.has_kernels Abelian.has_cokernels

universe e e' u

namespace AlgebraicGeometry.Space.CoherentSituation

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (D : CoherentSituation B S hS)

/-- The projection `X_T ⟶ T` of a base change along a flat morphism is flat (Stacks 03MO). -/
theorem isFlat_projection_of_isFlat (hflat : IsFlat B S hS D.f.hom) (T : SchemesOver D.Y) :
    IsFlat B S hS (D.projection T).hom :=
  (isFlat_isStableUnderBaseChange B S hS).of_isPullback
    (AlgebraicSpaces.isPullback_fiberProduct B S hS D.f T.hom) hflat

variable {D} {ξ : CoherentObject D} {T' : SchemesOver D.Y} (h : ξ.T ⟶ T')
  (hh : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h.left))
  (hfl : IsFlat B S hS (D.projection T').hom)
  [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    ((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS
      (D.relativeSquareSituation.relativeMap h)).toToposHom).obj
        (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space ξ.T)).O)))]
  [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space T')).O))]
  [HasExt.{e'} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space ξ.T)).O))]
  [EnoughInjectives (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space ξ.T)).O))]

/-- **The obstruction to lifting `ξ` across `h`, on `X_T`**: the class of Stacks 08VW, part (1),
read in `Ext²_{X_T}(𝒢, f̃^*t̃^*𝒥̃ ⊗ 𝒢)` through the equivalence of modules along `X_T ⊂ X_{T'}`. -/
def thickeningObstructionOnBase :
    Abelian.Ext.{e'} (objectToposModule ξ)
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space ξ.T)).O).flip.obj
          (objectToposModule ξ)).obj
            (D.relativeSquareSituation.relativeSquareBasePullbackIdeal h hh)) 2 :=
  (extDescentAddEquiv (D.relativeSquareSituation.relativeMapFirstOrderThickening h hh)
    (objectToposModule ξ) (D.relativeSquareSituation.relativeSquareBasePullbackIdeal h hh) 2).symm
      (thickeningLiftObstruction h hh hfl)

/-- `ξ` lifts across `h` exactly when its obstruction on `X_T` vanishes. -/
theorem nonempty_thickeningLift_iff_thickeningObstructionOnBase_eq_zero :
    Nonempty (D.ThickeningLift ξ h) ↔ thickeningObstructionOnBase h hh hfl = 0 :=
  (nonempty_thickeningLift_iff_obstruction_eq_zero h hh hfl).trans
    (map_eq_zero_iff _
      (extDescentAddEquiv (D.relativeSquareSituation.relativeMapFirstOrderThickening h hh)
        (objectToposModule ξ) (D.relativeSquareSituation.relativeSquareBasePullbackIdeal h hh)
          2).symm.injective).symm

end AlgebraicGeometry.Space.CoherentSituation

end
