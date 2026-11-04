module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackDeformationBridge.PullbackTrivial

/-!
# The difference from the trivial lift along a morphism of split thickenings

Let `ξ = (T, 𝒢)` be an object of `Coh_{X/Y}` (Stacks 08KB), `h : T ⟶ T'` and `h₂ : T ⟶ T'₂` split
first order thickenings with retractions `r`, `r₂`, and `g : T'₂ ⟶ T'` under `T`. If the class on
`X_T` of the pullback along `g` of every lift is the class of the lift followed by the map
`λ_g : 𝒢 ⊗ f_T^*𝒥 ⟶ 𝒢 ⊗ f_T^*𝒥₂` of coefficients
(`AlgebraicGeometry.Space.CoherentSituation.thickeningCoefficientMap`), then so is the difference
from the trivial lift
(`AlgebraicGeometry.Space.CoherentSituation.thickeningLiftDifference_pullback`): the trivial lifts
have class zero (`AlgebraicGeometry.Space.CoherentSituation.thickeningLiftExtClass_trivial`). This
is the naturality of `T_x(M) = Ext¹(𝒢, 𝒢 ⊗ M)` in `M` in the proofs of Stacks 08W8 and Stacks 08WA.

This module is a helper and carries no `@[stacks]` attribute.

## References

* [Stacks Project, Tag 08KB](https://stacks.math.columbia.edu/tag/08KB)
* [Stacks Project, Tag 08VW](https://stacks.math.columbia.edu/tag/08VW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor)

attribute [local instance 2000] CategoryTheory.instHasWeakSheafifyOfHasSheafify
attribute [local instance 6000] IsIso.epi_of_iso IsIso.mono_of_iso
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 5000] Abelian.has_kernels Abelian.has_cokernels

universe e u

namespace AlgebraicGeometry.Space.CoherentSituation

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {D : CoherentSituation B S hS}
  {ξ : CoherentObject D} {T' T'₂ : SchemesOver D.Y} {h : ξ.T ⟶ T'} {h₂ : ξ.T ⟶ T'₂}
  {r : T' ⟶ ξ.T} {r₂ : T'₂ ⟶ ξ.T} (hr : h ≫ r = 𝟙 ξ.T) (hr₂ : h₂ ≫ r₂ = 𝟙 ξ.T)
  (hh : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h.left))
  (hh₂ : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h₂.left))
  (hfl : IsFlat B S hS (D.projection T').hom) (hfl₂ : IsFlat B S hS (D.projection T'₂).hom)
  (g : T'₂ ⟶ T') (hg : h₂ ≫ g = h)
  [IsAffine ((BigFppfOver.toScheme B S hS).obj ξ.T.left)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T'.left)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T'₂.left)]
  [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    ((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS
      (D.relativeSquareSituation.relativeMap h)).toToposHom).obj
      (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space ξ.T)).O)))]
  [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space T')).O))]
  [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    ((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS
      (D.relativeSquareSituation.relativeMap h₂)).toToposHom).obj
      (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space ξ.T)).O)))]
  [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space T'₂)).O))]
  [HasExt.{e} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space ξ.T)).O))]

/-- **The difference from the trivial lift is natural along `g`**: if the class on `X_T` of the
pullback along `g` of every lift is its class followed by `λ_g`, then the difference of the
pullback of a class of lifts from the trivial lift is the difference of the class followed by `λ_g`
(`AlgebraicGeometry.Space.CoherentSituation.thickeningLiftDifference_mk`; the trivial lifts have
class zero, `AlgebraicGeometry.Space.CoherentSituation.thickeningLiftExtClass_trivial`). -/
theorem thickeningLiftDifference_pullback
    (hN : ∀ L : D.ThickeningLift ξ h,
      thickeningLiftExtClass h₂ r₂ hr₂ hh₂ hfl₂ (L.pullback g hg) =
        (thickeningLiftExtClass h r hr hh hfl L).comp
          (Abelian.Ext.mk₀ (thickeningCoefficientMap g hg hh hh₂)) (add_zero 1))
    (c : D.ThickeningLiftClass ξ h) :
    thickeningLiftDifference h₂ r₂ hr₂ hh₂ hfl₂ (ThickeningLiftClass.pullback g hg c) =
      (thickeningLiftDifference h r hr hh hfl c).comp
        (Abelian.Ext.mk₀ (thickeningCoefficientMap g hg hh hh₂)) (add_zero 1) := by
  induction c using Quotient.inductionOn with
  | h L =>
    rw [ThickeningLiftClass.pullback_mk, thickeningLiftDifference_mk, thickeningLiftDifference_mk,
      thickeningLiftExtClass_trivial, thickeningLiftExtClass_trivial, sub_zero, sub_zero]
    exact hN L

end AlgebraicGeometry.Space.CoherentSituation

end
