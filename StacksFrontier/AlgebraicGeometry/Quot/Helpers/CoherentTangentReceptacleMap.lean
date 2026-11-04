module

public import StacksFrontier.AlgebraicGeometry.Quot.Helpers.CoherentTangentReceptacle
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackChartTangent
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackAxiomHelpers.CoherentTangentBridge
public import StacksFrontier.Deformation.ToposThickening.Helpers.ExtDescentAlongThickening

/-!
# The map from the lift differences of `Coh_{X/Y}` over `k[V]` to `Ext¹(𝒢₀, 𝒢₀ ⊗ p^*Ṽ)`

Let `x₀ = (Spec k, 𝒢₀)` be an object of `Coh_{X/Y}` over a field `k`, with `Y` final. For a finite
dimensional `k`-vector space `V`, the lift differences of `x₀` across `Spec k ⊂ Spec k[V]` live in
`Ext¹(𝒢₀, p^*t^*𝒥 ⊗ 𝒢₀)` (Stacks 08VW, part (2)); the coefficient is `𝒢₀ ⊗ p^*Ṽ`
(`AlgebraicGeometry.Space.CoherentSituation.tangentCoefficientIso`). This file defines the
resulting map

`c_V : Ext¹(𝒢₀, p^*t^*𝒥 ⊗ 𝒢₀) ⟶ Ext¹(𝒢₀, 𝒢₀ ⊗ p^*Ṽ)`

into the receptacle `AlgebraicGeometry.Space.CoherentSituation.tangentExtFunctor`; it is a
bijection. This is the map `t` of the finite dimensionality criterion
`Deformation.finiteDimensional_artinianTangentSpace_of_natural_injection` for the tangent space
of Stacks 08W8, after the identification of lifts with lift differences. No declaration here
carries a `@[stacks]` attribute.

## Main definitions

* `AlgebraicGeometry.Space.CoherentSituation.toposModulesHasExt`: the `Ext` groups of the modules
  on `X_k` in the spelling of the small étale ringed topos, from those of the modules.
* `AlgebraicGeometry.Space.CoherentSituation.tangentExtMap`: the map `c_V`.

## Main results

* `AlgebraicGeometry.Space.CoherentSituation.bijective_tangentExtMap`: `c_V` is bijective.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

attribute [local instance 2000] CategoryTheory.instHasWeakSheafifyOfHasSheafify
attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance] pointTopology

namespace CoherentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (D : CoherentSituation B S hS)
  (hY : IsTerminal D.Y) {k : Type u} [Field k] (toS : Spec (.of k) ⟶ S)
  (hk : B.Contains (Spec (.of k))) (x₀ : CoherentObject D)
  (hx : (coherentCFG D).val.p.obj x₀ = Deformation.Artin.algebraOver k B S hS toS hk)
  [IsAffine ((BigFppfOver.toScheme B S hS).obj x₀.T.left)]
  [HasExt.{w} (Modules.{u, u} B S hS (D.space x₀.T).1 (D.space x₀.T).2)]

/-- **The `Ext` groups of the modules on `X_T` in the spelling of its small étale ringed topos**,
those of the modules on `X_T`: the two categories are the same. -/
abbrev toposModulesHasExt :
    HasExt.{w} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space x₀.T)).O)) :=
  inferInstanceAs (HasExt.{w} (Modules.{u, u} B S hS (D.space x₀.T).1 (D.space x₀.T).2))

/-- **The map `c_V`** from `Ext¹(𝒢₀, p^*t^*𝒥 ⊗ 𝒢₀)`, where the lift differences of `x₀` across
`Spec k ⊂ Spec k[V]` live, to the receptacle `Ext¹(𝒢₀, 𝒢₀ ⊗ p^*Ṽ)`: composition with the
identification of the coefficients
(`AlgebraicGeometry.Space.CoherentSituation.tangentCoefficientIso`). -/
def tangentExtMap (V : FGModuleCat.{u} k) :
    @Abelian.Ext.{w} _ _ _ (D.toposModulesHasExt x₀) (objectToposModule x₀)
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space x₀.T)).O).flip.obj
            (objectToposModule x₀)).obj
          (D.relativeSquareSituation.testSchemeBasePullbackIdeal
            (D.squareZeroTestMap hY toS hk x₀ hx ((Deformation.Artin.fgSiteModule B hk).obj V))
            (D.isFirstOrderThickening_squareZeroTestMap hY toS hk x₀ hx _))) 1 →
      (D.tangentExtFunctor x₀ (D.chartRingEquiv x₀ hx)).obj V :=
  letI := D.toposModulesHasExt x₀
  fun ξ ↦ Deformation.ToposThickening.extCompIsoAddEquiv
    (D.tangentCoefficientIso hY hx ((Deformation.Artin.fgSiteModule B hk).obj V)) 1 ξ

/-- **`c_V` is bijective**: it is composition with an isomorphism of coefficients. -/
theorem bijective_tangentExtMap (V : FGModuleCat.{u} k) :
    Function.Bijective (D.tangentExtMap hY toS hk x₀ hx V) :=
  let := D.toposModulesHasExt x₀
  (Deformation.ToposThickening.extCompIsoAddEquiv
    (D.tangentCoefficientIso hY hx ((Deformation.Artin.fgSiteModule B hk).obj V)) 1).bijective

/-- `c_V` is injective at `V = k`, as the finite dimensionality criterion asks. -/
theorem injective_tangentExtMap_self :
    Function.Injective (D.tangentExtMap hY toS hk x₀ hx (FGModuleCat.of k k)) :=
  (D.bijective_tangentExtMap hY toS hk x₀ hx _).1

end CoherentSituation

end AlgebraicGeometry.Space

end
