module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackDeformationBridge.DifferenceExt
public import StacksFrontier.AlgebraicGeometry.Quot.Helpers.ThickeningIdealTilde

/-!
# The map of coefficient modules induced by a morphism of thickenings

Let `ξ = (T, 𝒢)` be an object of `Coh_{X/Y}` (Stacks 08KB) and `h : T ⟶ T'`, `h₂ : T ⟶ T'₂` affine
first order thickenings with a morphism `g : T'₂ ⟶ T'` under `T`. The map `𝒥 ⟶ 𝒥₂` of ideals
induced by `g^♯` gives the map `λ_g : t^*𝒥 ⟶ t₂^*𝒥₂` on `T`
(`AlgebraicGeometry.Space.thickeningIdealMap`), and hence the map
`𝒢 ⊗ f_T^*𝒥 ⟶ 𝒢 ⊗ f_T^*𝒥₂` of the coefficient modules of the deformations of `ξ` across `h` and
`h₂`. This is the map along which the classes of lifts are compared
(`AlgebraicGeometry.Space.CoherentSituation.thickeningLiftDifference_pullback`).

## Main definitions

* `AlgebraicGeometry.Space.CoherentSituation.thickeningCoefficientMap`.

## References

* [Stacks Project, Tag 08KB](https://stacks.math.columbia.edu/tag/08KB)
* [Stacks Project, Tag 0CYE](https://stacks.math.columbia.edu/tag/0CYE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.CoherentSituation

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {D : CoherentSituation B S hS}
  {ξ : CoherentObject D} {T' T'₂ : SchemesOver D.Y} {h : ξ.T ⟶ T'} {h₂ : ξ.T ⟶ T'₂}

/-- `h₂ ≫ g = h` on the underlying morphisms of `BigFppfOver`. -/
theorem left_comp_left_eq_of_comp_eq (g : T'₂ ⟶ T') (hg : h₂ ≫ g = h) : h₂.left ≫ g.left = h.left :=
  congrArg CommaMorphism.left hg

variable [IsAffine ((BigFppfOver.toScheme B S hS).obj ξ.T.left)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T'.left)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T'₂.left)]

/-- **The map `𝒢 ⊗ f_T^*𝒥 ⟶ 𝒢 ⊗ f_T^*𝒥₂` of coefficient modules induced by `g : T'₂ ⟶ T'`
under `T`**: `𝒢` tensored with the pullback along `X_T ⟶ T` of the map
`λ_g : t^*𝒥 ⟶ t₂^*𝒥₂` of pulled-back ideals (`AlgebraicGeometry.Space.thickeningIdealMap`). -/
def thickeningCoefficientMap (g : T'₂ ⟶ T') (hg : h₂ ≫ g = h)
    (hh : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h.left))
    (hh₂ : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h₂.left)) :
    thickeningCoefficient ξ h hh ⟶ thickeningCoefficient ξ h₂ hh₂ :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
    (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space ξ.T)).O).flip.obj
      (objectToposModule ξ)).map
    ((smallEtaleRingedToposHom B S hS
      (D.relativeSquareSituation.projection ξ.T)).toRingedToposModulesHom.pullbackModules.map
      (thickeningIdealMap h.left h₂.left g.left (left_comp_left_eq_of_comp_eq g hg)
        (isIso_toRange_testSchemeMap h hh) (isFirstOrderThickening_range_yoneda_map B S hS _ hh)
        (isIso_toRange_testSchemeMap h₂ hh₂) (isFirstOrderThickening_range_yoneda_map B S hS _ hh₂)
        hh hh₂))

end AlgebraicGeometry.Space.CoherentSituation

end
