module

public import StacksFrontier.AlgebraicGeometry.Ample.DescentStep
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeIdEtaleChartTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmple

/-!
# The reading of an invertible module on a scheme over an algebraic space is invertible

Let `X` be an algebraic space over the base and `L` an invertible `𝒪_X`-module. For a scheme `U`
over the base and a morphism `p` from the algebraic space `U` represents to `X`, the pullback of
`L` to `U`, read as a module on the scheme `U`
(`AlgebraicGeometry.Space.baseChangeModule`), is an invertible `𝒪_U`-module.

## Main results

* `AlgebraicGeometry.Space.isInvertibleModule_baseChangeModule`: the statement above.

## The route

Invertibility is the existence of a tensor inverse, [Stacks, Tag 0B8K]. The pullback of `L` to
the small étale site of `U` is invertible, [Stacks, Tag 0B8P]; let `N'` be a tensor inverse of
it there, itself invertible and hence quasi-coherent. The reading on the scheme `U` is compatible
with the tensor product of quasi-coherent modules
(`AlgebraicGeometry.Space.restrictToChartSchemeIdEtaleChartTensorIso`) and with the structure
sheaf (`AlgebraicGeometry.Space.restrictToChartSchemeUnitIso`), so the reading of `N'` is a
tensor inverse of the reading of the pullback of `L`.

## References

* [Stacks Project, Tag 0B8K](https://stacks.math.columbia.edu/tag/0B8K)
* [Stacks Project, Tag 0B8P](https://stacks.math.columbia.edu/tag/0B8P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] modulesMonoidalCategory

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The pullback of an invertible module to a scheme over an algebraic space is invertible.**
For an invertible `𝒪_X`-module `L`, a scheme `U` of the site and a morphism `p` from the algebraic
space `U` represents to `X`, the `𝒪_U`-module `AlgebraicGeometry.Space.baseChangeModule L U p` is
invertible. -/
theorem isInvertibleModule_baseChangeModule {X : AlgebraicSpaces B S hS}
    (L : Modules.{u, u} B S hS X.1 X.2)
    (hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).property L)
    (U : BigFppfOver B S hS) (p : yoneda.obj U ⟶ X.1) :
    Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj U)
      (baseChangeModule B S hS L U p) := by
  let U' : AlgebraicSpaces B S hS := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩
  let f : U' ⟶ X := ObjectProperty.homMk p
  let N := (modulePullback B S hS f).obj L
  have hN := Stacks.SheafOfModules.isInvertible_pullbackModules_obj
    (f := smallEtaleRingedToposModulesHom B S hS f) (L := L) (hL := hL)
  obtain ⟨N₀, ⟨e⟩⟩ := (Stacks.SheafOfModules.Invertible.isInvertible_iff_exists_tensor_iso_unit
    _ _ _).1 hN
  let N' : Modules.{u, u} B S hS U'.1 U'.2 := N₀
  have hN' := Stacks.SheafOfModules.Invertible.isInvertible_of_tensor_iso_unit _
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS U').O).property (N := N)
    ((modulesTensorObjIso B S hS _ _ N' N).symm ≪≫
      (modulesBraidedCategory B S hS U'.1 U'.2).braiding N' N ≪≫
      modulesTensorObjIso B S hS _ _ N N' ≪≫ e)
  have qN : N.IsQuasicoherentOnSite := isQuasicoherentOnSite_modulePullback_of_isInvertible f L hL
  have qN' : N'.IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_of_isInvertible B S hS _ _ (hN'.toAlgebraicGeometry _ _ _)
  let t := restrictToChartSchemeIdEtaleChartTensorIso B S hS U N N' qN qN'
  let r := restrictToChartSchemeFunctor B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)
    (idEtaleChart B S hS U)
  let v := restrictToChartSchemeUnitIso B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)
    (idEtaleChart B S hS U)
  let e' := t.symm ≪≫ r.mapIso (modulesTensorObjIso B S hS _ _ N N' ≪≫ e) ≪≫ v
  exact
    (Stacks.SheafOfModules.Invertible.isInvertible_of_tensor_iso_unit _ _ e').toAlgebraicGeometry
      _ _ _

end AlgebraicGeometry.Space

end
