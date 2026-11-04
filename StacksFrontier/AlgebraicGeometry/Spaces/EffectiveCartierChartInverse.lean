module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeIdEtaleChartTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionEtalePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionIdealSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartIdealSheafPreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierDivisor
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleIdealSheafRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmple
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafChartRestriction

/-!
# The invertible sheaf of an effective Cartier divisor on an étale chart

Let `X` be an algebraic space over a scheme `S`, let `D ⊆ X` be an effective Cartier divisor and
let `c : U ⟶ X` be an étale morphism from a scheme `U` of the site.  The base change
`c^*𝒪_X(D)` of the invertible sheaf `𝒪_X(D)` of Stacks 0841 is a tensor inverse of the ideal
sheaf of the closed subscheme `D ×_X U` of `U`:

`c^*𝒪_X(D) ⊗_{𝒪_U} 𝓘_{D ×_X U} ≅ 𝒪_U`.

## Main results

* `AlgebraicGeometry.Space.nonempty_tensor_baseChangeModule_negativeTwist_iso_unit`.

## Implementation notes

The evaluation pairing `𝒪_X(D) ⊗ 𝓘_D ≅ 𝒪_X` is pulled back to `U`.  The base change of a module
to a scheme over `X` (`AlgebraicGeometry.Space.baseChangeModule`) is the inverse image of
Stacks 03LU followed by restriction to the Zariski site of the identity chart; both steps are
compatible with tensor products of quasi-coherent modules and carry the structure sheaf to the
structure sheaf.  Along the étale `c` the inverse image of `𝓘_D` is its étale restriction, which
is `𝓘_{c⁻¹D}` (Stacks 04CO), and the restriction of that sheaf of ideals to the scheme of the
chart is the ideal sheaf of the induced sheaf of ideals on `U`
(`AlgebraicGeometry.Space.restrictToChartSchemeIsoNegativeTwist`); the latter is the kernel of
the base change `D ×_X U ⟶ U` by `AlgebraicGeometry.Space.ker_rep_snd_eq_idealSheafDataOfChart`.

## References

* [Stacks Project, Tag 0841](https://stacks.math.columbia.edu/tag/0841)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 04CO](https://stacks.math.columbia.edu/tag/04CO)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace MonoidalCategory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] modulesMonoidalCategory

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The étale chart of `X` given by an étale morphism from a scheme of the site. -/
abbrev etaleChartOfHom {X : AlgebraicSpaces B S hS} {U : BigFppfOver B S hS}
    (c : yoneda.obj U ⟶ X.1)
    (hc : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) c) : SmallEtale B S hS X.1 :=
  ⟨CostructuredArrow.mk c, hc⟩

/-- The base change of the ideal sheaf of a closed subspace to an étale chart is the ideal sheaf
of the induced sheaf of ideals on that chart. -/
def baseChangeModuleIdealSheafIso {X : AlgebraicSpaces B S hS} (D : ClosedSubspaces B S hS X.1)
    {U : BigFppfOver B S hS} (c : yoneda.obj U ⟶ X.1)
    (hc : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) c) :
    baseChangeModule B S hS (idealSheafOfModules B S hS X D) U c ≅
      Stacks.Divisors.negativeTwist' (idealSheafDataOfChart B S hS X (definingIdealSheaf B S hS X D)
        (definingIdealSheaf_isCartesianOnAffineCharts B S hS X D) (etaleChartOfHom c hc)) :=
  (restrictToChartSchemeFunctor B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)
      (idEtaleChart B S hS U)).mapIso
    ((modulePullbackIsoEtaleModulePullback B S hS
      (chartToSpace B S hS X (etaleChartOfHom c hc))
      (isEtale_chartToSpace B S hS X (etaleChartOfHom c hc))).app _) ≪≫
  eqToIso (restrictToChartScheme_etaleModulePullback_idEtaleChart B S hS X _
    (etaleChartOfHom c hc)) ≪≫
  restrictToChartSchemeIsoNegativeTwist X (definingIdealSheaf B S hS X D)
    (definingIdealSheaf_isCartesianOnAffineCharts B S hS X D) (etaleChartOfHom c hc)

/-- **The base change of `𝒪_X(D)` to an étale chart is a tensor inverse of the ideal sheaf of the
divisor on that chart.**  For an effective Cartier divisor `D` on an algebraic space `X` and an
étale morphism `c : U ⟶ X` from a scheme of the site,

`c^*𝒪_X(D) ⊗_{𝒪_U} 𝓘_{D ×_X U} ≅ 𝒪_U`,

where `𝓘_{D ×_X U}` is the ideal sheaf of the sheaf of ideals that `𝓘_D` induces on `U`. -/
theorem nonempty_tensor_baseChangeModule_negativeTwist_iso_unit {X : AlgebraicSpaces B S hS}
    (D : ClosedSubspaces B S hS X.1) (hD : IsEffectiveCartierDivisor B S hS X D)
    {U : BigFppfOver B S hS} (c : yoneda.obj U ⟶ X.1)
    (hc : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) c) :
    Nonempty (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((BigFppfOver.toScheme B S hS).obj U).presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ ((BigFppfOver.toScheme B S hS).obj U).presheaf
          (forget₂ CommRingCat RingCat) ((BigFppfOver.toScheme B S hS).obj U).ringCatIsSheaf⟩).obj
        (baseChangeModule B S hS (associatedInvertibleSheaf B S hS X D hD) U c)).obj
        (Stacks.Divisors.negativeTwist' (idealSheafDataOfChart B S hS X
          (definingIdealSheaf B S hS X D) (definingIdealSheaf_isCartesianOnAffineCharts B S hS X D)
          (etaleChartOfHom c hc))) ≅
      _root_.SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf
        ((BigFppfOver.toScheme B S hS).obj U).presheaf
        ((BigFppfOver.toScheme B S hS).obj U).ringCatIsSheaf)) := by
  set L := associatedInvertibleSheaf B S hS X D hD
  set J := idealSheafOfModules B S hS X D
  let p : (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS) ⟶ X :=
    ObjectProperty.homMk c
  let r := restrictToChartSchemeFunctor B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)
    (idEtaleChart B S hS U)
  have hLq := isQuasicoherentOnSite_modulePullback_of_isInvertible p L
    ((Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mpr
      (associatedInvertibleSheaf_isInvertible B S hS X D hD))
  have hJq := isQuasicoherentOnSite_modulePullback_of_isInvertible p J
    ((Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mpr hD)
  have e1 := restrictToChartSchemeIdEtaleChartTensorIso B S hS U _ _ hLq hJq
  have e2 := r.mapIso (modulePullbackTensorIso B S hS p L J)
  have e3 := r.mapIso ((modulePullback B S hS p).mapIso
    (modulesTensorObjIso B S hS X.1 X.2 L J ≪≫ associatedInvertibleSheafEvaluation B S hS X D hD))
  have e4 := r.mapIso (modulePullbackUnitIso B S hS p) ≪≫
    restrictToChartSchemeUnitIso B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)
      (idEtaleChart B S hS U)
  exact ⟨((Stacks.SheafOfModules.Tensor.sheafTensor _).obj _).mapIso
      (baseChangeModuleIdealSheafIso D c hc).symm ≪≫ e1.symm ≪≫ e2.symm ≪≫ e3 ≪≫ e4⟩

end AlgebraicGeometry.Space

end
