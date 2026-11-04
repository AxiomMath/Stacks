module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ClosedSubspaceChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.StructureSheafChartStalkLength
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ClosedSubspaceCycleComponents

/-!
# The multiplicity of a component of a closed subspace, read on an étale chart

Let `Y ⊆ X` be a closed subspace of an algebraic space and let `V` be an étale scheme chart of
`X`. The base change `V ×_X Y` is an étale scheme chart of `Y` and its projection to `V` is a
closed immersion of schemes
(`AlgebraicGeometry.Space.isClosedImmersion_closedSubspaceBaseChangeChartProj`), so the
scheme-side multiplicity of Stacks 02QU, `Stacks.Chow.componentMultiplicity`, is defined at every
generic point of `V ×_X Y`. **It is the length of `𝒪_Y` at a geometric point over that generic
point**, which is the coefficient the algebraic-space theory of Stacks 0EE9 uses.

The comparison factors into two steps: the scheme-side multiplicity is the length of the stalk
of the subscheme over *itself* (`Stacks.Chow.componentMultiplicity_eq_length_stalk`, by
surjectivity of the stalk map of a closed immersion), and that length is the length of `𝒪_Y` at
the geometric point
(`AlgebraicGeometry.Space.geometricLength_structureSheafModule_eq_length_chartStalk`, Stacks 0EE1
on the chart). Nothing here needs `Y` integral, or the chart affine, or any Noetherian hypothesis.

## Main results

* `AlgebraicGeometry.Space.componentMultiplicity_closedSubspaceBaseChangeChartProj`: the
  multiplicity of a component of `V ×_X Y ⊆ V` is the length of `𝒪_Y` at a geometric point over
  its generic point.
* `AlgebraicGeometry.Space.closedSubspaceMultiplicity_eq_componentMultiplicity`: the same
  comparison in the terms of Stacks 0EE9 part (1), at the multiplicity `m_{W, Y}` of an integral
  closed subspace `W ⊆ Y`.

## References

* [Stacks Project, Tag 02QU](https://stacks.math.columbia.edu/tag/02QU)
* [Stacks Project, Tag 0EE1](https://stacks.math.columbia.edu/tag/0EE1)
* [Stacks Project, Tag 0EE9](https://stacks.math.columbia.edu/tag/0EE9)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The multiplicity of a component of the chart base change of a closed subspace is the length
of the structure sheaf of the subspace at a geometric point.** Let `Y ⊆ X` be a closed subspace of
an algebraic space, `V` an étale scheme chart of `X`, and `ξ` a generic point of the chart
`V ×_X Y` of `Y`. Then the multiplicity of Stacks 02QU of that component of the closed subscheme
`V ×_X Y ⊆ V` is the length of `𝒪_Y` at any geometric point of `Y` over the point of `|Y|` that
`ξ` determines.

The multiplicity is the length of the stalk of `V ×_X Y` at `ξ` over itself
(`Stacks.Chow.componentMultiplicity_eq_length_stalk`), and that is the length of `𝒪_Y` at the
geometric point
(`AlgebraicGeometry.Space.geometricLength_structureSheafModule_eq_length_chartStalk`). -/
theorem componentMultiplicity_closedSubspaceBaseChangeChartProj
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (Y : Subfunctor X) (hY : IsClosedSubspace B S hS Y) (V : SmallEtale B S hS X)
    (xbar : GeometricPoint B S hS Y.toFunctor)
    (ξ : genericPoints (chartScheme (closedSubspaceBaseChangeChart B S hS hX Y hY V)))
    (hξ : chartSchemeToPoints B S hS Y.toFunctor
        (closedSubspaceBaseChangeChart B S hS hX Y hY V) ξ.1 = xbar.image) :
    haveI := isClosedImmersion_closedSubspaceBaseChangeChartProj B S hS hX Y hY V
    Stacks.Chow.componentMultiplicity
        (closedSubspaceBaseChangeChartProj B S hS hX Y hY V) ξ =
      ((geometricLength B S hS ⟨Y.toFunctor, hY.1⟩ xbar
        (structureSheafModule B S hS ⟨Y.toFunctor, hY.1⟩)).toNat : ℤ) := by
  have := isClosedImmersion_closedSubspaceBaseChangeChartProj B S hS hX Y hY V
  rw [Stacks.Chow.componentMultiplicity_eq_length_stalk
      (closedSubspaceBaseChangeChartProj B S hS hX Y hY V) ξ,
    geometricLength_structureSheafModule_eq_length_chartStalk B S hS
      ⟨Y.toFunctor, hY.1⟩ xbar (closedSubspaceBaseChangeChart B S hS hX Y hY V) ξ.1 hξ]

/-- **The multiplicity of Stacks 0EE9 part (1) is the multiplicity of Stacks 02QU on a chart.**
Let `Y ⊆ X` be a closed subspace in Situation 0EDT, let `W ⊆ Y` be an integral closed subspace,
let `V` be an étale scheme chart of `X` and let `ξ` be a generic point of the chart `V ×_X Y` of
`Y` lying over the generic point of `W`. Then the multiplicity `m_{W, Y}` of the algebraic-space
theory is the multiplicity of that component of the closed subscheme `V ×_X Y ⊆ V`.

`m_{W, Y}` is a length at a geometric point, and it is the length at *any* geometric point over
the generic point of `W` (Stacks 0EE1,
`AlgebraicGeometry.Space.closedSubspaceMultiplicity_eq_toNat_geometricLength`), so it is
`AlgebraicGeometry.Space.componentMultiplicity_closedSubspaceBaseChangeChartProj` read at the
canonical representative. -/
theorem closedSubspaceMultiplicity_eq_componentMultiplicity
    (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace D.site D.base D.base_mem X)
    (Y : Subfunctor X) (hY : IsClosedSubspace D.site D.base D.base_mem Y)
    (V : SmallEtale D.site D.base D.base_mem X)
    (W : IntegralClosedSubspace D.site D.base D.base_mem Y.toFunctor)
    (ξ : genericPoints
      (chartScheme (closedSubspaceBaseChangeChart D.site D.base D.base_mem hX Y hY V)))
    (hξ : chartSchemeToPoints D.site D.base D.base_mem Y.toFunctor
        (closedSubspaceBaseChangeChart D.site D.base D.base_mem hX Y hY V) ξ.1 =
      W.ambientGenericPoint D.site D.base D.base_mem) :
    haveI := isClosedImmersion_closedSubspaceBaseChangeChartProj D.site D.base D.base_mem
      hX Y hY V
    closedSubspaceMultiplicity D Y hY W =
      Stacks.Chow.componentMultiplicity
        (closedSubspaceBaseChangeChartProj D.site D.base D.base_mem hX Y hY V) ξ := by
  have := isClosedImmersion_closedSubspaceBaseChangeChartProj D.site D.base D.base_mem hX Y hY V
  rw [closedSubspaceMultiplicity_eq_toNat_geometricLength D Y hY W
      (canonicalGeometricPoint D.site D.base D.base_mem Y.toFunctor
        (W.ambientGenericPoint D.site D.base D.base_mem))
      (canonicalGeometricPoint_image D.site D.base D.base_mem Y.toFunctor
        (W.ambientGenericPoint D.site D.base D.base_mem)),
    componentMultiplicity_closedSubspaceBaseChangeChartProj D.site D.base D.base_mem hX Y hY V
      (canonicalGeometricPoint D.site D.base D.base_mem Y.toFunctor
        (W.ambientGenericPoint D.site D.base D.base_mem)) ξ
      (hξ.trans (canonicalGeometricPoint_image D.site D.base D.base_mem Y.toFunctor
        (W.ambientGenericPoint D.site D.base D.base_mem)).symm)]

end AlgebraicGeometry.Space

end
