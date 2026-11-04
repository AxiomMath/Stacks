module

public import Mathlib.Algebra.Module.LinearMap.Defs
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.PredeformationTangent.DifferentialLinear
public import StacksFrontier.Deformation.Schlessinger.AssociatedTangentSpace
public import StacksFrontier.Deformation.TangentSpace.Predeformation

/-!
# Linearity of the differential of a morphism of predeformation categories (Stacks 06IJ)

Let `φ : 𝓕 ⟶ 𝓖` be a morphism of predeformation categories over `𝒞_Λ` whose associated
functors of fibrewise isomorphism classes both satisfy Schlessinger's condition (S2). Then
the two tangent spaces carry the canonical `k`-vector-space structures of Stacks 06IH, and
the differential of `φ` is `k`-linear for them.

## Main results

* `Deformation.differential_isLinearMap`: the differential of `φ` is `k`-linear, and
  `Deformation.isLinearMap_of_natural_on_fgModules`: a natural family of maps between additive
  `R`-linear functors on finitely generated `R`-modules is `R`-linear at `R`; both are re-exported
  from `StacksFrontier.Deformation.PredeformationTangent.DifferentialLinear`.

## References

* [Stacks Project, Tag 06IJ](https://stacks.math.columbia.edu/tag/06IJ)
-/

@[expose] public section

end
