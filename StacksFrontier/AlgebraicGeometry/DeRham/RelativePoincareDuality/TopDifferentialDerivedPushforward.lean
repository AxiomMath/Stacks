module

public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.Basic
public import StacksFrontier.AlgebraicGeometry.DeRham.DerivedDirectImage
public import StacksFrontier.AlgebraicGeometry.DeRham.SchemeComplex
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.HigherDirectImageAbelianBridge
public import StacksFrontier.Algebra.Homology.DerivedCategory.StandardModelScoped

/-!
# The top de Rham differential on `Rⁿ f_*`, in the derived category of `𝒪_S`-modules

In the situation of relative Poincaré duality ([Stacks, Tag 0G8G]) [Stacks, Tag 0G8J] says that
`d : Rⁿf_*Ω^{n-1}_{X/S} ⟶ Rⁿf_*Ωⁿ_{X/S}` is zero, a statement about the higher direct images of
the underlying abelian sheaves. The proof of [Stacks, Tag 0G8K] uses it inside `D(𝒪_S)`, as the
vanishing of `Hⁿ` of the derived direct image along `(X, f⁻¹𝒪_S) ⟶ (S, 𝒪_S)` of the
differential placed in degree zero. This file passes from the first statement to the second.

## Main results

* `RelativeDualitySituation.homologyFunctor_map_derivedPushforward_deRham_d_eq_zero`: if the top
  de Rham differential vanishes on `Rⁿf_*`, it vanishes on `Hⁿ` of the derived direct image.

## Implementation notes

The derived categories are taken at the standard model (`Stacks.StandardDerivedModel`), the
model at which the relative cup product of [Stacks, Tag 0B68] is stated.

## References

* [Stacks Project, Tag 0G8J](https://stacks.math.columbia.edu/tag/0G8J)
* [Stacks Project, Tag 0G8K](https://stacks.math.columbia.edu/tag/0G8K)
* [Stacks Project, Tag 01F1](https://stacks.math.columbia.edu/tag/01F1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped Stacks.StandardDerivedModel
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
  (derivedPushforward homologyFunctor_map_derivedPushforward_singleFunctor_map_eq_zero)

universe u

namespace AlgebraicGeometry.RelativeDualitySituation

variable (D : RelativeDualitySituation.{u})

/-- **The top de Rham differential vanishes on `Hⁿ` of the derived direct image along
`(X, f⁻¹𝒪_S) ⟶ (S, 𝒪_S)`** as soon as it vanishes on the abelian higher direct image `Rⁿf_*`,
which is the statement of [Stacks, Tag 0G8J]. -/
theorem homologyFunctor_map_derivedPushforward_deRham_d_eq_zero
    (h : (Stacks.Cohomology.AbelianSheaf.higherDirectImage D.f.base D.n).map
      ((SheafOfModules.toSheaf _).map (D.f.deRhamComplex.d (D.n - 1) D.n)) = 0) :
    (DerivedCategory.homologyFunctor _ (D.n : ℤ)).map
      ((derivedPushforward (Stacks.DeRhamDirectImage.inverseImageBaseProjection D.f)).map
        ((DerivedCategory.singleFunctor _ 0).map (D.f.deRhamComplex.d (D.n - 1) D.n))) = 0 :=
  homologyFunctor_map_derivedPushforward_singleFunctor_map_eq_zero
    (Stacks.DeRhamDirectImage.inverseImageBaseProjection D.f) (D.f.deRhamComplex.d (D.n - 1) D.n)
    D.n h

end AlgebraicGeometry.RelativeDualitySituation

end
