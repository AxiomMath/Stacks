module

public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionsChartPullback

/-!
# The coefficient of a meromorphic section with a fixed numerator

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B` and let `M` be a
sheaf of `𝒪_F`-modules.  A meromorphic section of `M` over an étale scheme chart `V` is an
element of `𝒦_F(V) ⊗_{𝒪_F(V)} M(V)` (`AlgebraicGeometry.Space.meromorphicSectionModule`), and
the sections that a *local* computation produces have the shape `r ⊗ (c • m)` with `m` a fixed
numerator in `M(V)`, `c` a regular function and `r` a meromorphic function.  This file moves the
function `c` from the numerator to the coefficient, and reads off what injectivity of
multiplication on such a section says about `c`.

## Main results

* `AlgebraicGeometry.Space.meromorphicSectionModule_tmul_smul`: a function in the numerator of
  a meromorphic section can be moved to its coefficient, `r ⊗ (c • m) = (c · r) ⊗ m`.
* `AlgebraicGeometry.Space.injective_algebraMap_mul_of_injective_tmul_smul`: injectivity of
  multiplication on a meromorphic section with numerator `c • m` gives injectivity of
  multiplication by `c` on the meromorphic functions over the chart.

## References

* [Stacks Project, Tag 0EN5](https://stacks.math.columbia.edu/tag/0EN5)
* [Stacks Project, Tag 0ENB](https://stacks.math.columbia.edu/tag/0ENB)
* [Stacks Project, Tag 0ENC](https://stacks.math.columbia.edu/tag/0ENC)
-/

@[expose] public section

open CategoryTheory Opposite TensorProduct

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] chartMeromorphicAlgebra

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- A function in the numerator of a meromorphic section moves to its coefficient: for a
function `c` on an étale scheme chart `V`, a section `m` of an `𝒪_F`-module over `V` and a
meromorphic function `r` on `V`,

`r ⊗ (c • m) = (c · r) ⊗ m`

in the meromorphic sections `𝒦_F(V) ⊗_{𝒪_F(V)} M(V)` over `V`, where `c · r` is the product in
`𝒦_F(V)` of `r` with the image of `c`. -/
theorem meromorphicSectionModule_tmul_smul
    (M : Modules.{u, u} B S hS F hF) (V : SmallEtale B S hS F)
    (c : chartRing B S hS F hF V)
    (r : (meromorphicChartSheaf B S hS F hF).obj.obj (op V)) (m : M.val.obj (op V)) :
    (r ⊗ₜ[chartRing B S hS F hF V] (c • m) :
        (meromorphicSectionModule B S hS F hF M).obj (op V)) =
      (algebraMap (chartRing B S hS F hF V)
          ((meromorphicChartSheaf B S hS F hF).obj.obj (op V)) c * r) ⊗ₜ[
        chartRing B S hS F hF V] m :=
  (TensorProduct.smul_tmul (R := chartRing B S hS F hF V) c r m).symm.trans
    (congrArg (· ⊗ₜ[chartRing B S hS F hF V] m) (Algebra.smul_def c r))

/-- If `r ↦ r ⊗ (c • m)` is injective on the meromorphic functions over an étale scheme chart
`V`, then multiplication by the image of the function `c` is injective on `𝒦_F(V)`. -/
theorem injective_algebraMap_mul_of_injective_tmul_smul
    (M : Modules.{u, u} B S hS F hF) (V : SmallEtale B S hS F)
    (c : chartRing B S hS F hF V) (m : M.val.obj (op V))
    (h : Function.Injective fun r : (meromorphicChartSheaf B S hS F hF).obj.obj (op V) ↦
      (r ⊗ₜ[chartRing B S hS F hF V] (c • m) :
        (meromorphicSectionModule B S hS F hF M).obj (op V))) :
    Function.Injective fun r : (meromorphicChartSheaf B S hS F hF).obj.obj (op V) ↦
      algebraMap (chartRing B S hS F hF V)
        ((meromorphicChartSheaf B S hS F hF).obj.obj (op V)) c * r :=
  fun r r' hrr' ↦ h <| (meromorphicSectionModule_tmul_smul B S hS F hF M V c r m).trans <|
    (congrArg (· ⊗ₜ[chartRing B S hS F hF V] m) hrr').trans
      (meromorphicSectionModule_tmul_smul B S hS F hF M V c r' m).symm

end AlgebraicGeometry.Space

end
