module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.WeilIICurveBoundOfWeightBound
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.WeilIIDimensionOneGoodOpen
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SmoothSupportSpecialization

/-!
# The curve case of Weil II from opens of the affine line

Deligne's proof of the weight bound on curves (Weil II 3.2.3; Kedlaya, *Fourier transforms and
p-adic Weil II*, §6) first treats affine opens of the affine line, where the Fourier transform is
available, and then passes to a general smooth curve `U`: a dense open `U'` of `U` is finite étale
over an open `V` of `𝔸¹_k`, the lisse sheaf is pushed down to `V`, and the finitely many remaining
points are handled by excision and the bound in dimension zero. That reduction is
`Stacks.EtaleCohomology.LAdicSheaf.satisfiesWeightBound_of_topologicalKrullDim_le_one`, the weight
bound for lisse sheaves in dimension at most one; applied to `ℱ_ρ`
(`Stacks.EtaleCohomology.weilIICurveBound_of_satisfiesWeightBound`) it gives the curve case of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main results

* `Stacks.EtaleCohomology.weilIICurveBound_of_openAffineLine`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.EtaleCohomology

/-- **The curve case of Weil II from the case of affine opens of the affine line**: a smooth
separated geometrically connected curve has topological dimension one, and the weight bound for
lisse sheaves in dimension at most one, obtained from opens of `𝔸¹_k` by a finite étale map from a
dense open, excision and dimension zero, applies to `ℱ_ρ`. -/
public theorem weilIICurveBound_of_openAffineLine (h : WeilIICurveBoundOpenAffineLine.{u}) :
    WeilIICurveBound.{u} :=
  weilIICurveBound_of_satisfiesWeightBound fun B U ℓ _ _ _ _ _ _ k _ _ f _ _ _ _ kbar _ _ _ _ p n
      _ _ hcard hℓ ι => by
    have : Nonempty U.1 := ConnectedSpace.toNonempty
    exact LAdicSheaf.satisfiesWeightBound_of_topologicalKrullDim_le_one (hcard := hcard) (ι := ι)
      h hℓ U f (topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field 1 f).le

end Stacks.EtaleCohomology
