module

public import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.AffineVanishing
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.AffineIntersectionComparison

/-!
# Čech cohomology of a quasi-coherent sheaf on a scheme

Let `X` be a scheme and let `U : I → X.Opens` be an open covering of `X` all of whose finite
intersections `U i₀ ⊓ … ⊓ U i_p` are affine.  Then for every quasi-coherent sheaf of modules `F`
on `X` the canonical comparison from the Čech cohomology of the covering to the cohomology of
`F` is an isomorphism, in every degree and as `Γ(X, 𝒪_X)`-modules.

The comparison is the component at `F` of the natural transformation
`Stacks.Cohomology.CechDerived.cechCohomologyToCohomology`, so the statement retains both its
canonical character and its naturality in the sheaf.

## Main results

* `Stacks.Cohomology.Cech.isIso_cechCohomologyToCohomology_app_of_isAffineOpen`, re-exported
  from `StacksFrontier.AlgebraicGeometry.Cohomology.Cech.AffineIntersectionComparison`, where it is
  proved together with the variant
  `Stacks.Cohomology.Cech.isIso_cechCohomologyToCohomology_app_of_affineDiagonal` for a covering
  by affine opens of a scheme with affine diagonal.

## Implementation notes

The acyclicity hypothesis of `Stacks.Cohomology.CechAcyclic.isIso_cechCohomologyToCohomology_app`
is vanishing of the module-valued right derived sections over each intersection, whereas the
vanishing available for quasi-coherent sheaves on an affine open,
`Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen`, is stated for the cohomology group of
the underlying abelian sheaf.  The two vanishings agree by
`Stacks.Cohomology.ModuleComparison.isZero_rightDerived_evaluation_iff_isZero_hgroup`.

## References

* [Stacks Project, Tag 01XD](https://stacks.math.columbia.edu/tag/01XD)
* [Stacks Project, Tag 01ET](https://stacks.math.columbia.edu/tag/01ET)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
-/
