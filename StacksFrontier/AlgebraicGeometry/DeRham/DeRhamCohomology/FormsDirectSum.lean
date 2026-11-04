module

public import StacksFrontier.AlgebraicGeometry.DeRham.DeRhamCohomology.FormsDirectSum.GradedExteriorAlgebra
public import StacksFrontier.AlgebraicGeometry.DeRham.DeRhamCohomology.FormsDirectSum.Decomposition

/-!
# The grading on differential forms

Let `A` be a commutative `R`-algebra graded by an additive commutative monoid `G`. If the grading
is an internal direct sum and multiplication respects degrees, then for every `p` the homogeneous
differential forms of each total degree give an internal direct-sum decomposition of the `p`-th
exterior power of the module of Kähler differentials. The wedge product is compatible with the
two gradings: it adds both the exterior degree and the total degree.

## Main results

* `KaehlerDifferential.gradedDifferentialFormComponent_wedgeMul_mem`: the wedge product of a form
  of exterior degree `p` and total degree `g` with a form of exterior degree `q` and total degree
  `h` lies in the component of exterior degree `p + q` and total degree `g + h`.
* `KaehlerDifferential.isInternal_gradedDifferentialFormComponent`: the homogeneous components of
  the `p`-forms are an internal direct sum.

## Implementation notes

The proof builds the graded exterior algebra of the graded module of Kähler differentials and
identifies it with the exterior algebra of the underlying module, from which the direct-sum
decomposition of each exterior power follows by taking the degree-`p` part. The intermediate
constructions — the graded module structure on differential forms, the graded algebra structure
on the homogeneous components of the exterior algebra, and the graded map induced by the
universal derivation — are all private to this file, since they exist only to carry that
identification.

Both grading hypotheses are used: the internal direct-sum decomposition of `A` supplies the
decomposition of the differentials, and compatibility of multiplication with degrees is what
makes the homogeneous components of the exterior algebra closed under multiplication.

## References

* [Stacks Project, Tag 0FU9](https://stacks.math.columbia.edu/tag/0FU9)
-/
