module

public import StacksFrontier.AlgebraicGeometry.DeRham.DifferentialGradedAlgebra.Basic

/-!
# The graded Leibniz rule for a wedge with a one-form, without degree transports

`AlgebraicGeometry.SheafOfModules.d_formProduct` of
`StacksFrontier.AlgebraicGeometry.DeRham.DifferentialGradedAlgebra.Basic` is the graded Leibniz rule

`d (ω ∧ η) = d ω ∧ η + (-1)^p ω ∧ d η`

on local sections of the exterior powers of the sheaf of relative differentials. Because the
degrees of the two products on the right are `p + 1 + q` and `p + (q + 1)` while the target has
degree `p + q + 1`, the statement carries two `HomologicalComplex.XIsoOfEq` transports.

At `q = 1` both of those are `HomologicalComplex.XIsoOfEq` at a proof of
`p + 1 + 1 = p + 1 + 1`, and at `q = 0` both are `HomologicalComplex.XIsoOfEq` at a proof of
`p + 1 = p + 1`, so in either case they are identities. This file records the rule with them
removed, which is the form every computation that wedges a form with the differential of a
function needs:
with the transports present, the residual goal `XIsoOfEq.hom.val.app U x = x` is not closed by
`rfl`, and `rw`/`map_zero` against that morphism run into the `TopCat.Sheaf` versus
`Sheaf (Opens.grothendieckTopology X)` instance clash documented in the implementation notes of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkwiseExactness`. Stating the rule once, here,
at the transport-free shape keeps that clash out of every consumer.

## Main results

* `AlgebraicGeometry.SheafOfModules.d_formProduct_one`: **the graded Leibniz rule for a wedge
  with a one-form**, with no transport along an equality of degrees.
* `AlgebraicGeometry.SheafOfModules.d_formProduct_zero`: **the same for a wedge with a
  degree-zero form**, which is the rule against a scalar once the degree-zero form is written as
  a multiple of the unit.

## Implementation notes

The proof is `AlgebraicGeometry.SheafOfModules.d_formProduct` at `q = 1` and nothing else: the
two statements are definitionally equal, because a proof of `p + 1 + 1 = p + 1 + 1` is
definitionally `rfl` by proof irrelevance and `HomologicalComplex.XIsoOfEq` at `rfl` is the
identity. The degree arithmetic reduces because `Nat.add` recurses on its second argument, so
`p + 0` is `p` and `p + 1 + 0` is `p + 1` with no rewriting. What the restatement buys is that the
*syntactic* form a consumer sees carries no `XIsoOfEq`, so `rw` and `map_zero` act on the products
directly.

**Where this belongs.** Beside `d_formProduct` itself, in
`StacksFrontier.AlgebraicGeometry.DeRham.DifferentialGradedAlgebra.Basic`. It is in its own file
only to keep two concurrent lines of work off the same file, and a later structural pass should
re-home it there; it is stated at that file's own variables, so moving it is a cut and paste.

## References

* [Stacks Project, Tag 0FM2](https://stacks.math.columbia.edu/tag/0FM2)
* [Stacks Project, Tag 0FKM](https://stacks.math.columbia.edu/tag/0FKM)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.SheafOfModules

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))
  (D : DeRhamDifferential B)

/-- **The graded Leibniz rule for a wedge with a one-form, on local sections**:

`d (ω ∧ ξ) = d ω ∧ ξ + (-1)^p ω ∧ d ξ`

for a local section `ω` of `⋀ᵖ Ω` and a local section `ξ` of `Ω`. This is
`AlgebraicGeometry.SheafOfModules.d_formProduct` at `q = 1`, where both of its degree
reindexings are the identity, so no transport along an equality of degrees appears. -/
theorem d_formProduct_one (p : ℕ) (U : (Opens X.carrier)ᵒᵖ)
    (ω : (B.exteriorPower p).val.obj U) (ξ : (B.exteriorPower 1).val.obj U) :
    ((deRhamComplex B D).d (p + 1) (p + 1 + 1)).val.app U (formProduct B p 1 U ω ξ) =
      formProduct B (p + 1) 1 U (((deRhamComplex B D).d p (p + 1)).val.app U ω) ξ +
        (-1 : ℤ) ^ p • formProduct B p 2 U ω
          (((deRhamComplex B D).d 1 (1 + 1)).val.app U ξ) :=
  d_formProduct B D p 1 U ω ξ

/-- **The graded Leibniz rule for a wedge with a degree-zero form, on local sections**:

`d (ω ∧ c) = d ω ∧ c + (-1)^p ω ∧ d c`

for a local section `ω` of `⋀ᵖ Ω` and a local section `c` of `⋀⁰ Ω`. This is
`AlgebraicGeometry.SheafOfModules.d_formProduct` at `q = 0`, where both of its degree
reindexings are the identity, so no transport along an equality of degrees appears. Taking `c` to
be a multiple `a · 1` of the unit turns it into the Leibniz rule against the scalar `a`, in the
right-handed form `d (a · ω) = a · d ω + (-1)^p (ω ∧ d a)`. -/
theorem d_formProduct_zero (p : ℕ) (U : (Opens X.carrier)ᵒᵖ)
    (ω : (B.exteriorPower p).val.obj U) (c : (B.exteriorPower 0).val.obj U) :
    ((deRhamComplex B D).d p (p + 1)).val.app U (formProduct B p 0 U ω c) =
      formProduct B (p + 1) 0 U (((deRhamComplex B D).d p (p + 1)).val.app U ω) c +
        (-1 : ℤ) ^ p • formProduct B p 1 U ω
          (((deRhamComplex B D).d 0 (0 + 1)).val.app U c) :=
  d_formProduct B D p 0 U ω c

end AlgebraicGeometry.SheafOfModules

end
