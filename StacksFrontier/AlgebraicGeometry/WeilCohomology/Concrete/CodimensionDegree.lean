module

public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.DegreeHomomorphism
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.WeilData
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.SmoothProjectiveComposition

/-!
# The degree of a class of top codimension

Let `X` be a smooth projective scheme over a field `k`. For `X` equidimensional of dimension `d`
the group `CH^d(X)` of the codimension grading is the group `CH_0(X)` of zero cycles, and the
degree of zero cycles of Chow Homology, Section 0AZ0, is a homomorphism `deg : CH^d(X) → ℤ`.
This file records it on the codimension-graded Chow groups
`CH^d(X) = ∏_e CH_{e-d}(X_e)` of `Stacks.Chow.codimensionChowGroup`: it is the degree
`Stacks.Chow.chowDegree` (Stacks 0AZ1) of the component on the part `X_d` of `X` of dimension
`d`, which is all of `X` when `X` is equidimensional of dimension `d`.

## Main definitions

* `Stacks.WeilCohomology.codimensionDegree`: `deg : CH^d(X) → ℤ`.

## References

* [Stacks Project, Section 0AZ0](https://stacks.math.columbia.edu/tag/0AZ0)
* [Stacks Project, Tag 0AZ1](https://stacks.math.columbia.edu/tag/0AZ1)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.Chow

universe u

namespace Stacks.WeilCohomology

variable {k : Type u} [Field k]

/-- **The degree `deg : CH^d(X) → ℤ`** of a class of codimension `d` on a smooth projective
scheme `X` over `k` (Chow Homology, Section 0AZ0): the degree of zero cycles (Stacks 0AZ1) of its
component `CH_{d-d}(X_d) = CH_0(X_d)` on the part `X_d` of `X` of dimension `d`. When `X` is
equidimensional of dimension `d`, `X_d = X` and `CH^d(X) = CH_0(X)`, and this is the degree of
zero cycles on `X`. -/
def codimensionDegree (X : (SmoothProjectiveScheme k).FullSubcategory) (d : ℕ) :
    codimensionChowGroup k X.obj.hom d →+ ℤ :=
  (chowDegree (fieldChowSituation k) (fun _ ↦ rfl)
      (partBase X.obj.hom d) (genericPoint (fieldChowSituation k).S)).comp <|
    (chowGroupDegreeEquiv _ _ (sub_self (d : ℤ))).toAddMonoidHom.comp <|
      Pi.evalAddMonoidHom (fun e : ℕ ↦ chowGroup (fieldChowSituation k) (partBase X.obj.hom e)
        ((e : ℤ) - d)) d

/-- The degree `codimensionDegree X d α` of `α ∈ CH^d(X)` is the degree `chowDegree` of the
component `α d ∈ CH_0(X_d)` of `α` on the part `X_d` of `X` of dimension `d`. -/
theorem codimensionDegree_apply (X : (SmoothProjectiveScheme k).FullSubcategory) (d : ℕ)
    (α : codimensionChowGroup k X.obj.hom d) :
    codimensionDegree X d α =
      chowDegree (fieldChowSituation k) (fun _ ↦ rfl)
        (partBase X.obj.hom d) (genericPoint (fieldChowSituation k).S)
        (chowGroupDegreeEquiv _ _ (sub_self (d : ℤ)) (α d)) :=
  rfl

end Stacks.WeilCohomology

end
