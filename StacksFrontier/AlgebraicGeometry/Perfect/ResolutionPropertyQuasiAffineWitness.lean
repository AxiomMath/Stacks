module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Perfect.ResolutionPropertyAmple
public import StacksFrontier.AlgebraicGeometry.Perfect.ResolutionPropertyQuasiAffineHom
public import StacksFrontier.AlgebraicGeometry.Scheme.Affine.PuncturedPlaneNotAffine
public import StacksFrontier.Examples.Scheme.PinchedPlane.Variety

/-!
# A quasi-affine, non-affine witness for the resolution property going up

[Stacks, Tag 0F88] is stated for a morphism that is affine **or** quasi-affine. The affine branch
and the quasi-affine branch are both proved, in
`StacksFrontier/AlgebraicGeometry/Perfect/ResolutionPropertyAffineHom.lean` and
`StacksFrontier/AlgebraicGeometry/Perfect/ResolutionPropertyQuasiAffineHom.lean`. This file records
that the quasi-affine branch is not a restatement of the affine one: it exhibits a morphism to
which the tagged theorem applies and the affine declaration does not.

The witness is the structure morphism of the punctured plane `A²_k ∖ {0}` over `Spec k`. The
punctured plane is quasi-affine (`Stacks.Examples.PinchedPlane.puncturedPlane_isQuasiAffine`) and
is not affine (`AlgebraicGeometry.not_isAffine_puncturedScheme`, Tag 01IL), so the morphism is
quasi-affine (by the instance
`AlgebraicGeometry.isQuasiAffineHom_of_isQuasiAffine_of_quasiSeparatedSpace`) and not affine, and
the resolution property of `A²_k ∖ {0}` is a conclusion only the quasi-affine branch delivers.

## Main results

* `Stacks.Examples.PinchedPlane.not_isAffineHom_puncturedPlaneStructure`: the witness morphism
  does not satisfy the hypothesis of the affine branch.
* `Stacks.Examples.PinchedPlane.hasResolutionProperty_puncturedPlane`: the punctured plane has
  the resolution property.

## Implementation notes

The remaining hypotheses of [Stacks, Tag 0F88] hold at `Y = Spec k` for the cheapest possible
reasons: `CompactSpace` and `QuasiSeparatedSpace` are instances for an affine scheme, and the
resolution property comes from [Stacks, Tag 0F87]
(`AlgebraicGeometry.hasResolutionProperty_of_isAmple`) applied to `𝒪_Y`, which is ample because
an affine scheme is quasi-affine ([Stacks, Tag 01QE],
`Stacks.Ample.isAmple_unitModule_of_isAffine`).

No tag sits on anything here. These are not clauses of [Stacks, Tag 0F88]; they are a witness
that its quasi-affine clause has content, and the tag's covering set is unchanged.

## References

* [Stacks Project, Tag 0F88](https://stacks.math.columbia.edu/tag/0F88)
* [Stacks Project, Tag 01IL](https://stacks.math.columbia.edu/tag/01IL)
* [Stacks Project, Tag 0F87](https://stacks.math.columbia.edu/tag/0F87)
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace Stacks.Examples.PinchedPlane

variable (k : Type u) [Field k]

/-- **The structure morphism of the punctured plane is not affine.** The source of an affine
morphism to an affine scheme is affine, and the punctured plane is not
([Stacks, Tag 01IL]). -/
theorem not_isAffineHom_puncturedPlaneStructure :
    ¬ IsAffineHom (puncturedPlaneStructure k) := fun h =>
  not_isAffine_puncturedScheme (puncturedAffinePlaneOf k)
    (@isAffine_of_isAffineHom _ _ (puncturedPlaneStructure k) h inferInstance)

/-- **The punctured plane has the resolution property.** This is [Stacks, Tag 0F88] at a morphism
that is quasi-affine and not affine, so the quasi-affine branch of that lemma is the only one
that reaches it. -/
theorem hasResolutionProperty_puncturedPlane : HasResolutionProperty (puncturedPlane k) :=
  have : HasResolutionProperty (Spec (.of k)) :=
    hasResolutionProperty_of_isAmple (Stacks.Ample.unitModule _)
      (Stacks.Ample.isAmple_unitModule_of_isAffine _)
  hasResolutionProperty_of_isAffineHom_or_isQuasiAffineHom (puncturedPlaneStructure k)
    (Or.inr inferInstance)

end Stacks.Examples.PinchedPlane

end
