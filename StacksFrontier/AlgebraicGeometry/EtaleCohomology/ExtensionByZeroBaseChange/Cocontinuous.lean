module

public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SliceEquivalence
public import Mathlib.CategoryTheory.Sites.CoverLifting

/-!
# Composition with an étale morphism is cocontinuous

Let `j : U ⟶ X` be an étale morphism, viewed as an object of the small étale site of `X`.
Composition with `j` is not only a continuous functor of sites but also a *cocontinuous* one:
a covering sieve of `U'` in the small étale site of `X`, pulled back to the small étale site
of `U`, is again covering. This is immediate from the slice description of the small étale
site of `U`, since the forgetful functor of a slice site is cocontinuous.

Together with continuity this puts restriction of sheaves along `j` in the middle of an
adjoint triple `j_! ⊣ j^{-1} ⊣ j_*`, which is what makes the extension-by-zero unit and the
direct-image counit invertible whenever composition with `j` is fully faithful.

## Main results

* `AlgebraicGeometry.smallEtalePostcompose_isCocontinuous` — composition with an étale
  morphism is a cocontinuous functor of small étale sites.

## References

* [Stacks Project, Tag 00XT](https://stacks.math.columbia.edu/tag/00XT)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable (B : AlgebraicGeometry.BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)
  (U : SmallEtale B X hX)

/-- Composition with an étale morphism `U ⟶ X` is a cocontinuous functor from the small étale
site of `U` to the small étale site of `X`: under the equivalence of the small étale site of
`U` with the localization of the small étale site of `X` at `U` it becomes the forgetful
functor of that slice, which is cocontinuous. -/
public instance smallEtalePostcompose_isCocontinuous :
    (smallEtalePostcompose B X hX U).IsCocontinuous
      (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
      (SmallEtale.topology B X hX) := by
  have hslice : (smallEtaleEquivalenceOver B X hX U).functor.IsCocontinuous
      (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
      ((SmallEtale.topology B X hX).over U) := by
    rw [← smallEtaleEquivalenceOver_topology B X hX U]
    infer_instance
  rw [← smallEtaleEquivalenceOver_restriction B X hX U]
  exact isCocontinuous_comp (smallEtaleEquivalenceOver B X hX U).functor (Over.forget U)
    (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
    ((SmallEtale.topology B X hX).over U)

end AlgebraicGeometry

end
