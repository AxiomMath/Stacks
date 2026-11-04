module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import StacksFrontier.AlgebraicGeometry.CurveLocalRing.ClosedPointDivisor
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.KoszulRegularSmoothCover
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SectionSchemeTheoreticImage
public import StacksFrontier.AlgebraicGeometry.Picard.DivisorSheafDegree
public import StacksFrontier.AlgebraicGeometry.Properties.NoetherianClosedPoints
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme

/-!
# The degree homomorphism of a smooth projective curve is onto `𝐙`

Let `X` be a curve over an algebraically closed field `k`, smooth and proper over `k`. Then
`deg : Pic(X) ⟶ 𝐙` is surjective. The class of degree one is the one supplied by a closed point
`x` of `X`, taken with its reduced closed subscheme structure.

Three facts meet. A closed point of a scheme locally of finite type over an algebraically closed
field is the image of a `k`-point `q : Spec k ⟶ X`
(`AlgebraicGeometry.pointOfClosedPoint`), which is a section of the structure morphism and —
the base being a one-point space — a closed immersion. A closed immersion that is a section cuts
out a closed subscheme `D` mapping isomorphically to the base
(`AlgebraicGeometry.isIso_subschemeι_ker_comp_of_section`); in particular `Γ(D, 𝒪_D) = k` and
`AlgebraicGeometry.picardDegree_divisorSchemePicardClass_eq_one` applies. And `D` is the
*reduced* point, because a scheme isomorphic to `Spec k` is reduced and the reduced closed
subscheme structure on a closed subset is unique ([Stacks, Tag 01J3]); so `D` is an effective
Cartier divisor by
`AlgebraicGeometry.IsCurve.isEffectiveCartierDivisor_vanishingIdeal_closure_singleton`, which is
[Stacks, Tag 0AG8] at a closed point of a smooth curve.

## Main results

* `AlgebraicGeometry.ker_pointOfClosedPoint_eq_vanishingIdeal`: the closed subscheme cut out by a
  `k`-point is the reduced point.
* `AlgebraicGeometry.picardDegree_divisorSchemePicardClass_pointOfClosedPoint_eq_one`: **a closed
  point of a smooth curve has degree one.**
* `AlgebraicGeometry.surjective_picardDegree_of_isAlgClosed`: **`deg : Pic(X) ⟶ 𝐙` is onto.**

## References

* [Stacks Project, Tag 01J3](https://stacks.math.columbia.edu/tag/01J3)
* [Stacks Project, Tag 0AG8](https://stacks.math.columbia.edu/tag/0AG8)
* [Stacks Project, Tag 02IL](https://stacks.math.columbia.edu/tag/02IL)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open Stacks.Divisors (IsEffectiveCartierDivisor)

universe u

namespace AlgebraicGeometry

attribute [local instance] AlgebraicGeometry.SmallEtale.zariskiPicardAddCommGroup

/-! ### The closed subscheme cut out by a `k`-point -/

section Point

variable (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [LocallyOfFiniteType f] {x : X} (hx : IsClosed ({x} : Set X))

/-- A `k`-point of `X` is a closed immersion: it is a section of `f`, and `Spec k` is a one-point
space. This is the step Mathlib takes inside
`AlgebraicGeometry.pointEquivClosedPoint`, named here because the divisor below needs it. -/
theorem isClosedImmersion_pointOfClosedPoint :
    IsClosedImmersion (pointOfClosedPoint f x hx) :=
  isClosedImmersion_of_comp_eq_id f _ (pointOfClosedPoint_comp f x hx)

/-- **The closed subscheme cut out by a `k`-point maps isomorphically to `Spec k`.** This is
`AlgebraicGeometry.isIso_subschemeι_ker_comp_of_section` at the section
`AlgebraicGeometry.pointOfClosedPoint`, and it is what makes the ring of functions on the point
equal to `k`. -/
theorem isIso_subschemeι_ker_pointOfClosedPoint_comp :
    IsIso ((pointOfClosedPoint f x hx).ker.subschemeι ≫ f) :=
  have := isClosedImmersion_pointOfClosedPoint k f hx
  isIso_subschemeι_ker_comp_of_section f _ (pointOfClosedPoint_comp f x hx)

/-- **The ring of functions on the closed subscheme cut out by a `k`-point is `k`**, in the shape
`AlgebraicGeometry.picardDegree_divisorSchemePicardClass_eq_one` takes it as an instance. The
closed subscheme maps isomorphically to `Spec k`, and taking global sections carries that
isomorphism to one of rings. -/
theorem isIso_ΓSpecIso_inv_comp_appTop_subschemeι_ker_pointOfClosedPoint :
    IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫
      ((pointOfClosedPoint f x hx).ker.subschemeι ≫ f).appTop) :=
  have := isIso_subschemeι_ker_pointOfClosedPoint_comp k f hx
  have := Stacks.AlgebraicGeometry.isIso_appTop_of_isIso
    ((pointOfClosedPoint f x hx).ker.subschemeι ≫ f)
  inferInstance

/-- The support of the ideal sheaf of a `k`-point is the point: the point map of
`AlgebraicGeometry.pointOfClosedPoint` is constant at `x`, and the support of a kernel is the
closure of the range. -/
theorem support_ker_pointOfClosedPoint :
    (pointOfClosedPoint f x hx).ker.support = Closeds.closure ({x} : Set X) := by
  have := isClosedImmersion_pointOfClosedPoint k f hx
  have h := Scheme.Hom.support_ker (pointOfClosedPoint f x hx)
  rw [Set.range_eq_singleton (pointOfClosedPoint_apply f x hx)] at h
  exact SetLike.coe_injective h

/-- The closed subscheme cut out by a `k`-point is reduced: it is isomorphic to `Spec k`. -/
theorem isReduced_subscheme_ker_pointOfClosedPoint :
    IsReduced (pointOfClosedPoint f x hx).ker.subscheme :=
  have := isIso_subschemeι_ker_pointOfClosedPoint_comp k f hx
  isReduced_of_isOpenImmersion ((pointOfClosedPoint f x hx).ker.subschemeι ≫ f)

/-- **The closed subscheme cut out by a `k`-point is the reduced point.** Its support is `{x}`
and it is reduced, and the reduced closed subscheme structure on a closed subset is unique,
which is the uniqueness half of [Stacks, Tag 01J3]. -/
theorem ker_pointOfClosedPoint_eq_vanishingIdeal :
    (pointOfClosedPoint f x hx).ker =
      Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X)) :=
  have := isReduced_subscheme_ker_pointOfClosedPoint k f hx
  Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme _ _
    (support_ker_pointOfClosedPoint k f hx)

end Point

/-! ### A closed point of a smooth curve has degree one -/

section Curve

variable (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] {x : X} (hx : IsClosed ({x} : Set X))

/-- **A `k`-point of a smooth curve is an effective Cartier divisor.** It cuts out the reduced
point by `AlgebraicGeometry.ker_pointOfClosedPoint_eq_vanishingIdeal`, which is an effective
Cartier divisor by
`AlgebraicGeometry.IsCurve.isEffectiveCartierDivisor_vanishingIdeal_closure_singleton`. -/
theorem isEffectiveCartierDivisor_ker_pointOfClosedPoint :
    IsEffectiveCartierDivisor (pointOfClosedPoint f x hx).ker := by
  rw [ker_pointOfClosedPoint_eq_vanishingIdeal k f hx]
  exact IsCurve.isEffectiveCartierDivisor_vanishingIdeal_closure_singleton k f hx

/-- **A closed point of a smooth curve is a Picard class of degree one.** This is the first
nonzero value of `AlgebraicGeometry.picardDegree` computed in this library: the point is an
effective Cartier divisor whose ring of functions is `k`, so
`AlgebraicGeometry.picardDegree_divisorSchemePicardClass_eq_one` applies to it. -/
theorem picardDegree_divisorSchemePicardClass_pointOfClosedPoint_eq_one [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) :
    letI := isEffectiveCartierDivisor_ker_pointOfClosedPoint k f hx
    picardDegree k f hdim (divisorSchemePicardClass (pointOfClosedPoint f x hx).ker) = 1 :=
  have := isEffectiveCartierDivisor_ker_pointOfClosedPoint k f hx
  have := isIso_ΓSpecIso_inv_comp_appTop_subschemeι_ker_pointOfClosedPoint k f hx
  picardDegree_divisorSchemePicardClass_eq_one k f hdim _

end Curve

/-- **The degree homomorphism `deg : Pic(X) ⟶ 𝐙` of a smooth proper curve over an algebraically
closed field is surjective.** A closed point exists, by [Stacks, Tag 02IL] in the form
`AlgebraicGeometry.closedPoints_nonempty` — a curve is integral, hence nonempty, and locally of
finite type over a field, hence locally Noetherian — and it is a class of degree one, so every
integer is the degree of one of its multiples.

This is the hypothesis `hdeg` carried through the étale cohomology of a projective curve,
[Stacks, Tag 03RQ]. -/
theorem surjective_picardDegree_of_isAlgClosed (k : Type u) [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] [IsCurve k f] [Smooth f]
    (hdim : topologicalKrullDim X ≤ 1) :
    Function.Surjective (picardDegree k f hdim) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨x, hx⟩ := closedPoints_nonempty X
  have := isEffectiveCartierDivisor_ker_pointOfClosedPoint k f
    (mem_closedPoints_iff.mp hx)
  exact surjective_picardDegree_of_eq_one k f hdim _
    (picardDegree_divisorSchemePicardClass_pointOfClosedPoint_eq_one k f
      (mem_closedPoints_iff.mp hx) hdim)

end AlgebraicGeometry

end
