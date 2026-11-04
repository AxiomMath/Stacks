module

public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.SpaceAffineDirectImage

/-!
# Stacks 0CUQ for algebraic spaces, unconditionally

Let `f : X ⟶ Y` be a quasi-compact morphism of algebraic spaces over `S` and let `F` be a
quasi-coherent `𝒪_X`-module. Then every weakly associated point of `f_*F` lies in the image of
`|f|`.

`StacksFrontier/AlgebraicGeometry/Spaces/WeaklyAssociatedPushforward.lean` proves this from
Stacks 0CU2, taken there as an explicit hypothesis, as
`AlgebraicGeometry.Space.not_isWeaklyAssociatedPoint_modulePushforward_of_notMem_range`.
Stacks 0CU2 is proved, with nothing assumed, as
`AlgebraicGeometry.Space.weaklyAssociatedPoints_modulePushforward_subset_image_of_isAffineHom` in
`StacksFrontier/AlgebraicGeometry/Divisors/MorphismWeaklyAssociated/SpaceAffineDirectImage.lean`;
this file supplies it.

## Main results

* `AlgebraicGeometry.Space.not_isWeaklyAssociatedPoint_modulePushforward` and
  `AlgebraicGeometry.Space.weaklyAssociatedPoints_modulePushforward_subset_range`:
  **Stacks 0CUQ**, pointwise and as an inclusion of sets of points.

## References

* [Stacks Project, Tag 0CU2](https://stacks.math.columbia.edu/tag/0CU2)
* [Stacks Project, Tag 0CUQ](https://stacks.math.columbia.edu/tag/0CUQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0CUQ.** Let `f : X ⟶ Y` be a quasi-compact morphism of algebraic spaces over `S`,
let `F` be a quasi-coherent `𝒪_X`-module and let `y` be a point of `Y` outside the image of
`|f|`. Then `y` is not weakly associated to `f_*F`.

This is
`AlgebraicGeometry.Space.not_isWeaklyAssociatedPoint_modulePushforward_of_notMem_range` with its
Stacks 0CU2 hypothesis discharged by
`AlgebraicGeometry.Space.weaklyAssociatedPoints_modulePushforward_subset_image_of_isAffineHom`.
Quasi-separatedness of `f`, which the source assumes, is not needed; see the implementation notes
of `StacksFrontier/AlgebraicGeometry/Spaces/WeaklyAssociatedPushforward.lean`. -/
@[stacks 0CUQ]
theorem not_isWeaklyAssociatedPoint_modulePushforward
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hfqc : IsQuasiCompact B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite)
    (y : points B S hS Y.1) (hy : y ∉ Set.range (pointsMap B S hS X.1 f.hom)) :
    ¬ IsWeaklyAssociatedPoint B S hS Y ((modulePushforward B S hS f).obj F) y :=
  not_isWeaklyAssociatedPoint_modulePushforward_of_notMem_range B S hS
    (fun g hg H hH ↦
      weaklyAssociatedPoints_modulePushforward_subset_image_of_isAffineHom B S hS g hg H hH)
    f hfqc F hF y hy

/-- **Stacks 0CUQ, as an inclusion of sets of points.** Let `f : X ⟶ Y` be a quasi-compact
morphism of algebraic spaces over `S` and let `F` be a quasi-coherent `𝒪_X`-module. Then every
weakly associated point of `f_*F` lies in the image of `|f|`.

This is the pointwise statement
`AlgebraicGeometry.Space.not_isWeaklyAssociatedPoint_modulePushforward` contraposed. -/
@[stacks 0CUQ "as an inclusion of sets of points"]
theorem weaklyAssociatedPoints_modulePushforward_subset_range
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hfqc : IsQuasiCompact B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite) :
    weaklyAssociatedPoints B S hS Y ((modulePushforward B S hS f).obj F) ⊆
      Set.range (pointsMap B S hS X.1 f.hom) := fun y hy =>
  not_not.1 fun hny =>
    not_isWeaklyAssociatedPoint_modulePushforward B S hS f hfqc F hF y hny hy

end AlgebraicGeometry.Space

end
