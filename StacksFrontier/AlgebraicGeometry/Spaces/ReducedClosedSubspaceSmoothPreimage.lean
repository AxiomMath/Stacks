module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.SmoothLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedSmooth
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransform
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage

/-!
# The reduced closed subspace along a smooth morphism

Let `f : Y ⟶ X` be a smooth morphism of algebraic spaces over `S` and let `T` be a closed set of
points of `X`. The inverse image along `f` of the reduced closed subspace of `X` on `T` is the
reduced closed subspace of `Y` on `|f|⁻¹(T)`.

This is the step of the proof of **Stacks 0509** which shows that the reduced induced closed
subspace of a presentation on an invariant closed set is invariant: there the two inverse images
along the smooth source and target maps of the groupoid are reduced closed subspaces with the same
point set, hence equal by the uniqueness half of **Stacks 03IQ**.

## Main results

* `AlgebraicGeometry.Space.preimage_reducedClosedSubspace_of_isSmooth`: the inverse image along a
  smooth morphism of the reduced closed subspace on `T` is the reduced closed subspace on the
  inverse image of `T`.

## Implementation notes

The inverse image is a closed subspace by `AlgebraicGeometry.Space.isClosedSubspace_preimage`
(**Stacks 083Q**), its point set is the inverse image of the point set of the reduced closed
subspace by `AlgebraicGeometry.Space.range_pointsMap_preimage_ι`, and it is reduced because it is
smooth over the reduced closed subspace: the projection to it is a base change of `f`, smoothness
is stable under base change (**Stacks 03ZE**), and the source of a smooth morphism to a reduced
algebraic space is reduced (`AlgebraicGeometry.Space.isReduced_of_isSmooth`). The uniqueness half
of **Stacks 03IQ**, `AlgebraicGeometry.Space.eq_reducedClosedSubspace`, then identifies it.

## References

* [Stacks Project, Tag 03IQ](https://stacks.math.columbia.edu/tag/03IQ)
* [Stacks Project, Tag 03ZE](https://stacks.math.columbia.edu/tag/03ZE)
* [Stacks Project, Tag 0509](https://stacks.math.columbia.edu/tag/0509)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The reduced closed subspace is stable under smooth inverse image.** For a smooth morphism
`f : Y ⟶ X` of algebraic spaces over `S` and a closed set `T` of points of `X`, the inverse image
along `f` of the reduced closed subspace of `X` on `T` is the reduced closed subspace of `Y` on
`|f|⁻¹(T)`. -/
theorem preimage_reducedClosedSubspace_of_isSmooth
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : Y ⟶ X) (hf : IsSmooth B S hS f)
    (T : Set (points B S hS X)) (hT : IsClosed T) :
    (reducedClosedSubspace B S hS X hX T hT).preimage f =
      reducedClosedSubspace B S hS Y hY (pointsMap B S hS Y f ⁻¹' T)
        (hT.preimage (continuous_pointsMap B S hS f)) := by
  set Z := reducedClosedSubspace B S hS X hX T hT with hZdef
  have hZc : IsClosedSubspace B S hS Z := isClosedSubspace_reducedClosedSubspace B S hS X hX T hT
  have hPc : IsClosedSubspace B S hS (Z.preimage f) :=
    isClosedSubspace_preimage B S hS f Z hX hY hZc
  refine eq_reducedClosedSubspace B S hS Y hY _ _ (Z.preimage f) hPc ?_ ?_
  · rw [range_pointsMap_preimage_ι B S hS f Z, hZdef,
      range_pointsMap_ι_reducedClosedSubspace B S hS X hX T hT]
  · have hsq := Subfunctor.isPullback_preimage f Z
    let X' : AlgebraicSpaces B S hS := ⟨X, hX⟩
    let Y' : AlgebraicSpaces B S hS := ⟨Y, hY⟩
    let Z' : AlgebraicSpaces B S hS := ⟨Z.toFunctor, hZc.1⟩
    let P' : AlgebraicSpaces B S hS := ⟨(Z.preimage f).toFunctor, hPc.1⟩
    have hsq' : IsPullback
        (ObjectProperty.homMk (Z.fromPreimage f) : P' ⟶ Z')
        (ObjectProperty.homMk (Z.preimage f).ι : P' ⟶ Y')
        (ObjectProperty.homMk Z.ι : Z' ⟶ X')
        (ObjectProperty.homMk f : Y' ⟶ X') :=
      IsPullback.of_map_of_faithful
        (F := ObjectProperty.ι (fun T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
          IsAlgebraicSpace B S hS T)) hsq
    have hBC := isSmooth_isStableUnderBaseChange B S hS
    have hsm : IsSmooth B S hS (Z.fromPreimage f) :=
      hBC.of_isPullback hsq'.flip (show IsSmooth B S hS f from hf)
    exact isReduced_of_isSmooth B S hS hPc.1 hZc.1 (Z.fromPreimage f) hsm
      (hasEtaleLocalProperty_isReduced_reducedClosedSubspace B S hS X hX T hT)

end AlgebraicGeometry.Space

end
