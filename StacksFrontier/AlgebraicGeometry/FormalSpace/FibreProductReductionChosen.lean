module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FibreProductFormalBase
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FibreProductReduction
public import StacksFrontier.AlgebraicGeometry.FormalSpace.GeneralReduction
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocallyNoetherianSource
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableLocalOnSourceAndTargetRefined

/-!
# The reduction of a fibre product of formal algebraic spaces, for the chosen reductions

Let `S` be a scheme contained in a big fppf site `B`, and let `X ⟶ Z` and `Y ⟶ Z` be morphisms
of formal algebraic spaces over `S`. **Stacks 0CB9** states the identity
`(X ×_Z Y)_red = (X_red ×_{Z_red} Y_red)_red`. This file states it for the fibre products
`CategoryTheory.Limits.pullback` and the reductions `AlgebraicGeometry.FormalSpace.reduction`
supplied by Stacks 0AIN, deducing it from the form for arbitrary reductions and arbitrary models
of the fibre products, `AlgebraicGeometry.FormalSpace.exists_iso_reduction_fibreProduct`.

Both fibre products are formal algebraic spaces by Stacks 0AJ3
(`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_pullback_of_isFormalAlgebraicSpace`): for
`X_red ×_{Z_red} Y_red` this needs that the reduction of a formal algebraic space is a formal
algebraic space, which is Stacks 0AJI applied to the inclusion of the reduction, a morphism
representable by objects of the site. So both have reductions, and the morphisms
`X_red ⟶ Z_red` and `Y_red ⟶ Z_red` are those induced by the universal property of the
reduction (`AlgebraicGeometry.FormalSpace.Reduction.map`).

## Main results

* `AlgebraicGeometry.FormalSpace.IsReduction.isFormalAlgebraicSpace`: the reduction of a formal
  algebraic space is a formal algebraic space.
* `AlgebraicGeometry.FormalSpace.exists_iso_reduction_pullback`: **Stacks 0CB9**.

## References

* [Stacks Project, Tag 0AIN](https://stacks.math.columbia.edu/tag/0AIN)
* [Stacks Project, Tag 0AJ3](https://stacks.math.columbia.edu/tag/0AJ3)
* [Stacks Project, Tag 0AJI](https://stacks.math.columbia.edu/tag/0AJI)
* [Stacks Project, Tag 0CB9](https://stacks.math.columbia.edu/tag/0CB9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The source of a reduction of a formal algebraic space is a formal algebraic space: the
inclusion is representable by objects of the site, hence by algebraic spaces, and Stacks 0AJI
applies. -/
theorem IsReduction.isFormalAlgebraicSpace {X Xred : FppfSheaf B S hS} {i : Xred ⟶ X}
    (h : IsReduction B S hS X Xred i) (hX : IsFormalAlgebraicSpace B S hS X) :
    IsFormalAlgebraicSpace B S hS Xred :=
  isFormalAlgebraicSpace_of_isRepresentableByAlgebraicSpacesULift B S hS i hX
    (isRepresentableByAlgebraicSpacesULift_of_relativelyRepresentable B S hS h.representable)

/-- The chosen reduction of a formal algebraic space is a formal algebraic space. -/
theorem isFormalAlgebraicSpace_reduction {X : FppfSheaf B S hS}
    (hX : IsFormalAlgebraicSpace B S hS X) :
    IsFormalAlgebraicSpace B S hS (liftSheaf B S hS (reduction B S hS X hX).space) :=
  (reduction B S hS X hX).isReduction.isFormalAlgebraicSpace hX

/-- The fibre product `X_red ×_{Z_red} Y_red` of the chosen reductions of formal algebraic spaces,
over the morphisms of reductions induced by `f : X ⟶ Z` and `g : Y ⟶ Z`, is a formal algebraic
space. -/
theorem isFormalAlgebraicSpace_pullback_reduction {X Y Z : FppfSheaf B S hS}
    (hX : IsFormalAlgebraicSpace B S hS X) (hY : IsFormalAlgebraicSpace B S hS Y)
    (hZ : IsFormalAlgebraicSpace B S hS Z) (f : X ⟶ Z) (g : Y ⟶ Z) :
    IsFormalAlgebraicSpace B S hS
      (pullback (liftSheafMap B S hS ((reduction B S hS X hX).map (reduction B S hS Z hZ) f))
        (liftSheafMap B S hS ((reduction B S hS Y hY).map (reduction B S hS Z hZ) g))) :=
  isFormalAlgebraicSpace_pullback_of_isFormalAlgebraicSpace B S hS _ _
    (isFormalAlgebraicSpace_reduction hZ) (isFormalAlgebraicSpace_reduction hX)
    (isFormalAlgebraicSpace_reduction hY)

/-- **Stacks 0CB9.** Let `X ⟶ Z` and `Y ⟶ Z` be morphisms of formal algebraic spaces over `S`.
Then `(X ×_Z Y)_red = (X_red ×_{Z_red} Y_red)_red`: the reduction of the fibre product
`X ×_Z Y` and the reduction of the fibre product of the reductions `X_red ×_{Z_red} Y_red`
(both fibre products being formal algebraic spaces by Stacks 0AJ3, and the reductions those
supplied by Stacks 0AIN) are isomorphic, by an isomorphism lying over the morphism
`X_red ×_{Z_red} Y_red ⟶ X ×_Z Y` induced by the inclusions of the reductions. -/
@[stacks 0CB9]
theorem exists_iso_reduction_pullback {X Y Z : FppfSheaf B S hS}
    (hX : IsFormalAlgebraicSpace B S hS X) (hY : IsFormalAlgebraicSpace B S hS Y)
    (hZ : IsFormalAlgebraicSpace B S hS Z) (f : X ⟶ Z) (g : Y ⟶ Z) :
    ∃ e : liftSheaf B S hS (reduction B S hS _
          (isFormalAlgebraicSpace_pullback_reduction hX hY hZ f g)).space ≅
        liftSheaf B S hS (reduction B S hS (pullback f g)
          (isFormalAlgebraicSpace_pullback_of_isFormalAlgebraicSpace B S hS f g hZ hX hY)).space,
      e.hom ≫ (reduction B S hS (pullback f g)
          (isFormalAlgebraicSpace_pullback_of_isFormalAlgebraicSpace B S hS f g hZ hX hY)
          ).inclusion =
        (reduction B S hS _ (isFormalAlgebraicSpace_pullback_reduction hX hY hZ f g)).inclusion ≫
          pullback.map _ _ f g (reduction B S hS X hX).inclusion (reduction B S hS Y hY).inclusion
            (reduction B S hS Z hZ).inclusion
            ((reduction B S hS X hX).liftSheafMap_map (reduction B S hS Z hZ) f)
            ((reduction B S hS Y hY).liftSheafMap_map (reduction B S hS Z hZ) g) := by
  obtain ⟨cmp, e, h₁, h₂, he⟩ := exists_iso_reduction_fibreProduct hX hY hZ
    (reduction B S hS X hX).isReduction (reduction B S hS Y hY).isReduction
    (reduction B S hS Z hZ).isReduction
    ((reduction B S hS X hX).liftSheafMap_map (reduction B S hS Z hZ) f)
    ((reduction B S hS Y hY).liftSheafMap_map (reduction B S hS Z hZ) g)
    (IsPullback.of_hasPullback f g) (IsPullback.of_hasPullback _ _)
    (reduction B S hS (pullback f g)
      (isFormalAlgebraicSpace_pullback_of_isFormalAlgebraicSpace B S hS f g hZ hX hY)).isReduction
    (reduction B S hS _ (isFormalAlgebraicSpace_pullback_reduction hX hY hZ f g)).isReduction
  refine ⟨e, he.trans ?_⟩
  congr 1
  refine pullback.hom_ext ?_ ?_
  · rw [h₁]; exact (pullback.lift_fst _ _ _).symm
  · rw [h₂]; exact (pullback.lift_snd _ _ _).symm

end AlgebraicGeometry.FormalSpace

end
