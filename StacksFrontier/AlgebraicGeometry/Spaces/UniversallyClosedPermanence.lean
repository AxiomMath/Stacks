module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosed

/-!
# Permanence properties of universally closed morphisms of algebraic spaces

A morphism of algebraic spaces over a scheme `S` is universally closed when every base change
of it is closed on the points of Tags 03BU and 03BX. This file proves that such a morphism is
closed, and the consequence Stacks 04NX draws from that together with stability under base
change and composition: in a commuting triangle `X ⟶ Y ⟶ Z` whose second leg is separated,
universal closedness of the composite descends to the first leg, so that the image of `|X|` in
`|Y|` is closed.

Stability under base change (**Stacks 03IS**) and under composition (**Stacks 03IU**) are
`AlgebraicGeometry.Space.universallyClosed_pullback` and
`AlgebraicGeometry.Space.universallyClosed_comp` of
`StacksFrontier.AlgebraicGeometry.Spaces.SeparationMorphismProperties`, which prove them with no
algebraicity hypothesis on the source.

## Main results

* `AlgebraicGeometry.Space.isClosed_of_universallyClosed`: a universally closed morphism of
  algebraic spaces is closed.
* `AlgebraicGeometry.Space.universallyClosed_of_comp_of_isSeparated` and
  `AlgebraicGeometry.Space.isClosed_range_of_comp_of_isSeparated` are the two assertions of
  part (1) of Stacks 04NX.

## References

* [Stacks Project, Tag 03IS](https://stacks.math.columbia.edu/tag/03IS)
* [Stacks Project, Tag 03IU](https://stacks.math.columbia.edu/tag/03IU)
* [Stacks Project, Tag 04NX](https://stacks.math.columbia.edu/tag/04NX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### A universally closed morphism is closed -/

/-- A universally closed morphism of algebraic spaces over `S` is closed. -/
theorem isClosed_of_universallyClosed {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hf : UniversallyClosed B S hS f) :
    IsClosedMorphism B S hS f :=
  isClosedMap_pointsMap_of_pullback_fst_id B S hS f (hf Y hY (𝟙 Y))

/-! ### Stacks 04NX, part (1) -/

/-- **Stacks 04NX, part (1).** Let `X ⟶ Y ⟶ Z` be morphisms of algebraic spaces over `S`. If
the composite `X ⟶ Z` is universally closed and `Y ⟶ Z` is separated, then `X ⟶ Y` is
universally closed. -/
@[stacks 04NX "part (1): universal closedness", ega "II 5.4.9" "5.4.3 univ. closed"]
theorem universallyClosed_of_comp_of_isSeparated {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (g : Y ⟶ Z)
    (hfg : UniversallyClosed B S hS (f ≫ g)) (hg : IsSeparated B S hS g) :
    UniversallyClosed B S hS f := by
  intro T hT t
  have hQ : IsAlgebraicSpace B S hS (pullback t f) :=
    isAlgebraicSpace_pullback B S hS t f hT hX hY
  have hP : IsAlgebraicSpace B S hS (pullback (t ≫ g) (f ≫ g)) :=
    isAlgebraicSpace_pullback B S hS (t ≫ g) (f ≫ g) hT hX hZ
  have hmc : IsClosedMorphism B S hS (pullback.mapDesc t f g) :=
    isClosed_of_universallyClosed B S hS hP _
      (universallyClosed_of_isClosedImmersion B S hS hQ hP _
        (isClosedImmersion_mapDesc B S hS t f g hg))
  have hcomp := IsClosedMorphism.comp B S hS (hfg T hT (t ≫ g)) hmc
  have hfactor : pullback.mapDesc t f g ≫ pullback.fst (t ≫ g) (f ≫ g) =
      pullback.fst t f := by
    simp [pullback.mapDesc, pullback.map, pullback.lift_fst]
  rwa [hfactor] at hcomp

/-- **Stacks 04NX, part (1).** Under the hypotheses of
`AlgebraicGeometry.Space.universallyClosed_of_comp_of_isSeparated`, the image of `|X|` in
`|Y|` is closed. -/
@[stacks 04NX "part (1): closed image"]
theorem isClosed_range_of_comp_of_isSeparated {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (g : Y ⟶ Z)
    (hfg : UniversallyClosed B S hS (f ≫ g)) (hg : IsSeparated B S hS g) :
    _root_.IsClosed (Set.range (pointsMap B S hS X f)) :=
  (isClosed_of_universallyClosed B S hS hY f
    (universallyClosed_of_comp_of_isSeparated B S hS hX hY hZ f g hfg hg)).isClosed_range

end AlgebraicGeometry.Space

end
