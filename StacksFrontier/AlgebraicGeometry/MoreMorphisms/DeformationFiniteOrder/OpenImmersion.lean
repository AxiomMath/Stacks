module

public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import StacksFrontier.AlgebraicGeometry.Etale.FpqcDescentApplication.OpenImmersion
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.DeformationFiniteOrder.Etale
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.DeformationFiniteOrder.FiniteType
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.Diagonal
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.Monomorphism
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.Topological
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Open immersions, isomorphisms and monomorphisms along a finite-order deformation

In a cartesian finite-order deformation diagram, and likewise in a flat deformation diagram, the
morphism `f` of closed subschemes is an open immersion, an isomorphism, or a monomorphism exactly
when its ambient deformation `f'` is.

## Main definitions

* `Stacks.Thickenings.CartesianFiniteOrderDeformationDiagram.diagonalDiagram`: the cartesian
  finite-order deformation diagram whose horizontal morphisms are the relative diagonals of `f` and
  of `f'`.

## Main results

* `Stacks.Thickenings.isPullback_pullbackMap_self`: a cartesian square with monomorphic left edge
  induces a cartesian square between the self-fibre products.
* `Stacks.Thickenings.CartesianFiniteOrderDeformationDiagram.isOpenImmersion_iff`: `f` is an open
  immersion if and only if `f'` is.
* `Stacks.Thickenings.CartesianFiniteOrderDeformationDiagram.isIso_iff`: `f` is an isomorphism if
  and only if `f'` is.
* `Stacks.Thickenings.CartesianFiniteOrderDeformationDiagram.mono_iff`: `f` is a monomorphism if
  and only if `f'` is.
* `Stacks.Thickenings.FlatDeformationDiagram.isOpenImmersion_iff`: `f` is an open immersion if and
  only if `f'` is.
* `Stacks.Thickenings.FlatDeformationDiagram.isIso_iff`: `f` is an isomorphism if and only if `f'`
  is.
* `Stacks.Thickenings.FlatDeformationDiagram.mono_iff`: `f` is a monomorphism if and only if `f'`
  is.

## References

* [Stacks Project, Tag 02LC](https://stacks.math.columbia.edu/tag/02LC)
* [Stacks Project, Tag 06AG](https://stacks.math.columbia.edu/tag/06AG)
* [Stacks Project, Tag 0BPG](https://stacks.math.columbia.edu/tag/0BPG)
* [Stacks Project, Tag 0CF4](https://stacks.math.columbia.edu/tag/0CF4)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Thickenings

/-- A cartesian square `(i, f, f', j)` with monomorphic left edge induces a cartesian square
between the two self-fibre products: `X ×_Y X` is the base change of `X' ×_{Y'} X'` along
`j : Y ⟶ Y'`. -/
theorem isPullback_pullbackMap_self {X X' Y Y' : Scheme.{u}} {i : X ⟶ X'} {f : X ⟶ Y}
    {f' : X' ⟶ Y'} {j : Y ⟶ Y'} [Mono i] (e : f ≫ j = i ≫ f') (h : IsPullback i f f' j) :
    IsPullback (pullback.map f f f' f' i i j e e)
      (pullback.fst f f ≫ f) (pullback.fst f' f' ≫ f') j := by
  have hmfst : pullback.map f f f' f' i i j e e ≫ pullback.fst f' f' =
      pullback.fst f f ≫ i := pullback.lift_fst _ _ _
  have hmsnd : pullback.map f f f' f' i i j e e ≫ pullback.snd f' f' =
      pullback.snd f f ≫ i := pullback.lift_snd _ _ _
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk (W := pullback f f)
    (f := pullback.fst f' f' ≫ f') (g := j)
    (fst := pullback.map f f f' f' i i j e e) (snd := pullback.fst f f ≫ f)
    ?_ ?_ ?_ ?_ ?_)
  · rw [← Category.assoc, hmfst, Category.assoc, ← e, Category.assoc]
  · intro s
    exact pullback.lift (h.lift (s.fst ≫ pullback.fst f' f') s.snd (by simpa using s.condition))
      (h.lift (s.fst ≫ pullback.snd f' f') s.snd
        (by rw [Category.assoc, ← pullback.condition]; simpa using s.condition))
      (by rw [h.lift_snd, h.lift_snd])
  · intro s
    apply pullback.hom_ext
    · rw [Category.assoc, hmfst, ← Category.assoc, pullback.lift_fst, h.lift_fst]
    · rw [Category.assoc, hmsnd, ← Category.assoc, pullback.lift_snd, h.lift_fst]
  · intro s
    rw [← Category.assoc, pullback.lift_fst, h.lift_snd]
  · intro s m hm₁ _
    apply pullback.hom_ext <;> simp only [pullback.lift_fst, pullback.lift_snd] <;>
      refine (cancel_mono i).mp ?_ <;>
      simp only [Category.assoc, h.lift_fst, ← hmfst, ← hmsnd, ← hm₁]

namespace CartesianFiniteOrderDeformationDiagram

/-- Being an open immersion is invariant under a cartesian finite-order deformation with flat
ambient source. -/
@[stacks 06AG "open_immersion"]
theorem isOpenImmersion_iff (D : CartesianFiniteOrderDeformationDiagram.{u}) :
    IsOpenImmersion D.f ↔ IsOpenImmersion D.f' := by
  refine ⟨fun _ ↦ ?_, property_of_baseChange @IsOpenImmersion.{u} D⟩
  have : Etale D.f' := D.etale_iff.1 inferInstance
  have : UniversallyInjective D.f' := (universallyInjective_left_iff_right D.iX_thickening
    D.iY_thickening (Arrow.homMk D.f D.f' D.f_thickening_comm)).1
      (inferInstance : UniversallyInjective D.f)
  infer_instance

/-- Being an isomorphism is invariant under a cartesian finite-order deformation with flat ambient
source. -/
@[stacks 06AG "isomorphism"]
theorem isIso_iff (D : CartesianFiniteOrderDeformationDiagram.{u}) :
    IsIso D.f ↔ IsIso D.f' := by
  refine ⟨fun _ ↦ ?_, property_of_baseChange (MorphismProperty.isomorphisms Scheme.{u}) D⟩
  exact (isIso_iff_isOpenImmersion_and_surjective D.f').2 ⟨D.isOpenImmersion_iff.1 inferInstance,
    (surjective_left_iff_right D.iX_thickening D.iY_thickening
      (Arrow.homMk D.f D.f' D.f_thickening_comm)).1 (inferInstance : Surjective D.f)⟩

/-- The cartesian finite-order deformation diagram obtained by passing to relative diagonals:
the source thickening is unchanged and the target thickening is the induced map between the two
self-fibre products, so that the two horizontal morphisms are the relative diagonals of `f` and
of `f'`. -/
@[ega "IV 16.4.1" "special case"]
noncomputable def diagonalDiagram (D : CartesianFiniteOrderDeformationDiagram.{u}) :
    CartesianFiniteOrderDeformationDiagram.{u} where
  S := D.S
  S' := D.S'
  iS := D.iS
  iS_finiteOrder := D.iS_finiteOrder
  X := D.X
  X' := D.X'
  iX := D.iX
  iX_thickening := D.iX_thickening
  Y := pullback D.f D.f
  Y' := pullback D.f' D.f'
  iY := pullback.map D.f D.f D.f' D.f' D.iX D.iX D.iY D.f_thickening_comm D.f_thickening_comm
  iY_thickening := by
    have heq : pullback.map D.f D.f D.f' D.f' D.iX D.iX D.iY
          D.f_thickening_comm D.f_thickening_comm =
        diagonalTargetMap D.iX D.f D.f' D.iY D.f_thickening_comm.symm := by
      apply pullback.hom_ext <;>
        simp [diagonalTargetMap, diagonalBaseComparison, diagonalTargetFst, diagonalTargetSnd,
          pullback.map, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
          pullback.lift_snd_assoc]
    rw [heq]
    exact isThickening_diagonalTargetMap D.iX D.f D.f' D.iY D.f_thickening_comm.symm
      D.iX_thickening D.iY_thickening
  pX := D.pX
  pX' := D.pX'
  pY := pullback.fst D.f D.f ≫ D.pX
  pY' := pullback.fst D.f' D.f' ≫ D.pX'
  f := pullback.diagonal D.f
  f' := pullback.diagonal D.f'
  f_over_S := by rw [← Category.assoc, pullback.diagonal_fst, Category.id_comp]
  f'_over_S' := by rw [← Category.assoc, pullback.diagonal_fst, Category.id_comp]
  f_thickening_comm := by
    apply pullback.hom_ext <;>
      simp [pullback.map, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
        pullback.lift_snd_assoc]
  X_cartesian := D.X_cartesian
  Y_cartesian := by
    have _ : IsClosedImmersion D.iX := D.iX_thickening.1
    have htop := isPullback_pullbackMap_self (i := D.iX) (f := D.f) (f' := D.f') (j := D.iY)
      D.f_thickening_comm D.isPullback_f
    simpa only [Category.assoc, D.f_over_S, D.f'_over_S'] using htop.paste_vert D.Y_cartesian
  X'_flat := D.X'_flat

/-- Being a monomorphism is invariant under a cartesian finite-order deformation with flat ambient
source. -/
@[stacks 06AG "monomorphism"]
theorem mono_iff (D : CartesianFiniteOrderDeformationDiagram.{u}) :
    Mono D.f ↔ Mono D.f' :=
  ⟨fun hf ↦ (pullback.isIso_diagonal_iff D.f').1
      ((isIso_iff D.diagonalDiagram).1 ((pullback.isIso_diagonal_iff D.f).2 hf)),
    property_of_baseChange (MorphismProperty.monomorphisms Scheme.{u}) D⟩

end CartesianFiniteOrderDeformationDiagram

namespace FlatDeformationDiagram

/-- Being an open immersion is invariant under a flat deformation diagram. -/
@[stacks 0CF4 "open_immersion"]
theorem isOpenImmersion_iff (D : FlatDeformationDiagram.{u}) :
    IsOpenImmersion D.f ↔ IsOpenImmersion D.f' := by
  refine ⟨fun _ ↦ ?_, MorphismProperty.of_isPullback D.isPullback_f⟩
  have : Etale D.f' := D.etale_iff.1 inferInstance
  have : UniversallyInjective D.f' := D.universallyInjective_iff.1 inferInstance
  infer_instance

/-- Being an isomorphism is invariant under a flat deformation diagram. -/
@[stacks 0CF4 "isomorphism"]
theorem isIso_iff (D : FlatDeformationDiagram.{u}) : IsIso D.f ↔ IsIso D.f' := by
  refine ⟨fun _ ↦ (isIso_iff_isOpenImmersion_and_surjective D.f').2
    ⟨D.isOpenImmersion_iff.1 inferInstance, D.surjective_iff.1 inferInstance⟩,
    MorphismProperty.of_isPullback (P := MorphismProperty.isomorphisms Scheme.{u}) D.isPullback_f⟩

/-- Being a monomorphism is invariant under a flat deformation diagram. -/
@[stacks 0CF4 "monomorphism"]
theorem mono_iff (D : FlatDeformationDiagram.{u}) : Mono D.f ↔ Mono D.f' :=
  D.toCartesianFiniteTypeMorphism.mono_iff

end FlatDeformationDiagram

end Stacks.Thickenings

end
