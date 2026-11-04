module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.BivariantVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ZeroCycleDegree
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralDegree
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperPermanence

/-!
# Supports and residue degrees of cycles on integral closed subspaces

In Situation 0EDT let `X/B` be good. Two facts about the cycles of Stacks 0EP1 on `X` and the
residue degrees of a morphism `p : X ⟶ Y`:

* if `|X|` is quasi-compact, a cycle on `X` has finite support, the point sets of the integral
  closed subspaces with nonzero coefficient forming a locally finite family of nonempty sets;
* the inclusion of an integral closed subspace `Z ⊆ X` induces isomorphisms of residue fields,
  so the residue degree of `Z ⟶ X ⟶ Y` at a point of `Z` is that of `p` at its image.

## Main results

* `AlgebraicGeometry.Space.finite_support_of_compactSpace`: a cycle on a space with
  quasi-compact space of points has finite support.
* `AlgebraicGeometry.Space.cycleResidueDegree_ι_comp`: the residue degree along the composite of
  the inclusion of an integral closed subspace with a morphism is the residue degree of the
  morphism at the image.

## References

* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EP1](https://stacks.math.columbia.edu/tag/0EP1)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- A cycle on an algebraic space with quasi-compact space of points has finite support. -/
theorem finite_support_of_compactSpace (sX : X ⟶ D.space) (k : ℤ)
    [CompactSpace (points D.site D.base D.base_mem X)] (α : CycleGroup D sX k) :
    (Function.support α.1).Finite := by
  refine (α.2.1.finite_nonempty_of_compact).subset fun Z hZ => ?_
  have hZ' : α.1 Z ≠ 0 := hZ
  have : IrreducibleSpace (points D.site D.base D.base_mem Z.subspace.toFunctor) :=
    Z.isIntegralSpace.2.2
  obtain ⟨z⟩ : Nonempty (points D.site D.base D.base_mem Z.subspace.toFunctor) := inferInstance
  show (if α.1 Z = 0 then ∅ else subspacePointSet D.site D.base D.base_mem X Z.subspace).Nonempty
  rw [if_neg hZ']
  exact ⟨_, z, rfl⟩

/-- The residue degree along the composite of the inclusion of an integral closed subspace
`Z ⊆ X` with a morphism `p : X ⟶ Y` is the residue degree of `p` at the image. -/
theorem cycleResidueDegree_ι_comp (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) (p : X ⟶ Y) (Z : IntegralClosedSubspace D.site D.base D.base_mem X)
    (z : points D.site D.base D.base_mem Z.subspace.toFunctor) :
    cycleResidueDegree D (Z.subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX Z) sY hY
        (Z.subspace.ι ≫ p) z =
      cycleResidueDegree D sX hX sY hY p
        (pointsMap D.site D.base D.base_mem Z.subspace.toFunctor Z.subspace.ι z) := by
  have hdecZ := D.isDecentSpace_of_isGood _ (isGood_integralClosedSubspace D sX hX Z)
  have hdecX := D.isDecentSpace_of_isGood sX hX
  have hdecY := D.isDecentSpace_of_isGood sY hY
  have hcomp := residueFieldDegreeAt_comp D.site D.base D.base_mem hX.1 hY.1 hdecZ hdecX hdecY
    Z.subspace.ι p z
  have hone :
      residueFieldDegreeAt D.site D.base D.base_mem hX.1 hdecZ hdecX Z.subspace.ι z = 1 := by
    have hmono : Mono (residueFieldMorphism D.site D.base D.base_mem Z.subspace.toFunctor hdecZ z ≫
        Z.subspace.ι) := by
      have := (residueFieldRepresentative D.site D.base D.base_mem Z.subspace.toFunctor hdecZ
        z).2.2
      exact mono_comp _ _
    have hiso := (isIso_residueFieldHom_iff_mono D.site D.base D.base_mem Z.subspace.toFunctor X
      hX.1 hdecZ hdecX Z.subspace.ι z).2 hmono
    have hbij := ConcreteCategory.bijective_of_isIso
      (CommRingCat.ofHom (residueFieldHom D.site D.base D.base_mem Z.subspace.toFunctor X hX.1
        hdecZ hdecX Z.subspace.ι z))
    let := residueFieldAlgebra D.site D.base D.base_mem hX.1 hdecZ hdecX Z.subspace.ι z
    show Module.finrank _ _ = 1
    rw [← (AlgEquiv.ofBijective (Algebra.ofId _ _) hbij).toLinearEquiv.finrank_eq,
      Module.finrank_self]
  show residueFieldDegreeAt D.site D.base D.base_mem hY.1 hdecZ hdecY (Z.subspace.ι ≫ p) z =
    residueFieldDegreeAt D.site D.base D.base_mem hY.1 hdecX hdecY p _
  rw [hcomp, hone, one_mul]

end AlgebraicGeometry.Space

end
