module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.Dominant
public import StacksFrontier.AlgebraicGeometry.Morphisms.DimensionFormula.FunctionField
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.GeneralDimensionFormula

/-!
# The generic point under a birational morphism

A birational morphism from an integral scheme is an isomorphism on the stalk at the generic
point, and this file collects what that gives: the residue fields agree there, so the
residue-field transcendence degree vanishes at the generic point and the correction term of the
dimension formula of [Stacks, Tag 0BAE] vanishes at every point.

## Main results

* `AlgebraicGeometry.isMax_genericPoint`: the generic point of an irreducible scheme is maximal
  in the specialization order.
* `AlgebraicGeometry.ringKrullDim_stalk_genericPoint_eq_zero`: the local ring there has
  dimension zero.
* `AlgebraicGeometry.isIso_residueFieldMap_of_isIso_stalkMap`: an isomorphism on a stalk induces
  an isomorphism on residue fields.
* `AlgebraicGeometry.residueFieldTranscendenceDegree_genericPoint_eq_zero`: the residue-field
  transcendence degree of a birational morphism vanishes at the generic point.
* `AlgebraicGeometry.genericResidueFieldTranscendenceDegreeAt_eq_zero`: the correction term of
  the dimension formula vanishes at every point of the source.
* `AlgebraicGeometry.IsBirational.genericPoint_eq`: a birational morphism of integral schemes
  carries the generic point to the generic point, stated with birationality as a hypothesis
  rather than as the instance `IsDominant`.

## References

* [Stacks Project, Tag 0BAE](https://stacks.math.columbia.edu/tag/0BAE)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The generic point of an irreducible scheme is maximal in the specialization order. -/
theorem isMax_genericPoint (X : Scheme.{u}) [IrreducibleSpace X] :
    IsMax (genericPoint X) := fun y _ => by
  rw [Scheme.le_iff_specializes]
  exact genericPoint_specializes y

/-- The local ring of an irreducible scheme at its generic point has dimension zero. -/
theorem ringKrullDim_stalk_genericPoint_eq_zero (X : Scheme.{u}) [IrreducibleSpace X] :
    ringKrullDim (X.presheaf.stalk (genericPoint X)) = 0 := by
  rw [ringKrullDim_stalk_eq_coheight, Order.coheight_eq_zero.2 (isMax_genericPoint X)]
  rfl

/-- An isomorphism of local rings induces an isomorphism of residue fields. -/
theorem isIso_residueFieldMap_of_isIso_stalkMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (x : X) [IsIso (f.stalkMap x)] : IsIso (f.residueFieldMap x) :=
  (IsLocalRing.ResidueField.mapEquiv
    (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv).toCommRingCatIso.isIso_hom

/-- A birational morphism from an integral scheme induces an isomorphism of residue fields at
the generic point, so the residue-field transcendence degree vanishes there. -/
theorem residueFieldTranscendenceDegree_genericPoint_eq_zero {X Y : Scheme.{u}}
    [IsIntegral X] (f : X ⟶ Y) (hf : IsBirational f) :
    residueFieldTranscendenceDegree f (genericPoint X) = 0 := by
  have hη : genericPoint X ∈ genericPoints X := by simp [genericPoints_eq_singleton]
  have _ : IsIso (f.stalkMap (genericPoint X)) := hf.isIso_stalkMap _ hη
  have _ : IsIso (f.residueFieldMap (genericPoint X)) :=
    isIso_residueFieldMap_of_isIso_stalkMap f (genericPoint X)
  let _ : Algebra (Y.residueField (f (genericPoint X))) (X.residueField (genericPoint X)) :=
    (f.residueFieldMap (genericPoint X)).hom.toAlgebra
  have _ : Module.Finite (Y.residueField (f (genericPoint X)))
      (X.residueField (genericPoint X)) :=
    Module.Finite.of_surjective (Algebra.linearMap _ _)
      (ConcreteCategory.bijective_of_isIso (f.residueFieldMap (genericPoint X))).2
  have _ : Algebra.IsAlgebraic (Y.residueField (f (genericPoint X)))
      (X.residueField (genericPoint X)) := Algebra.IsAlgebraic.of_finite _ _
  exact Cardinal.toENat_eq_zero.mpr trdeg_eq_zero

/-- For a birational morphism from an integral scheme the correction term of the dimension
formula of [Stacks, Tag 0BAE] vanishes at every point: the source has a single generic point. -/
theorem genericResidueFieldTranscendenceDegreeAt_eq_zero {X Y : Scheme.{u}}
    [IsIntegral X] (f : X ⟶ Y) (hf : IsBirational f) (x : X) :
    genericResidueFieldTranscendenceDegreeAt f x = 0 := by
  refine le_antisymm (iSup_le fun ξ => ?_) zero_le
  have hξ : (ξ.1 : X) = genericPoint X := by
    simpa [genericPoints_eq_singleton] using (ξ.1.2 : (ξ.1 : X) ∈ genericPoints X)
  rw [hξ]
  exact (residueFieldTranscendenceDegree_genericPoint_eq_zero f hf).le

/-- A birational morphism of integral schemes carries the generic point to the generic point.
This is `AlgebraicGeometry.genericPoint_eq_of_isDominant` with birationality as a hypothesis in
place of the instance `IsDominant`, which is what the consumers below have to hand. -/
theorem IsBirational.genericPoint_eq {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) (hf : IsBirational f) : f (genericPoint X) = genericPoint Y :=
  have := hf.isDominant
  genericPoint_eq_of_isDominant f

end AlgebraicGeometry

end
