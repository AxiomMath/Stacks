module

public import StacksFrontier.AlgebraicGeometry.DeRham.DifferentialGradedAlgebra.ClassMorphismRelativeCup
public import StacksFrontier.AlgebraicGeometry.DeRham.DifferentialGradedAlgebra.ActionTotalComplexUnit
public import StacksFrontier.Algebra.Homology.DerivedCategory.StandardModelScoped

/-!
# The unit law of the derived action

Let `𝒜` be a sheaf of differential graded algebras over a sheaf of rings `A` on a topological
space, with derived action `μ : 𝒜 ⊗^𝐋 𝒜 ⟶ 𝒜` in `D(A)` (the canonical map to the total tensor
complex followed by the multiplication) and unit `u : A ⟶ 𝒜`. The unit acts trivially: the
composite `(u ⊗ 1) ≫ μ : A ⊗^𝐋 𝒜 ⟶ 𝒜` is the canonical map to the total tensor complex followed by
the left unitor of complexes, and it is an isomorphism, the structure sheaf being K-flat.

Together with `CategoryTheory.eq_of_comp_eq_of_linear` this is the argument by which Differential
Graded Sheaves, Section 0FU3, reads an `𝒜`-linear map out of the regular module off its value at
`1`, carried out in the derived category.

## Main results

* `AlgebraicGeometry.SheafOfModules.map_derivedAction_regular`: the derived action precomposed
  with a map of complexes in the first factor.
* `AlgebraicGeometry.SheafOfModules.isIso_dgaUnitHom_derivedAction`: the unit law
  `(u ⊗ 1) ≫ μ` is an isomorphism.

## References

* [Stacks Project, Section 0FU3](https://stacks.math.columbia.edu/tag/0FU3)
* [Stacks Project, Tag 0FU7](https://stacks.math.columbia.edu/tag/0FU7)
-/

@[expose] public section

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

open CategoryTheory Opposite TopologicalSpace
open Stacks.SheafOfModules.Tensor (ringSheaf sheafTensor)
open scoped CategoryTheory.Prod Stacks.Topology.SheafTensorAdditiveOnOpens

open scoped Stacks.StandardDerivedModel

universe u

namespace AlgebraicGeometry.SheafOfModules

section Generic

variable {S : RingedSpace.{u, u}}
  (𝒜 : _root_.SheafOfModules.DifferentialGradedAlgebra.{u, u} (ringSheaf S.sheaf))

/-- **The derived action precomposed in the first factor with a map of complexes** `u : K ⟶ 𝒜` is
the canonical map `K ⊗^𝐋 𝒜 ⟶ Tot(K ⊗ 𝒜)` followed by `Tot(u ⊗ 1)` and the action of the regular
module on total tensor complexes. -/
theorem map_derivedAction_regular
    {K : CochainComplex (_root_.SheafOfModules.{u} (ringSheaf S.sheaf)) ℤ} (u : K ⟶ 𝒜.complex) :
    (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor S.sheaf)).map
        (DerivedCategory.Q.map u ×ₘ 𝟙 (DerivedCategory.Q.obj 𝒜.complex)) ≫
        derivedAction 𝒜 (_root_.SheafOfModules.DifferentialGradedModule.regularModule 𝒜) =
      (Stacks.Cohomology.DerivedPullbackTensor.derivedToTensorNatTrans S).app (K, 𝒜.complex) ≫
        DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap u (𝟙 𝒜.complex)
          (sheafTensor S.sheaf) (ComplexShape.up ℤ) ≫
          dgAction (_root_.SheafOfModules.DifferentialGradedModule.regularModule 𝒜)) := by
  have hn := (Stacks.Cohomology.DerivedPullbackTensor.derivedToTensorNatTrans S).naturality
    (X := (K, 𝒜.complex)) (Y := (𝒜.complex, 𝒜.complex)) (u ×ₘ 𝟙 𝒜.complex)
  have hid : DerivedCategory.Q.map (𝟙 𝒜.complex) = 𝟙 (DerivedCategory.Q.obj 𝒜.complex) :=
    DerivedCategory.Q.map_id _
  dsimp only [Functor.comp_map, Functor.prod_map] at hn
  rw [hid] at hn
  rw [Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair_map] at hn
  unfold derivedAction
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hn).trans ((Category.assoc _ _ _).trans
    (congrArg (_ ≫ ·) (DerivedCategory.Q.map_comp _ _).symm)))

/-- **A unit acting invertibly on complexes acts invertibly in the derived category.** If `K` is
K-flat and `Tot(u ⊗ 1)` followed by the action is an isomorphism of complexes, then
`(u ⊗ 1) ≫ μ : K ⊗^𝐋 𝒜 ⟶ 𝒜` is an isomorphism. -/
theorem isIso_map_derivedAction_regular
    {K : CochainComplex (_root_.SheafOfModules.{u} (ringSheaf S.sheaf)) ℤ}
    (hK : Stacks.SheafOfModules.IsKFlat S.sheaf K) (u : K ⟶ 𝒜.complex)
    [IsIso (HomologicalComplex.mapBifunctorMap u (𝟙 𝒜.complex) (sheafTensor S.sheaf)
        (ComplexShape.up ℤ) ≫
        dgAction (_root_.SheafOfModules.DifferentialGradedModule.regularModule 𝒜))] :
    IsIso ((Functor.uncurry.obj
        (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor S.sheaf)).map
        (DerivedCategory.Q.map u ×ₘ 𝟙 (DerivedCategory.Q.obj 𝒜.complex)) ≫
        derivedAction 𝒜 (_root_.SheafOfModules.DifferentialGradedModule.regularModule 𝒜)) := by
  have h1 : IsIso ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct S.sheaf).toTensor
      K 𝒜.complex) :=
    (congrArg IsIso ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
      S.sheaf).toTensor_eq_comparisonLeft K 𝒜.complex hK)).mpr inferInstance
  have h2 := Functor.map_isIso DerivedCategory.Q (HomologicalComplex.mapBifunctorMap u
    (𝟙 𝒜.complex) (sheafTensor S.sheaf) (ComplexShape.up ℤ) ≫
    dgAction (_root_.SheafOfModules.DifferentialGradedModule.regularModule 𝒜))
  exact (congrArg IsIso (map_derivedAction_regular 𝒜 u)).mpr (@IsIso.comp_isIso _ _ _ _ _ _ _ h1 h2)

end Generic

section Unit

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier}
  (𝒜 : _root_.SheafOfModules.DifferentialGradedAlgebra.{u, u} (ringSheaf A))

/-- **The unit law of the derived action**: for a sheaf of differential graded algebras `𝒜` over
`A`, the unit `A ⟶ 𝒜` in the first factor followed by the derived action
`𝒜 ⊗^𝐋 𝒜 ⟶ 𝒜` is an isomorphism `A ⊗^𝐋 𝒜 ⟶ 𝒜` of `D(A)`: the structure sheaf is K-flat and on
total tensor complexes the composite is the left unitor (`dgAction_regular_unit`). -/
instance isIso_dgaUnitHom_derivedAction :
    IsIso ((Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
        (baseRingedSpace A).sheaf)).map
        (dgaUnitHom 𝒜 ×ₘ 𝟙 (DerivedCategory.Q.obj 𝒜.complex)) ≫
        derivedAction (S := baseRingedSpace A) 𝒜
          (_root_.SheafOfModules.DifferentialGradedModule.regularModule 𝒜)) := by
  have hU : IsIso (HomologicalComplex.mapBifunctorMap (dgUnitComplexHom 𝒜) (𝟙 𝒜.complex)
      (sheafTensor A) (ComplexShape.up ℤ) ≫
      dgAction (_root_.SheafOfModules.DifferentialGradedModule.regularModule 𝒜)) :=
    (congrArg IsIso (dgAction_regular_unit 𝒜)).mpr (Iso.isIso_hom _)
  exact @isIso_map_derivedAction_regular (baseRingedSpace A) 𝒜 _
    (Stacks.SheafOfModules.isKFlat_single_obj_unit A 0) (dgUnitComplexHom 𝒜) hU

end Unit

end AlgebraicGeometry.SheafOfModules
