module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedTensorCounitCriterion
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedTensorAssociativity
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedPullbackTensorFactorization

/-!
# The composition of two derived tensor products

Let `(𝒞, 𝒪)` be a ringed site, let `𝒜`, `𝒜'` and `𝒜''` be sheaves of differential graded
`𝒪`-algebras, let `𝒩` be a differential graded `(𝒜, 𝒜')`-bimodule and `𝒩'` a differential
graded `(𝒜', 𝒜'')`-bimodule. If the canonical map `𝒩 ⊗^𝐋_{𝒜'} 𝒩' ⟶ 𝒩 ⊗_{𝒜'} 𝒩'` of
`D(𝒜'', d)` is an isomorphism, then

`(ℳ ⊗^𝐋_𝒜 𝒩) ⊗^𝐋_{𝒜'} 𝒩' = ℳ ⊗^𝐋_𝒜 (𝒩 ⊗_{𝒜'} 𝒩')`

as functors `D(𝒜, d) ⟶ D(𝒜'', d)`
([Stacks, Tag 0FTL](https://stacks.math.columbia.edu/tag/0FTL)).

## Main definitions

* `SheafOfModules.DifferentialGradedModule.homotopyTensorAssocIso`: associativity of the tensor
  product on homotopy categories, `(- ⊗_𝒜 𝒩) ⊗_{𝒜'} 𝒩' ≅ - ⊗_𝒜 (𝒩 ⊗_{𝒜'} 𝒩')`.
* `SheafOfModules.DifferentialGradedModule.derivedTensorProductCompCounit`: the canonical map
  `(ℳ ⊗^𝐋_𝒜 𝒩) ⊗^𝐋_{𝒜'} 𝒩' ⟶ ℳ ⊗_𝒜 (𝒩 ⊗_{𝒜'} 𝒩')`, natural in `ℳ`.
* `SheafOfModules.DifferentialGradedModule.derivedTensorProductCompIso`: the isomorphism
  `(ℳ ⊗^𝐋_𝒜 𝒩) ⊗^𝐋_{𝒜'} 𝒩' ≅ ℳ ⊗^𝐋_𝒜 (𝒩 ⊗_{𝒜'} 𝒩')` of functors `D(𝒜, d) ⥤ D(𝒜'', d)`.

## Main results

* `SheafOfModules.DifferentialGradedModule.isIso_derivedTensorProductCounit_app_tensor`: under the
  hypothesis, the canonical map `(𝒫 ⊗_𝒜 𝒩) ⊗^𝐋_{𝒜'} 𝒩' ⟶ (𝒫 ⊗_𝒜 𝒩) ⊗_{𝒜'} 𝒩'` is invertible for
  every flat and K-flat `𝒫`.
* `SheafOfModules.DifferentialGradedModule.isLeftDerivedFunctor_derivedTensorProductComp`: the
  composite of the two derived tensor products is the left derived functor of
  `ℳ ↦ ℳ ⊗_𝒜 (𝒩 ⊗_{𝒜'} 𝒩')`.

## References

* [Stacks Project, Tag 0FTL](https://stacks.math.columbia.edu/tag/0FTL)
* [Stacks Project, Tag 0FTK](https://stacks.math.columbia.edu/tag/0FTK)
* [Stacks Project, Tag 0FTJ](https://stacks.math.columbia.edu/tag/0FTJ)
* [Stacks Project, Tag 0FSH](https://stacks.math.columbia.edu/tag/0FSH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Sheaf

universe u

namespace SheafOfModules

namespace DifferentialGradedModule

section Generic

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] [HasWeakSheafify J (Type u)]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}]
  {Osharp : Sheaf J CommRingCat.{u}}
  {A A' : DifferentialGradedAlgebra.{u, u} (toRingCat J Osharp)}

omit [HasWeakSheafify J (Type u)] in
/-- If `𝒩 ⊗_{𝒜'} ℒ` is acyclic, so is `(𝒫 ⊗_𝒜 𝒩) ⊗_{𝒜'} ℒ` for every K-flat `𝒫`. -/
theorem acyclic_dgTensor_dgTensorRight {N : DifferentialGradedBimodule.{u, u, u} A A'}
    (L : LeftDifferentialGradedModule.{u, u, u} A')
    (hNL : (RelativeTensor.dgTensor N.toRightModule L).Acyclic)
    {P : DifferentialGradedModule.{u, u, u} A} (hP : RelativeTensor.IsKFlat P) :
    (RelativeTensor.dgTensor (RelativeTensor.dgTensorRight P N) L).Acyclic := by
  let e := (toCochainComplex _).mapIso (RelativeTensor.dgTensorAssocIso N L.unitBimodule P)
  exact (acyclic_iff_of_iso e).2
    (hP (RelativeTensor.bimoduleTensor N L.unitBimodule).toLeftDifferentialGradedModule hNL)

end Generic

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

variable {X : AlgebraicGeometry.RingedSite.{u, u, u}}
  {A A' A'' : DifferentialGradedAlgebra.{u, u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
  (N : DifferentialGradedBimodule.{u, u, u} A A') (N' : DifferentialGradedBimodule.{u, u, u} A' A'')

/-- If the canonical map `𝒩 ⊗^𝐋_{𝒜'} 𝒩' ⟶ 𝒩 ⊗_{𝒜'} 𝒩'` is an isomorphism of `D(𝒜'', d)`, then so is
the canonical map `(𝒫 ⊗_𝒜 𝒩) ⊗^𝐋_{𝒜'} 𝒩' ⟶ (𝒫 ⊗_𝒜 𝒩) ⊗_{𝒜'} 𝒩'` for every flat and K-flat right
differential graded `𝒜`-module `𝒫`. -/
theorem isIso_derivedTensorProductCounit_app_tensor
    (hN : IsIso ((derivedTensorProductCounit N').app
      ((HomotopyCategory.quotient A').obj N.toRightModule)))
    {P : DifferentialGradedModule.{u, u, u} A}
    (hP : RelativeTensor.IsGradedFlat
        (GradedModule.ofDifferentialGraded
          (A := (A : DifferentialGradedAlgebra.{u, u} (toRingCat X.J X.O))) P) ∧
      RelativeTensor.IsKFlat (A := (A : DifferentialGradedAlgebra.{u, u} (toRingCat X.J X.O))) P) :
    IsIso ((derivedTensorProductCounit N').app
      ((HomotopyCategory.quotient A').obj ((tensorData N).functor.obj P))) := by
  have : HasSheafify X.J AddCommGrpCat.{u} := inferInstance
  have : X.J.WEqualsLocallyBijective AddCommGrpCat.{u} := inferInstance
  obtain ⟨R', r', hr', -, hR'⟩ := exists_flat_quasiIso
    (A := (A' : DifferentialGradedAlgebra.{u, u} (toRingCat X.J X.O)).op)
    N'.toLeftDifferentialGradedModule.opRight
  have hc : (cone r').complex.Acyclic := (acyclic_cone_iff_quasiIso _ r').2 hr'
  rw [isIso_derivedTensorProductCounit_app_iff N' r' hR' hc] at hN ⊢
  exact acyclic_dgTensor_dgTensorRight (C := X.C) (cone r').unopLeft hN hP.2

/-- **Associativity of the tensor product of differential graded modules**:
`(- ⊗_𝒜 𝒩) ⊗_{𝒜'} 𝒩' ≅ - ⊗_𝒜 (𝒩 ⊗_{𝒜'} 𝒩')`. -/
noncomputable def tensorAssocNatIso :
    (tensorData N).functor ⋙ (tensorData N').functor ≅
      (tensorData (DifferentialGradedBimodule.tensorBimodule N N')).functor :=
  RelativeTensor.dgTensorAssocNatIso (C := X.C) (J := X.J) (Osharp := X.O) N N'

/-- The functor `- ⊗_𝒜 𝒩` of differential graded modules, followed by the quotient functor, is
the quotient functor followed by the induced functor of homotopy categories. -/
theorem quotient_comp_pullbackTensor_tensorData
    {B : DifferentialGradedAlgebra.{u, u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (M : DifferentialGradedBimodule.{u, u, u} A B) :
    HomotopyCategory.quotient A ⋙
        HomotopyCategory.pullbackTensor idPullbackDataHomotopyExtension (tensorData M) =
      (tensorData M).functor ⋙ HomotopyCategory.quotient B := by
  rw [HomotopyCategory.quotient_comp_pullbackTensor, pullbackTensorFunctor,
    idPullbackData_functor_eq]
  rfl

/-- **Associativity of the tensor product on homotopy categories**:
`(- ⊗_𝒜 𝒩) ⊗_{𝒜'} 𝒩' ≅ - ⊗_𝒜 (𝒩 ⊗_{𝒜'} 𝒩')` as functors `K(Mod(𝒜, d)) ⥤ K(Mod(𝒜'', d))`. -/
noncomputable def homotopyTensorAssocIso :
    HomotopyCategory.pullbackTensor idPullbackDataHomotopyExtension (tensorData N) ⋙
        HomotopyCategory.pullbackTensor idPullbackDataHomotopyExtension (tensorData N') ≅
      HomotopyCategory.pullbackTensor idPullbackDataHomotopyExtension
        (tensorData (DifferentialGradedBimodule.tensorBimodule N N')) :=
  Quotient.natIsoLift _
    (eqToIso (calc HomotopyCategory.quotient A ⋙
            (HomotopyCategory.pullbackTensor idPullbackDataHomotopyExtension (tensorData N) ⋙
              HomotopyCategory.pullbackTensor idPullbackDataHomotopyExtension (tensorData N'))
          _ = (HomotopyCategory.quotient A ⋙
              HomotopyCategory.pullbackTensor idPullbackDataHomotopyExtension (tensorData N)) ⋙
              HomotopyCategory.pullbackTensor idPullbackDataHomotopyExtension (tensorData N') :=
            (Functor.assoc _ _ _).symm
          _ = ((tensorData N).functor ⋙ HomotopyCategory.quotient A') ⋙
              HomotopyCategory.pullbackTensor idPullbackDataHomotopyExtension (tensorData N') := by
            rw [quotient_comp_pullbackTensor_tensorData N]
          _ = (tensorData N).functor ⋙ (HomotopyCategory.quotient A' ⋙
              HomotopyCategory.pullbackTensor idPullbackDataHomotopyExtension (tensorData N')) :=
            Functor.assoc _ _ _
          _ = (tensorData N).functor ⋙
              ((tensorData N').functor ⋙ HomotopyCategory.quotient A'') := by
            rw [quotient_comp_pullbackTensor_tensorData N']
          _ = ((tensorData N).functor ⋙ (tensorData N').functor) ⋙ HomotopyCategory.quotient A'' :=
            (Functor.assoc _ _ _).symm) ≪≫
      Functor.isoWhiskerRight (tensorAssocNatIso N N') (HomotopyCategory.quotient A'') ≪≫
      eqToIso (quotient_comp_pullbackTensor_tensorData
        (DifferentialGradedBimodule.tensorBimodule N N')).symm)

/-- **The canonical map `(ℳ ⊗^𝐋_𝒜 𝒩) ⊗^𝐋_{𝒜'} 𝒩' ⟶ ℳ ⊗_𝒜 (𝒩 ⊗_{𝒜'} 𝒩')`**, natural in the
object `ℳ` of `K(Mod(𝒜, d))`: the canonical map of the first derived tensor product carried by
the second, followed by the canonical map of the second and by associativity. -/
noncomputable def derivedTensorProductCompCounit :
    toDerivedCategory.{u, u, u} A ⋙ (derivedTensorProduct N ⋙ derivedTensorProduct N') ⟶
      HomotopyCategory.pullbackTensor idPullbackDataHomotopyExtension
          (tensorData (DifferentialGradedBimodule.tensorBimodule N N')) ⋙
        toDerivedCategory.{u, u, u} A'' :=
  (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (derivedTensorProductCounit N) (derivedTensorProduct N') ≫
      (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft
          (HomotopyCategory.pullbackTensor idPullbackDataHomotopyExtension (tensorData N))
          (derivedTensorProductCounit N') ≫
          (Functor.associator _ _ _).inv ≫
            Functor.whiskerRight (homotopyTensorAssocIso N N').hom (toDerivedCategory A'')

/-- At a flat and K-flat module the canonical map of the composite is an isomorphism, under the
hypothesis of Tag 0FTL. -/
theorem isIso_derivedTensorProductCompCounit_app
    (hN : IsIso ((derivedTensorProductCounit N').app
      ((HomotopyCategory.quotient A').obj N.toRightModule)))
    {P : DifferentialGradedModule.{u, u, u} A}
    (hP : RelativeTensor.IsGradedFlat
        (GradedModule.ofDifferentialGraded
          (A := (A : DifferentialGradedAlgebra.{u, u} (toRingCat X.J X.O))) P) ∧
      RelativeTensor.IsKFlat (A := (A : DifferentialGradedAlgebra.{u, u} (toRingCat X.J X.O))) P) :
    IsIso ((derivedTensorProductCompCounit N N').app ((HomotopyCategory.quotient A).obj P)) := by
  have := isIso_derivedTensorProductCounit_app N hP
  have : IsIso ((derivedTensorProductCounit N').app
      ((HomotopyCategory.pullbackTensor idPullbackDataHomotopyExtension (tensorData N)).obj
        ((HomotopyCategory.quotient A).obj P))) :=
    isIso_derivedTensorProductCounit_app_tensor N N' hN hP
  simp only [derivedTensorProductCompCounit, NatTrans.comp_app, Functor.associator_inv_app,
    Functor.associator_hom_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  infer_instance

/-- **The composite of the two derived tensor products is the left derived functor of
`ℳ ↦ ℳ ⊗_𝒜 (𝒩 ⊗_{𝒜'} 𝒩')`**, under the hypothesis of Tag 0FTL. -/
theorem isLeftDerivedFunctor_derivedTensorProductComp
    (hN : IsIso ((derivedTensorProductCounit N').app
      ((HomotopyCategory.quotient A').obj N.toRightModule))) :
    (derivedTensorProduct N ⋙ derivedTensorProduct N').IsLeftDerivedFunctor
      (derivedTensorProductCompCounit N N') (quasiIsomorphisms.{u, u, u} A) :=
  isLeftDerivedFunctor_of_isIso_app_of_isGood _
    (tensorExactnessData (DifferentialGradedBimodule.tensorBimodule N N')) _ _
    fun _ hP => isIso_derivedTensorProductCompCounit_app N N' hN hP

/-- Let `(𝒞, 𝒪)` be a ringed site, let `𝒜`, `𝒜'`, `𝒜''` be sheaves of differential graded
`𝒪`-algebras, let `𝒩` be a differential graded `(𝒜, 𝒜')`-bimodule and `𝒩'` a differential graded
`(𝒜', 𝒜'')`-bimodule. Assume that the canonical map `𝒩 ⊗^𝐋_{𝒜'} 𝒩' ⟶ 𝒩 ⊗_{𝒜'} 𝒩'` of `D(𝒜'', d)` is
an isomorphism. Then `(ℳ ⊗^𝐋_𝒜 𝒩) ⊗^𝐋_{𝒜'} 𝒩' = ℳ ⊗^𝐋_𝒜 (𝒩 ⊗_{𝒜'} 𝒩')` as functors
`D(𝒜, d) ⥤ D(𝒜'', d)`. -/
@[stacks 0FTL]
noncomputable def derivedTensorProductCompIso
    (hN : IsIso ((derivedTensorProductCounit N').app
      ((HomotopyCategory.quotient A').obj N.toRightModule))) :
    derivedTensorProduct N ⋙ derivedTensorProduct N' ≅
      derivedTensorProduct (DifferentialGradedBimodule.tensorBimodule N N') :=
  haveI := isLeftDerivedFunctor_derivedTensorProductComp N N' hN
  Functor.leftDerivedUnique _ _ (derivedTensorProductCompCounit N N')
    (derivedTensorProductCounit (DifferentialGradedBimodule.tensorBimodule N N'))
    (quasiIsomorphisms.{u, u, u} A)

end DifferentialGradedModule

end SheafOfModules

end
