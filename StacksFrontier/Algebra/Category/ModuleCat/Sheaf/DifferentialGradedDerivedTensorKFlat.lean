module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedTensorProduct
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeDifferentialGradedModuleToposPullback

/-!
# The derived tensor product with a flat bimodule is the ordinary one

Let `(𝒞, 𝒪)` be a ringed site, let `𝒜` and `𝒜'` be sheaves of differential graded
`𝒪`-algebras, and let `𝒩` be a differential graded `(𝒜, 𝒜')`-bimodule which is good as a left
differential graded `𝒜`-module. Then `ℳ ⊗^𝐋_𝒜 𝒩 = ℳ ⊗_𝒜 𝒩` for every right differential
graded `𝒜`-module `ℳ` ([Stacks, Tag 0FTK](https://stacks.math.columbia.edu/tag/0FTK)).

The derived tensor product is `SheafOfModules.DifferentialGradedModule.derivedTensorProduct`,
the functor of Tag 0FTG (1), and the canonical map from it to the ordinary tensor product is its
comparison map `derivedTensorProductCounit`. The statement is that this comparison is an
isomorphism of functors.

A left differential graded `𝒜`-module is read as a right differential graded `𝒜^{opp}`-module
(`SheafOfModules.LeftDifferentialGradedModule.opRight`), and goodness and K-flatness of a left
module mean goodness and K-flatness of that right module (Tag 0FRM).

## Main results

* `SheafOfModules.DifferentialGradedModule.acyclic_dgTensor_of_isKFlat_opRight`: if a left
  differential graded `𝒜`-module `𝒩` is K-flat, read as a right differential graded
  `𝒜^{opp}`-module, then `𝒦 ⊗_𝒜 𝒩` is acyclic for every acyclic right module `𝒦`.
* `SheafOfModules.DifferentialGradedModule.isIso_derivedTensorProductCounit_of_isGood`: if `𝒩`
  is good (Tag 0FSA) as a left differential graded `𝒜`-module, the comparison
  `ℳ ⊗^𝐋_𝒜 𝒩 ⟶ ℳ ⊗_𝒜 𝒩` is an isomorphism of functors (Tag 0FTK).
* `SheafOfModules.DifferentialGradedModule.isIso_derivedTensorProductCounit`: the same when `𝒩`
  is merely K-flat as a left differential graded `𝒜`-module.
* `SheafOfModules.DifferentialGradedModule.derivedTensorProductIsoTensor`: the resulting
  natural isomorphism `ℳ ⊗^𝐋_𝒜 𝒩 ≅ ℳ ⊗_𝒜 𝒩`.
* `SheafOfModules.DifferentialGradedModule.isIso_derivedTensorCounit`: the comparison is an
  isomorphism for an abstract tensor product functor, given its exactness on the resolving class
  and that it carries acyclic modules to acyclic ones.

## References

* [Stacks Project, Tag 0FTK](https://stacks.math.columbia.edu/tag/0FTK)
* [Stacks Project, Tag 0FTG](https://stacks.math.columbia.edu/tag/0FTG)
* [Stacks Project, Tag 0FTF](https://stacks.math.columbia.edu/tag/0FTF)
* [Stacks Project, Tag 0FSA](https://stacks.math.columbia.edu/tag/0FSA)
* [Stacks Project, Tag 0FRM](https://stacks.math.columbia.edu/tag/0FRM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Sheaf

universe t a m s z v u v₁ u₁

namespace SheafOfModules

namespace DifferentialGradedModule

/-- A quasi-isomorphism of right differential graded modules becomes invertible in the derived
category. -/
private theorem isIso_toDerivedCategory_map_of_quasiIso
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
    [HasSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
    {A : DifferentialGradedAlgebra.{t, a} R}
    {M M₂ : DifferentialGradedModule.{t, a, m} A} (ψ : M ⟶ M₂)
    (hψ : QuasiIso ψ.toHomologicalComplex) :
    IsIso ((toDerivedCategory.{t, a, m} A).map ((HomotopyCategory.quotient A).map ψ)) :=
  isIso_toDerivedCategory_map_of_acyclic_cone A ψ ((acyclic_cone_iff_quasiIso A ψ).2 hψ)

section KFlat

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  [HasSheafify J AddCommGrpCat.{s}] [J.WEqualsLocallyBijective AddCommGrpCat.{s}]
  [HasSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
  {A A' : DifferentialGradedAlgebra.{t, a} R}
  {N : DifferentialGradedBimodule.{t, a, z} A A'}
  {D : TensorFunctorData.{t, a, m, z, s} A A' N}
  {g : GoodResolutionData.{t, a, m, v, u} A}

/-- **The tensor product with a bimodule which is K-flat on the left carries a homomorphism
with acyclic cone to a quasi-isomorphism.** -/
theorem quasiIso_tensor_map_of_acyclic
    (hE : PullbackTensorExactnessData (idPullbackData.{t, a, m} (A := A)) D g)
    (hKFlat : ∀ K : DifferentialGradedModule.{t, a, m} A, K.complex.Acyclic →
      ((pullbackTensorFunctor (idPullbackData.{t, a, m} (A := A)) D).obj K).complex.Acyclic)
    {M M₂ : DifferentialGradedModule.{t, a, m} A} (ψ : M ⟶ M₂)
    (hψ : QuasiIso ψ.toHomologicalComplex) :
    QuasiIso ((pullbackTensorFunctor (idPullbackData.{t, a, m} (A := A)) D).map
      ψ).toHomologicalComplex :=
  (acyclic_cone_iff_quasiIso A'
      ((pullbackTensorFunctor (idPullbackData.{t, a, m} (A := A)) D).map ψ)).1 fun n =>
    (hKFlat (cone ψ) ((acyclic_cone_iff_quasiIso A ψ).2 hψ) n).of_iso (hE.coneIso ψ)

variable [(quasiIsomorphisms.{t, a, m} A).HasRightCalculusOfFractions]

/-- **The canonical map `ℳ ⊗^𝐋_𝒜 𝒩 ⟶ ℳ ⊗_𝒜 𝒩` is an isomorphism at every right differential
graded `𝒜`-module**, when `𝒩` is K-flat as a left differential graded `𝒜`-module. -/
theorem isIso_derivedTensorCounit_app
    (hE : PullbackTensorExactnessData (idPullbackData.{t, a, m} (A := A)) D g)
    (hKFlat : ∀ K : DifferentialGradedModule.{t, a, m} A, K.complex.Acyclic →
      ((pullbackTensorFunctor (idPullbackData.{t, a, m} (A := A)) D).obj K).complex.Acyclic)
    (X : HomotopyCategory.{t, a, m} A) :
    IsIso ((derivedPullbackTensorCounit
      (idPullbackDataHomotopyExtension.{t, a, m} (A := A)) hE).app X) := by
  obtain ⟨P, p, hP, hp⟩ := g.exists_isGood X.as
  have := isIso_derivedPullbackTensorCounit_app_of_isGood
    (idPullbackDataHomotopyExtension.{t, a, m} (A := A)) hE hP
  have : IsIso ((toDerivedCategory A).map ((HomotopyCategory.quotient A).map p)) :=
    isIso_toDerivedCategory_map_of_quasiIso p hp
  have hq : IsIso ((toDerivedCategory.{t, a, s} A').map ((HomotopyCategory.quotient A').map
      ((pullbackTensorFunctor (idPullbackData.{t, a, m} (A := A)) D).map p))) :=
    isIso_toDerivedCategory_map_of_quasiIso _ (quasiIso_tensor_map_of_acyclic hE hKFlat p hp)
  have : IsIso ((toDerivedCategory A ⋙
      derivedPullbackTensor (idPullbackDataHomotopyExtension.{t, a, m} (A := A)) hE).map
        ((HomotopyCategory.quotient A).map p)) := by
    dsimp only [Functor.comp_map]
    infer_instance
  have : IsIso ((HomotopyCategory.pullbackTensor
      (idPullbackDataHomotopyExtension.{t, a, m} (A := A)) D ⋙
        toDerivedCategory.{t, a, s} A').map ((HomotopyCategory.quotient A).map p)) := hq
  have hnat := (derivedPullbackTensorCounit
    (idPullbackDataHomotopyExtension.{t, a, m} (A := A)) hE).naturality
      ((HomotopyCategory.quotient A).map p)
  have key : (derivedPullbackTensorCounit
        (idPullbackDataHomotopyExtension.{t, a, m} (A := A)) hE).app X =
      inv ((toDerivedCategory A ⋙
          derivedPullbackTensor (idPullbackDataHomotopyExtension.{t, a, m} (A := A)) hE).map
        ((HomotopyCategory.quotient A).map p)) ≫
        (derivedPullbackTensorCounit
          (idPullbackDataHomotopyExtension.{t, a, m} (A := A)) hE).app
            ((HomotopyCategory.quotient A).obj P) ≫
          (HomotopyCategory.pullbackTensor (idPullbackDataHomotopyExtension.{t, a, m} (A := A)) D ⋙
            toDerivedCategory.{t, a, s} A').map ((HomotopyCategory.quotient A).map p) := by
    rw [← hnat, IsIso.inv_hom_id_assoc]
    rfl
  rw [key]
  infer_instance

/-- **For an abstract tensor product functor, the canonical map `ℳ ⊗^𝐋_𝒜 𝒩 ⟶ ℳ ⊗_𝒜 𝒩` is an
isomorphism of functors** as soon as the tensor product carries acyclic modules to acyclic ones.
-/
theorem isIso_derivedTensorCounit
    (hE : PullbackTensorExactnessData (idPullbackData.{t, a, m} (A := A)) D g)
    (hKFlat : ∀ K : DifferentialGradedModule.{t, a, m} A, K.complex.Acyclic →
      ((pullbackTensorFunctor (idPullbackData.{t, a, m} (A := A)) D).obj K).complex.Acyclic) :
    IsIso (derivedPullbackTensorCounit
      (idPullbackDataHomotopyExtension.{t, a, m} (A := A)) hE) := by
  rw [NatTrans.isIso_iff_isIso_app]
  exact fun X => isIso_derivedTensorCounit_app hE hKFlat X

end KFlat

/-! ### Tensoring with a left module which is K-flat -/

section LeftKFlat

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] [HasWeakSheafify J (Type m)]
  [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasSheafify J AddCommGrpCat.{m}]
  {Osharp : Sheaf J CommRingCat.{t}} {A : DifferentialGradedAlgebra.{t, m} (toRingCat J Osharp)}

/-- **The tensor product of an acyclic module with a left module which is K-flat is acyclic.**
Let `L` be a left differential graded `A`-module which is K-flat as a right differential graded
`A.op`-module and let `K` be an acyclic right differential graded `A`-module. Then
`K ⊗_A L = L ⊗_{A.op} K` is acyclic. -/
theorem acyclic_dgTensor_of_isKFlat_opRight {L : LeftDifferentialGradedModule.{t, m, m} A}
    (hL : RelativeTensor.IsKFlat L.opRight) {K : DifferentialGradedModule.{t, m, m} A}
    (hK : K.complex.Acyclic) : (RelativeTensor.dgTensor K L).Acyclic := by
  have h := RelativeTensor.acyclic_dgTensor_of_acyclic_dgTensor_op K L.opRight (hL K.opLeft hK)
  rwa [LeftDifferentialGradedModule.opRight_unopLeft] at h

end LeftKFlat

/-! ### Tag 0FTK -/

section DerivedTensorProduct

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

variable {X : AlgebraicGeometry.RingedSite.{u, u, u}}
  {A A' : DifferentialGradedAlgebra.{u, u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
  (N : DifferentialGradedBimodule.{u, u, u} A A')

/-- **The derived tensor product with a bimodule which is K-flat on the left is the tensor
product.** Let `𝒩` be a differential graded `(𝒜, 𝒜')`-bimodule which is K-flat as a left
differential graded `𝒜`-module. Then the canonical map `ℳ ⊗^𝐋_𝒜 𝒩 ⟶ ℳ ⊗_𝒜 𝒩` is an
isomorphism of functors. -/
theorem isIso_derivedTensorProductCounit
    (hN : RelativeTensor.IsKFlat.{u, u, u, u}
      (A := (A : DifferentialGradedAlgebra.{u, u} (toRingCat X.J X.O)).op)
      N.toLeftDifferentialGradedModule.opRight) :
    IsIso (derivedTensorProductCounit N) :=
  isIso_derivedTensorCounit (tensorExactnessData N) fun _ hK =>
    acyclic_dgTensor_of_isKFlat_opRight hN hK

/-- **The derived tensor product with a bimodule which is K-flat on the left is the tensor
product**: the natural isomorphism `ℳ ⊗^𝐋_𝒜 𝒩 ≅ ℳ ⊗_𝒜 𝒩` of Tag 0FTK. -/
noncomputable def derivedTensorProductIsoTensor
    (hN : RelativeTensor.IsKFlat.{u, u, u, u}
      (A := (A : DifferentialGradedAlgebra.{u, u} (toRingCat X.J X.O)).op)
      N.toLeftDifferentialGradedModule.opRight) :
    toDerivedCategory.{u, u, u} A ⋙ derivedTensorProduct N ≅
      HomotopyCategory.pullbackTensor idPullbackDataHomotopyExtension (tensorData N) ⋙
        toDerivedCategory.{u, u, u} A' :=
  haveI := isIso_derivedTensorProductCounit N hN
  asIso (derivedTensorProductCounit N)

/-- Let `(𝒞, 𝒪)` be a ringed site, `𝒜`, `𝒜'` differential graded `𝒪`-algebras and `𝒩` a
differential graded `(𝒜, 𝒜')`-bimodule which is good (Tag 0FSA) as a left differential graded
`𝒜`-module. Then `ℳ ⊗^𝐋_𝒜 𝒩 = ℳ ⊗_𝒜 𝒩` for every differential graded `𝒜`-module `ℳ`: the canonical
map from the derived tensor product to the tensor product is an isomorphism of functors. -/
@[stacks 0FTK "M ⊗^L_A N = M ⊗_A N for N good as a left module"]
theorem isIso_derivedTensorProductCounit_of_isGood
    (hN : IsGoodToposBaseChange.{u, v₁, u₁} (Y := X.toRingedTopos)
      (A := (A : DifferentialGradedAlgebra.{u, u} (toRingCat X.J X.O)).op)
      N.toLeftDifferentialGradedModule.opRight) :
    IsIso (derivedTensorProductCounit N) :=
  isIso_derivedTensorProductCounit N hN.isKFlat

end DerivedTensorProduct

end DifferentialGradedModule

end SheafOfModules

end
