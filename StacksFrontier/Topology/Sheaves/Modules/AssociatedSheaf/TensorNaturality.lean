module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AssociatedSheafIsos
public import StacksFrontier.Topology.Sheaves.Modules.AssociatedSheaf.Tensor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BifunctorReductionMachinery

/-!
# Construction (3) commutes with the tensor product naturally

The comparison `ℱ_{M ⊗_R N} ≅ ℱ_M ⊗_{𝒪_X} ℱ_N` of construction (3) of Stacks 01BH with the tensor
product is natural in `M` and in `N`, already at the level of presheaves.

## References

* [Stacks Project, Tag 01BH](https://stacks.math.columbia.edu/tag/01BH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
  TopologicalSpace

namespace Stacks.AssociatedSheaf

universe u

attribute [local instance] hasModuleSheafify moduleSheafifyWEqualsLocallyBijective

attribute [local implicit_reducible] structureSheafRing
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
  Stacks.SheafOfModules.TensorSheafification.sheafify
  Stacks.SheafOfModules.TensorSheafification.tensorUnitMap
  Stacks.SheafOfModules.TensorSheafification.toSheafify
  _root_.SheafOfModules.forget _root_.PresheafOfModules.restrictScalars
  _root_.PresheafOfModules.toPresheaf _root_.PresheafOfModulesOfCommRing.Monoidal.tensorObj
  _root_.PresheafOfModules.tensorObj

variable (X : RingedSpace.{u, u}) {R : Type u} [CommRing R] (α : R →+* X.presheaf.obj (op ⊤))

/-- Two additive maps out of `A ⊗ (M ⊗ N)` agree if they agree on elements `a ⊗ (m ⊗ n)`. -/
private theorem apply_eq_of_tmul_tmul {R S A M N G F : Type*} [CommSemiring R] [CommSemiring S]
    [AddCommMonoid A] [Module S A] [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
    [Module S (TensorProduct R M N)] [AddCommMonoid G]
    [FunLike F (TensorProduct S A (TensorProduct R M N)) G]
    [AddMonoidHomClass F (TensorProduct S A (TensorProduct R M N)) G] (φ ψ : F)
    (h : ∀ (a : A) (m : M) (n : N),
      φ (a ⊗ₜ[S] (m ⊗ₜ[R] n)) = ψ (a ⊗ₜ[S] (m ⊗ₜ[R] n)))
    (x : TensorProduct S A (TensorProduct R M N)) : φ x = ψ x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul a z =>
    induction z using TensorProduct.induction_on with
    | zero => rw [TensorProduct.tmul_zero, map_zero, map_zero]
    | add z w hz hw => rw [TensorProduct.tmul_add, map_add, map_add, hz, hw]
    | tmul m n => exact h a m n

public theorem associatedPresheafTensorIso_naturality_left {M M' : ModuleCat.{u} R}
    (f : M ⟶ M') (N : ModuleCat.{u} R) :
    letI : MonoidalCategory (PresheafOfModules.{u} (structureSheafRing X).obj) :=
      PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)
    (associatedPresheafFunctor X α).map (f ▷ N) ≫ (associatedPresheafTensorIso X α M' N).hom =
      (associatedPresheafTensorIso X α M N).hom ≫
        ((associatedPresheafFunctor X α).map f ▷ associatedPresheaf X α N) := by
  refine PresheafOfModules.hom_ext fun U => ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  let := ((globalSectionsMap X α).app U).hom.toAlgebra
  let : Module ↑((constantRingPresheaf X R).obj U) (TensorProduct R M N) :=
    ((constantModulePresheaf X (M ⊗ N)).obj U).isModule
  refine apply_eq_of_tmul_tmul _ _ ?_ x
  exact fun _ _ _ => rfl

public theorem associatedPresheafTensorIso_naturality_right (M : ModuleCat.{u} R)
    {N N' : ModuleCat.{u} R} (g : N ⟶ N') :
    letI : MonoidalCategory (PresheafOfModules.{u} (structureSheafRing X).obj) :=
      PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)
    (associatedPresheafFunctor X α).map (M ◁ g) ≫ (associatedPresheafTensorIso X α M N').hom =
      (associatedPresheafTensorIso X α M N).hom ≫
        (associatedPresheaf X α M ◁ (associatedPresheafFunctor X α).map g) := by
  refine PresheafOfModules.hom_ext fun U => ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  let := ((globalSectionsMap X α).app U).hom.toAlgebra
  let : Module ↑((constantRingPresheaf X R).obj U) (TensorProduct R M N') :=
    ((constantModulePresheaf X (M ⊗ N')).obj U).isModule
  let : Module ↑((constantRingPresheaf X R).obj U) (TensorProduct R M N) :=
    ((constantModulePresheaf X (M ⊗ N)).obj U).isModule
  refine apply_eq_of_tmul_tmul _ _ ?_ x
  exact fun _ _ _ => rfl

public theorem map_comp_comp {C D : Type*} [Category* C] [Category* D] (S : C ⥤ D) {a b c d : C}
    (x : a ⟶ b) (y : b ⟶ c) (z : c ⟶ d) : S.map ((x ≫ y) ≫ z) = S.map x ≫ S.map y ≫ S.map z := by
  rw [Functor.map_comp, Functor.map_comp, Category.assoc]

public theorem map_comp_comp' {C D : Type*} [Category* C] [Category* D] (S : C ⥤ D) {a b c d : C}
    (x : a ⟶ b) (y : b ⟶ c) (z : c ⟶ d) : S.map ((x ≫ y) ≫ z) = (S.map x ≫ S.map y) ≫ S.map z := by
  rw [Functor.map_comp, Functor.map_comp]

/-- In a monoidal category, whiskering commutes with a tensor product of maps compatible with a
morphism. -/
public theorem whiskerRight_comp_tensorHom_of_comp {C : Type*} [Category* C] [MonoidalCategory C]
    {A A' B A₁ A₁' B₁ : C} (f : A ⟶ A') (uA : A ⟶ A₁) (uA' : A' ⟶ A₁') (uB : B ⟶ B₁)
    (g : A₁ ⟶ A₁') (h : f ≫ uA' = uA ≫ g) :
    f ▷ B ≫ (uA' ⊗ₘ uB) = (uA ⊗ₘ uB) ≫ g ▷ B₁ := by
  rw [MonoidalCategory.tensorHom_def, MonoidalCategory.tensorHom_def, ← Category.assoc,
    ← MonoidalCategory.comp_whiskerRight, h, MonoidalCategory.comp_whiskerRight, Category.assoc,
    Category.assoc, MonoidalCategory.whisker_exchange]

public theorem assocTensorIso_naturality_left {M M' : ModuleCat.{u} R}
    (f : M ⟶ M') (N : ModuleCat.{u} R) :
    letI : MonoidalCategory (PresheafOfModules.{u} (structureSheafRing X).obj) :=
      PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)
    (associatedSheafFunctor.{u, u} X α).map (X := M ⊗ N) (Y := M' ⊗ N) (f ▷ N) ≫
        (associatedSheafTensorIso X α M' N).hom =
      (associatedSheafTensorIso X α M N).hom ≫
        (Stacks.SheafOfModules.TensorSheafification.sheafify X.presheaf
          (structureSheafRing X).property).map
          (X := PresheafOfModules.tensorObj (O := X.presheaf)
            ((associatedSheafFunctor.{u, u} X α).obj M).val
            ((associatedSheafFunctor.{u, u} X α).obj N).val)
          (Y := PresheafOfModules.tensorObj (O := X.presheaf)
            ((associatedSheafFunctor.{u, u} X α).obj M').val
            ((associatedSheafFunctor.{u, u} X α).obj N).val)
          ((SheafOfModules.forget (structureSheafRing X) ⋙
              PresheafOfModules.restrictScalars (𝟙 (structureSheafRing X).obj)).map
            (X := (associatedSheafFunctor.{u, u} X α).obj M)
            (Y := (associatedSheafFunctor.{u, u} X α).obj M')
            ((associatedSheafFunctor.{u, u} X α).map (X := M) (Y := M') f) ▷
            (SheafOfModules.forget (structureSheafRing X) ⋙
              PresheafOfModules.restrictScalars (𝟙 (structureSheafRing X).obj)).obj
              ((associatedSheafFunctor.{u, u} X α).obj N)) := by
  let : MonoidalCategory (PresheafOfModules.{u} (structureSheafRing X).obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)
  have hT : CommSq
      ((associatedPresheafFunctor X α).map (X := M) (Y := M') f ▷ associatedPresheaf X α N)
      (Stacks.SheafOfModules.TensorSheafification.tensorUnitMap X.presheaf
        (structureSheafRing X).property (associatedPresheaf X α M) (associatedPresheaf X α N))
      (Stacks.SheafOfModules.TensorSheafification.tensorUnitMap X.presheaf
        (structureSheafRing X).property (associatedPresheaf X α M') (associatedPresheaf X α N))
      ((SheafOfModules.forget (structureSheafRing X) ⋙
          PresheafOfModules.restrictScalars (𝟙 (structureSheafRing X).obj)).map
          (X := (associatedSheafFunctor.{u, u} X α).obj M)
          (Y := (associatedSheafFunctor.{u, u} X α).obj M')
          ((associatedSheafFunctor.{u, u} X α).map (X := M) (Y := M') f) ▷
        (SheafOfModules.forget (structureSheafRing X) ⋙
          PresheafOfModules.restrictScalars (𝟙 (structureSheafRing X).obj)).obj
          ((associatedSheafFunctor.{u, u} X α).obj N)) := by
    refine ⟨PresheafOfModules.hom_ext fun sectionObj =>
      ModuleCat.tensor_ext (R := X.presheaf.obj sectionObj)
        (M := (associatedPresheaf X α M).obj sectionObj)
        (N := (associatedPresheaf X α N).obj sectionObj) fun leftSection rightSection => ?_⟩
    have unitNaturality :=
      (Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction X.presheaf
        (structureSheafRing X).property).unit.naturality
        (X := associatedPresheaf X α M) (Y := associatedPresheaf X α M')
        ((associatedPresheafFunctor X α).map (X := M) (Y := M') f)
    have sectionNaturality := congrArg
      (fun morphism : associatedPresheaf X α M ⟶
        (SheafOfModules.forget (structureSheafRing X) ⋙
          PresheafOfModules.restrictScalars (𝟙 (structureSheafRing X).obj)).obj
          ((associatedSheafFunctor.{u, u} X α).obj M') =>
        PresheafOfModules.Hom.app morphism sectionObj leftSection) unitNaturality
    exact congrArg
      (fun value : ((associatedSheafFunctor.{u, u} X α).obj M').val.obj sectionObj =>
        TensorProduct.tmul (X.presheaf.obj sectionObj) value
        (PresheafOfModules.Hom.app
          (Stacks.SheafOfModules.TensorSheafification.toSheafify X.presheaf
            (structureSheafRing X).property (associatedPresheaf X α N)) sectionObj rightSection))
      sectionNaturality
  exact (((CommSq.mk (associatedPresheafTensorIso_naturality_left X α f N)).map
    (Stacks.SheafOfModules.TensorSheafification.sheafify X.presheaf
      (structureSheafRing X).property)).vert_comp
    (hT.map (Stacks.SheafOfModules.TensorSheafification.sheafify X.presheaf
      (structureSheafRing X).property))).w

/-- In a monoidal category, whiskering on the left commutes with a tensor product of maps
compatible with a morphism. -/
public theorem whiskerLeft_comp_tensorHom_of_comp {C : Type*} [Category* C] [MonoidalCategory C]
    {A B B' A₁ B₁ B₁' : C} (g : B ⟶ B') (uA : A ⟶ A₁) (uB : B ⟶ B₁) (uB' : B' ⟶ B₁')
    (k : B₁ ⟶ B₁') (h : g ≫ uB' = uB ≫ k) :
    A ◁ g ≫ (uA ⊗ₘ uB') = (uA ⊗ₘ uB) ≫ A₁ ◁ k := by
  rw [MonoidalCategory.tensorHom_def', MonoidalCategory.tensorHom_def', ← Category.assoc,
    ← MonoidalCategory.whiskerLeft_comp, h, MonoidalCategory.whiskerLeft_comp, Category.assoc,
    Category.assoc, ← MonoidalCategory.whisker_exchange]

public theorem assocTensorIso_naturality_right (M : ModuleCat.{u} R) {N N' : ModuleCat.{u} R}
    (g : N ⟶ N') :
    letI : MonoidalCategory (PresheafOfModules.{u} (structureSheafRing X).obj) :=
      PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)
    (associatedSheafFunctor.{u, u} X α).map (X := M ⊗ N) (Y := M ⊗ N') (M ◁ g) ≫
        (associatedSheafTensorIso X α M N').hom =
      (associatedSheafTensorIso X α M N).hom ≫
        (Stacks.SheafOfModules.TensorSheafification.sheafify X.presheaf
          (structureSheafRing X).property).map
          (X := PresheafOfModules.tensorObj (O := X.presheaf)
            ((associatedSheafFunctor.{u, u} X α).obj M).val
            ((associatedSheafFunctor.{u, u} X α).obj N).val)
          (Y := PresheafOfModules.tensorObj (O := X.presheaf)
            ((associatedSheafFunctor.{u, u} X α).obj M).val
            ((associatedSheafFunctor.{u, u} X α).obj N').val)
          ((SheafOfModules.forget (structureSheafRing X) ⋙
              PresheafOfModules.restrictScalars (𝟙 (structureSheafRing X).obj)).obj
              ((associatedSheafFunctor.{u, u} X α).obj M) ◁
            (SheafOfModules.forget (structureSheafRing X) ⋙
              PresheafOfModules.restrictScalars (𝟙 (structureSheafRing X).obj)).map
            (X := (associatedSheafFunctor.{u, u} X α).obj N)
            (Y := (associatedSheafFunctor.{u, u} X α).obj N')
            ((associatedSheafFunctor.{u, u} X α).map (X := N) (Y := N') g)) := by
  let : MonoidalCategory (PresheafOfModules.{u} (structureSheafRing X).obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)
  have hT : CommSq
      (associatedPresheaf X α M ◁ (associatedPresheafFunctor X α).map (X := N) (Y := N') g)
      (Stacks.SheafOfModules.TensorSheafification.tensorUnitMap X.presheaf
        (structureSheafRing X).property (associatedPresheaf X α M) (associatedPresheaf X α N))
      (Stacks.SheafOfModules.TensorSheafification.tensorUnitMap X.presheaf
        (structureSheafRing X).property (associatedPresheaf X α M) (associatedPresheaf X α N'))
      ((SheafOfModules.forget (structureSheafRing X) ⋙
          PresheafOfModules.restrictScalars (𝟙 (structureSheafRing X).obj)).obj
          ((associatedSheafFunctor.{u, u} X α).obj M) ◁
        (SheafOfModules.forget (structureSheafRing X) ⋙
          PresheafOfModules.restrictScalars (𝟙 (structureSheafRing X).obj)).map
          (X := (associatedSheafFunctor.{u, u} X α).obj N)
          (Y := (associatedSheafFunctor.{u, u} X α).obj N')
          ((associatedSheafFunctor.{u, u} X α).map (X := N) (Y := N') g)) := by
    refine ⟨PresheafOfModules.hom_ext fun sectionObj =>
      ModuleCat.tensor_ext (R := X.presheaf.obj sectionObj)
        (M := (associatedPresheaf X α M).obj sectionObj)
        (N := (associatedPresheaf X α N).obj sectionObj) fun leftSection rightSection => ?_⟩
    have unitNaturality :=
      (Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction X.presheaf
        (structureSheafRing X).property).unit.naturality
        (X := associatedPresheaf X α N) (Y := associatedPresheaf X α N')
        ((associatedPresheafFunctor X α).map (X := N) (Y := N') g)
    have sectionNaturality := congrArg
      (fun morphism : associatedPresheaf X α N ⟶
        (SheafOfModules.forget (structureSheafRing X) ⋙
          PresheafOfModules.restrictScalars (𝟙 (structureSheafRing X).obj)).obj
          ((associatedSheafFunctor.{u, u} X α).obj N') =>
        PresheafOfModules.Hom.app morphism sectionObj rightSection) unitNaturality
    exact congrArg
      (fun value : ((associatedSheafFunctor.{u, u} X α).obj N').val.obj sectionObj =>
        TensorProduct.tmul (X.presheaf.obj sectionObj)
        (PresheafOfModules.Hom.app
          (Stacks.SheafOfModules.TensorSheafification.toSheafify X.presheaf
            (structureSheafRing X).property (associatedPresheaf X α M)) sectionObj leftSection)
        value)
      sectionNaturality
  exact (((CommSq.mk (associatedPresheafTensorIso_naturality_right X α M g)).map
    (Stacks.SheafOfModules.TensorSheafification.sheafify X.presheaf
      (structureSheafRing X).property)).vert_comp
    (hT.map (Stacks.SheafOfModules.TensorSheafification.sheafify X.presheaf
      (structureSheafRing X).property))).w

end Stacks.AssociatedSheaf

end
