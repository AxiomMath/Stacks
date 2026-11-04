module

public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.FreeDirectImage
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorCoherence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorLeftUnitorSections

/-!
# The left unit constraint of the twist commutes with base change

For a morphism of schemes `f : X ⟶ Y` and an `𝒪_Y`-module `A`, the pullback of the left unit
constraint `𝒪_Y ⊗ A ≅ A` is the left unit constraint of `f^*A`, read through the comparison
`f^*(𝒪_Y ⊗ A) ≅ f^*𝒪_Y ⊗ f^*A` of Stacks 01CD and `f^*𝒪_Y ≅ 𝒪_X`. This is
`Stacks.PullbackTensorCoherence.pullbackTensorComparison_leftUnitor`, stated for the
monoidal structure `Stacks.PullbackGradedAlgebra.monoidalCategory`, transported to the
sheaf-tensor spelling the twist `AlgebraicGeometry.ProjectiveQuot.twist` is written in. Applied
to `𝒪(d)` on `ℙⁿ_T` it is the compatibility of `𝒪 ⊗ 𝒪(d) ≅ 𝒪(d)` with the base change
`ℙⁿ_{T'} ⟶ ℙⁿ_T`, used for the free frame of `π_*(𝒪^{⊕ r}(m))` in the proof of Stacks 0DPA.

## Main results

* `AlgebraicGeometry.ProjectiveQuot.pullback_map_tensorLeftUnitor_hom`.
* `AlgebraicGeometry.ProjectiveQuot.tensorLeftUnitor_hom_naturality`.
* `AlgebraicGeometry.ProjectiveQuot.pullback_map_tensorLeftUnitor_hom_twistingSheaf`.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 0DPA](https://stacks.math.columbia.edu/tag/0DPA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.ProjectiveQuot

section
attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

/-- The left unitor of `Stacks.PullbackGradedAlgebra.monoidalCategory` is
`AlgebraicGeometry.Scheme.Modules.tensorLeftUnitor`: both send `r ⊗ b` to `r • b`. -/
theorem leftUnitor_hom_eq_tensorLeftUnitor_hom {Y : Scheme.{u}} (A : Y.Modules) :
    (MonoidalCategoryStruct.leftUnitor
      (C := SheafOfModules (Stacks.RingedSpace.structureRingSheaf Y.toSheafedSpace)) A).hom =
      (Scheme.Modules.tensorLeftUnitor Y A).hom := by
  refine Stacks.PullbackTensorCoherence.tensor_hom_ext fun U r b => ?_
  exact (Stacks.PullbackTensorCoherence.leftUnitor_hom_tmul U r b).trans
    (Stacks.SheafOfModules.tensorProductLeftUnitor_hom_val_app_tmul _ _ A U r b).symm

/-- The sheafification of `PresheafOfModules.tensorHom u v` acts on a local pure tensor
factorwise. -/
private theorem sheafification_map_tensorHom_tmul {X : Scheme.{u}} {A A' B B' : X.Modules}
    (u : A ⟶ A') (v : B ⟶ B') (U : (TopologicalSpace.Opens X)ᵒᵖ) (a : A.val.obj U)
    (b : B.val.obj U) :
    ((PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).map
        (PresheafOfModules.tensorHom u.val v.val)).val.app U
      (Stacks.PullbackTensorCoherence.tmul X.toSheafedSpace A B U a b) =
      Stacks.PullbackTensorCoherence.tmul X.toSheafedSpace A' B' U (u.val.app U a)
        (v.val.app U b) :=
  (PresheafOfModules.unit_naturality_apply (α := 𝟙 X.ringCatSheaf.obj)
      (PresheafOfModules.tensorHom u.val v.val) U (a ⊗ₜ b)).trans
    (congrArg ((PresheafOfModules.tensorSheafUnit A' B').app U)
      (PresheafOfModules.tensorHom_tmul u.val v.val U a b))

/-- Right whiskering in `Stacks.PullbackGradedAlgebra.monoidalCategory` is the sheaf tensor
product applied to a morphism in the first variable. -/
theorem whiskerRight_eq_sheafTensor_map_app {X : Scheme.{u}} {A B : X.Modules} (u : A ⟶ B)
    (M : X.Modules) :
    MonoidalCategoryStruct.whiskerRight
      (C := SheafOfModules (Stacks.RingedSpace.structureRingSheaf X.toSheafedSpace)) u M =
      ((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨X.toSheafedSpace.presheaf, X.toSheafedSpace.IsSheaf⟩).map u).app M := by
  refine Stacks.PullbackTensorCoherence.tensor_hom_ext fun U a b => ?_
  exact (Stacks.PullbackTensorCoherence.whiskerRight_tmul u U a b).trans
    (sheafification_map_tensorHom_tmul u (𝟙 M) U a b).symm

/-- **The pullback of the left unit constraint** is the left unit constraint of the pullback,
read through the comparison of Stacks 01CD and `f^*𝒪_Y ≅ 𝒪_X`. -/
theorem pullback_map_tensorLeftUnitor_hom {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Y.Modules) :
    (Scheme.Modules.pullback f).map (Scheme.Modules.tensorLeftUnitor Y A).hom =
      (Stacks.RingedSpace.comparisonBifunctorIso f.toLRSHom.toShHom).hom.app
          (SheafOfModules.unit Y.ringCatSheaf, A) ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨X.toSheafedSpace.presheaf, X.toSheafedSpace.IsSheaf⟩).map
            (Scheme.Modules.pullbackUnitIso f).hom).app ((Scheme.Modules.pullback f).obj A) ≫
        (Scheme.Modules.tensorLeftUnitor X ((Scheme.Modules.pullback f).obj A)).hom :=
  (congrArg (Scheme.Modules.pullback f).map (leftUnitor_hom_eq_tensorLeftUnitor_hom A).symm).trans
    ((Stacks.PullbackTensorCoherence.pullbackTensorComparison_leftUnitor
        f.toLRSHom.toShHom A).trans
      (congrArg₂ (fun x y => (Stacks.RingedSpace.comparisonBifunctorIso f.toLRSHom.toShHom).hom.app
          (SheafOfModules.unit Y.ringCatSheaf, A) ≫ x ≫ y)
        (whiskerRight_eq_sheafTensor_map_app (Scheme.Modules.pullbackUnitIso f).hom
          ((Scheme.Modules.pullback f).obj A))
        (leftUnitor_hom_eq_tensorLeftUnitor_hom ((Scheme.Modules.pullback f).obj A))))

/-- Left whiskering in `Stacks.PullbackGradedAlgebra.monoidalCategory` is the sheaf tensor
product applied to a morphism in the second variable. -/
theorem whiskerLeft_eq_sheafTensor_obj_map {X : Scheme.{u}} (M : X.Modules) {A B : X.Modules}
    (v : A ⟶ B) :
    MonoidalCategoryStruct.whiskerLeft
      (C := SheafOfModules (Stacks.RingedSpace.structureRingSheaf X.toSheafedSpace)) M v =
      ((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨X.toSheafedSpace.presheaf, X.toSheafedSpace.IsSheaf⟩).obj M).map v := by
  refine Stacks.PullbackTensorCoherence.tensor_hom_ext fun U a b => ?_
  exact (Stacks.PullbackTensorCoherence.whiskerLeft_tmul v U a b).trans
    (sheafification_map_tensorHom_tmul (𝟙 M) v U a b).symm

/-- **Naturality of the left unit constraint** `𝒪_X ⊗ M ≅ M` in `M`. -/
theorem tensorLeftUnitor_hom_naturality {X : Scheme.{u}} {M N : X.Modules} (v : M ⟶ N) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨X.toSheafedSpace.presheaf, X.toSheafedSpace.IsSheaf⟩).obj
        (SheafOfModules.unit X.ringCatSheaf)).map v ≫ (Scheme.Modules.tensorLeftUnitor X N).hom =
      (Scheme.Modules.tensorLeftUnitor X M).hom ≫ v :=
  (congrArg₂ (· ≫ ·) (whiskerLeft_eq_sheafTensor_obj_map _ v).symm
      (leftUnitor_hom_eq_tensorLeftUnitor_hom N).symm).trans
    ((MonoidalCategory.leftUnitor_naturality
        (C := SheafOfModules (Stacks.RingedSpace.structureRingSheaf X.toSheafedSpace)) v).trans
      (congrArg (· ≫ v) (leftUnitor_hom_eq_tensorLeftUnitor_hom M)))
end

variable {n : ℕ}

/-- **The left unit constraint `𝒪 ⊗ 𝒪(d) ≅ 𝒪(d)` commutes with base change**
`ℙⁿ_{T'} ⟶ ℙⁿ_T`, read through the base-change isomorphisms of the twist, of `𝒪(d)` and of the
structure sheaf. -/
theorem pullback_map_tensorLeftUnitor_hom_twistingSheaf {T' T : Scheme.{u}} (g : T' ⟶ T)
    (d : ℤ) :
    (Scheme.Modules.pullback (projectiveSpaceOverMap n g)).map
        (Scheme.Modules.tensorLeftUnitor _ (twistingSheaf n T d)).hom ≫
        (twistingSheafPullbackIso n g d).hom =
      (twistPullbackIso g d (Scheme.unitModule (projectiveSpaceOver n T))).inv ≫
        twistMap d (Scheme.Modules.pullbackUnitIso (projectiveSpaceOverMap n g)).hom ≫
        (Scheme.Modules.tensorLeftUnitor _ (twistingSheaf n T' d)).hom := by
  set h := projectiveSpaceOverMap n g
  set H := Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
    ⟨(projectiveSpaceOver n T').toSheafedSpace.presheaf,
      (projectiveSpaceOver n T').toSheafedSpace.IsSheaf⟩
  set v := (twistingSheafPullbackIso n g d).hom
  set w := (Scheme.Modules.pullbackUnitIso h).hom
  have key : (H.map w).app ((Scheme.Modules.pullback h).obj (twistingSheaf n T d)) ≫
        (Scheme.Modules.tensorLeftUnitor _
          ((Scheme.Modules.pullback h).obj (twistingSheaf n T d))).hom ≫ v =
      ((H.map (𝟙 _)).app _ ≫ (H.obj _).map v) ≫
        ((H.map w).app (twistingSheaf n T' d) ≫ (H.obj _).map (𝟙 _)) ≫
        (Scheme.Modules.tensorLeftUnitor _ (twistingSheaf n T' d)).hom := by
    have e1 : (H.map (𝟙 ((Scheme.Modules.pullback h).obj
        (Scheme.unitModule (projectiveSpaceOver n T))))).app
          ((Scheme.Modules.pullback h).obj (twistingSheaf n T d)) = 𝟙 _ := by
      have hm := H.map_id ((Scheme.Modules.pullback h).obj
        (Scheme.unitModule (projectiveSpaceOver n T)))
      exact congrArg (fun φ => φ.app ((Scheme.Modules.pullback h).obj (twistingSheaf n T d))) hm
    have e2 : (H.obj (Scheme.unitModule (projectiveSpaceOver n T'))).map
        (𝟙 (twistingSheaf n T' d)) = 𝟙 _ :=
      (H.obj (Scheme.unitModule (projectiveSpaceOver n T'))).map_id (twistingSheaf n T' d)
    have nat := (H.map w).naturality v
    have nl := tensorLeftUnitor_hom_naturality v
    exact (congrArg (_ ≫ ·) nl.symm).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ _) nat.symm).trans ((Category.assoc _ _ _).trans
        (congrArg₂ (· ≫ ·) ((Category.id_comp _).symm.trans (congrArg (· ≫ _) e1.symm))
          (congrArg (· ≫ _) ((Category.comp_id _).symm.trans (congrArg (_ ≫ ·) e2.symm)))))))
  exact (congrArg (· ≫ v) (pullback_map_tensorLeftUnitor_hom h (twistingSheaf n T d))).trans
    ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans key)))

end AlgebraicGeometry.ProjectiveQuot

end
