module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackGradedAlgebra
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackUnitValue

/-!
# The unit of a pullback of a sheaf of graded algebras, through Tag 03LU

Let `(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi and `B` a sheaf of
graded `O_D`-algebras.  The pullback `f^*B` of
`Stacks.Sheaves.GradedAlgebraPullback.toposPullbackGradedAlgebra` has the module pullbacks `f^*B_n`
as homogeneous pieces, and its unit is the pure tensor `1 ⊗ 1` of the extension of scalars of the
inverse image.  This file proves that the unit `O_C ⟶ f^*B_0` is the pullback `f^*(1_B)` of the
unit `1_B : O_D ⟶ B_0`, read through the identification `O_C ≅ f^*O_D` of **Tag 03LU**
(`Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso`).  It is the unit companion of
`Stacks.Sheaves.GradedAlgebraPullback.pullbackTensorIso_hom_app_comp_mulSheaf`.

## Main results

* `Stacks.Sheaves.GradedAlgebraPullback.pullbackModulesObjUnitIso_inv_comp_oneHom`: the
  identification `f^*O_D ≅ O_C` followed by the unit of `f^*B` is `f^*(1_B)`.
* `Stacks.Sheaves.GradedAlgebraPullback.oneHom_toposPullbackGradedAlgebra`: **the unit of `f^*B`
  is `O_C ≅ f^*O_D ⟶ f^*B_0`.**

## Implementation notes

The identity is transposed along the adjunction of Stacks 03CZ of the extension of scalars along
`f♯`, where the transpose of the identification is the structure map
(`Stacks.Sheaves.RingedToposModules.fSharpAdjunction_homEquiv_pullbackModulesObjUnitIso_inv`) and
the transpose of an extension of scalars is the unit `x ↦ 1 ⊗ x`; both sides are then morphisms
out of the structure sheaf of `f⁻¹O_D`, compared on the unit section.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 0FQX](https://stacks.math.columbia.edu/tag/0FQX)
* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open AlgebraicGeometry
open Stacks.Sheaves.RingedToposModules Stacks.Sheaves.FinitePresentation
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.GradedAlgebraInverseImage Stacks.Sheaves.GradedAlgebraExtendScalars

namespace Stacks.Sheaves.GradedAlgebraPullback

universe w v u

variable {X Y : RingedTopos.{v, u, w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (f : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)
  (B : SheafOfModules.GradedAlgebra.{w, w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))

omit [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The inverse image of the unit `1_B : O_D ⟶ B_0` takes the unit section of `f⁻¹O_D` to the
unit of the inverse image `f⁻¹B` of the graded algebra. -/
theorem inverseImageModules_map_oneHom_val_app_one (U : X.Cᵒᵖ) :
    ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
        (SheafOfModules.GradedAlgebra.oneHom B)).val.app U
        (1 : (inverseImageRingSheaf f.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj.obj U) =
      (inverseImageGradedAlgebra f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
        B).one.eval U := by
  let : PreservesFiniteLimits f.toToposHom.inverseImage := f.toToposHom.preservesFiniteLimits
  have h1 : (1 : (inverseImageRingSheaf f.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj.obj U) =
      (transportSections X.J f.toToposHom.inverseImage U).map
        (ringOneHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) default :=
    (congrArg (fun t => (sectionsFunctor X.J U).map t
        (default :
          (transportSections X.J f.toToposHom.inverseImage U).obj (⊤_ (Sheaf Y.J (Type w)))))
      (ringOne_map_aux X.J f.toToposHom.inverseImage
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).symm
  have h2 : ringOneHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ≫
      (moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
        (SheafOfModules.GradedAlgebra.oneHom B) = oneSheafHom B := by
    refine Sheaf.hom_ext (NatTrans.ext (funext fun V => ?_))
    ext z
    exact (SheafOfModules.GradedAlgebra.oneHom_val_app B V 1).trans (one_smul _ _)
  rw [h1]
  change (transportSections X.J f.toToposHom.inverseImage U).map
      ((moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
        (SheafOfModules.GradedAlgebra.oneHom B))
      ((transportSections X.J f.toToposHom.inverseImage U).map
        (ringOneHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) default) =
    (transportSections X.J f.toToposHom.inverseImage U).map (oneSheafHom B) default
  exact ((transportSections X.J f.toToposHom.inverseImage U).map_comp_apply _ _ _).symm.trans
    (congrArg (fun t => (transportSections X.J f.toToposHom.inverseImage U).map t default) h2)

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- The transpose along Stacks 03CZ of the extension of scalars of the inverse image of the unit
`1_B` is that inverse image followed by the unit `x ↦ 1 ⊗ x` of the adjunction. -/
theorem fSharpAdjunction_homEquiv_map_inverseImageModules_map_oneHom :
    (fSharpAdjunction f).homEquiv
        ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
        ((extendScalars X.J (fSharpCommRing f)
          (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property).obj
          ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj
            (B.piece 0)))
        ((extendScalars X.J (fSharpCommRing f)
          (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property).map
          ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
            (SheafOfModules.GradedAlgebra.oneHom B))) =
      (inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
          (SheafOfModules.GradedAlgebra.oneHom B) ≫
        (fSharpAdjunction f).unit.app
          ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj
            (B.piece 0)) :=
  ((fSharpAdjunction f).homEquiv_unit _ _ _).trans ((fSharpAdjunction f).unit.naturality _).symm

/-- `Stacks.Sheaves.GradedAlgebraPullback.pullbackModulesObjUnitIso_inv_comp_oneHom` with the
pullback written as the extension of scalars of the inverse image. -/
theorem pullbackModulesObjUnitIso_inv_comp_oneHom_extendScalars :
    (pullbackModulesObjUnitIso f).inv ≫
        SheafOfModules.GradedAlgebra.oneHom (toposPullbackGradedAlgebra f B) =
      (extendScalars X.J (fSharpCommRing f)
          (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property).map
        ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
          (SheafOfModules.GradedAlgebra.oneHom B)) := by
  refine ((fSharpAdjunction f).homEquiv
    ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    ((toposPullbackGradedAlgebra f B).piece 0)).injective ?_
  refine ((fSharpAdjunction f).homEquiv_naturality_right _ _).trans ?_
  rw [fSharpAdjunction_homEquiv_pullbackModulesObjUnitIso_inv]
  refine Eq.trans ?_ (fSharpAdjunction_homEquiv_map_inverseImageModules_map_oneHom f B).symm
  refine (SheafOfModules.unitHomEquiv (R := inverseImageRingSheaf f.toToposHom
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) _).injective (Subtype.ext (funext fun U => ?_))
  change ((toposPullbackGradedAlgebra f B).oneHom).val.app U
      ((SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit f.fSharpInverseImage).val.app U
        (1 : (inverseImageRingSheaf f.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj.obj U)) =
    ((fSharpAdjunction f).unit.app
      ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj
        (B.piece 0))).val.app U
      (((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
        B.oneHom).val.app U (1 : (inverseImageRingSheaf f.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj.obj U))
  refine (congrArg (fun t => (ConcreteCategory.hom
      ((toposPullbackGradedAlgebra f B).oneHom.val.app U)) t)
    (SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit_val_app_one
      f.fSharpInverseImage U)).trans ?_
  refine ((SheafOfModules.GradedAlgebra.oneHom_val_app _ U 1).trans (one_smul _ _)).trans ?_
  refine Eq.trans ?_ (congrArg (fun t => (ConcreteCategory.hom
      (((fSharpAdjunction f).unit.app
        ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj
          (B.piece 0))).val.app U)) t)
    (inverseImageModules_map_oneHom_val_app_one f B U)).symm
  refine Eq.trans ?_ (extendRestrictScalarsAdjunction_unit_app_val_app_apply _ _ _ _ _ _ _).symm
  exact extendScalarsGradedAlgebra_one_eval _ _ _ _ _ U

/-- **The unit of the pullback of a sheaf of graded algebras is the pullback of the unit, read
through Tag 03LU**: the identification `f^*O_D ≅ O_C` followed by the unit `O_C ⟶ (f^*B)_0` is
`f^*(1_B) : f^*O_D ⟶ f^*B_0`. -/
theorem pullbackModulesObjUnitIso_inv_comp_oneHom :
    (pullbackModulesObjUnitIso f).inv ≫
        SheafOfModules.GradedAlgebra.oneHom (toposPullbackGradedAlgebra f B) =
      (f.pullbackModules).map (SheafOfModules.GradedAlgebra.oneHom B) :=
  pullbackModulesObjUnitIso_inv_comp_oneHom_extendScalars f B

/-- **The unit of the pullback of a sheaf of graded algebras is the pullback of the unit**, read
through the identification `O_C ≅ f^*O_D` of Tag 03LU. -/
theorem oneHom_toposPullbackGradedAlgebra :
    SheafOfModules.GradedAlgebra.oneHom (toposPullbackGradedAlgebra f B) =
      (pullbackModulesObjUnitIso f).hom ≫
        (f.pullbackModules).map (SheafOfModules.GradedAlgebra.oneHom B) :=
  (Iso.inv_comp_eq _).1 (pullbackModulesObjUnitIso_inv_comp_oneHom f B)

end Stacks.Sheaves.GradedAlgebraPullback

end
