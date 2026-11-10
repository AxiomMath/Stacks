module

public import StacksFrontier.AlgebraicGeometry.DeRham.DifferentialGradedAlgebra.ActionTotalComplex
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.UnitLeftFactorCollapse
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedUnitAlgebraHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedConeIdentity
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomFilteredColimit
public import StacksFrontier.Algebra.Homology.MapBifunctorNatIso

@[expose] public section

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

open CategoryTheory Opposite TopologicalSpace
open scoped TensorProduct
open scoped Stacks.Topology.SheafTensorAdditiveOnOpens
open Stacks.SheafOfModules.Tensor (ringSheaf sheafTensor)

universe u

namespace AlgebraicGeometry.SheafOfModules

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier}
  (𝒜 : _root_.SheafOfModules.DifferentialGradedAlgebra.{u, u} (ringSheaf A))

/-- The unit `A[0] ⟶ 𝒜` of a sheaf of differential graded algebras, `r ↦ r · 1` in degree
zero, as a morphism of complexes out of the structure sheaf complex. -/
noncomputable def dgUnitComplexHom :
    AlgebraicGeometry.RingedSite.structureSheafComplex (Stacks.SheafOfModules.opensRingedSite A) ⟶
      𝒜.complex :=
  _root_.SheafOfModules.DifferentialGradedAlgebra.unitAlgebraComplexHom
    (𝒜 : _root_.SheafOfModules.DifferentialGradedAlgebra.{u, u}
      (CategoryTheory.Sheaf.toRingCat (Opens.grothendieckTopology X.carrier) A))

/-- **The unit acts trivially**: the action of `𝒜` on itself, precomposed with the unit
`A[0] ⟶ 𝒜` in the first factor, is the left unitor `Tot(A[0] ⊗_A 𝒜) ≅ 𝒜`. -/
theorem dgAction_regular_unit :
    HomologicalComplex.mapBifunctorMap (dgUnitComplexHom 𝒜) (𝟙 𝒜.complex) (sheafTensor A)
        (ComplexShape.up ℤ) ≫
        dgAction (_root_.SheafOfModules.DifferentialGradedModule.regularModule 𝒜) =
      (AlgebraicGeometry.RingedSite.structureSheafComplexTensorLeftIso
        (Stacks.SheafOfModules.opensRingedSite A) 𝒜.complex).hom := by
  refine HomologicalComplex.hom_ext _ _ fun k => ?_
  refine HomologicalComplex.mapBifunctor.hom_ext fun p q hpq => ?_
  by_cases hp : p = 0
  · subst hp
    obtain rfl : q = k := by simpa using hpq
    let R := _root_.SheafOfModules.DifferentialGradedModule.regularModule 𝒜
    have e1 := HomologicalComplex.ι_mapBifunctorMap (dgUnitComplexHom 𝒜) (𝟙 𝒜.complex)
      (sheafTensor A) (ComplexShape.up ℤ) 0 q q hpq
    have e2 := ι_dgActionDesc R 0 q q hpq
    have e3 : ((sheafTensor A).obj (𝒜.complex.X 0)).map
        ((𝟙 𝒜.complex : 𝒜.complex ⟶ 𝒜.complex).f q) =
        𝟙 _ := ((sheafTensor A).obj (𝒜.complex.X 0)).map_id _
    have hL : HomologicalComplex.ιMapBifunctor _ 𝒜.complex (sheafTensor A) (ComplexShape.up ℤ)
          0 q q hpq ≫ (HomologicalComplex.mapBifunctorMap (dgUnitComplexHom 𝒜) (𝟙 𝒜.complex)
            (sheafTensor A) (ComplexShape.up ℤ) ≫ dgAction R).f q =
        ((sheafTensor A).map ((dgUnitComplexHom 𝒜).f 0)).app (𝒜.complex.X q) ≫
          dgActionComponent R 0 q ≫ (𝒜.complex.XIsoOfEq hpq).hom := by
      refine (Category.assoc _ _ _).symm.trans ?_
      refine (congrArg (· ≫ dgActionDesc R q) e1).trans ?_
      refine (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ?_)
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg (· ≫ _) e3).trans ((Category.id_comp _).trans e2)
    rw [hL]
    refine sheafTensor_hom_ext fun U x y => ?_
    have hR := AlgebraicGeometry.RingedSite.leftUnitor_hom_f_val_app
      (Stacks.SheafOfModules.opensRingedSite A) 𝒜.complex q U.unop x y
    refine Eq.trans ?_ hR.symm
    change (𝒜.complex.XIsoOfEq hpq).hom.val.app U ((dgActionComponent R 0 q).val.app U
        ((((sheafTensor A).map ((dgUnitComplexHom 𝒜).f 0)).app (𝒜.complex.X q)).val.app U _)) = _
    rw [tensorFunctor_map_unit_apply (A := A)]
    refine (congrArg (fun z => (𝒜.complex.XIsoOfEq hpq).hom.val.app U z)
      (dgActionComponent_unit_apply R 0 q U (((dgUnitComplexHom 𝒜).f 0).val.app U x) y)).trans ?_
    refine (XIsoOfEq_hom_val_app 𝒜.complex hpq U _).trans ?_
    let r : (ringSheaf A).obj.obj U := x
    have hu : ((dgUnitComplexHom 𝒜).f 0).val.app U x = r • 𝒜.one.eval U := rfl
    rw [hu]
    have hs : (R.mul 0 q).app U (r • 𝒜.one.eval U) y = r • (R.mul 0 q).app U (𝒜.one.eval U) y :=
      (R.mul 0 q).map_smul_left U r _ y
    rw [hs]
    have h1 : _root_.SheafOfModules.gradedCast (fun r ↦ (𝒜.complex.X r).val.obj U) hpq
        ((R.mul 0 q).app U (𝒜.one.eval U) y) = y :=
      eq_of_heq ((_root_.SheafOfModules.gradedCast_heq _ hpq _).trans (𝒜.one_mul q U y))
    have hc : ∀ {a b : ℤ} (h : a = b) (z : (𝒜.complex.X a).val.obj U),
        _root_.SheafOfModules.gradedCast (fun r ↦ (𝒜.complex.X r).val.obj U) h (r • z) =
          r • _root_.SheafOfModules.gradedCast (fun r ↦ (𝒜.complex.X r).val.obj U) h z := by
      intro a b h z
      subst h
      rfl
    exact (hc hpq _).trans (congrArg (r • ·) h1)
  · refine Limits.IsZero.eq_of_src ?_ _ _
    exact ((sheafTensor A).map_isZero
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 _ p hp)).obj _

/-- **A morphism out of the regular module is right multiplication by its value at the unit**:
for a morphism `x : 𝒜 ⟶ N` of right differential graded `𝒜`-modules, the underlying morphism of
complexes is `𝒜 ≅ Tot(A[0] ⊗_A 𝒜) ⟶ Tot(N ⊗_A 𝒜) ⟶ N`, the unit followed by `x` in the first
factor, then the action of `𝒜` on `N`. -/
theorem dgAction_regularHom_eq {N : _root_.SheafOfModules.DifferentialGradedModule.{u, u, u} 𝒜}
    (x : _root_.SheafOfModules.DifferentialGradedModule.regularModule 𝒜 ⟶ N) :
    x.toHomologicalComplex =
      (AlgebraicGeometry.RingedSite.structureSheafComplexTensorLeftIso
          (Stacks.SheafOfModules.opensRingedSite A) 𝒜.complex).inv ≫
        HomologicalComplex.mapBifunctorMap (dgUnitComplexHom 𝒜 ≫ x.toHomologicalComplex)
          (𝟙 𝒜.complex) (sheafTensor.{u, u, u, u, u} A) (ComplexShape.up ℤ) ≫ dgAction N := by
  have h₁ : HomologicalComplex.mapBifunctorMap (dgUnitComplexHom 𝒜 ≫ x.toHomologicalComplex)
        (𝟙 𝒜.complex) (sheafTensor.{u, u, u, u, u} A) (ComplexShape.up ℤ) =
      HomologicalComplex.mapBifunctorMap (dgUnitComplexHom 𝒜) (𝟙 𝒜.complex)
          (sheafTensor.{u, u, u, u, u} A) (ComplexShape.up ℤ) ≫
        HomologicalComplex.mapBifunctorMap x.toHomologicalComplex (𝟙 𝒜.complex)
          (sheafTensor.{u, u, u, u, u} A) (ComplexShape.up ℤ) :=
    ((HomologicalComplex.mapBifunctorMap_comp (sheafTensor.{u, u, u, u, u} A) (ComplexShape.up ℤ)
      (dgUnitComplexHom 𝒜) (𝟙 𝒜.complex) x.toHomologicalComplex (𝟙 𝒜.complex)).trans
        (congrArg (HomologicalComplex.mapBifunctorMap _ · (sheafTensor.{u, u, u, u, u} A)
            (ComplexShape.up ℤ))
          (Category.comp_id _))).symm
  have h₂ := dgAction_naturality x
  have h₃ := dgAction_regular_unit 𝒜
  rw [h₁]
  refine Eq.trans ?_ (congrArg (_ ≫ ·) (Category.assoc _ _ _).symm)
  refine Eq.trans ?_ (congrArg (fun t => _ ≫ _ ≫ t) h₂.symm)
  refine Eq.trans ?_ (congrArg (_ ≫ ·) (Category.assoc _ _ _))
  refine Eq.trans ?_ (congrArg (fun t => _ ≫ t ≫ x.toHomologicalComplex) h₃.symm)
  exact (Iso.inv_hom_id_assoc _ _).symm

end AlgebraicGeometry.SheafOfModules
