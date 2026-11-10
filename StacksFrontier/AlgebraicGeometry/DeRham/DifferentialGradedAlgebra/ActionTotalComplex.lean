module

public import StacksFrontier.AlgebraicGeometry.DeRham.CupProduct.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafTensorAdditiveOnOpens
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedForgetColimits

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
  {𝒜 : _root_.SheafOfModules.DifferentialGradedAlgebra.{u, u} (ringSheaf A)}
  (M : _root_.SheafOfModules.DifferentialGradedModule.{u, u, u} 𝒜)

/-- The right action `M^n ⊗ 𝒜^i ⟶ M^{n+i}` on the presheaf tensor product. -/
noncomputable def dgActionPresheafMap (n i : ℤ) :
    PresheafOfModules.tensorObj (O := A.obj) (M.complex.X n).val (𝒜.complex.X i).val ⟶
      (PresheafOfModules.restrictScalars (𝟙 (ringSheaf A).obj)).obj (M.complex.X (n + i)).val :=
  PresheafOfModules.ofBilinear (M.mul n i)

/-- **The right action `M^n ⊗_A 𝒜^i ⟶ M^{n+i}`** of a sheaf of differential graded algebras on a
right differential graded module, on the tensor product of sheaves of modules. -/
noncomputable def dgActionComponent (n i : ℤ) :
    ((sheafTensor A).obj (M.complex.X n)).obj (𝒜.complex.X i) ⟶ M.complex.X (n + i) :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf A).obj)).symm
    (dgActionPresheafMap M n i)

/-- The action on a local pure tensor is the action of the module. -/
theorem dgActionComponent_unit_apply (n i : ℤ) (U : (Opens X.carrier)ᵒᵖ)
    (x : (M.complex.X n).val.obj U) (y : (𝒜.complex.X i).val.obj U) :
    (dgActionComponent M n i).val.app U
        (((PresheafOfModules.sheafificationAdjunction (R := ringSheaf A)
          (𝟙 (ringSheaf A).obj)).unit.app
          (PresheafOfModules.tensorObj (M.complex.X n).val (𝒜.complex.X i).val)).app U
            (x ⊗ₜ[A.obj.obj U] y)) =
      (M.mul n i).app U x y :=
  lift_unit_apply (Opens.grothendieckTopology X.carrier) (𝟙 (ringSheaf A).obj)
    (PresheafOfModules.tensorObj (O := A.obj) (M.complex.X n).val (𝒜.complex.X i).val)
    (M.complex.X (n + i)) (dgActionPresheafMap M n i) U (x ⊗ₜ[A.obj.obj U] y)

/-- Two morphisms out of a tensor product of sheaves of modules agree as soon as they agree on
the sheafification-unit images of local pure tensors. -/
theorem sheafTensor_hom_ext {P Q N : _root_.SheafOfModules.{u} (ringSheaf A)}
    {f g : ((sheafTensor A).obj P).obj Q ⟶ N}
    (h : ∀ (U : (Opens X.carrier)ᵒᵖ) (x : P.val.obj U) (y : Q.val.obj U),
      f.val.app U (((PresheafOfModules.sheafificationAdjunction (R := ringSheaf A)
          (𝟙 (ringSheaf A).obj)).unit.app (PresheafOfModules.tensorObj P.val Q.val)).app U
            (x ⊗ₜ[A.obj.obj U] y)) =
        g.val.app U (((PresheafOfModules.sheafificationAdjunction (R := ringSheaf A)
          (𝟙 (ringSheaf A).obj)).unit.app (PresheafOfModules.tensorObj P.val Q.val)).app U
            (x ⊗ₜ[A.obj.obj U] y))) : f = g := by
  refine (PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf A).obj)).injective ?_
  refine PresheafOfModules.hom_ext fun U => ModuleCat.MonoidalCategory.tensor_ext fun x y => ?_
  exact (sheafificationHomEquiv_apply _ U _).trans
    ((h U x y).trans (sheafificationHomEquiv_apply _ U _).symm)

/-- Evaluating a morphism of sheaves of modules on a fixed local section is additive in the
morphism. -/
private def homEvalAt {P N : _root_.SheafOfModules.{u} (ringSheaf A)}
    (U : (Opens X.carrier)ᵒᵖ) (x : P.val.obj U) : (P ⟶ N) →+ N.val.obj U where
  toFun f := f.val.app U x
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Reindexing a term of a complex along an equality of degrees, on a local section, is the
transport of `SheafOfModules.gradedCast`. -/
theorem XIsoOfEq_hom_val_app (K : CochainComplex (_root_.SheafOfModules.{u} (ringSheaf A)) ℤ)
    {p q : ℤ} (h : p = q) (U : (Opens X.carrier)ᵒᵖ) (x : (K.X p).val.obj U) :
    (K.XIsoOfEq h).hom.val.app U x =
      _root_.SheafOfModules.gradedCast (fun r ↦ (K.X r).val.obj U) h x := by
  subst h
  rfl

/-- **The signed Leibniz rule for the components of the action.** -/
theorem dgActionComponent_d (n i : ℤ) :
    dgActionComponent M n i ≫ M.complex.d (n + i) (n + i + 1) =
      ((sheafTensor A).map (M.complex.d n (n + 1))).app (𝒜.complex.X i) ≫
          dgActionComponent M (n + 1) i ≫
            (M.complex.XIsoOfEq (show n + 1 + i = n + i + 1 by omega)).hom +
        (Int.negOnePow n : ℤ) • (((sheafTensor A).obj (M.complex.X n)).map
          (𝒜.complex.d i (i + 1)) ≫ dgActionComponent M n (i + 1) ≫
            (M.complex.XIsoOfEq (show n + (i + 1) = n + i + 1 by omega)).hom) := by
  refine sheafTensor_hom_ext fun U x y => ?_
  change homEvalAt (N := M.complex.X (n + i + 1)) U _
      (dgActionComponent M n i ≫ M.complex.d (n + i) (n + i + 1)) =
    homEvalAt (P := ((sheafTensor A).obj (M.complex.X n)).obj (𝒜.complex.X i))
      (N := M.complex.X (n + i + 1)) U _
      (((sheafTensor A).map (M.complex.d n (n + 1))).app (𝒜.complex.X i) ≫
          dgActionComponent M (n + 1) i ≫
            (M.complex.XIsoOfEq (show n + 1 + i = n + i + 1 by omega)).hom +
        (Int.negOnePow n : ℤ) • (((sheafTensor A).obj (M.complex.X n)).map
          (𝒜.complex.d i (i + 1)) ≫ dgActionComponent M n (i + 1) ≫
            (M.complex.XIsoOfEq (show n + (i + 1) = n + i + 1 by omega)).hom))
  rw [map_add, map_zsmul]
  change (M.complex.d (n + i) (n + i + 1)).val.app U ((dgActionComponent M n i).val.app U _) =
    (M.complex.XIsoOfEq _).hom.val.app U ((dgActionComponent M (n + 1) i).val.app U
        ((((sheafTensor A).map (M.complex.d n (n + 1))).app (𝒜.complex.X i)).val.app U _)) +
      (Int.negOnePow n : ℤ) • (M.complex.XIsoOfEq _).hom.val.app U
        ((dgActionComponent M n (i + 1)).val.app U
          ((((sheafTensor A).obj (M.complex.X n)).map (𝒜.complex.d i (i + 1))).val.app U _))
  rw [tensorFunctor_map_unit_apply (A := A), tensorFunctor_obj_map_unit_apply (A := A),
    dgActionComponent_unit_apply, dgActionComponent_unit_apply, dgActionComponent_unit_apply,
    XIsoOfEq_hom_val_app, XIsoOfEq_hom_val_app]
  exact M.leibniz n i U x y

/-- The total complex `Tot(M ⊗_A 𝒜)` of a right differential graded module and the algebra. -/
noncomputable abbrev dgActionSource : CochainComplex (_root_.SheafOfModules.{u} (ringSheaf A)) ℤ :=
  HomologicalComplex.mapBifunctor M.complex 𝒜.complex (sheafTensor A) (ComplexShape.up ℤ)

/-- The degree-`k` component of the action: the descent of the components of total degree `k`. -/
noncomputable def dgActionDesc (k : ℤ) : (dgActionSource M).X k ⟶ M.complex.X k :=
  HomologicalComplex.mapBifunctorDesc (K₁ := M.complex) (K₂ := 𝒜.complex) (F := sheafTensor A)
    (c := ComplexShape.up ℤ) fun n i h =>
      dgActionComponent M n i ≫ (M.complex.XIsoOfEq (show n + i = k from h)).hom

/-- On the `(n, i)` summand of total degree `k`, the degree-`k` component of the action is the
action `M^n ⊗ 𝒜^i ⟶ M^{n+i}` followed by the identification `M^{n+i} ≅ M^k`. -/
@[reassoc (attr := simp)]
theorem ι_dgActionDesc (n i k : ℤ) (h : n + i = k) :
    HomologicalComplex.ιMapBifunctor M.complex 𝒜.complex (sheafTensor A) (ComplexShape.up ℤ)
        n i k h ≫ dgActionDesc M k =
      dgActionComponent M n i ≫ (M.complex.XIsoOfEq h).hom :=
  HomologicalComplex.ι_mapBifunctorDesc _ n i h

private theorem ι_d_dgActionDesc (n i : ℤ) :
    HomologicalComplex.ιMapBifunctor M.complex 𝒜.complex (sheafTensor A) (ComplexShape.up ℤ)
        n i (n + i) rfl ≫ ((dgActionSource M).d (n + i) (n + i + 1) ≫
          dgActionDesc M (n + i + 1)) =
      ((sheafTensor A).map (M.complex.d n (n + 1))).app (𝒜.complex.X i) ≫
          dgActionComponent M (n + 1) i ≫
            (M.complex.XIsoOfEq (show n + 1 + i = n + i + 1 by omega)).hom +
        (Int.negOnePow n : ℤ) • (((sheafTensor A).obj (M.complex.X n)).map
          (𝒜.complex.d i (i + 1)) ≫ dgActionComponent M n (i + 1) ≫
            (M.complex.XIsoOfEq (show n + (i + 1) = n + i + 1 by omega)).hom) := by
  have hπ₁ : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (n + 1, i) = n + i + 1 := show n + 1 + i = n + i + 1 by omega
  have hπ₂ : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (n, i + 1) = n + i + 1 := show n + (i + 1) = n + i + 1 by omega
  rw [HomologicalComplex.mapBifunctor.d_eq]
  simp only [Preadditive.add_comp, Preadditive.comp_add, Category.assoc,
    HomologicalComplex.mapBifunctor.ι_D₁_assoc, HomologicalComplex.mapBifunctor.ι_D₂_assoc,
    HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _
      (show (ComplexShape.up ℤ).Rel n (n + 1) from rfl) i (n + i + 1) hπ₁,
    HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ n
      (show (ComplexShape.up ℤ).Rel i (i + 1) from rfl) (n + i + 1) hπ₂,
    Linear.units_smul_comp, ι_dgActionDesc]
  have e₁ : ComplexShape.ε₁ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (n, i) =
    1 := rfl
  have e₂ : ComplexShape.ε₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (n, i) =
    n.negOnePow := rfl
  rw [e₁, e₂, one_smul, Units.smul_def]

/-- **The right action as a morphism of complexes** `Tot(M ⊗_A 𝒜) ⟶ M`: on the `(n, i)`
summand it is the action `M^n ⊗ 𝒜^i ⟶ M^{n+i}`, and the signed Leibniz rule of `M` is the
statement that this family commutes with the differentials. -/
noncomputable def dgAction : dgActionSource M ⟶ M.complex where
  f := dgActionDesc M
  comm' k k' hk := by
    obtain rfl : k + 1 = k' := hk
    refine HomologicalComplex.mapBifunctor.hom_ext fun n i hni => ?_
    obtain rfl : n + i = k := hni
    refine ((ι_dgActionDesc_assoc M n i (n + i) rfl _).trans ?_).trans
      (ι_d_dgActionDesc M n i).symm
    simp only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom]
    exact dgActionComponent_d M n i

/-- The degree-`k` component of `dgAction M` is `dgActionDesc M k`. -/
@[simp]
theorem dgAction_f (k : ℤ) : (dgAction M).f k = dgActionDesc M k := rfl

/-- A morphism of right differential graded modules commutes with the components of the action. -/
theorem dgActionComponent_naturality
    {M N : _root_.SheafOfModules.DifferentialGradedModule.{u, u, u} 𝒜}
    (f : M ⟶ N) (n i : ℤ) :
    ((sheafTensor A).map (f.toHomologicalComplex.f n)).app (𝒜.complex.X i) ≫
        dgActionComponent N n i =
      dgActionComponent M n i ≫ f.toHomologicalComplex.f (n + i) := by
  refine sheafTensor_hom_ext fun U x y => ?_
  change (dgActionComponent N n i).val.app U
      ((((sheafTensor A).map (f.toHomologicalComplex.f n)).app (𝒜.complex.X i)).val.app U _) =
    (f.toHomologicalComplex.f (n + i)).val.app U ((dgActionComponent M n i).val.app U _)
  rw [tensorFunctor_map_unit_apply (A := A), dgActionComponent_unit_apply,
    dgActionComponent_unit_apply]
  exact (f.map_mul n i U x y).symm

/-- **A morphism of right differential graded modules commutes with the action**:
`Tot(f ⊗ 1) ≫ act_N = act_M ≫ f`. -/
theorem dgAction_naturality {M N : _root_.SheafOfModules.DifferentialGradedModule.{u, u, u} 𝒜}
    (f : M ⟶ N) :
    HomologicalComplex.mapBifunctorMap f.toHomologicalComplex (𝟙 𝒜.complex) (sheafTensor A)
        (ComplexShape.up ℤ) ≫ dgAction N =
      dgAction M ≫ f.toHomologicalComplex := by
  refine HomologicalComplex.hom_ext _ _ fun k => ?_
  refine HomologicalComplex.mapBifunctor.hom_ext fun n i hni => ?_
  simp only [HomologicalComplex.comp_f, dgAction_f, HomologicalComplex.ι_mapBifunctorMap_assoc,
    HomologicalComplex.id_f, CategoryTheory.Functor.map_id, Category.id_comp, ι_dgActionDesc,
    ι_dgActionDesc_assoc]
  rw [← Category.assoc, dgActionComponent_naturality, Category.assoc,
    HomologicalComplex.XIsoOfEq_hom_naturality]

/-- **The action and the shift in the first factor.** Let `N` be a right differential graded
module whose underlying complex is `M[n]` and whose action is that of `M` read in the shifted
degree (as for the translate `M[n]` of Differential Graded Sheaves, Section 0FRY). Then the
action of `N` is the shift of the action of `M`, through the identification
`Tot(M[n] ⊗ 𝒜) ≅ Tot(M ⊗ 𝒜)[n]` of `CochainComplex.mapBifunctorShift₁Iso`, which carries no
sign. -/
theorem dgAction_shift (n : ℤ) (N : _root_.SheafOfModules.DifferentialGradedModule.{u, u, u} 𝒜)
    (hN : N.complex = M.complex⟦n⟧)
    (hmul : ∀ (p q : ℤ) (U : (Opens X.carrier)ᵒᵖ) (x : (N.complex.X p).val.obj U)
      (x' : (M.complex.X (p + n)).val.obj U) (y : (𝒜.complex.X q).val.obj U), HEq x x' →
        HEq ((N.mul p q).app U x y) ((M.mul (p + n) q).app U x' y)) :
    dgAction N =
      eqToHom (congrArg (fun K => HomologicalComplex.mapBifunctor K 𝒜.complex (sheafTensor A)
          (ComplexShape.up ℤ)) hN) ≫
        (CochainComplex.mapBifunctorShift₁Iso M.complex 𝒜.complex (sheafTensor A) n).hom ≫
          (dgAction M)⟦n⟧' ≫ eqToHom hN.symm := by
  obtain ⟨Nc, Nmul, h₁, h₂, h₃⟩ := N
  dsimp only at hN hmul ⊢
  subst hN
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  refine HomologicalComplex.hom_ext _ _ fun k => ?_
  refine HomologicalComplex.mapBifunctor.hom_ext fun p q hpq => ?_
  set N : _root_.SheafOfModules.DifferentialGradedModule.{u, u, u} 𝒜 :=
    ⟨M.complex⟦n⟧, Nmul, h₁, h₂, h₃⟩
  have hpq' : p + q = k := hpq
  have eR := CochainComplex.ι_mapBifunctorShift₁Iso_hom_f M.complex 𝒜.complex (sheafTensor A) n
    p q k hpq (p + n) (k + n) rfl rfl
  rw [dgAction_f, ι_dgActionDesc, HomologicalComplex.comp_f, ← Category.assoc, eR]
  simp only [CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom,
    Iso.refl_inv, Category.id_comp,
    Category.assoc, CochainComplex.shiftFunctor_map_f', dgAction_f, ι_dgActionDesc]
  have hid : ((sheafTensor A).map (𝟙 (M.complex.X (p + n)))).app (𝒜.complex.X q) = 𝟙 _ := by
    rw [CategoryTheory.Functor.map_id, NatTrans.id_app]
  refine Eq.trans ?_ (congrArg (· ≫ _) hid).symm
  refine Eq.trans ?_ (Category.id_comp _).symm
  refine sheafTensor_hom_ext fun U x y => ?_
  have e1 := dgActionComponent_unit_apply N p q U x y
  have e2 := dgActionComponent_unit_apply M (p + n) q U x y
  have hk : p + n + q = k + n := by omega
  have l2 := XIsoOfEq_hom_val_app M.complex hk U ((M.mul (p + n) q).app U x y)
  refine (congrArg (fun z => ((M.complex⟦n⟧).XIsoOfEq hpq).hom.val.app U z) e1).trans ?_
  refine (XIsoOfEq_hom_val_app (M.complex⟦n⟧) hpq U ((Nmul p q).app U x y)).trans ?_
  refine Eq.trans ?_
    ((congrArg (fun z => (M.complex.XIsoOfEq hk).hom.val.app U z) e2).trans l2).symm
  exact eq_of_heq ((_root_.SheafOfModules.gradedCast_heq _ _ _).trans
    ((hmul p q U x x y HEq.rfl).trans
      (_root_.SheafOfModules.gradedCast_heq (fun r ↦ (M.complex.X r).val.obj U) hk _).symm))

end AlgebraicGeometry.SheafOfModules
