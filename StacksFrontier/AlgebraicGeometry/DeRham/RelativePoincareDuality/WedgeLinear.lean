module

public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.RelativeHodgePairing
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PowerPresentationSequences

/-!
# Linearity of the wedge product over the global functions

Let `f : X ⟶ S` be a morphism of schemes and `g ∈ Γ(X, 𝒪_X)`. Multiplying the first factor of the
wedge product `Ω^a_{X/S} ⊗ Ω^b_{X/S} ⟶ Ω^{a+b}_{X/S}` by `g` is the same as multiplying its value
by `g`: the multiplication of the algebra of differential forms is `𝒪_X`-bilinear. The same holds
for the wedge product in `D(𝒪_X)` and for its shift.

## Main results

* `AlgebraicGeometry.Scheme.Hom.mulSheaf_smulHom_left`: the sheaf-level statement.
-/

@[expose] public noncomputable section

open scoped Stacks.StandardDerivedModel Stacks.Topology.SheafTensorAdditiveOnOpens
open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor canonicalDerivedTensorProduct)

universe u

namespace HomologicalComplex

variable {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]
  [Preadditive C₁] [Preadditive C₂] [Preadditive D]
  [HasZeroObject C₁] [HasZeroObject C₂] [HasZeroObject D]
  (F : C₁ ⥤ C₂ ⥤ D) [F.Additive] [∀ M : C₁, (F.obj M).Additive]

/-- **The identification `Tot(F(M[-a], N[-b])) ≅ F(M, N)[-a-b]` is natural in `M`.** -/
theorem mapBifunctorMap_single_comp_mapBifunctorSingleSingleIso_hom {M M' : C₁} (φ : M ⟶ M')
    (N : C₂) (a b : ℤ)
    [HasMapBifunctor ((single C₁ (ComplexShape.up ℤ) a).obj M)
      ((single C₂ (ComplexShape.up ℤ) b).obj N) F (ComplexShape.up ℤ)]
    [HasMapBifunctor ((single C₁ (ComplexShape.up ℤ) a).obj M')
      ((single C₂ (ComplexShape.up ℤ) b).obj N) F (ComplexShape.up ℤ)] :
    mapBifunctorMap ((single C₁ (ComplexShape.up ℤ) a).map φ)
        (𝟙 ((single C₂ (ComplexShape.up ℤ) b).obj N)) F (ComplexShape.up ℤ) ≫
      (mapBifunctorSingleSingleIso F M' N a b).hom =
    (mapBifunctorSingleSingleIso F M N a b).hom ≫
      (single D (ComplexShape.up ℤ) (a + b)).map ((F.map φ).app N) := by
  refine HomologicalComplex.to_single_hom_ext ?_
  refine mapBifunctor.hom_ext fun i j hij => ?_
  by_cases h : i = a ∧ j = b
  · obtain ⟨rfl, rfl⟩ := h
    simp only [HomologicalComplex.comp_f, ι_mapBifunctorMap_assoc,
      ι_mapBifunctorSingleSingleIso_hom_f, ι_mapBifunctorSingleSingleIso_hom_f_assoc,
      HomologicalComplex.single_map_f_self, HomologicalComplex.id_f, Functor.map_id,
      Category.comp_id, Category.assoc, Iso.inv_hom_id_assoc]
    simp only [CategoryTheory.Functor.map_id, Category.id_comp]
    rw [← NatTrans.comp_app_assoc, ← Functor.map_comp, Category.assoc, Category.assoc,
      Iso.inv_hom_id, Category.comp_id, Functor.map_comp, NatTrans.comp_app_assoc,
      ← (F.map φ).naturality_assoc]
  · exact (isZero_obj_obj_single_obj_X_X F M N a b i j (not_and_or.mp h)).eq_of_src _ _

end HomologicalComplex

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **Multiplication by a global function on the first factor of the wedge product**:
`(g ω) ∧ η = g (ω ∧ η)`. -/
theorem mulSheaf_smulHom_left (g : Γ(X, ⊤)) (a b : ℤ) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).map
        (Stacks.Cohomology.InvertibleDerived.smulHom (X := X.toRingedSpace) g
          (relativeDifferentialForms f a))).app (relativeDifferentialForms f b) ≫
      (relativeDifferentialFormsAlgebra f).mulSheaf a b =
    (relativeDifferentialFormsAlgebra f).mulSheaf a b ≫
      Stacks.Cohomology.InvertibleDerived.smulHom (X := X.toRingedSpace) g
        (relativeDifferentialForms f (a + b)) := by
  refine PresheafOfModules.tensorSheaf_hom_ext (J := Opens.grothendieckTopology X)
    (Osharp := X.sheaf) (F := relativeDifferentialForms f a) (G := relativeDifferentialForms f b)
    (Q := relativeDifferentialForms f (a + b)) fun U x y => ?_
  have h := Stacks.TensorSheafWorld.tensorSheafBifunctor_map_val_app_tensorSheafUnit
    (Osharp := X.sheaf) (F := relativeDifferentialForms f a) (G := relativeDifferentialForms f b)
    (Stacks.Cohomology.InvertibleDerived.smulHom (X := X.toRingedSpace) g
      (relativeDifferentialForms f a)) (𝟙 (relativeDifferentialForms f b)) U x y
  have e : ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).map
        (Stacks.Cohomology.InvertibleDerived.smulHom (X := X.toRingedSpace) g
          (relativeDifferentialForms f a))).app (relativeDifferentialForms f b) =
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).map
        (Stacks.Cohomology.InvertibleDerived.smulHom (X := X.toRingedSpace) g
          (relativeDifferentialForms f a))).app (relativeDifferentialForms f b) ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj
          (relativeDifferentialForms f a)).map (𝟙 (relativeDifferentialForms f b)) :=
    (Category.comp_id _).symm.trans (congrArg (fun k => _ ≫ k)
      (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj
        (relativeDifferentialForms f a)).map_id (relativeDifferentialForms f b)).symm)
  refine (congrArg (fun z => ((relativeDifferentialFormsAlgebra f).mulSheaf a b).val.app U z)
      ((congrArg (fun k => k.val.app U ((PresheafOfModules.tensorSheafUnit
        (relativeDifferentialForms f a) (relativeDifferentialForms f b)).app U (x ⊗ₜ y))) e).trans
        h)).trans ?_
  refine ((SheafOfModules.GradedAlgebra.mulSheaf_unit _ a b U _ _).trans ?_).trans
    (congrArg (fun w => (Stacks.Cohomology.InvertibleDerived.smulHom (X := X.toRingedSpace) g
      (relativeDifferentialForms f (a + b))).val.app U w)
      (SheafOfModules.GradedAlgebra.mulSheaf_unit _ a b U x y)).symm
  exact ((relativeDifferentialFormsAlgebra f).mul a b).map_smul_left U _ x y

/-- Multiplication by `g ∈ Γ(X, 𝒪_X)` on `Ω^a_{X/S}` placed in degree zero. -/
abbrev formsInDegreeZeroSMul (g : Γ(X, ⊤)) (a : ℤ) :
    formsInDegreeZero f a ⟶ formsInDegreeZero f a :=
  DerivedCategory.Q.map ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).map
    (Stacks.Cohomology.InvertibleDerived.smulHom (X := X.toRingedSpace) g
      (relativeDifferentialForms f a)))

/-- **The wedge product in `D(𝒪_X)` is linear over `Γ(X, 𝒪_X)` in its first factor.** -/
theorem formsDerivedWedge_smul_left (g : Γ(X, ⊤)) (a b : ℤ) :
    ((derivedTensorProductFunctor X.sheaf).map (f.formsInDegreeZeroSMul g a)).app
        (formsInDegreeZero f b) ≫ formsDerivedWedge f a b =
      formsDerivedWedge f a b ≫ f.formsInDegreeZeroSMul g (a + b) := by
  have key := (canonicalDerivedTensorProduct X.sheaf).toTensor_naturality
    ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).map
      (Stacks.Cohomology.InvertibleDerived.smulHom (X := X.toRingedSpace) g
        (relativeDifferentialForms f a)))
    (𝟙 ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj
      (relativeDifferentialForms f b)))
  have e1 : ((canonicalDerivedTensorProduct X.sheaf).tensor.obj (formsInDegreeZero f a)).map
      (DerivedCategory.Q.map (𝟙 ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj
        (relativeDifferentialForms f b)))) = 𝟙 _ :=
    (congrArg _ (DerivedCategory.Q.map_id _)).trans
      (((canonicalDerivedTensorProduct X.sheaf).tensor.obj (formsInDegreeZero f a)).map_id _)
  have key' := (congrArg (fun k => _ ≫ k ≫ (canonicalDerivedTensorProduct X.sheaf).toTensor _ _)
    e1.symm).trans key
  have key'' := ((congrArg (fun k => _ ≫ k) (Category.id_comp _).symm).trans key')
  refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) key'').trans
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ((DerivedCategory.Q.map_comp _ _).symm.trans
      ((congrArg DerivedCategory.Q.map ?_).trans (DerivedCategory.Q.map_comp _ _)))).trans
      (Category.assoc _ _ _).symm)))
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _)
    (HomologicalComplex.mapBifunctorMap_single_comp_mapBifunctorSingleSingleIso_hom
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf) _ _ 0 0)).trans
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
      (((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) (0 + 0)).map_comp _ _).symm.trans
        ((congrArg _ (mulSheaf_smulHom_left f g a b)).trans
          ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) (0 + 0)).map_comp _ _)))).trans
      (Category.assoc _ _ _).symm)))

/-- **The shifted wedge product `Ω^a ⊗^L Ω^b[n] ⟶ Ω^c[n]` is linear over `Γ(X, 𝒪_X)` in its first
factor**: the commutation of the derived tensor product with the shift is natural in the first
variable ([Stacks, Tag 06YU]), and the unshifted wedge product is linear. -/
theorem formsDerivedWedgeShift_smul_left (g : Γ(X, ⊤)) (n a b c : ℤ) (h : a + b = c) :
    ((derivedTensorProductFunctor X.sheaf).map (f.formsInDegreeZeroSMul g a)).app
        ((formsInDegreeZero f b)⟦n⟧) ≫ formsDerivedWedgeShift f n a b c h =
      formsDerivedWedgeShift f n a b c h ≫ (f.formsInDegreeZeroSMul g c)⟦n⟧' := by
  subst h
  let := (canonicalDerivedTensorProduct X.sheaf).commShift_right (formsInDegreeZero f a)
  have := (canonicalDerivedTensorProduct X.sheaf).commShift₂.commShift_map
    (f.formsInDegreeZeroSMul g a)
  have hc := NatTrans.shift_app_comm
    ((derivedTensorProductFunctor X.sheaf).map (f.formsInDegreeZeroSMul g a)) n
    (formsInDegreeZero f b)
  have hinner : ((derivedTensorProductFunctor X.sheaf).map (f.formsInDegreeZeroSMul g a)).app
        (formsInDegreeZero f b) ≫ formsDerivedWedge f a b ≫ eqToHom rfl =
      (formsDerivedWedge f a b ≫ eqToHom rfl) ≫ f.formsInDegreeZeroSMul g (a + b) :=
    (congrArg (_ ≫ ·) (Category.comp_id (formsDerivedWedge f a b))).trans
      ((formsDerivedWedge_smul_left f g a b).trans
        (congrArg (· ≫ _) (Category.comp_id (formsDerivedWedge f a b)).symm))
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hc.symm).trans
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ((Functor.map_comp _ _ _).symm.trans
      ((congrArg _ hinner).trans (Functor.map_comp _ _ _)))).trans (Category.assoc _ _ _).symm)))

end AlgebraicGeometry.Scheme.Hom

end
