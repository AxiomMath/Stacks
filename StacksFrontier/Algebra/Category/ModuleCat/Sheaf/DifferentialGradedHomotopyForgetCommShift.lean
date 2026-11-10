module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedForgetConnecting

/-!
# Forgetting the action `K(Mod(A, d)) ⥤ D(O)` commutes with the translations

Let `X` be a ringed site and `(A, d)` a sheaf of differential graded algebras on it. Forgetting the
action of `A` and localizing gives the functor
`SheafOfModules.DifferentialGradedModule.homotopyForget : K(Mod(A, d)) ⥤ D(O)`, through which
the forgetful functor `D(A, d) ⥤ D(O)` is defined. This file equips it with its commutation with
the translations, transported from the one of `K(Mod(A, d)) ⥤ K(O)`
(`SheafOfModules.DifferentialGradedModule.homotopyForgetComplex_commShift`) along the
localization `K(O) ⥤ D(O)`, and computes it: at a module `M` it is the commutation of the
localization functor `Q` with the translation, at the underlying complex of `M`.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.homotopyForgetIso`: `homotopyForget` is forgetting the
  action into `K(O)` followed by the localization `K(O) ⥤ D(O)`.
* `SheafOfModules.DifferentialGradedModule.homotopyForget_commShift`: the commutation with the
  translations.

## Main results

* `SheafOfModules.DifferentialGradedModule.homotopyForget_commShiftIso_hom_app`: its value at a
  module.
-/

@[expose] public section

open CategoryTheory

universe w u

namespace SheafOfModules.DifferentialGradedModule

variable {X : AlgebraicGeometry.RingedSite.{u, u, u}}
  (A : DifferentialGradedAlgebra.{u, u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
  [HasDerivedCategory.{w} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]

/-- **Forgetting the action into `D(O)` is forgetting it into `K(O)` followed by the localization
`K(O) ⥤ D(O)`**: the components are Mathlib's identification
`DerivedCategory.quotientCompQhIso`. -/
noncomputable def homotopyForgetIso :
    homotopyForgetComplex A ⋙ DerivedCategory.Qh ≅ homotopyForget.{w} A :=
  NatIso.ofComponents
    (fun Z => (DerivedCategory.quotientCompQhIso _).app Z.as.complex) (by
      rintro ⟨M⟩ ⟨N⟩ f
      obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient A).map_surjective f
      exact DerivedCategory.quotientCompQhIso_hom_naturality g.toHomologicalComplex)

/-- **Forgetting the action `K(Mod(A, d)) ⥤ D(O)` commutes with the translations.** -/
@[instance_reducible]
noncomputable instance homotopyForget_commShift : (homotopyForget.{w} A).CommShift ℤ :=
  Functor.CommShift.ofIso (homotopyForgetIso A) ℤ

/-- The identification `homotopyForgetIso` commutes with the translations, for the commutation
`homotopyForget_commShift` of `homotopyForget` with the translations. -/
instance homotopyForgetIso_hom_commShift : NatTrans.CommShift (homotopyForgetIso.{w} A).hom ℤ :=
  Functor.CommShift.ofIso_compatibility (homotopyForgetIso A) ℤ

omit [HasDerivedCategory (SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf X.O))] in
/-- The underlying complex of the translate of a module, read in `K(O)`. -/
private theorem homotopyForgetComplex_obj_shift (n : ℤ) (M : DifferentialGradedModule.{u, u, u} A) :
    (homotopyForgetComplex A).obj (((HomotopyCategory.quotient A).obj M)⟦n⟧) =
      (_root_.HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj (M.complex⟦n⟧) :=
  congrArg (_root_.HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
    (homotopyShift_complex A n M)

omit [HasDerivedCategory (SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf X.O))] in
private theorem homotopyForgetComplex_commShiftIso_hom_app' (n : ℤ)
    (M : DifferentialGradedModule.{u, u, u} A) :
    ((homotopyForgetComplex A).commShiftIso n).hom.app ((HomotopyCategory.quotient A).obj M) =
      eqToHom (homotopyForgetComplex_obj_shift A n M) ≫
        ((_root_.HomotopyCategory.quotient _ (ComplexShape.up ℤ)).commShiftIso n).hom.app
          M.complex :=
  homotopyForgetComplex_commShiftIso_hom_app A n M

/-- **The underlying complex of the translate of a module, read in `D(O)`.** -/
theorem homotopyForget_obj_shift (n : ℤ) (M : DifferentialGradedModule.{u, u, u} A) :
    (homotopyForget.{w} A).obj (((HomotopyCategory.quotient A).obj M)⟦n⟧) =
      DerivedCategory.Q.obj (M.complex⟦n⟧) :=
  congrArg DerivedCategory.Q.obj (homotopyShift_complex A n M)

/-- The localization functor `K(C) ⥤ D(C)` composed with the quotient sends a transport along an
equality of complexes to a transport, through Mathlib's identification of the composite with
`DerivedCategory.Q`. -/
private theorem quotientCompQhIso_inv_Qh_eqToHom {C : Type*} [Category* C] [Abelian C]
    [HasDerivedCategory.{w} C] {K K' : CochainComplex C ℤ} (h : K = K') :
    (DerivedCategory.quotientCompQhIso C).inv.app K ≫
        DerivedCategory.Qh.map (eqToHom (congrArg
          (_root_.HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj h)) ≫
        (DerivedCategory.quotientCompQhIso C).hom.app K' =
      eqToHom (congrArg DerivedCategory.Q.obj h) := by
  subst h
  simp

/-- **The commutation of forgetting the action with the translations, at a module**: the
transport along the identification of the underlying complex of the translate with the translate
of the underlying complex, followed by the commutation of `Q` with the translation. -/
theorem homotopyForget_commShiftIso_hom_app (n : ℤ) (M : DifferentialGradedModule.{u, u, u} A) :
    ((homotopyForget.{w} A).commShiftIso n).hom.app ((HomotopyCategory.quotient A).obj M) =
      eqToHom (homotopyForget_obj_shift A n M) ≫
        (DerivedCategory.Q.commShiftIso n).hom.app M.complex := by
  have h1 := NatTrans.shift_app_comm (homotopyForgetIso.{w} A).hom n
    ((HomotopyCategory.quotient A).obj M)
  have hQ : DerivedCategory.Qh.map (((homotopyForgetComplex A).commShiftIso n).hom.app
      ((HomotopyCategory.quotient A).obj M)) =
      DerivedCategory.Qh.map (eqToHom (homotopyForgetComplex_obj_shift A n M)) ≫
        DerivedCategory.Qh.map
          (((_root_.HomotopyCategory.quotient _ (ComplexShape.up ℤ)).commShiftIso n).hom.app
            M.complex) := by
    rw [homotopyForgetComplex_commShiftIso_hom_app']
    exact Functor.map_comp _ _ _
  rw [Functor.commShiftIso_comp_hom_app, hQ] at h1
  have h2 := NatTrans.shift_app_comm (DerivedCategory.quotientCompQhIso
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).hom n M.complex
  rw [Functor.commShiftIso_comp_hom_app] at h2
  have h3 : (homotopyForgetIso.{w} A).hom.app (((HomotopyCategory.quotient A).obj M)⟦n⟧) ≫
      ((homotopyForget.{w} A).commShiftIso n).hom.app ((HomotopyCategory.quotient A).obj M) =
      DerivedCategory.Qh.map (eqToHom (homotopyForgetComplex_obj_shift A n M)) ≫
        (DerivedCategory.quotientCompQhIso _).hom.app (M.complex⟦n⟧) ≫
          (DerivedCategory.Q.commShiftIso n).hom.app M.complex := by
    exact h1.symm.trans ((Category.assoc _ _ _).trans ((Category.assoc _ _ _).trans
      (congrArg (fun t => DerivedCategory.Qh.map
        (eqToHom (homotopyForgetComplex_obj_shift A n M)) ≫ t)
        ((Category.assoc _ _ _).symm.trans h2))))
  have h4 : ((homotopyForget.{w} A).commShiftIso n).hom.app ((HomotopyCategory.quotient A).obj M) =
      (homotopyForgetIso.{w} A).inv.app (((HomotopyCategory.quotient A).obj M)⟦n⟧) ≫
        (homotopyForgetIso.{w} A).hom.app (((HomotopyCategory.quotient A).obj M)⟦n⟧) ≫
          ((homotopyForget.{w} A).commShiftIso n).hom.app ((HomotopyCategory.quotient A).obj M) :=
    (Iso.inv_hom_id_app_assoc (homotopyForgetIso.{w} A)
      (((HomotopyCategory.quotient A).obj M)⟦n⟧)
      (((homotopyForget.{w} A).commShiftIso n).hom.app ((HomotopyCategory.quotient A).obj M))).symm
  refine h4.trans ((congrArg (fun t => (homotopyForgetIso.{w} A).inv.app
    (((HomotopyCategory.quotient A).obj M)⟦n⟧) ≫ t) h3).trans ?_)
  refine (Category.assoc _ _ _).symm.trans ((Category.assoc _ _ _).symm.trans ?_)
  exact congrArg (fun t => t ≫ (DerivedCategory.Q.commShiftIso n).hom.app M.complex)
    ((Category.assoc _ _ _).trans
      (quotientCompQhIso_inv_Qh_eqToHom (homotopyShift_complex A n M)))

/-! ### The connecting morphism landing in the translate by two -/

/-- For a functor `H` commuting with the translations, moving a translate by one past `H` and
adding up two translations by one. -/
private theorem comp_map_shiftFunctorAdd'_inv {C D : Type*} [Category* C] [Category* D]
    [HasShift C ℤ] [HasShift D ℤ] (H : C ⥤ D) [H.CommShift ℤ] {W : D} {Z₁ Z : C}
    (e : Z₁ = Z⟦(1 : ℤ)⟧) (d : W ⟶ H.obj (Z₁⟦(1 : ℤ)⟧)) :
    d ≫ H.map ((eqToHom e)⟦(1 : ℤ)⟧') ≫
        H.map ((shiftFunctorAdd' C (1 : ℤ) 1 2 (by norm_num)).inv.app Z) ≫
        (H.commShiftIso (2 : ℤ)).hom.app Z =
      (d ≫ (H.commShiftIso (1 : ℤ)).hom.app Z₁) ≫ (H.map (eqToHom e))⟦(1 : ℤ)⟧' ≫
        ((H.commShiftIso (1 : ℤ)).hom.app Z)⟦(1 : ℤ)⟧' ≫
        (shiftFunctorAdd' D (1 : ℤ) 1 2 (by norm_num)).inv.app (H.obj Z) := by
  subst e
  rw [Functor.commShiftIso_add' H (show (1 : ℤ) + 1 = 2 by norm_num),
    Functor.CommShift.isoAdd'_hom_app]
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id, Category.id_comp, Category.assoc,
    ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  dsimp only [Functor.comp_obj]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp]

/-- Forgetting the action of an image under the localization functor `K(Mod(A, d)) ⥤ D(A, d)` is
forgetting it on the homotopy category. -/
private theorem derivedForget_map_toDerivedCategory_map'' {Z Z' : HomotopyCategory.{u, u, u} A}
    (f : Z ⟶ Z') :
    (derivedForget.{w} A).map ((toDerivedCategory A).map f) = (homotopyForget.{w} A).map f := by
  have h := Functor.congr_hom (toDerivedCategory_comp_derivedForget.{w} A) f
  refine h.trans ?_
  change 𝟙 _ ≫ (homotopyForget.{w} A).map f ≫ 𝟙 _ = (homotopyForget.{w} A).map f
  rw [Category.id_comp, Category.comp_id]

private theorem derivedForget_assemble
    {S : ShortComplex (DifferentialGradedModule.{u, u, u} A)} (hS : S.ShortExact)
    {Z : HomotopyCategory.{u, u, u} A}
    (e : (HomotopyCategory.quotient A).obj S.X₁ = Z⟦(1 : ℤ)⟧) :
    (derivedForget.{w} A).map (shortExactδTranslate hS ≫
          ((toDerivedCategory A).commShiftIso (1 : ℤ)).inv.app
            ((HomotopyCategory.quotient A).obj S.X₁)) ≫
        (homotopyForget.{w} A).map ((eqToHom e)⟦(1 : ℤ)⟧') ≫
        (homotopyForget.{w} A).map
          ((shiftFunctorAdd' (HomotopyCategory.{u, u, u} A) (1 : ℤ) 1 2 (by norm_num)).inv.app Z) ≫
        ((homotopyForget.{w} A).commShiftIso (2 : ℤ)).hom.app Z =
      DerivedCategory.triangleOfSESδ (toCochainComplex_shortExact A S hS) ≫
        ((homotopyForget.{w} A).map (eqToHom e))⟦(1 : ℤ)⟧' ≫
        (((homotopyForget.{w} A).commShiftIso (1 : ℤ)).hom.app Z)⟦(1 : ℤ)⟧' ≫
        (shiftFunctorAdd' (DerivedCategory _) (1 : ℤ) 1 2 (by norm_num)).inv.app
          ((homotopyForget.{w} A).obj Z) := by
  refine (comp_map_shiftFunctorAdd'_inv (homotopyForget.{w} A) e _).trans ?_
  rw [homotopyForget_commShiftIso_hom_app, ← derivedForget_map_shortExactδTranslate hS]
  rfl

/-- **The connecting morphism of a short exact sequence `0 → K → L → M → 0` of right differential
graded modules, read as a morphism `M ⟶ P[2]` of `D(A, d)`** when `K` is identified with a
translate `P[1]` in `K(Mod(A, d))`: the connecting morphism `M ⟶ K[1]` of Tag 0FTB followed by the
identification `K[1] ≅ P[1][1] ≅ P[2]`. -/
noncomputable def shortExactδTwo {S : ShortComplex (DifferentialGradedModule.{u, u, u} A)}
    (hS : S.ShortExact) (P : DifferentialGradedModule.{u, u, u} A)
    (e : (HomotopyCategory.quotient A).obj S.X₁ = ((HomotopyCategory.quotient A).obj P)⟦(1 : ℤ)⟧) :
    (moduleToDerivedCategory.{u, u, u} A).obj S.X₃ ⟶
      ((moduleToDerivedCategory.{u, u, u} A).obj P)⟦(2 : ℤ)⟧ :=
  shortExactδTranslate hS ≫
    ((toDerivedCategory A).commShiftIso (1 : ℤ)).inv.app ((HomotopyCategory.quotient A).obj S.X₁) ≫
    (toDerivedCategory A).map ((eqToHom e)⟦(1 : ℤ)⟧' ≫
      (shiftFunctorAdd' (HomotopyCategory.{u, u, u} A) (1 : ℤ) 1 2 (by norm_num)).inv.app
        ((HomotopyCategory.quotient A).obj P)) ≫
    ((toDerivedCategory A).commShiftIso (2 : ℤ)).hom.app ((HomotopyCategory.quotient A).obj P)

/-- **Forgetting the action on the connecting morphism landing in the translate by two** gives the
connecting morphism `M ⟶ K[1]` of the underlying short exact sequence of complexes, followed by the
identification `K[1] ≅ P[1][1] ≅ P[2]` in `D(O)`. -/
theorem derivedForget_map_shortExactδTwo
    {S : ShortComplex (DifferentialGradedModule.{u, u, u} A)} (hS : S.ShortExact)
    (P : DifferentialGradedModule.{u, u, u} A)
    (e : (HomotopyCategory.quotient A).obj S.X₁ = ((HomotopyCategory.quotient A).obj P)⟦(1 : ℤ)⟧)
    (hX : S.X₁.complex = P.complex⟦(1 : ℤ)⟧) :
    (derivedForget.{w} A).map (shortExactδTwo A hS P e ≫
        ((toDerivedCategory A).commShiftIso (2 : ℤ)).inv.app
          ((HomotopyCategory.quotient A).obj P)) ≫
      eqToHom (congrArg DerivedCategory.Q.obj
        (HomotopyCategory.shiftFunctor_obj_complex A 2 P)) ≫
      (DerivedCategory.Q.commShiftIso (2 : ℤ)).hom.app P.complex =
    DerivedCategory.triangleOfSESδ (toCochainComplex_shortExact A S hS) ≫
      (DerivedCategory.Q.map (eqToHom hX))⟦(1 : ℤ)⟧' ≫
      ((DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app P.complex)⟦(1 : ℤ)⟧' ≫
      (shiftFunctorAdd' (DerivedCategory _) (1 : ℤ) 1 2 (by norm_num)).inv.app
        (DerivedCategory.Q.obj P.complex) := by
  have hc1P := homotopyForget_commShiftIso_hom_app A 1 P
  have hc2P := homotopyForget_commShiftIso_hom_app A 2 P
  have hE : (homotopyForget.{w} A).map (eqToHom e) ≫
      ((homotopyForget.{w} A).commShiftIso (1 : ℤ)).hom.app ((HomotopyCategory.quotient A).obj P) =
      DerivedCategory.Q.map (eqToHom hX) ≫
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app P.complex := by
    rw [hc1P, eqToHom_map, eqToHom_map]
    exact eqToHom_trans_assoc _ _ _
  have hL : (derivedForget.{w} A).map (shortExactδTwo A hS P e ≫
        ((toDerivedCategory A).commShiftIso (2 : ℤ)).inv.app
          ((HomotopyCategory.quotient A).obj P)) ≫
      eqToHom (congrArg DerivedCategory.Q.obj
        (HomotopyCategory.shiftFunctor_obj_complex A 2 P)) ≫
      (DerivedCategory.Q.commShiftIso (2 : ℤ)).hom.app P.complex =
      (derivedForget.{w} A).map (shortExactδTranslate hS ≫
        ((toDerivedCategory A).commShiftIso (1 : ℤ)).inv.app
          ((HomotopyCategory.quotient A).obj S.X₁)) ≫
        (homotopyForget.{w} A).map ((eqToHom e)⟦(1 : ℤ)⟧') ≫
        (homotopyForget.{w} A).map ((shiftFunctorAdd' (HomotopyCategory.{u, u, u} A)
          (1 : ℤ) 1 2 (by norm_num)).inv.app ((HomotopyCategory.quotient A).obj P)) ≫
        ((homotopyForget.{w} A).commShiftIso (2 : ℤ)).hom.app
          ((HomotopyCategory.quotient A).obj P) := by
    have hg : shortExactδTwo A hS P e ≫
        ((toDerivedCategory A).commShiftIso (2 : ℤ)).inv.app
          ((HomotopyCategory.quotient A).obj P) =
        (shortExactδTranslate hS ≫
          ((toDerivedCategory A).commShiftIso (1 : ℤ)).inv.app
            ((HomotopyCategory.quotient A).obj S.X₁)) ≫
          (toDerivedCategory A).map ((eqToHom e)⟦(1 : ℤ)⟧' ≫
            (shiftFunctorAdd' (HomotopyCategory.{u, u, u} A) (1 : ℤ) 1 2 (by norm_num)).inv.app
              ((HomotopyCategory.quotient A).obj P)) := by
      simp only [shortExactδTwo, Category.assoc, Iso.hom_inv_id_app]
      exact congrArg (fun t => shortExactδTranslate hS ≫ _ ≫ t) (Category.comp_id _)
    have h2' : eqToHom (congrArg DerivedCategory.Q.obj
        (HomotopyCategory.shiftFunctor_obj_complex A 2 P)) ≫
        (DerivedCategory.Q.commShiftIso (2 : ℤ)).hom.app P.complex =
        ((homotopyForget.{w} A).commShiftIso (2 : ℤ)).hom.app
          ((HomotopyCategory.quotient A).obj P) := hc2P.symm
    refine (congrArg (fun t => _ ≫ t) h2').trans ?_
    refine (congrArg (fun t => (derivedForget.{w} A).map t ≫ _) hg).trans ?_
    refine (congrArg (· ≫ _) (Functor.map_comp _ _ _)).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine congrArg (fun t => _ ≫ t) ?_
    refine (congrArg (· ≫ _) (derivedForget_map_toDerivedCategory_map'' A _)).trans ?_
    refine (congrArg (· ≫ _) (Functor.map_comp _ _ _)).trans ?_
    exact Category.assoc _ _ _
  have hE' := congrArg (fun f => (shiftFunctor (DerivedCategory
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) (1 : ℤ)).map f) hE
  simp only [Functor.map_comp] at hE'
  refine hL.trans ((derivedForget_assemble A hS e).trans ?_)
  exact congrArg (fun t => DerivedCategory.triangleOfSESδ (toCochainComplex_shortExact A S hS) ≫ t)
    (((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _)
      (hE'.trans (Functor.map_comp _ _ _)))).trans (Category.assoc _ _ _))

end SheafOfModules.DifferentialGradedModule
