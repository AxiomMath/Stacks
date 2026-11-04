module

public import StacksFrontier.RingTheory.Dualizing.MapDerivedCategoryJunction

/-!
# A square of exact functors, read on derived categories at the class of a complex

Let `Θ : A ⥤ B`, `G : B ⥤ B'`, `F : A ⥤ A'` and `Θ' : A' ⥤ B'` be exact functors of abelian
categories and `e : Θ ⋙ G ≅ F ⋙ Θ'`. On derived categories `e` induces
`Θ_D ⋙ G_D ≅ (F ⋙ Θ')_D ≅ F_D ⋙ Θ'_D`, through `Dualizing.mapDerivedCategoryCompNatIso`. This
file computes that composite at the class `Q K` of a complex, read through the homotopy category:
it is `Qh` of the degreewise comparison `e`, up to the factorizations of the functors through the
localizations.

## Main definitions

* `Stacks.DerivedCategorySquare.degreewiseHom`: `e` applied degreewise, `G(Θ K) ⟶ Θ'(F K)`.

## Main results

* `Stacks.DerivedCategorySquare.mapDerivedCategoryCompNatIso_trans_symm_hom_app_Q`: the composite
  `Θ_D ⋙ G_D ≅ F_D ⋙ Θ'_D` at `Q K` is `Qh` of `degreewiseHom`, up to the factorizations.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.DerivedCategorySquare

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

/-- `Qh ∘ quotient` and `Q` agree on morphisms, through `DerivedCategory.quotientCompQhIso`. -/
theorem quotientCompQhIso_hom_app_comp_Q_map_comp_inv_app {C : Type*} [Category* C] [Abelian C]
    [HasDerivedCategory C] {K L : CochainComplex C ℤ} (φ : K ⟶ L) :
    (DerivedCategory.quotientCompQhIso C).hom.app K ≫ DerivedCategory.Q.map φ ≫
        (DerivedCategory.quotientCompQhIso C).inv.app L =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map φ) := by
  rw [← DerivedCategory.quotientCompQhIso_hom_naturality_assoc, Iso.hom_inv_id_app]
  exact Category.comp_id _

/-- A functor carries a split identity `f ≫ g = 𝟙` to one. -/
theorem map_comp_map_eq_id {𝒞 𝒟 : Type*} [Category* 𝒞] [Category* 𝒟] (Fn : 𝒞 ⥤ 𝒟)
    {a b : 𝒞} (f : a ⟶ b) (g : b ⟶ a) (h : f ≫ g = 𝟙 a) : Fn.map f ≫ Fn.map g = 𝟙 _ := by
  rw [← Fn.map_comp, h, Fn.map_id]

section Degreewise

variable {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
  [HasZeroMorphisms A] [HasZeroMorphisms B] [HasZeroMorphisms A'] [HasZeroMorphisms B']
  (Θ : A ⥤ B) (G : B ⥤ B') (F : A ⥤ A') (Θ' : A' ⥤ B')
  [Θ.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] [F.PreservesZeroMorphisms]
  [Θ'.PreservesZeroMorphisms] (e : Θ ⋙ G ≅ F ⋙ Θ')

/-- The comparison `e : Θ ⋙ G ≅ F ⋙ Θ'` applied degreewise to a complex. -/
def degreewiseHom (K : CochainComplex A ℤ) :
    (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((Θ.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ⟶
      (Θ'.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) where
  f n := e.hom.app (K.X n)
  comm' i j _ := (e.hom.naturality (K.d i j)).symm

/-- The component of `degreewiseHom` in degree `n` is `e.hom` at `K.X n`. -/
@[simp]
theorem degreewiseHom_f (K : CochainComplex A ℤ) (n : ℤ) :
    (degreewiseHom Θ G F Θ' e K).f n = e.hom.app (K.X n) := rfl

/-- The inverse of `e` applied degreewise to a complex. -/
def degreewiseInv (K : CochainComplex A ℤ) :
    (Θ'.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ⟶
      (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((Θ.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) where
  f n := e.inv.app (K.X n)
  comm' i j _ := (e.inv.naturality (K.d i j)).symm

/-- The component of `degreewiseInv` in degree `n` is `e.inv` at `K.X n`. -/
@[simp]
theorem degreewiseInv_f (K : CochainComplex A ℤ) (n : ℤ) :
    (degreewiseInv Θ G F Θ' e K).f n = e.inv.app (K.X n) := rfl

/-- `degreewiseInv` is a left inverse of `degreewiseHom`. -/
@[reassoc (attr := simp)]
theorem degreewiseHom_comp_degreewiseInv (K : CochainComplex A ℤ) :
    degreewiseHom Θ G F Θ' e K ≫ degreewiseInv Θ G F Θ' e K = 𝟙 _ := by
  ext n
  simp

/-- `degreewiseInv` is a right inverse of `degreewiseHom`. -/
@[reassoc (attr := simp)]
theorem degreewiseInv_comp_degreewiseHom (K : CochainComplex A ℤ) :
    degreewiseInv Θ G F Θ' e K ≫ degreewiseHom Θ G F Θ' e K = 𝟙 _ := by
  ext n
  simp

end Degreewise

section CompIso

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  [Preadditive A] [Preadditive B] [Preadditive C] [Preadditive D]
  (F₁ : A ⥤ B) (F₂ : B ⥤ C) (G₁ : A ⥤ D) (G₂ : D ⥤ C)
  [F₁.Additive] [F₂.Additive] [G₁.Additive] [G₂.Additive]

/-- The component of a transformation of composites applied degreewise, read through the
identifications of the action of a composite with the composite of the actions. -/
theorem mapHomologicalComplexCompIso_natTrans_app_f (τ : F₁ ⋙ F₂ ⟶ G₁ ⋙ G₂)
    (K : CochainComplex A ℤ) (n : ℤ) :
    (((Functor.mapHomologicalComplexCompIso (Iso.refl _) _).hom ≫
        NatTrans.mapHomologicalComplex τ _ ≫
          (Functor.mapHomologicalComplexCompIso (Iso.refl _) _).inv :
      (F₁.mapHomologicalComplex _ ⋙ F₂.mapHomologicalComplex _ :
        CochainComplex A ℤ ⥤ CochainComplex C ℤ) ⟶
      (G₁.mapHomologicalComplex _ ⋙ G₂.mapHomologicalComplex _ :
        CochainComplex A ℤ ⥤ CochainComplex C ℤ)).app K).f n = τ.app (K.X n) := by
  simp only [NatTrans.comp_app, HomologicalComplex.comp_f,
    Functor.mapHomologicalComplexCompIso_hom_app_f, Functor.mapHomologicalComplexCompIso_inv_app_f,
    Iso.refl_hom, Iso.refl_inv, NatTrans.id_app, NatTrans.mapHomologicalComplex_app_f]
  exact (Category.id_comp _).trans (Category.comp_id _)

end CompIso

section BaseChangeComplex

variable {VX VY VX' VY' RX RY RX' RY' : Type*} [Category* VX] [Category* VY] [Category* VX']
  [Category* VY'] [Category* RX] [Category* RY] [Category* RX'] [Category* RY']
  [HasZeroMorphisms VX] [HasZeroMorphisms VY] [HasZeroMorphisms VX'] [HasZeroMorphisms VY']
  [HasZeroMorphisms RX] [HasZeroMorphisms RY] [HasZeroMorphisms RX'] [HasZeroMorphisms RY']
  {fs : VX ⥤ VY} {gi : VY ⥤ VY'} {g'i : VX ⥤ VX'} {f's : VX' ⥤ VY'}
  {ΘX : VX ⥤ RX} {ΘY : VY ⥤ RY} {ΘX' : VX' ⥤ RX'} {ΘY' : VY' ⥤ RY'}
  {fr : RX ⥤ RY} {gp : RY ⥤ RY'} {g'p : RX ⥤ RX'} {f'r : RX' ⥤ RY'}
  [fs.PreservesZeroMorphisms] [gi.PreservesZeroMorphisms] [g'i.PreservesZeroMorphisms]
  [f's.PreservesZeroMorphisms] [ΘX.PreservesZeroMorphisms] [ΘY.PreservesZeroMorphisms]
  [ΘX'.PreservesZeroMorphisms] [ΘY'.PreservesZeroMorphisms] [fr.PreservesZeroMorphisms]
  [gp.PreservesZeroMorphisms] [g'p.PreservesZeroMorphisms] [f'r.PreservesZeroMorphisms]

/-- A degreewise base change map `cbc` carried along `Θ`, followed by the comparisons `PUC'` of
direct images and `Cmp'` of inverse images. -/
abbrev baseChangeLeftComplex (PUC' : f's ⋙ ΘY' ≅ ΘX' ⋙ f'r) (Cmp' : ΘX ⋙ g'p ≅ g'i ⋙ ΘX')
    (K : CochainComplex VX ℤ)
    (cbcN : (fs.mapHomologicalComplex _ ⋙ gi.mapHomologicalComplex _ :
        CochainComplex VX ℤ ⥤ CochainComplex VY' ℤ) ⟶
      (g'i.mapHomologicalComplex _ ⋙ f's.mapHomologicalComplex _ :
        CochainComplex VX ℤ ⥤ CochainComplex VY' ℤ)) :=
  (ΘY'.mapHomologicalComplex (ComplexShape.up ℤ)).map (cbcN.app K) ≫
    degreewiseHom f's ΘY' ΘX' f'r PUC' ((g'i.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
    (f'r.mapHomologicalComplex (ComplexShape.up ℤ)).map (degreewiseInv ΘX g'p g'i ΘX' Cmp' K)

/-- The comparisons `Cmp` of inverse images and `PUC` of direct images, followed by a degreewise
base change map `mbcC`. -/
abbrev baseChangeRightComplex (PUC : fs ⋙ ΘY ≅ ΘX ⋙ fr) (Cmp : ΘY ⋙ gp ≅ gi ⋙ ΘY')
    (K : CochainComplex VX ℤ)
    (mbcC : (gp.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((fr.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((ΘX.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ⟶
      (f'r.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((g'p.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((ΘX.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))) :=
  degreewiseInv ΘY gp gi ΘY' Cmp ((fs.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
    (gp.mapHomologicalComplex (ComplexShape.up ℤ)).map (degreewiseHom fs ΘY ΘX fr PUC K) ≫ mbcC

/-- **A degreewise identity of base change maps, transported along comparisons, at a complex.**
If `Θ` carries a base change map `bc` to `mbc` through the comparisons `PUC` of direct images and
`Cmp` of inverse images at every object, then it does so degreewise at every complex, for any
transformation `cbc` and complex map `mbc` with components `bc` and `mbc`. -/
theorem degreewise_baseChange_eq
    (PUC : fs ⋙ ΘY ≅ ΘX ⋙ fr) (PUC' : f's ⋙ ΘY' ≅ ΘX' ⋙ f'r) (Cmp : ΘY ⋙ gp ≅ gi ⋙ ΘY')
    (Cmp' : ΘX ⋙ g'p ≅ g'i ⋙ ΘX') (bc : fs ⋙ gi ⟶ g'i ⋙ f's) (mbc : fr ⋙ gp ⟶ g'p ⋙ f'r)
    (hD : ∀ M, ΘY'.map (bc.app M) ≫ PUC'.hom.app (g'i.obj M) ≫ f'r.map (Cmp'.inv.app M) =
      Cmp.inv.app (fs.obj M) ≫ gp.map (PUC.hom.app M) ≫ mbc.app (ΘX.obj M))
    (K : CochainComplex VX ℤ)
    (cbcN : (fs.mapHomologicalComplex _ ⋙ gi.mapHomologicalComplex _ :
        CochainComplex VX ℤ ⥤ CochainComplex VY' ℤ) ⟶
      (g'i.mapHomologicalComplex _ ⋙ f's.mapHomologicalComplex _ :
        CochainComplex VX ℤ ⥤ CochainComplex VY' ℤ))
    (hcbc : ∀ n, (cbcN.app K).f n = bc.app (K.X n))
    (mbcC : (gp.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((fr.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((ΘX.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ⟶
      (f'r.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((g'p.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((ΘX.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)))
    (hmbc : ∀ n, mbcC.f n = mbc.app (((ΘX.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).X n)) :
    baseChangeLeftComplex PUC' Cmp' K cbcN = baseChangeRightComplex PUC Cmp K mbcC := by
  ext n
  simp only [baseChangeLeftComplex, baseChangeRightComplex, HomologicalComplex.comp_f,
    Functor.mapHomologicalComplex_map_f, degreewiseHom_f, degreewiseInv_f, hcbc, hmbc]
  exact hD (K.X n)

end BaseChangeComplex

variable {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
  [Abelian A] [Abelian B] [Abelian A'] [Abelian B']
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory A'] [HasDerivedCategory B']
  (Θ : A ⥤ B) (G : B ⥤ B') (F : A ⥤ A') (Θ' : A' ⥤ B')
  [Θ.Additive] [G.Additive] [F.Additive] [Θ'.Additive]
  [PreservesFiniteLimits Θ] [PreservesFiniteColimits Θ]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits Θ'] [PreservesFiniteColimits Θ']
  (e : Θ ⋙ G ≅ F ⋙ Θ')

/-- **The square `e` on derived categories at the class of a complex.** Precomposed with the
factorizations of `G` through the homotopy category and of `Θ` through `Q`, the composite
`Θ_D ⋙ G_D ≅ (F ⋙ Θ')_D ≅ F_D ⋙ Θ'_D` at `Q K` is `Qh` of the degreewise comparison, followed by
the factorizations of `Θ'` and `F`. -/
theorem mapDerivedCategoryCompNatIso_trans_symm_hom_app_Q (K : CochainComplex A ℤ) :
    G.mapDerivedCategoryFactorsh.inv.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        ((Θ.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≫
      G.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso B).hom.app
          ((Θ.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        Θ.mapDerivedCategoryFactors.inv.app K) ≫
      (Dualizing.mapDerivedCategoryCompNatIso Θ G (F ⋙ Θ') e).hom.app (DerivedCategory.Q.obj K) ≫
      (Dualizing.mapDerivedCategoryCompNatIso F Θ' (F ⋙ Θ') (Iso.refl _)).inv.app
        (DerivedCategory.Q.obj K) =
    DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        (degreewiseHom Θ G F Θ' e K)) ≫
      (DerivedCategory.quotientCompQhIso B').hom.app
        ((Θ'.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≫
      Θ'.mapDerivedCategoryFactors.inv.app ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
      Θ'.mapDerivedCategory.map (F.mapDerivedCategoryFactors.inv.app K) := by
  have h :=
    G.mapDerivedCategoryFactorsh_hom_app ((Θ.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
  have h' : G.mapDerivedCategoryFactorsh.inv.app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          ((Θ.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≫
      G.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso B).hom.app
          ((Θ.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≫
      G.mapDerivedCategoryFactors.hom.app ((Θ.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) =
      DerivedCategory.Qh.map ((G.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app
          ((Θ.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≫
        (DerivedCategory.quotientCompQhIso B').hom.app _ := by
    rw [← cancel_epi (G.mapDerivedCategoryFactorsh.hom.app _), Iso.hom_inv_id_app_assoc, h]
    simp only [Category.assoc]
    rw [← DerivedCategory.Qh.map_comp_assoc, Iso.inv_hom_id_app]
    simp
  rw [Dualizing.mapDerivedCategoryCompNatIso_hom_app_Q,
    Dualizing.mapDerivedCategoryCompNatIso_inv_app_Q]
  simp only [Functor.map_comp, Category.assoc]
  rw [← G.mapDerivedCategory.map_comp_assoc (Θ.mapDerivedCategoryFactors.inv.app K),
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp, reassoc_of% h',
    Iso.inv_hom_id_app_assoc, DerivedCategory.quotientCompQhIso_hom_naturality_assoc,
    ← Functor.map_comp_assoc]
  simp only [Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_hom]
  have hd : (Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ)).hom.app K ≫
      (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ Θ')) (ComplexShape.up ℤ)).inv.app K =
        degreewiseHom Θ G F Θ' e K := by
    ext n
    simp [Functor.mapHomologicalComplexCompIso]
  rw [hd]
  exact (congrArg (· ≫ _) (DerivedCategory.Qh.map_id _)).trans (Category.id_comp _)

section Equivalence

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] (E : C ≌ D)
  [E.functor.Additive] [E.inverse.Additive]
  [PreservesFiniteLimits E.functor] [PreservesFiniteColimits E.functor]
  [PreservesFiniteLimits E.inverse] [PreservesFiniteColimits E.inverse]

/-- The functor of the equivalence of derived categories induced by `E` is the derived functor of
`E.functor`. -/
theorem mapDerivedCategoryEquivalenceOfEquivalence_functor :
    (Dualizing.mapDerivedCategoryEquivalenceOfEquivalence E).functor =
      E.functor.mapDerivedCategory := rfl

/-- The inverse of the equivalence of derived categories induced by `E` is the derived functor of
`E.inverse`. -/
theorem mapDerivedCategoryEquivalenceOfEquivalence_inverse :
    (Dualizing.mapDerivedCategoryEquivalenceOfEquivalence E).inverse =
      E.inverse.mapDerivedCategory := rfl

/-- **The counit of the equivalence of derived categories induced by an exact equivalence, at the
class of a complex**: the factorizations of the two functors through `Q`, followed by `Q` of the
counit applied degreewise. -/
theorem mapDerivedCategoryEquivalenceOfEquivalence_counitIso_hom_app_Q
    (L : CochainComplex D ℤ) :
    (Dualizing.mapDerivedCategoryEquivalenceOfEquivalence E).counitIso.hom.app
        (DerivedCategory.Q.obj L) =
      E.functor.mapDerivedCategory.map (E.inverse.mapDerivedCategoryFactors.hom.app L) ≫
        E.functor.mapDerivedCategoryFactors.hom.app
          ((E.inverse.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) ≫
        DerivedCategory.Q.map
          ((E.mapHomologicalComplex (ComplexShape.up ℤ)).counitIso.hom.app L) := by
  rw [← Iso.app_hom]
  dsimp only [Dualizing.mapDerivedCategoryEquivalenceOfEquivalence]
  rw [Localization.equivalence_counitIso_app]
  simp [Localization.Lifting.iso]
  rfl

end Equivalence

section Pushforward

variable {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
  (EX : A ≌ A') (EY : B ≌ B') (fs : A ⥤ B) (pT pr : A' ⥤ B')
  (PIs : pT ⋙ EY.inverse ≅ EX.inverse ⋙ fs) (pTI : pr ≅ pT)

/-- **A comparison of direct images, transported along equivalences.** From
`PIs : pT ⋙ Ψ_Y ≅ Ψ_X ⋙ f_*` (for `Ψ = E.inverse`) and `pTI : pr ≅ pT`, the comparison
`f_* ⋙ Θ_Y ≅ Θ_X ⋙ pr` for `Θ = E.functor`. -/
def transportedPushforwardIso : fs ⋙ EY.functor ≅ EX.functor ⋙ pr :=
  Functor.isoWhiskerRight ((Functor.leftUnitor fs).symm ≪≫ Functor.isoWhiskerRight EX.unitIso fs ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft EX.functor PIs.symm) EY.functor ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft EX.functor (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft pT EY.counitIso ≪≫ Functor.rightUnitor pT ≪≫ pTI.symm)

/-- The component of `transportedPushforwardIso` at an object `M`. -/
theorem transportedPushforwardIso_hom_app (M : A) :
    (transportedPushforwardIso EX EY fs pT pr PIs pTI).hom.app M =
      EY.functor.map (fs.map (EX.unitIso.hom.app M)) ≫
        EY.functor.map (PIs.inv.app (EX.functor.obj M)) ≫
        EY.counitIso.hom.app (pT.obj (EX.functor.obj M)) ≫ pTI.inv.app (EX.functor.obj M) := by
  simp [transportedPushforwardIso]

end Pushforward

end Stacks.DerivedCategorySquare
