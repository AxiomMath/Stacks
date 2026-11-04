module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedBaseChangePlusPasting
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryPlusCompIsoh

/-!
# Horizontal pasting of base change maps between bounded below right derived functors

For two base change squares side by side, with exact horizontal functors `G₁, G₂` and `H₁, H₂`
composing to `G` and `H`, the base change map of the pasted square is the composite of the base
change maps of the two squares, read through the identifications
`G₁.mapDerivedCategoryPlus ⋙ G₂.mapDerivedCategoryPlus ≅ G.mapDerivedCategoryPlus`.

## Main definitions

* `Stacks.Cohomology.DerivedBaseChangePlus.pasteH`: the horizontal pasting of two squares.

## Main results

* `Stacks.Cohomology.DerivedBaseChangePlus.derivedBaseChangePlus_pasteH`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.DerivedBaseChangePlus

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

section ReassocH

variable {C : Type*} [Category* C]

/-- Inverting a commutative square of isomorphisms `a ≫ b ≫ c = x ≫ y`, applied with `exact`
where the spellings of the objects differ. -/
lemma inv_chain {X₀ X₁ X₂ X₃ X₄ : C} {a : X₀ ⟶ X₁} {b : X₁ ⟶ X₂} {c : X₂ ⟶ X₃}
    {x : X₀ ⟶ X₄} {y : X₄ ⟶ X₃} {a' : X₁ ⟶ X₀} {b' : X₂ ⟶ X₁} {c' : X₃ ⟶ X₂}
    {x' : X₄ ⟶ X₀} {y' : X₃ ⟶ X₄} (h : a ≫ b ≫ c = x ≫ y) (ha : a' ≫ a = 𝟙 _)
    (hb : b' ≫ b = 𝟙 _) (hc : c' ≫ c = 𝟙 _) (hx : x ≫ x' = 𝟙 _) (hy : y ≫ y' = 𝟙 _) :
    c' ≫ b' ≫ a' = y' ≫ x' := by
  have e : c' ≫ b' ≫ a' ≫ a ≫ b ≫ c = 𝟙 _ := by
    simp only [reassoc_of% ha, reassoc_of% hb, hc]
  calc c' ≫ b' ≫ a' = c' ≫ b' ≫ a' ≫ (x ≫ y) ≫ y' ≫ x' := by
        simp only [Category.assoc, reassoc_of% hy, hx, Category.comp_id]
    _ = y' ≫ x' := by
        rw [← h]
        simp only [Category.assoc] at e ⊢
        rw [reassoc_of% e]

/-- The rewriting pattern of `derivedBaseChangePlus_pasteH`, applied with `exact` where the
spellings of the objects differ. -/
lemma pasteH_chain {P₀ P₁ P₂ P₃ P₄ Q₁ Q₂ Q₃ Q₄ Q₅ R₀ R₁ R₂ R₃ R₄ R₅ R₆ Z : C}
    {u : P₀ ⟶ P₁} {d : P₁ ⟶ Z} {gi : P₁ ⟶ P₂} {m1 : P₂ ⟶ P₃} {d2 : P₃ ⟶ P₄} {eh : P₄ ⟶ Z}
    {gi0 : P₀ ⟶ Q₁} {mu : Q₁ ⟶ P₂} {a1 : Q₁ ⟶ Q₂} {b1 : Q₂ ⟶ Q₃} {c1 : Q₃ ⟶ Q₄}
    {e1 : Q₄ ⟶ P₃} {d2' : Q₄ ⟶ Q₅} {r1 : Q₅ ⟶ P₄} {fh2 : Q₃ ⟶ R₁} {q2 : R₁ ⟶ R₂}
    {u2 : R₂ ⟶ R₃} {r2 : R₃ ⟶ Q₅} {fh2' : Q₂ ⟶ R₀} {q1 : R₀ ⟶ R₁} {rq : R₃ ⟶ R₄}
    {rfH : R₄ ⟶ Z} {qeH : R₂ ⟶ R₅} {uH : R₅ ⟶ R₄} {fhG : P₀ ⟶ R₆} {qeG : R₆ ⟶ R₀}
    {qP : R₆ ⟶ R₅}
    (sL : u ≫ d = fhG ≫ qP ≫ uH ≫ rfH) (n1 : u ≫ gi = gi0 ≫ mu)
    (f1 : mu ≫ m1 = a1 ≫ b1 ≫ c1 ≫ e1) (n3 : e1 ≫ d2 = d2' ≫ r1)
    (f2 : c1 ≫ d2' = fh2 ≫ q2 ≫ u2 ≫ r2) (n5 : b1 ≫ fh2 = fh2' ≫ q1)
    (c6 : r2 ≫ r1 ≫ eh = rq ≫ rfH) (n7 : u2 ≫ rq = qeH ≫ uH)
    (c8 : gi0 ≫ a1 ≫ fh2' = fhG ≫ qeG) (h : qP = qeG ≫ q1 ≫ q2 ≫ qeH) :
    u ≫ d = u ≫ gi ≫ m1 ≫ d2 ≫ eh := by
  rw [sL, reassoc_of% n1, reassoc_of% f1, reassoc_of% n3, reassoc_of% f2, reassoc_of% n5, c6,
    reassoc_of% n7, reassoc_of% c8, h]
  simp only [Category.assoc]

end ReassocH

section Horizontal

variable {A A' A'' B B' B'' : Type*} [Category* A] [Category* A'] [Category* A'']
  [Category* B] [Category* B'] [Category* B'']
  [Abelian A] [Abelian A'] [Abelian A''] [Abelian B] [Abelian B'] [Abelian B'']
  [HasDerivedCategory A] [HasDerivedCategory A'] [HasDerivedCategory A'']
  [HasDerivedCategory B] [HasDerivedCategory B'] [HasDerivedCategory B'']
  [EnoughInjectives A] [EnoughInjectives A'] [EnoughInjectives A'']
  {F : A ⥤ B} {F' : A' ⥤ B'} {F'' : A'' ⥤ B''}
  {G₁ : B ⥤ B'} {G₂ : B' ⥤ B''} {G : B ⥤ B''} {H₁ : A ⥤ A'} {H₂ : A' ⥤ A''} {H : A ⥤ A''}
  [F.Additive] [F'.Additive] [F''.Additive]
  [G₁.Additive] [G₂.Additive] [G.Additive] [H₁.Additive] [H₂.Additive] [H.Additive]
  [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
  [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H₁] [PreservesFiniteColimits H₁]
  [PreservesFiniteLimits H₂] [PreservesFiniteColimits H₂]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]

/-- The horizontal pasting `F ⋙ G ⟶ H ⋙ F''` of two base change squares, along
`G₁ ⋙ G₂ ≅ G` and `H₁ ⋙ H₂ ≅ H`. -/
def pasteH (α₁ : F ⋙ G₁ ⟶ H₁ ⋙ F') (α₂ : F' ⋙ G₂ ⟶ H₂ ⋙ F'') (eG : G₁ ⋙ G₂ ≅ G)
    (eH : H₁ ⋙ H₂ ≅ H) : F ⋙ G ⟶ H ⋙ F'' :=
  Functor.whiskerLeft F eG.inv ≫ (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight α₁ G₂ ≫ (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft H₁ α₂ ≫ (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight eH.hom F''

omit [HasDerivedCategory A] [HasDerivedCategory A'] [HasDerivedCategory A'']
  [HasDerivedCategory B] [HasDerivedCategory B'] [HasDerivedCategory B'']
  [EnoughInjectives A] [EnoughInjectives A'] [EnoughInjectives A'']
  [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
  [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H₁] [PreservesFiniteColimits H₁]
  [PreservesFiniteLimits H₂] [PreservesFiniteColimits H₂]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H] in
/-- The homotopy-level form of the horizontal pasting. -/
lemma hmap_pasteH (α₁ : F ⋙ G₁ ⟶ H₁ ⋙ F') (α₂ : F' ⋙ G₂ ⟶ H₂ ⋙ F'') (eG : G₁ ⋙ G₂ ≅ G)
    (eH : H₁ ⋙ H₂ ≅ H) (K : HomotopyCategory.Plus A) :
    (hmap G H (pasteH α₁ α₂ eG eH) K : G.mapHomotopyCategoryPlus.obj
        (F.mapHomotopyCategoryPlus.obj K) ⟶
      F''.mapHomotopyCategoryPlus.obj (H.mapHomotopyCategoryPlus.obj K)) =
      ((Functor.mapHomotopyCategoryPlusNatTrans eG.inv).app (F.mapHomotopyCategoryPlus.obj K) :
          G.mapHomotopyCategoryPlus.obj (F.mapHomotopyCategoryPlus.obj K) ⟶
            G₂.mapHomotopyCategoryPlus.obj
              (G₁.mapHomotopyCategoryPlus.obj (F.mapHomotopyCategoryPlus.obj K))) ≫
        G₂.mapHomotopyCategoryPlus.map (hmap G₁ H₁ α₁ K) ≫
        hmap G₂ H₂ α₂ (H₁.mapHomotopyCategoryPlus.obj K) ≫
        (F''.mapHomotopyCategoryPlus.map
          ((Functor.mapHomotopyCategoryPlusNatTrans eH.hom).app K :
            H₂.mapHomotopyCategoryPlus.obj (H₁.mapHomotopyCategoryPlus.obj K) ⟶
              H.mapHomotopyCategoryPlus.obj K)) := by
  apply (HomotopyCategory.Plus.ι B'').map_injective
  show (NatTrans.mapHomotopyCategory (pasteH α₁ α₂ eG eH) (ComplexShape.up ℤ)).app K.obj =
    (NatTrans.mapHomotopyCategory eG.inv (ComplexShape.up ℤ)).app
        ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj K.obj) ≫
      (G₂.mapHomotopyCategory (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomotopyCategory α₁ (ComplexShape.up ℤ)).app K.obj) ≫
      (NatTrans.mapHomotopyCategory α₂ (ComplexShape.up ℤ)).app
        ((H₁.mapHomotopyCategory (ComplexShape.up ℤ)).obj K.obj) ≫
      (F''.mapHomotopyCategory (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomotopyCategory eH.hom (ComplexShape.up ℤ)).app K.obj)
  obtain ⟨K₀⟩ := K.obj
  show (HomotopyCategory.quotient B'' (ComplexShape.up ℤ)).map
      ((NatTrans.mapHomologicalComplex (pasteH α₁ α₂ eG eH) (ComplexShape.up ℤ)).app K₀) =
    (HomotopyCategory.quotient B'' (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex eG.inv (ComplexShape.up ℤ)).app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K₀)) ≫
      (HomotopyCategory.quotient B'' (ComplexShape.up ℤ)).map
        ((G₂.mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((NatTrans.mapHomologicalComplex α₁ (ComplexShape.up ℤ)).app K₀)) ≫
      (HomotopyCategory.quotient B'' (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex α₂ (ComplexShape.up ℤ)).app
          ((H₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj K₀)) ≫
      (HomotopyCategory.quotient B'' (ComplexShape.up ℤ)).map
        ((F''.mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((NatTrans.mapHomologicalComplex eH.hom (ComplexShape.up ℤ)).app K₀))
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
  congr 1
  ext n
  simp [pasteH]

/-- **Horizontal pasting of base change maps.** -/
theorem derivedBaseChangePlus_pasteH (α₁ : F ⋙ G₁ ⟶ H₁ ⋙ F') (α₂ : F' ⋙ G₂ ⟶ H₂ ⋙ F'')
    (eG : G₁ ⋙ G₂ ≅ G) (eH : H₁ ⋙ H₂ ≅ H) :
    derivedBaseChangePlus F F'' G H (pasteH α₁ α₂ eG eH) =
      Functor.whiskerLeft F.rightDerivedFunctorPlus
          (Functor.mapDerivedCategoryPlusCompIsoh eG).inv ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (derivedBaseChangePlus F F' G₁ H₁ α₁) G₂.mapDerivedCategoryPlus ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft H₁.mapDerivedCategoryPlus (derivedBaseChangePlus F' F'' G₂ H₂ α₂) ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (Functor.mapDerivedCategoryPlusCompIsoh eH).hom
          F''.rightDerivedFunctorPlus := by
  refine (F.rightDerivedFunctorPlus ⋙ G.mapDerivedCategoryPlus).rightDerived_ext
    (derivedBaseChangePlusUnit F G) (HomotopyCategory.Plus.quasiIso A) _ _ _
    (NatTrans.ext (funext fun K => ?_))
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp]
  have sL := (derivedBaseChangePlus_fac F F'' G H (pasteH α₁ α₂ eG eH) K).trans
    (derivedBaseChangePlusAux_app' G H (pasteH α₁ α₂ eG eH) K)
  have n1 := (Functor.mapDerivedCategoryPlusCompIsoh eG).inv.naturality
    (F.rightDerivedFunctorPlusUnit.app K)
  have f1 : G₂.mapDerivedCategoryPlus.map
        (G₁.mapDerivedCategoryPlus.map (F.rightDerivedFunctorPlusUnit.app K)) ≫
      G₂.mapDerivedCategoryPlus.map
        ((derivedBaseChangePlus F F' G₁ H₁ α₁).app (DerivedCategory.Plus.Qh.obj K)) =
      G₂.mapDerivedCategoryPlus.map
          (G₁.mapDerivedCategoryPlusFactorsh.hom.app (F.mapHomotopyCategoryPlus.obj K)) ≫
        G₂.mapDerivedCategoryPlus.map (DerivedCategory.Plus.Qh.map (hmap G₁ H₁ α₁ K)) ≫
        G₂.mapDerivedCategoryPlus.map
          (F'.rightDerivedFunctorPlusUnit.app (H₁.mapHomotopyCategoryPlus.obj K)) ≫
        G₂.mapDerivedCategoryPlus.map
          (F'.rightDerivedFunctorPlus.map (H₁.mapDerivedCategoryPlusFactorsh.inv.app K)) := by
    rw [← Functor.map_comp, derivedBaseChangePlus_fac, derivedBaseChangePlusAux_app']
    simp only [Functor.map_comp]
  have n3 := (derivedBaseChangePlus F' F'' G₂ H₂ α₂).naturality
    (H₁.mapDerivedCategoryPlusFactorsh.inv.app K)
  have f2 := (derivedBaseChangePlus_fac F' F'' G₂ H₂ α₂ (H₁.mapHomotopyCategoryPlus.obj K)).trans
    (derivedBaseChangePlusAux_app' G₂ H₂ α₂ (H₁.mapHomotopyCategoryPlus.obj K))
  have n5 := G₂.mapDerivedCategoryPlusFactorsh.hom.naturality (hmap G₁ H₁ α₁ K)
  have c6 : F''.rightDerivedFunctorPlus.map
        (H₂.mapDerivedCategoryPlusFactorsh.inv.app (H₁.mapHomotopyCategoryPlus.obj K)) ≫
      F''.rightDerivedFunctorPlus.map
        (H₂.mapDerivedCategoryPlus.map (H₁.mapDerivedCategoryPlusFactorsh.inv.app K)) ≫
      F''.rightDerivedFunctorPlus.map
        ((Functor.mapDerivedCategoryPlusCompIsoh eH).hom.app (DerivedCategory.Plus.Qh.obj K)) =
      F''.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Qh.map
          ((Functor.mapHomotopyCategoryPlusNatTrans eH.hom).app K)) ≫
        F''.rightDerivedFunctorPlus.map (H.mapDerivedCategoryPlusFactorsh.inv.app K) := by
    rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
    exact congrArg _ (Functor.mapDerivedCategoryPlusCompIsoh_compatible eH K)
  have n7 := F''.rightDerivedFunctorPlusUnit.naturality
    ((Functor.mapHomotopyCategoryPlusNatTrans eH.hom).app K)
  have hx : DerivedCategory.Plus.Qh.map
        ((Functor.mapHomotopyCategoryPlusNatTrans eG.hom).app (F.mapHomotopyCategoryPlus.obj K)) ≫
      DerivedCategory.Plus.Qh.map
        ((Functor.mapHomotopyCategoryPlusNatTrans eG.inv).app (F.mapHomotopyCategoryPlus.obj K)) =
        𝟙 _ := by
    have : (Functor.mapHomotopyCategoryPlusNatTrans eG.hom).app (F.mapHomotopyCategoryPlus.obj K) ≫
        (Functor.mapHomotopyCategoryPlusNatTrans eG.inv).app (F.mapHomotopyCategoryPlus.obj K) =
          𝟙 _ := by
      apply (HomotopyCategory.Plus.ι B'').map_injective
      show (NatTrans.mapHomotopyCategory eG.hom (ComplexShape.up ℤ)).app
          (F.mapHomotopyCategoryPlus.obj K).obj ≫
        (NatTrans.mapHomotopyCategory eG.inv (ComplexShape.up ℤ)).app
          (F.mapHomotopyCategoryPlus.obj K).obj = 𝟙 _
      rw [← NatTrans.comp_app, ← NatTrans.mapHomotopyCategory_comp, Iso.hom_inv_id,
        NatTrans.mapHomotopyCategory_id]
      rfl
    exact (Functor.map_comp _ _ _).symm.trans ((congrArg _ this).trans
      (CategoryTheory.Functor.map_id _ _))
  have hb : G₂.mapDerivedCategoryPlus.map
        (G₁.mapDerivedCategoryPlusFactorsh.hom.app (F.mapHomotopyCategoryPlus.obj K)) ≫
      G₂.mapDerivedCategoryPlus.map
        (G₁.mapDerivedCategoryPlusFactorsh.inv.app (F.mapHomotopyCategoryPlus.obj K)) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.hom_inv_id_app]
    exact CategoryTheory.Functor.map_id _ _
  have c8 := inv_chain
    (Functor.mapDerivedCategoryPlusCompIsoh_compatible eG (F.mapHomotopyCategoryPlus.obj K))
    (Iso.hom_inv_id_app _ _) hb (Iso.inv_hom_id_app (Functor.mapDerivedCategoryPlusCompIsoh eG) _)
    hx (Iso.inv_hom_id_app G.mapDerivedCategoryPlusFactorsh _)
  have h : DerivedCategory.Plus.Qh.map (hmap G H (pasteH α₁ α₂ eG eH) K) =
      DerivedCategory.Plus.Qh.map
          ((Functor.mapHomotopyCategoryPlusNatTrans eG.inv).app (F.mapHomotopyCategoryPlus.obj K)) ≫
        DerivedCategory.Plus.Qh.map (G₂.mapHomotopyCategoryPlus.map (hmap G₁ H₁ α₁ K)) ≫
        DerivedCategory.Plus.Qh.map (hmap G₂ H₂ α₂ (H₁.mapHomotopyCategoryPlus.obj K)) ≫
        DerivedCategory.Plus.Qh.map (F''.mapHomotopyCategoryPlus.map
          ((Functor.mapHomotopyCategoryPlusNatTrans eH.hom).app K)) :=
    (congrArg _ (hmap_pasteH α₁ α₂ eG eH K)).trans ((Functor.map_comp _ _ _).trans
      (whisker_eq _ ((Functor.map_comp _ _ _).trans (whisker_eq _ (Functor.map_comp _ _ _)))))
  exact pasteH_chain sL n1 f1 n3 f2 n5 c6 n7.symm c8 h

end Horizontal

end Stacks.Cohomology.DerivedBaseChangePlus
