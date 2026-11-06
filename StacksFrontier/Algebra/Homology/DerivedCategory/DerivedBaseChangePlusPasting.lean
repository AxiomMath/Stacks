module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedBaseChangePlus
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusNatIsoGlue
public import StacksFrontier.Algebra.Homology.DerivedCategory.BaseChangeBoundedBelow
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedSquareTransComposition

/-!
# Pasting of base change maps between bounded below right derived functors

Test file.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.DerivedBaseChangePlus

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

section Reassoc

variable {C : Type*} [Category* C]

/-- A reassociation, applied with `exact` where the spellings of the objects differ. -/
lemma reassoc_2_2 {X₀ X₁ X₂ X₃ X₄ X₅ X₆ : C} (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂) (c : X₂ ⟶ X₃)
    (d : X₃ ⟶ X₄) (e : X₄ ⟶ X₅) (f : X₅ ⟶ X₆) :
    a ≫ (b ≫ c) ≫ (d ≫ e) ≫ f = a ≫ b ≫ c ≫ d ≫ e ≫ f := by
  simp only [Category.assoc]

/-- A cancellation and an exchange, applied with `exact` where the spellings of the objects
differ. -/
lemma cancel_exchange {X₀ X₁ X₂ X₃ X₄ X₅ X₆ X₇ X₈ : C} (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂)
    (c : X₂ ⟶ X₃) (d : X₃ ⟶ X₄) (e : X₄ ⟶ X₃) (f : X₃ ⟶ X₅) (g : X₅ ⟶ X₆) (h : X₆ ⟶ X₇)
    (f' : X₂ ⟶ X₈) (c' : X₈ ⟶ X₅) (hde : d ≫ e = 𝟙 _) (hcf : c ≫ f = f' ≫ c') :
    (a ≫ b ≫ c ≫ d) ≫ e ≫ f ≫ g ≫ h = a ≫ b ≫ f' ≫ c' ≫ g ≫ h := by
  simp only [Category.assoc, reassoc_of% hde, reassoc_of% hcf]

/-- The cancellation pattern of `derivedBaseChangePlus_comp_derivedBaseChangePlusIso_hom`. -/
lemma chain_cancel {X₀ X₁ X₂ X₃ X₄ X₅ X₆ X₇ X₈ X₉ : C} (fh : X₀ ⟶ X₁)
    (q : X₁ ⟶ X₂) (u' : X₂ ⟶ X₃) (x : X₃ ⟶ X₄) (y : X₄ ⟶ X₅) (ci : X₅ ⟶ X₆) (n : X₆ ⟶ X₇)
    (cb : X₇ ⟶ X₈) (ib : X₈ ⟶ X₉) (z : X₃ ⟶ X₅) (w : X₂ ⟶ X₆) (qe : X₂ ⟶ X₁) (w' : X₁ ⟶ X₇)
    (fhi : X₁ ⟶ X₀) (bu : X₀ ⟶ X₉) (s2 : x ≫ y = z) (s3 : u' ≫ z ≫ ci = w)
    (s4 : w ≫ n = qe ≫ w') (s5 : q ≫ qe = 𝟙 _) (s6 : w' ≫ cb ≫ ib = fhi ≫ bu)
    (s9 : fh ≫ fhi = 𝟙 _) :
    (fh ≫ q ≫ u' ≫ x) ≫ y ≫ ci ≫ n ≫ cb ≫ ib = bu := by
  simp only [Category.assoc, reassoc_of% s2, reassoc_of% s3, reassoc_of% s4, reassoc_of% s5,
    s6, reassoc_of% s9]

end Reassoc

section Coherence

variable {A B C : Type*} [Category* A] [Category* B] [Category* C]
  [Abelian A] [Abelian B] [Abelian C] [HasDerivedCategory C]

/-- `Qh` of a component of the identity comparison of a composite is an identity. -/
lemma qh_map_mapHomotopyCategoryPlusCompIso_refl_hom_app (P : A ⥤ B) (Q : B ⥤ C) [P.Additive]
    [Q.Additive] (K : HomotopyCategory.Plus A) :
    DerivedCategory.Plus.Qh.map
        ((Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (P ⋙ Q))).hom.app K) = 𝟙 _ :=
  (congrArg DerivedCategory.Plus.Qh.map (rfl : (Functor.mapHomotopyCategoryPlusCompIso
    (Iso.refl (P ⋙ Q))).hom.app K = 𝟙 _)).trans (DerivedCategory.Plus.Qh.map_id _)

/-- `Qh` of a component of the inverse identity comparison of a composite is an identity. -/
lemma qh_map_mapHomotopyCategoryPlusCompIso_refl_inv_app (P : A ⥤ B) (Q : B ⥤ C) [P.Additive]
    [Q.Additive] (K : HomotopyCategory.Plus A) :
    DerivedCategory.Plus.Qh.map
        ((Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (P ⋙ Q))).inv.app K) = 𝟙 _ :=
  (congrArg DerivedCategory.Plus.Qh.map (rfl : (Functor.mapHomotopyCategoryPlusCompIso
    (Iso.refl (P ⋙ Q))).inv.app K = 𝟙 _)).trans (DerivedCategory.Plus.Qh.map_id _)

end Coherence

section Naturality

variable {A A' B B' : Type*} [Category* A] [Category* A'] [Category* B] [Category* B']
  [Abelian A] [Abelian A'] [Abelian B] [Abelian B']
  [HasDerivedCategory A] [HasDerivedCategory A'] [HasDerivedCategory B] [HasDerivedCategory B']
  [EnoughInjectives A] [EnoughInjectives A']
  {F F₀ : A ⥤ B} {F' F₀' : A' ⥤ B'} (G : B ⥤ B') (G' : A ⥤ A')
  [F.Additive] [F₀.Additive] [F'.Additive] [F₀'.Additive] [G.Additive] [G'.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits G'] [PreservesFiniteColimits G']

/-- The degreewise action of `α : F ⋙ G ⟶ G' ⋙ F'` on a bounded below complex, with source and
target spelled through the induced functors of the four sides. -/
abbrev hmap (α : F ⋙ G ⟶ G' ⋙ F') (K : HomotopyCategory.Plus A) :
    G.mapHomotopyCategoryPlus.obj (F.mapHomotopyCategoryPlus.obj K) ⟶
      F'.mapHomotopyCategoryPlus.obj (G'.mapHomotopyCategoryPlus.obj K) :=
  (Functor.mapHomotopyCategoryPlusNatTrans α).app K

/-- The components of `derivedBaseChangePlusAux`, with the identity comparisons dropped. -/
theorem derivedBaseChangePlusAux_app' (α : F ⋙ G ⟶ G' ⋙ F') (K : HomotopyCategory.Plus A) :
    (derivedBaseChangePlusAux F F' G G' α).app K =
      G.mapDerivedCategoryPlusFactorsh.hom.app (F.mapHomotopyCategoryPlus.obj K) ≫
        DerivedCategory.Plus.Qh.map (hmap G G' α K) ≫
        F'.rightDerivedFunctorPlusUnith.app (G'.mapHomotopyCategoryPlus.obj K) ≫
        F'.rightDerivedFunctorPlus.map (G'.mapDerivedCategoryPlusFactorsh.inv.app K) := by
  rw [derivedBaseChangePlusAux_app, qh_map_mapHomotopyCategoryPlusCompIso_refl_hom_app,
    qh_map_mapHomotopyCategoryPlusCompIso_refl_inv_app]
  exact (whisker_eq _ (Category.id_comp _)).trans
    (whisker_eq _ (whisker_eq _ (Category.id_comp _)))

/-- Two maps out of `RF ⋙ G` are equal if they agree after precomposition with `G` of the
derived-functor unit of `RF`. -/
private theorem rightDerivedFunctorPlus_comp_ext {X Y Z : Type*} [Category* X] [Category* Y]
    [Category* Z] [Abelian X] [Abelian Y] [Abelian Z] [HasDerivedCategory X]
    [HasDerivedCategory Y] [HasDerivedCategory Z] [EnoughInjectives X] (F : X ⥤ Y) (G : Y ⥤ Z)
    [F.Additive] [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    {H : DerivedCategory.Plus X ⥤ DerivedCategory.Plus Z}
    {η₁ η₂ : F.rightDerivedFunctorPlus ⋙ G.mapDerivedCategoryPlus ⟶ H}
    (h : ∀ K : HomotopyCategory.Plus X,
      G.mapDerivedCategoryPlus.map (F.rightDerivedFunctorPlusUnith.app K) ≫
          η₁.app (DerivedCategory.Plus.Qh.obj K) =
        G.mapDerivedCategoryPlus.map (F.rightDerivedFunctorPlusUnith.app K) ≫
          η₂.app (DerivedCategory.Plus.Qh.obj K)) :
    η₁ = η₂ :=
  (F.rightDerivedFunctorPlus ⋙ G.mapDerivedCategoryPlus).rightDerived_ext
    (derivedBaseChangePlusUnit F G) (HomotopyCategory.Plus.quasiIso X) _ _ _
    (NatTrans.ext (funext h))

omit [HasDerivedCategory A] [HasDerivedCategory A'] [HasDerivedCategory B] [HasDerivedCategory B']
  [EnoughInjectives A] [EnoughInjectives A'] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits G'] [PreservesFiniteColimits G'] in
/-- The homotopy-level form of a compatibility `e ≫ α₀ = α ≫ e'` of base change squares. -/
lemma mapHomotopyCategoryPlus_natIso_square (e : F ≅ F₀) (e' : F' ≅ F₀') (α : F ⋙ G ⟶ G' ⋙ F')
    (α₀ : F₀ ⋙ G ⟶ G' ⋙ F₀')
    (h : Functor.whiskerRight e.hom G ≫ α₀ = α ≫ Functor.whiskerLeft G' e'.hom)
    (K : HomotopyCategory.Plus A) :
    G.mapHomotopyCategoryPlus.map ((Functor.mapHomotopyCategoryPlusNatIso e).hom.app K) ≫
        hmap G G' α₀ K =
      hmap G G' α K ≫
        (Functor.mapHomotopyCategoryPlusNatIso e').hom.app (G'.mapHomotopyCategoryPlus.obj K) := by
  apply (HomotopyCategory.Plus.ι B').map_injective
  show (NatTrans.mapHomotopyCategory (Functor.whiskerRight e.hom G) (ComplexShape.up ℤ)).app
      K.obj ≫ (NatTrans.mapHomotopyCategory α₀ (ComplexShape.up ℤ)).app K.obj =
    (NatTrans.mapHomotopyCategory α (ComplexShape.up ℤ)).app K.obj ≫
      (NatTrans.mapHomotopyCategory (Functor.whiskerLeft G' e'.hom) (ComplexShape.up ℤ)).app
        K.obj
  rw [← NatTrans.comp_app, ← NatTrans.mapHomotopyCategory_comp, h,
    NatTrans.mapHomotopyCategory_comp, NatTrans.comp_app]

/-- **Naturality of the base change map in the vertical functors.** For isomorphisms
`e : F ≅ F₀` and `e' : F' ≅ F₀'` carrying `α` to `α₀`, the base change maps of `α` and of `α₀`
correspond under the invariance comparisons `RF ≅ RF₀` and `RF' ≅ RF₀'`. -/
theorem derivedBaseChangePlus_natIso (e : F ≅ F₀) (e' : F' ≅ F₀') (α : F ⋙ G ⟶ G' ⋙ F')
    (α₀ : F₀ ⋙ G ⟶ G' ⋙ F₀')
    (h : Functor.whiskerRight e.hom G ≫ α₀ = α ≫ Functor.whiskerLeft G' e'.hom) :
    Functor.whiskerRight (Functor.rightDerivedFunctorPlusNatIso e).hom G.mapDerivedCategoryPlus ≫
        derivedBaseChangePlus F₀ F₀' G G' α₀ =
      derivedBaseChangePlus F F' G G' α ≫
        Functor.whiskerLeft G'.mapDerivedCategoryPlus
          (Functor.rightDerivedFunctorPlusNatIso e').hom := by
  refine rightDerivedFunctorPlus_comp_ext F G fun K => ?_
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  have hL : G.mapDerivedCategoryPlus.map (F.rightDerivedFunctorPlusUnith.app K) ≫
      G.mapDerivedCategoryPlus.map
        ((Functor.rightDerivedFunctorPlusNatIso e).hom.app (DerivedCategory.Plus.Qh.obj K)) ≫
      (derivedBaseChangePlus F₀ F₀' G G' α₀).app (DerivedCategory.Plus.Qh.obj K) =
      G.mapDerivedCategoryPlus.map (DerivedCategory.Plus.Qh.map
        ((Functor.mapHomotopyCategoryPlusNatIso e).hom.app K)) ≫
        (derivedBaseChangePlusAux F₀ F₀' G G' α₀).app K := by
    rw [← Category.assoc, ← Functor.map_comp,
      Functor.rightDerivedFunctorPlusNatIso_hom_fac_app, Functor.map_comp, Category.assoc,
      derivedBaseChangePlus_fac]
  have hR : G.mapDerivedCategoryPlus.map (F.rightDerivedFunctorPlusUnith.app K) ≫
      (derivedBaseChangePlus F F' G G' α).app (DerivedCategory.Plus.Qh.obj K) ≫
      (Functor.rightDerivedFunctorPlusNatIso e').hom.app
        (G'.mapDerivedCategoryPlus.obj (DerivedCategory.Plus.Qh.obj K)) =
      (derivedBaseChangePlusAux F F' G G' α).app K ≫
      (Functor.rightDerivedFunctorPlusNatIso e').hom.app
        (G'.mapDerivedCategoryPlus.obj (DerivedCategory.Plus.Qh.obj K)) := by
    rw [← Category.assoc, derivedBaseChangePlus_fac]
  rw [hL, hR, derivedBaseChangePlusAux_app', derivedBaseChangePlusAux_app']
  have n₁ := G.mapDerivedCategoryPlusFactorsh.hom.naturality
    ((Functor.mapHomotopyCategoryPlusNatIso e).hom.app K)
  have n₂ := (Functor.rightDerivedFunctorPlusNatIso e').hom.naturality
    (G'.mapDerivedCategoryPlusFactorsh.inv.app K)
  have f₂ := Functor.rightDerivedFunctorPlusNatIso_hom_fac_app e' (G'.mapHomotopyCategoryPlus.obj K)
  have hsq : DerivedCategory.Plus.Qh.map (G.mapHomotopyCategoryPlus.map
        ((Functor.mapHomotopyCategoryPlusNatIso e).hom.app K)) ≫
        DerivedCategory.Plus.Qh.map (hmap G G' α₀ K) =
      DerivedCategory.Plus.Qh.map (hmap G G' α K) ≫ DerivedCategory.Plus.Qh.map
        ((Functor.mapHomotopyCategoryPlusNatIso e').hom.app
          (G'.mapHomotopyCategoryPlus.obj K)) := by
    rw [← Functor.map_comp, ← Functor.map_comp,
      mapHomotopyCategoryPlus_natIso_square G G' e e' α α₀ h K]
  simp only [Functor.comp_map, Functor.comp_obj] at n₁ n₂
  simp only [Category.assoc]
  rw [reassoc_of% n₁, reassoc_of% hsq, n₂, reassoc_of% f₂]

end Naturality

section Vertical

variable {A A' B B' C C' : Type*} [Category* A] [Category* A'] [Category* B] [Category* B']
  [Category* C] [Category* C']
  [Abelian A] [Abelian A'] [Abelian B] [Abelian B'] [Abelian C] [Abelian C']
  [HasDerivedCategory A] [HasDerivedCategory A'] [HasDerivedCategory B] [HasDerivedCategory B']
  [HasDerivedCategory C] [HasDerivedCategory C']
  [EnoughInjectives A] [EnoughInjectives A'] [EnoughInjectives B] [EnoughInjectives B']
  {F₁ : A ⥤ B} {F₁' : A' ⥤ B'} {F₂ : B ⥤ C} {F₂' : B' ⥤ C'}
  {GA : A ⥤ A'} {GB : B ⥤ B'} {GC : C ⥤ C'}
  [F₁.Additive] [F₁'.Additive] [F₂.Additive] [F₂'.Additive]
  [GA.Additive] [GB.Additive] [GC.Additive]
  [PreservesFiniteLimits GA] [PreservesFiniteColimits GA]
  [PreservesFiniteLimits GB] [PreservesFiniteColimits GB]
  [PreservesFiniteLimits GC] [PreservesFiniteColimits GC]

/-- The vertical pasting `(F₁ ⋙ F₂) ⋙ GC ⟶ GA ⋙ (F₁' ⋙ F₂')` of two base change squares. -/
def pasteV (α₁ : F₁ ⋙ GB ⟶ GA ⋙ F₁') (α₂ : F₂ ⋙ GC ⟶ GB ⋙ F₂') :
    (F₁ ⋙ F₂) ⋙ GC ⟶ GA ⋙ (F₁' ⋙ F₂') :=
  (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft F₁ α₂ ≫ (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight α₁ F₂' ≫ (Functor.associator _ _ _).hom

omit [HasDerivedCategory A] [HasDerivedCategory A'] [HasDerivedCategory B] [HasDerivedCategory B']
  [HasDerivedCategory C] [HasDerivedCategory C'] [EnoughInjectives A] [EnoughInjectives A']
  [EnoughInjectives B] [EnoughInjectives B'] [PreservesFiniteLimits GA]
  [PreservesFiniteColimits GA] [PreservesFiniteLimits GB] [PreservesFiniteColimits GB]
  [PreservesFiniteLimits GC] [PreservesFiniteColimits GC] in
/-- The homotopy-level form of the vertical pasting. -/
lemma hmap_pasteV (α₁ : F₁ ⋙ GB ⟶ GA ⋙ F₁') (α₂ : F₂ ⋙ GC ⟶ GB ⋙ F₂')
    (K : HomotopyCategory.Plus A) :
    (hmap GC GA (pasteV α₁ α₂) K : GC.mapHomotopyCategoryPlus.obj
        (F₂.mapHomotopyCategoryPlus.obj (F₁.mapHomotopyCategoryPlus.obj K)) ⟶
      F₂'.mapHomotopyCategoryPlus.obj (F₁'.mapHomotopyCategoryPlus.obj
        (GA.mapHomotopyCategoryPlus.obj K))) =
      hmap GC GB α₂ (F₁.mapHomotopyCategoryPlus.obj K) ≫
        F₂'.mapHomotopyCategoryPlus.map (hmap GB GA α₁ K) := by
  apply (HomotopyCategory.Plus.ι C').map_injective
  show (NatTrans.mapHomotopyCategory (pasteV α₁ α₂) (ComplexShape.up ℤ)).app K.obj =
    (NatTrans.mapHomotopyCategory α₂ (ComplexShape.up ℤ)).app
        ((F₁.mapHomotopyCategory (ComplexShape.up ℤ)).obj K.obj) ≫
      (F₂'.mapHomotopyCategory (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomotopyCategory α₁ (ComplexShape.up ℤ)).app K.obj)
  obtain ⟨K₀⟩ := K.obj
  show (HomotopyCategory.quotient C' (ComplexShape.up ℤ)).map
      ((NatTrans.mapHomologicalComplex (pasteV α₁ α₂) (ComplexShape.up ℤ)).app K₀) =
    (HomotopyCategory.quotient C' (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex α₂ (ComplexShape.up ℤ)).app
          ((F₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj K₀)) ≫
      (HomotopyCategory.quotient C' (ComplexShape.up ℤ)).map
        ((F₂'.mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((NatTrans.mapHomologicalComplex α₁ (ComplexShape.up ℤ)).app K₀))
  rw [← Functor.map_comp]
  congr 1
  ext n
  simp [pasteV]

omit [HasDerivedCategory A] [HasDerivedCategory A'] [HasDerivedCategory B] [HasDerivedCategory B']
  [HasDerivedCategory C] [HasDerivedCategory C'] [EnoughInjectives A] [EnoughInjectives A']
  [EnoughInjectives B] [EnoughInjectives B'] [PreservesFiniteLimits GA]
  [PreservesFiniteColimits GA] [PreservesFiniteLimits GB] [PreservesFiniteColimits GB]
  [PreservesFiniteLimits GC] [PreservesFiniteColimits GC] in
variable [HasDerivedCategory C'] in
/-- The image in the bounded below derived category of the homotopy-level form of the vertical
pasting. -/
lemma qh_hmap_pasteV (α₁ : F₁ ⋙ GB ⟶ GA ⋙ F₁') (α₂ : F₂ ⋙ GC ⟶ GB ⋙ F₂')
    (K : HomotopyCategory.Plus A) :
    DerivedCategory.Plus.Qh.map (hmap GC GA (pasteV α₁ α₂) K : GC.mapHomotopyCategoryPlus.obj
        (F₂.mapHomotopyCategoryPlus.obj (F₁.mapHomotopyCategoryPlus.obj K)) ⟶
      F₂'.mapHomotopyCategoryPlus.obj (F₁'.mapHomotopyCategoryPlus.obj
        (GA.mapHomotopyCategoryPlus.obj K))) =
      DerivedCategory.Plus.Qh.map (hmap GC GB α₂ (F₁.mapHomotopyCategoryPlus.obj K)) ≫
        DerivedCategory.Plus.Qh.map (F₂'.mapHomotopyCategoryPlus.map (hmap GB GA α₁ K)) := by
  rw [← Functor.map_comp, hmap_pasteV]

/-- **Vertical pasting of base change maps.** For two base change squares on top of each other,
the base change map of the pasted square, followed by the composition comparison
`R(F₁' ⋙ F₂') ⟶ RF₁' ⋙ RF₂'`, is the composition comparison `R(F₁ ⋙ F₂) ⟶ RF₁ ⋙ RF₂`
followed by the two base change maps. -/
theorem derivedBaseChangePlus_pasteV (α₁ : F₁ ⋙ GB ⟶ GA ⋙ F₁') (α₂ : F₂ ⋙ GC ⟶ GB ⋙ F₂') :
    derivedBaseChangePlus (F₁ ⋙ F₂) (F₁' ⋙ F₂') GC GA (pasteV α₁ α₂) ≫
        Functor.whiskerLeft GA.mapDerivedCategoryPlus
          (Functor.rightDerivedFunctorPlusComp F₁' F₂') =
      Functor.whiskerRight (Functor.rightDerivedFunctorPlusComp F₁ F₂) GC.mapDerivedCategoryPlus ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft F₁.rightDerivedFunctorPlus (derivedBaseChangePlus F₂ F₂' GC GB α₂) ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (derivedBaseChangePlus F₁ F₁' GB GA α₁) F₂'.rightDerivedFunctorPlus ≫
        (Functor.associator _ _ _).hom := by
  refine rightDerivedFunctorPlus_comp_ext (F₁ ⋙ F₂) GC fun K => ?_
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp, Category.comp_id]
  have hL : GC.mapDerivedCategoryPlus.map ((F₁ ⋙ F₂).rightDerivedFunctorPlusUnith.app K) ≫
      (derivedBaseChangePlus (F₁ ⋙ F₂) (F₁' ⋙ F₂') GC GA (pasteV α₁ α₂)).app
        (DerivedCategory.Plus.Qh.obj K) ≫
      (F₁'.rightDerivedFunctorPlusComp F₂').app
        (GA.mapDerivedCategoryPlus.obj (DerivedCategory.Plus.Qh.obj K)) =
      GC.mapDerivedCategoryPlusFactorsh.hom.app ((F₁ ⋙ F₂).mapHomotopyCategoryPlus.obj K) ≫
        DerivedCategory.Plus.Qh.map (hmap GC GB α₂ (F₁.mapHomotopyCategoryPlus.obj K)) ≫
        DerivedCategory.Plus.Qh.map (F₂'.mapHomotopyCategoryPlus.map (hmap GB GA α₁ K)) ≫
        F₂'.rightDerivedFunctorPlusUnith.app
          (F₁'.mapHomotopyCategoryPlus.obj (GA.mapHomotopyCategoryPlus.obj K)) ≫
        F₂'.rightDerivedFunctorPlus.map
          (F₁'.rightDerivedFunctorPlusUnith.app (GA.mapHomotopyCategoryPlus.obj K)) ≫
        F₂'.rightDerivedFunctorPlus.map
          (F₁'.rightDerivedFunctorPlus.map (GA.mapDerivedCategoryPlusFactorsh.inv.app K)) := by
    rw [← Category.assoc, derivedBaseChangePlus_fac, derivedBaseChangePlusAux_app']
    have n := (F₁'.rightDerivedFunctorPlusComp F₂').naturality
      (GA.mapDerivedCategoryPlusFactorsh.inv.app K)
    have u := Functor.unit_comp_rightDerivedFunctorPlusComp_app F₁' F₂'
      (GA.mapHomotopyCategoryPlus.obj K)
    simp only [Functor.comp_obj, Functor.comp_map] at n u ⊢
    simp only [Category.assoc]
    rw [n, reassoc_of% u, qh_hmap_pasteV]
    simp only [Category.assoc]
  refine hL.trans ?_
  have n2 :=
    (derivedBaseChangePlus F₂ F₂' GC GB α₂).naturality
      (F₁.rightDerivedFunctorPlusUnith.app K : DerivedCategory.Plus.Qh.obj
        (F₁.mapHomotopyCategoryPlus.obj K) ⟶
          F₁.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Qh.obj K))
  have f2 := derivedBaseChangePlus_fac F₂ F₂' GC GB α₂ (F₁.mapHomotopyCategoryPlus.obj K)
  have f1 := derivedBaseChangePlus_fac F₁ F₁' GB GA α₁ K
  have nu := F₂'.rightDerivedFunctorPlusUnith.naturality (hmap GB GA α₁ K)
  have u1 : GC.mapDerivedCategoryPlus.map ((F₁ ⋙ F₂).rightDerivedFunctorPlusUnith.app K) ≫
      GC.mapDerivedCategoryPlus.map ((F₁.rightDerivedFunctorPlusComp F₂).app
        (DerivedCategory.Plus.Qh.obj K)) =
      GC.mapDerivedCategoryPlus.map (F₂.rightDerivedFunctorPlusUnith.app
        (F₁.mapHomotopyCategoryPlus.obj K)) ≫
      GC.mapDerivedCategoryPlus.map (F₂.rightDerivedFunctorPlus.map
        (F₁.rightDerivedFunctorPlusUnith.app K)) := by
    rw [← Functor.map_comp, Functor.unit_comp_rightDerivedFunctorPlusComp_app]
    exact Functor.map_comp _ _ _
  simp only [Functor.comp_obj, Functor.comp_map] at n2 f2 f1 nu u1
  have f1' : F₂'.rightDerivedFunctorPlus.map (GB.mapDerivedCategoryPlus.map
        (F₁.rightDerivedFunctorPlusUnith.app K)) ≫
      F₂'.rightDerivedFunctorPlus.map ((derivedBaseChangePlus F₁ F₁' GB GA α₁).app
        (DerivedCategory.Plus.Qh.obj K)) =
      F₂'.rightDerivedFunctorPlus.map (GB.mapDerivedCategoryPlusFactorsh.hom.app
          (F₁.mapHomotopyCategoryPlus.obj K)) ≫
        F₂'.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Qh.map (hmap GB GA α₁ K)) ≫
        F₂'.rightDerivedFunctorPlus.map (F₁'.rightDerivedFunctorPlusUnith.app
          (GA.mapHomotopyCategoryPlus.obj K)) ≫
        F₂'.rightDerivedFunctorPlus.map (F₁'.rightDerivedFunctorPlus.map
          (GA.mapDerivedCategoryPlusFactorsh.inv.app K)) := by
    rw [← Functor.map_comp, derivedBaseChangePlus_fac, derivedBaseChangePlusAux_app']
    simp only [Functor.map_comp]
  refine Eq.symm (((Category.assoc _ _ _).symm.trans ((eq_whisker u1 _).trans
    (Category.assoc _ _ _))).trans ?_)
  refine (whisker_eq _ ((Category.assoc _ _ _).symm.trans ((eq_whisker n2 _).trans
    (Category.assoc _ _ _)))).trans ?_
  refine ((Category.assoc _ _ _).symm.trans (eq_whisker f2 _)).trans ?_
  refine (whisker_eq _ f1').trans ?_
  rw [derivedBaseChangePlusAux_app']
  have hc : F₂'.rightDerivedFunctorPlus.map
        (GB.mapDerivedCategoryPlusFactorsh.inv.app (F₁.mapHomotopyCategoryPlus.obj K)) ≫
      F₂'.rightDerivedFunctorPlus.map
        (GB.mapDerivedCategoryPlusFactorsh.hom.app (F₁.mapHomotopyCategoryPlus.obj K)) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  exact cancel_exchange _ _ _ _ _ _ _ _ _ _ hc nu.symm

end Vertical

section Exact

variable {A A' B B' : Type*} [Category* A] [Category* A'] [Category* B] [Category* B']
  [Abelian A] [Abelian A'] [Abelian B] [Abelian B']
  [HasDerivedCategory A] [HasDerivedCategory A'] [HasDerivedCategory B] [HasDerivedCategory B']
  [EnoughInjectives A] [EnoughInjectives A'] [EnoughInjectives B]
  (α : A ⥤ A') [α.Additive] [PreservesFiniteLimits α] [PreservesFiniteColimits α]
  (β : B ⥤ B') [β.Additive] [PreservesFiniteLimits β] [PreservesFiniteColimits β]
  (F : A ⥤ B) [F.Additive] (F' : A' ⥤ B') [F'.Additive]

/-- The base change map of the inverse of an isomorphism `α ⋙ F' ≅ F ⋙ β`, followed by the
base change isomorphism `Stacks.Cohomology.BoundedBelowComplexes.derivedBaseChangePlusIso`, is
the identity. -/
theorem derivedBaseChangePlus_comp_derivedBaseChangePlusIso_hom (e : α ⋙ F' ≅ F ⋙ β)
    (hacyclic : ∀ I : A, Injective I → F'.rightAcyclic (α.obj I)) :
    derivedBaseChangePlus F F' β α e.inv ≫
        (Stacks.Cohomology.BoundedBelowComplexes.derivedBaseChangePlusIso α β F F' e
          hacyclic).hom = 𝟙 _ := by
  refine rightDerivedFunctorPlus_comp_ext F β fun K => ?_
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    NatTrans.id_app, Stacks.Cohomology.BoundedBelowComplexes.derivedBaseChangePlusIso,
    Iso.trans_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Iso.symm_hom]
  have s2 : F'.rightDerivedFunctorPlus.map (α.mapDerivedCategoryPlusFactorsh.inv.app K) ≫
      F'.rightDerivedFunctorPlus.map ((Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus
        α).inv.app (DerivedCategory.Plus.Qh.obj K)) =
      F'.rightDerivedFunctorPlus.map (α.rightDerivedFunctorPlusUnith.app K) := by
    rw [← Functor.map_comp,
      ← Functor.unit_comp_rightDerivedFunctorPlusIsoMapDerivedCategoryPlus_hom_app α K,
      Category.assoc, Iso.hom_inv_id_app]
    exact congrArg _ (Category.comp_id _)
  have s3 : F'.rightDerivedFunctorPlusUnith.app (α.mapHomotopyCategoryPlus.obj K) ≫
      F'.rightDerivedFunctorPlus.map (α.rightDerivedFunctorPlusUnith.app K) ≫
      (Functor.rightDerivedFunctorPlusCompIsoOfRightAcyclic α F' hacyclic).inv.app
        (DerivedCategory.Plus.Qh.obj K) = (α ⋙ F').rightDerivedFunctorPlusUnith.app K :=
    (Category.assoc _ _ _).symm.trans ((eq_whisker
      (Functor.unit_comp_rightDerivedFunctorPlusComp_app α F' K).symm _).trans
      ((Category.assoc _ _ _).trans ((whisker_eq _ (Iso.hom_inv_id_app
        (Functor.rightDerivedFunctorPlusCompIsoOfRightAcyclic α F' hacyclic) _)).trans
        (Category.comp_id _))))
  have s4 := Functor.rightDerivedFunctorPlusNatIso_hom_fac_app e K
  have s5 : DerivedCategory.Plus.Qh.map (hmap β α e.inv K) ≫
      DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusNatIso e).hom.app K) =
        𝟙 _ := by
    have : hmap β α e.inv K ≫ (Functor.mapHomotopyCategoryPlusNatIso e).hom.app K = 𝟙 _ := by
      apply (HomotopyCategory.Plus.ι B').map_injective
      show (NatTrans.mapHomotopyCategory e.inv (ComplexShape.up ℤ)).app K.obj ≫
        (NatTrans.mapHomotopyCategory e.hom (ComplexShape.up ℤ)).app K.obj = 𝟙 _
      rw [← NatTrans.comp_app, ← NatTrans.mapHomotopyCategory_comp, Iso.inv_hom_id,
        NatTrans.mapHomotopyCategory_id]
      rfl
    exact (Functor.map_comp _ _ _).symm.trans ((congrArg _ this).trans
      (CategoryTheory.Functor.map_id _ _))
  have s6 : (F ⋙ β).rightDerivedFunctorPlusUnith.app K ≫
      (Functor.rightDerivedFunctorPlusCompIsoOfRightAcyclic F β
        (fun I _ ↦ Functor.rightAcyclic_of_exact β (F.obj I))).hom.app
          (DerivedCategory.Plus.Qh.obj K) ≫
      (Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus β).hom.app
        (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Qh.obj K)) =
      β.mapDerivedCategoryPlusFactorsh.inv.app (F.mapHomotopyCategoryPlus.obj K) ≫
        β.mapDerivedCategoryPlus.map (F.rightDerivedFunctorPlusUnith.app K) := by
    have n := (Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus β).hom.naturality
      (F.rightDerivedFunctorPlusUnith.app K)
    exact (Category.assoc _ _ _).symm.trans ((eq_whisker
      (Functor.unit_comp_rightDerivedFunctorPlusComp_app F β K) _).trans
      ((Category.assoc _ _ _).trans ((whisker_eq _ n).trans ((Category.assoc _ _ _).symm.trans
        (eq_whisker (Functor.unit_comp_rightDerivedFunctorPlusIsoMapDerivedCategoryPlus_hom_app
          β (F.mapHomotopyCategoryPlus.obj K)) _)))))
  have s9 := Iso.hom_inv_id_app β.mapDerivedCategoryPlusFactorsh (F.mapHomotopyCategoryPlus.obj K)
  refine ((Category.assoc _ _ _).symm.trans
    (eq_whisker (derivedBaseChangePlus_fac F F' β α e.inv K) _)).trans ?_
  refine (eq_whisker (derivedBaseChangePlusAux_app' β α e.inv K) _).trans ?_
  refine Eq.trans ?_ (Category.comp_id _).symm
  exact chain_cancel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s2 s3 s4 s5 s6 s9

/-- **The base change isomorphism of an isomorphism `e : α ⋙ F' ≅ F ⋙ β` of underived functors,
read backwards, is the base change map of `e⁻¹`.** -/
theorem derivedBaseChangePlusIso_inv (e : α ⋙ F' ≅ F ⋙ β)
    (hacyclic : ∀ I : A, Injective I → F'.rightAcyclic (α.obj I)) :
    (Stacks.Cohomology.BoundedBelowComplexes.derivedBaseChangePlusIso α β F F' e
      hacyclic).inv = derivedBaseChangePlus F F' β α e.inv :=
  ((Iso.comp_hom_eq_id _).1
    (derivedBaseChangePlus_comp_derivedBaseChangePlusIso_hom α β F F' e hacyclic)).symm

end Exact

end Stacks.Cohomology.DerivedBaseChangePlus
