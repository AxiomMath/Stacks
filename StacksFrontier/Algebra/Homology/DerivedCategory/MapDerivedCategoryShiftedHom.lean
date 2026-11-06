module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import StacksFrontier.CategoryTheory.Shift.ShiftedHomMapAlong

/-!
# Transporting shifted morphisms of derived categories along an exact functor

Let `F : C ⥤ D` be an exact functor of abelian categories. It acts on derived categories by
`CategoryTheory.Functor.mapDerivedCategory`, which commutes with the shift, so a morphism
`x : Q Z ⟶ (Q K)⟦n⟧` of `D(C)` between complexes `Z` and `K` can be transported to a morphism of
`D(D)` between complexes `Z'` and `L` as soon as comparison maps of complexes `z : Z' ⟶ F Z` and
`κ : F K ⟶ L` are given: this is `CategoryTheory.ShiftedHom.mapAlong` along `F.mapDerivedCategory`,
with the comparisons read through the canonical identification of `F.mapDerivedCategory` with
the degreewise action of `F` on complexes. For `Z = ℤ` placed in degree zero this is how
hypercohomology classes are pulled back.

This file proves the properties of that transport which a system of hypercohomology groups and
its long exact sequences need, at the level of complexes:

* transporting along `F` and then along `G` is transporting along any functor `H` isomorphic to
  `F ⋙ G` (`CategoryTheory.Functor.mapAlongExact_mapAlongExact`);
* transporting is compatible with composition by morphisms of complexes
  (`CategoryTheory.Functor.mapAlongExact_comp_Q_map`) and with the connecting morphisms of short
  exact sequences of complexes (`CategoryTheory.Functor.mapAlongExact_comp_triangleOfSESδ`);
* on complexes concentrated in degree zero it is the action of `F` on `Ext`-groups
  (`CategoryTheory.Functor.mapAlongExact_single_hom`).

## Main definitions

* `CategoryTheory.Functor.mapDerivedCategoryIsoComp`: for an isomorphism `F ⋙ G ≅ H` of exact
  functors, the induced isomorphism `H.mapDerivedCategory ≅ F.mapDerivedCategory ⋙
  G.mapDerivedCategory`, which commutes with the shift.
* `CategoryTheory.Functor.mapAlongExact`: the transport of a shifted morphism between images of
  complexes along an exact functor.
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits

universe w₁ w₂ w₃ t₁ t₂

namespace CategoryTheory.Functor

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

variable {C₁ : Type*} [Category C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type*} [Category C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
  {C₃ : Type*} [Category C₃] [Abelian C₃] [HasDerivedCategory.{w₃} C₃]

open Stacks.DerivedCategoryComparisons

/-! ### Isomorphic exact functors and composites -/

section Comparisons

/-- **The isomorphism induced on derived categories by an isomorphism of exact functors commutes
with the shift.** It is lifted through the localization from the degreewise isomorphism, which
commutes with the shift because the shift of complexes is computed degreewise. -/
instance commShift_mapDerivedCategoryIsoOfNatIso_hom (F G : C₁ ⥤ C₂)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G) :
    NatTrans.CommShift (mapDerivedCategoryIsoOfNatIso F G e).hom ℤ := by
  have : NatTrans.CommShift (NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)).hom ℤ := by
    constructor
    intro a
    ext K i
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      HomologicalComplex.comp_f, Functor.mapHomologicalComplex_commShiftIso_hom_app_f,
      Category.id_comp, Category.comp_id]
    rfl
  let : NatTrans.CommShift (Localization.Lifting.iso DerivedCategory.Q
      (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ))
      (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
      F.mapDerivedCategory).hom ℤ :=
    inferInstanceAs (NatTrans.CommShift F.mapDerivedCategoryFactors.hom ℤ)
  let : NatTrans.CommShift (Localization.Lifting.iso DerivedCategory.Q
      (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ))
      (G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
      G.mapDerivedCategory).hom ℤ :=
    inferInstanceAs (NatTrans.CommShift G.mapDerivedCategoryFactors.hom ℤ)
  exact localization_liftNatTrans_commShift DerivedCategory.Q
    (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ))
    (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    F.mapDerivedCategory G.mapDerivedCategory
    (Functor.whiskerRight (NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)).hom
      DerivedCategory.Q)

variable (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃) (H : C₁ ⥤ C₃)
  [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]

/-- For an isomorphism `e : F ⋙ G ≅ H` of exact functors, the isomorphism
`H.mapDerivedCategory ≅ F.mapDerivedCategory ⋙ G.mapDerivedCategory` of their actions on derived
categories. -/
def mapDerivedCategoryIsoComp (e : F ⋙ G ≅ H) :
    H.mapDerivedCategory ≅ F.mapDerivedCategory ⋙ G.mapDerivedCategory :=
  mapDerivedCategoryIsoOfNatIso H (F ⋙ G) e.symm ≪≫
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso F G

/-- The isomorphism `mapDerivedCategoryIsoComp` commutes with the shifts by `ℤ`. -/
instance commShift_mapDerivedCategoryIsoComp_hom (e : F ⋙ G ≅ H) :
    NatTrans.CommShift (mapDerivedCategoryIsoComp F G H e).hom ℤ := by
  dsimp only [mapDerivedCategoryIsoComp, Iso.trans_hom]
  infer_instance

/-- The isomorphism `mapDerivedCategoryIsoComp` at the image of a cochain complex, read through
the identifications of the three actions on derived categories with the degreewise actions. -/
lemma mapDerivedCategoryIsoComp_hom_app_Q (e : F ⋙ G ≅ H) (P : CochainComplex C₁ ℤ) :
    (mapDerivedCategoryIsoComp F G H e).hom.app (DerivedCategory.Q.obj P) ≫
        G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P) ≫
          G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex _).obj P) =
      H.mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)).inv.app P) := by
  have h₃ : (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso F G).hom.app
        (DerivedCategory.Q.obj P) ≫
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P) ≫
        G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex _).obj P) =
      (F ⋙ G).mapDerivedCategoryFactors.hom.app P := by
    rw [← cancel_mono ((F ⋙ G).mapDerivedCategoryFactors.inv.app P), assoc, assoc,
      ← Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso_inv_app_Q F G P,
      Iso.hom_inv_id_app, Iso.hom_inv_id_app]
    rfl
  simp only [mapDerivedCategoryIsoComp, Iso.trans_hom, NatTrans.comp_app, assoc, h₃,
    mapDerivedCategoryIsoOfNatIso_hom_app_Q H (F ⋙ G) e.symm P, Iso.inv_hom_id_app]
  simp only [Functor.comp_obj, comp_id]
  rfl

/-- The inverse of `mapDerivedCategoryIsoComp` at the image of a cochain complex. -/
lemma mapDerivedCategoryIsoComp_inv_app_Q (e : F ⋙ G ≅ H) (P : CochainComplex C₁ ℤ) :
    (mapDerivedCategoryIsoComp F G H e).inv.app (DerivedCategory.Q.obj P) =
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P) ≫
        G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex _).obj P) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)).hom.app P) ≫
            H.mapDerivedCategoryFactors.inv.app P := by
  rw [← cancel_epi ((mapDerivedCategoryIsoComp F G H e).hom.app (DerivedCategory.Q.obj P)),
    Iso.hom_inv_id_app, reassoc_of% (mapDerivedCategoryIsoComp_hom_app_Q F G H e P),
    ← DerivedCategory.Q.map_comp_assoc, Iso.inv_hom_id_app]
  simp only [DerivedCategory.Q.map_id, Category.id_comp, Iso.hom_inv_id_app]
  rfl

end Comparisons

/-! ### Transport of shifted morphisms between complexes -/

section MapAlongExact

variable (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- **The transport of a shifted morphism between complexes along an exact functor.** For
complexes `Z, K` over `C₁` and `Z', L` over `C₂`, maps of complexes `z : Z' ⟶ F Z` and
`κ : F K ⟶ L`, and `x : Q Z ⟶ (Q K)⟦n⟧`, the morphism `Q Z' ⟶ (Q L)⟦n⟧` obtained by applying
`F.mapDerivedCategory` to `x` and composing with `z` and `κ`. -/
def mapAlongExact {Z K : CochainComplex C₁ ℤ} {Z' L : CochainComplex C₂ ℤ}
    (z : Z' ⟶ (F.mapHomologicalComplex _).obj Z) (κ : (F.mapHomologicalComplex _).obj K ⟶ L)
    {n : ℤ} (x : ShiftedHom (DerivedCategory.Q.obj Z) (DerivedCategory.Q.obj K) n) :
    ShiftedHom (DerivedCategory.Q.obj Z') (DerivedCategory.Q.obj L) n :=
  ShiftedHom.mapAlong F.mapDerivedCategory
    (DerivedCategory.Q.map z ≫ F.mapDerivedCategoryFactors.inv.app Z)
    (F.mapDerivedCategoryFactors.hom.app K ≫ DerivedCategory.Q.map κ) x

/-- `CategoryTheory.Functor.mapAlongExact` as an additive map. -/
def mapAlongExactAddHom {Z K : CochainComplex C₁ ℤ} {Z' L : CochainComplex C₂ ℤ}
    (z : Z' ⟶ (F.mapHomologicalComplex _).obj Z) (κ : (F.mapHomologicalComplex _).obj K ⟶ L)
    (n : ℤ) :
    ShiftedHom (DerivedCategory.Q.obj Z) (DerivedCategory.Q.obj K) n →+
      ShiftedHom (DerivedCategory.Q.obj Z') (DerivedCategory.Q.obj L) n :=
  ShiftedHom.mapAlongAddHom F.mapDerivedCategory
    (DerivedCategory.Q.map z ≫ F.mapDerivedCategoryFactors.inv.app Z)
    (F.mapDerivedCategoryFactors.hom.app K ≫ DerivedCategory.Q.map κ) n

/-- The additive map `mapAlongExactAddHom` sends `x` to `mapAlongExact z κ x`. -/
@[simp]
lemma mapAlongExactAddHom_apply {Z K : CochainComplex C₁ ℤ} {Z' L : CochainComplex C₂ ℤ}
    (z : Z' ⟶ (F.mapHomologicalComplex _).obj Z) (κ : (F.mapHomologicalComplex _).obj K ⟶ L)
    (n : ℤ) (x : ShiftedHom (DerivedCategory.Q.obj Z) (DerivedCategory.Q.obj K) n) :
    F.mapAlongExactAddHom z κ n x = F.mapAlongExact z κ x := rfl

/-- **Transporting along two exact functors in succession** is transporting along any exact
functor `H` isomorphic to their composite, with the composite comparison maps. -/
lemma mapAlongExact_mapAlongExact (G : C₂ ⥤ C₃) (H : C₁ ⥤ C₃)
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H] (e : F ⋙ G ≅ H)
    {Z K : CochainComplex C₁ ℤ} {Z' L : CochainComplex C₂ ℤ} {Z'' M : CochainComplex C₃ ℤ}
    (z : Z' ⟶ (F.mapHomologicalComplex _).obj Z) (κ : (F.mapHomologicalComplex _).obj K ⟶ L)
    (z' : Z'' ⟶ (G.mapHomologicalComplex _).obj Z') (κ' : (G.mapHomologicalComplex _).obj L ⟶ M)
    {n : ℤ} (x : ShiftedHom (DerivedCategory.Q.obj Z) (DerivedCategory.Q.obj K) n) :
    G.mapAlongExact z' κ' (F.mapAlongExact z κ x) =
      H.mapAlongExact (z' ≫ (G.mapHomologicalComplex _).map z ≫
          (NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)).hom.app Z)
        ((NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)).inv.app K ≫
          (G.mapHomologicalComplex _).map κ ≫ κ') x := by
  have hZ : (mapDerivedCategoryIsoComp F G H e).hom.app (DerivedCategory.Q.obj Z) =
      H.mapDerivedCategoryFactors.hom.app Z ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)).inv.app Z) ≫
          G.mapDerivedCategoryFactors.inv.app ((F.mapHomologicalComplex _).obj Z) ≫
            G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.inv.app Z) := by
    rw [← reassoc_of% (mapDerivedCategoryIsoComp_hom_app_Q F G H e Z)]
    simp only [Iso.hom_inv_id_app_assoc, ← Functor.map_comp, Iso.hom_inv_id_app]
    exact ((Category.comp_id _).symm.trans
      (congrArg (fun t => _ ≫ t) (G.mapDerivedCategory.map_id _).symm))
  have hnat : ∀ {P P' : CochainComplex C₂ ℤ} (f : P ⟶ P'),
      G.mapDerivedCategoryFactors.inv.app P ≫ G.mapDerivedCategory.map (DerivedCategory.Q.map f) =
        DerivedCategory.Q.map ((G.mapHomologicalComplex _).map f) ≫
          G.mapDerivedCategoryFactors.inv.app P' := fun f =>
    (G.mapDerivedCategoryFactors.inv.naturality f).symm
  refine (ShiftedHom.mapAlong_mapAlong F.mapDerivedCategory G.mapDerivedCategory
    H.mapDerivedCategory (mapDerivedCategoryIsoComp F G H e).hom _ _ _ _
    (DerivedCategory.Q.map (z' ≫ (G.mapHomologicalComplex _).map z ≫
      (NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)).hom.app Z) ≫
        H.mapDerivedCategoryFactors.inv.app Z) ?_ x).trans ?_
  · rw [hZ]
    simp only [Functor.map_comp, assoc, Iso.inv_hom_id_app_assoc, reassoc_of% hnat]
    simp only [← DerivedCategory.Q.map_comp_assoc, Iso.hom_inv_id_app]
    exact congrArg (fun t => DerivedCategory.Q.map (z' ≫ t) ≫ _) (Category.comp_id _)
  · unfold mapAlongExact
    congr 1
    simp only [Functor.map_comp, assoc, G.mapDerivedCategoryFactors_hom_naturality_assoc,
      reassoc_of% (mapDerivedCategoryIsoComp_hom_app_Q F G H e K)]

/-- **Transporting is natural in the target complex.** -/
lemma mapAlongExact_comp_Q_map {Z K : CochainComplex C₁ ℤ} {Z' L L' : CochainComplex C₂ ℤ}
    (z : Z' ⟶ (F.mapHomologicalComplex _).obj Z) (κ : (F.mapHomologicalComplex _).obj K ⟶ L)
    (g : L ⟶ L') {n : ℤ}
    (x : ShiftedHom (DerivedCategory.Q.obj Z) (DerivedCategory.Q.obj K) n) :
    F.mapAlongExact z κ x ≫ (DerivedCategory.Q.map g)⟦n⟧' = F.mapAlongExact z (κ ≫ g) x := by
  simp [mapAlongExact, ShiftedHom.mapAlong]

/-- **Transporting is natural in the source complex.** -/
lemma mapAlongExact_Q_map {Z K K' : CochainComplex C₁ ℤ} {Z' L : CochainComplex C₂ ℤ}
    (z : Z' ⟶ (F.mapHomologicalComplex _).obj Z) (g : K ⟶ K')
    (κ : (F.mapHomologicalComplex _).obj K' ⟶ L) {n : ℤ}
    (x : ShiftedHom (DerivedCategory.Q.obj Z) (DerivedCategory.Q.obj K) n) :
    F.mapAlongExact z κ (x ≫ (DerivedCategory.Q.map g)⟦n⟧') =
      F.mapAlongExact z ((F.mapHomologicalComplex _).map g ≫ κ) x := by
  simp only [mapAlongExact, ShiftedHom.mapAlong_def, Functor.map_comp, assoc]
  rw [reassoc_of% (F.mapDerivedCategory.commShiftIso_hom_naturality (DerivedCategory.Q.map g) n),
    ← Functor.map_comp_assoc (shiftFunctor _ n), F.mapDerivedCategoryFactors_hom_naturality g]
  simp only [Functor.map_comp, assoc]

/-- **Transporting is compatible with the connecting morphisms of short exact sequences of
complexes.** Let `S` be a short exact sequence of complexes over `C₁`, `S'` one over `C₂`, and
`ψ : F S ⟶ S'` a morphism of short complexes. Composing with the connecting morphism of `S` and
then transporting with the first component of `ψ` is transporting with the third component of
`ψ` and then composing with the connecting morphism of `S'`. -/
lemma mapAlongExact_comp_triangleOfSESδ {Z : CochainComplex C₁ ℤ} {Z' : CochainComplex C₂ ℤ}
    (z : Z' ⟶ (F.mapHomologicalComplex _).obj Z) {S : ShortComplex (CochainComplex C₁ ℤ)}
    (hS : S.ShortExact) {S' : ShortComplex (CochainComplex C₂ ℤ)} (hS' : S'.ShortExact)
    (ψ : S.map (F.mapHomologicalComplex _) ⟶ S') {n m : ℤ} (h : 1 + n = m)
    (x : ShiftedHom (DerivedCategory.Q.obj Z) (DerivedCategory.Q.obj S.X₃) n) :
    F.mapAlongExact z ψ.τ₁ (x.comp (DerivedCategory.triangleOfSESδ hS) h) =
      (F.mapAlongExact z ψ.τ₃ x).comp (DerivedCategory.triangleOfSESδ hS') h := by
  refine ShiftedHom.mapAlong_comp _ _ _ _ x _ _ ?_ h
  have hn := DerivedCategory.triangleOfSESδ_naturality
    (hS.map_of_exact (F.mapHomologicalComplex (ComplexShape.up ℤ))) hS' ψ
  simp only [ShortComplex.map_X₁, ShortComplex.map_X₃] at hn
  simp only [ShiftedHom.map, DerivedCategory.map_triangleOfSESδ, assoc,
    Iso.inv_hom_id_app_assoc]
  rw [← Functor.map_comp, Iso.inv_hom_id_app_assoc, hn]

/-- **On complexes concentrated in degree zero, transporting is the action on `Ext`-groups.**
For objects `X, Y` of `C₁` and `X', Y'` of `C₂` with maps `z₀ : X' ⟶ F X` and `κ₀ : F Y ⟶ Y'`,
transporting the shifted morphism of an `Ext`-class `e` with the single-complex comparisons is the
shifted morphism of `z₀ ∘ F(e) ∘ κ₀`. -/
lemma mapAlongExact_single_hom [HasExt.{t₁} C₁] [HasExt.{t₂} C₂] {X Y : C₁} {X' Y' : C₂}
    (z₀ : X' ⟶ F.obj X) (κ₀ : F.obj Y ⟶ Y') {n : ℕ} (e : Abelian.Ext X Y n) :
    F.mapAlongExact
        ((HomologicalComplex.single C₂ (ComplexShape.up ℤ) 0).map z₀ ≫
          (F.mapCochainComplexSingleFunctor 0).inv.app X)
        ((F.mapCochainComplexSingleFunctor 0).hom.app Y ≫
          (HomologicalComplex.single C₂ (ComplexShape.up ℤ) 0).map κ₀) e.hom =
      ((Abelian.Ext.mk₀ z₀).comp ((e.mapExactFunctor F).comp (Abelian.Ext.mk₀ κ₀) (add_zero n))
        (zero_add n)).hom := by
  rw [Abelian.Ext.comp_hom, Abelian.Ext.comp_hom, Abelian.Ext.mapExactFunctor_hom,
    Abelian.Ext.mk₀_hom, Abelian.Ext.mk₀_hom, ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀]
  simp only [mapAlongExact, ShiftedHom.mapAlong, DerivedCategory.Q.map_comp, assoc,
    Functor.map_comp]
  have hX : DerivedCategory.Q.map ((F.mapCochainComplexSingleFunctor 0).inv.app X) ≫
      F.mapDerivedCategoryFactors.inv.app ((CochainComplex.singleFunctor C₁ 0).obj X) =
        (F.mapDerivedCategorySingleFunctor 0).inv.app X := by
    rw [← F.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app X, assoc]
    exact (congrArg (fun t => _ ≫ t) (F.mapDerivedCategoryFactors.hom_inv_id_app _)).trans
      (comp_id _)
  have hY : F.mapDerivedCategoryFactors.hom.app ((CochainComplex.singleFunctor C₁ 0).obj Y) ≫
      DerivedCategory.Q.map ((F.mapCochainComplexSingleFunctor 0).hom.app Y) =
        (F.mapDerivedCategorySingleFunctor 0).hom.app Y := by
    rw [← F.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app Y,
      ← assoc]
    exact (congrArg (fun t => t ≫ _) (F.mapDerivedCategoryFactors.hom_inv_id_app _)).trans
      (id_comp _)
  rw [reassoc_of% hX, ← Functor.map_comp_assoc (shiftFunctor _ (n : ℤ)), hY]
  rfl

/-- Shifted morphisms `Q Z ⟶ (Q (K⟦b⟧))⟦a⟧` are shifted morphisms `Q Z ⟶ (Q K)⟦c⟧` for
`b + a = c`: the commutation of `Q` with the shift followed by
`CategoryTheory.ShiftedHom.shiftTargetAddEquiv`. -/
def shiftedHomShiftAddEquiv (Z K : CochainComplex C₁ ℤ) (a b c : ℤ) (h : b + a = c) :
    ShiftedHom (DerivedCategory.Q.obj Z) (DerivedCategory.Q.obj (K⟦b⟧)) a ≃+
      ShiftedHom (DerivedCategory.Q.obj Z) (DerivedCategory.Q.obj K) c where
  toFun x := ShiftedHom.shiftTargetAddEquiv _ _ a b c h
    (x ≫ ((DerivedCategory.Q.commShiftIso b).hom.app K)⟦a⟧')
  invFun y := (ShiftedHom.shiftTargetAddEquiv _ _ a b c h).symm y ≫
    ((DerivedCategory.Q.commShiftIso b).inv.app K)⟦a⟧'
  left_inv x := by simp [← Functor.map_comp]
  right_inv y := by simp [← Functor.map_comp]
  map_add' x y := by simp

/-- The equivalence `shiftedHomShiftAddEquiv` sends `x` to
`CategoryTheory.ShiftedHom.shiftTargetAddEquiv` applied to the composite of `x` with the
commutation of `Q` with the shift. -/
lemma shiftedHomShiftAddEquiv_apply (Z K : CochainComplex C₁ ℤ) (a b c : ℤ) (h : b + a = c)
    (x : ShiftedHom (DerivedCategory.Q.obj Z) (DerivedCategory.Q.obj (K⟦b⟧)) a) :
    shiftedHomShiftAddEquiv Z K a b c h x = ShiftedHom.shiftTargetAddEquiv _ _ a b c h
      (x ≫ ((DerivedCategory.Q.commShiftIso b).hom.app K)⟦a⟧') := rfl

/-- **Transporting is compatible with `shiftedHomShiftAddEquiv`**: the comparison of `F (K⟦b⟧)`
with `L⟦b⟧` is the commutation of `F` with the shift of complexes followed by `κ⟦b⟧'`. -/
lemma mapAlongExact_shiftedHomShiftAddEquiv {Z K : CochainComplex C₁ ℤ}
    {Z' L : CochainComplex C₂ ℤ} (z : Z' ⟶ (F.mapHomologicalComplex _).obj Z)
    (κ : (F.mapHomologicalComplex _).obj K ⟶ L) (a b c : ℤ) (h : b + a = c)
    (x : ShiftedHom (DerivedCategory.Q.obj Z) (DerivedCategory.Q.obj (K⟦b⟧)) a) :
    F.mapAlongExact z κ (shiftedHomShiftAddEquiv Z K a b c h x) =
      shiftedHomShiftAddEquiv Z' L a b c h
        (F.mapAlongExact z (((F.mapHomologicalComplex _).commShiftIso b).hom.app K ≫ κ⟦b⟧') x) := by
  rw [shiftedHomShiftAddEquiv_apply, shiftedHomShiftAddEquiv_apply, mapAlongExact,
    ShiftedHom.mapAlong_shiftTargetAddEquiv]
  congr 1
  have hF := NatTrans.shift_app_comm F.mapDerivedCategoryFactors.hom b K
  have hQ := (DerivedCategory.Q.commShiftIso b).hom.naturality κ
  simp only [Functor.commShiftIso_comp_hom_app, Functor.comp_map, assoc] at hF hQ
  rw [ShiftedHom.mapAlong_shift_map, mapAlongExact, ShiftedHom.mapAlong_comp_shift_map]
  congr 1
  simp only [Functor.map_comp, assoc, DerivedCategory.Q.map_comp]
  rw [reassoc_of% hF, hQ]

omit [HasDerivedCategory C₁] [HasDerivedCategory C₂] [PreservesFiniteLimits F]
  [PreservesFiniteColimits F] in
/-- **The single complexes in successive degrees are compatible with an additive functor**: the
identification `(Y[m])⟦1⟧ ≅ Y[n]` for `1 + n = m` commutes with the degreewise action of `F` and
with maps `φ : F A ⟶ B`. -/
lemma mapHomologicalComplex_map_singleFunctors_shiftIso_hom_app {A : C₁} {B : C₂}
    (φ : F.obj A ⟶ B) (n m : ℤ) (h : 1 + n = m) :
    (F.mapHomologicalComplex _).map
        (((CochainComplex.singleFunctors C₁).shiftIso 1 n m h).hom.app A) ≫
      (F.mapCochainComplexSingleFunctor n).hom.app A ≫
        (HomologicalComplex.single C₂ (ComplexShape.up ℤ) n).map φ =
    ((F.mapHomologicalComplex _).commShiftIso (1 : ℤ)).hom.app
        ((HomologicalComplex.single C₁ (ComplexShape.up ℤ) m).obj A) ≫
      ((F.mapCochainComplexSingleFunctor m).hom.app A ≫
        (HomologicalComplex.single C₂ (ComplexShape.up ℤ) m).map φ)⟦(1 : ℤ)⟧' ≫
      ((CochainComplex.singleFunctors C₂).shiftIso 1 n m h).hom.app B := by
  obtain rfl : m = n + 1 := by omega
  ext
  simp [CochainComplex.singleFunctors, Functor.mapCochainComplexSingleFunctor,
    HomologicalComplex.single_map_f_self, HomologicalComplex.singleObjXSelf,
    HomologicalComplex.singleObjXIsoOfEq, eqToHom_map]

end MapAlongExact

end CategoryTheory.Functor

/-! ### The long exact sequence of shifted morphisms out of a fixed object -/

namespace CategoryTheory

open Pretriangulated

variable {𝒯 : Type*} [Category* 𝒯] [Preadditive 𝒯] [HasZeroObject 𝒯]
  [HasShift 𝒯 ℤ] [∀ n : ℤ, (CategoryTheory.shiftFunctor 𝒯 n).Additive] [Pretriangulated 𝒯]

/-- Exactness at the middle vertex of a distinguished triangle of the shifted morphisms out of a
fixed object. -/
lemma Pretriangulated.Triangle.shiftedHom_exact₂ (T : Triangle 𝒯)
    (hT : T ∈ distTriang 𝒯) {A : 𝒯} {n : ℤ}
    (x : ShiftedHom A T.obj₂ n) (hx : x ≫ T.mor₂⟦n⟧' = 0) :
    ∃ y : ShiftedHom A T.obj₁ n, y ≫ T.mor₁⟦n⟧' = x :=
  (ShortComplex.ab_exact_iff _).1
    ((preadditiveCoyoneda.obj (Opposite.op A)).homologySequence_exact₂ T hT n) x hx

/-- Exactness at the third vertex of a distinguished triangle of the shifted morphisms out of a
fixed object. -/
lemma Pretriangulated.Triangle.shiftedHom_exact₃ (T : Triangle 𝒯)
    (hT : T ∈ distTriang 𝒯) {A : 𝒯} {n m : ℤ}
    (h : 1 + n = m) (x : ShiftedHom A T.obj₃ n) (hx : x.comp T.mor₃ h = 0) :
    ∃ y : ShiftedHom A T.obj₂ n, y ≫ T.mor₂⟦n⟧' = x :=
  (ShortComplex.ab_exact_iff _).1
    ((preadditiveCoyoneda.obj (Opposite.op A)).homologySequence_exact₃ T hT n m (by omega)) x
    (by rwa [Pretriangulated.preadditiveCoyoneda_homologySequenceδ_apply])

/-- Exactness at the shifted first vertex of a distinguished triangle of the shifted morphisms
out of a fixed object. -/
lemma Pretriangulated.Triangle.shiftedHom_exact₁ (T : Triangle 𝒯)
    (hT : T ∈ distTriang 𝒯) {A : 𝒯} {n m : ℤ}
    (h : 1 + n = m) (x : ShiftedHom A T.obj₁ m) (hx : x ≫ T.mor₁⟦m⟧' = 0) :
    ∃ y : ShiftedHom A T.obj₃ n, y.comp T.mor₃ h = x := by
  obtain ⟨y, hy⟩ := (ShortComplex.ab_exact_iff _).1
    ((preadditiveCoyoneda.obj (Opposite.op A)).homologySequence_exact₁ T hT n m (by omega)) x hx
  exact ⟨y,
    (Pretriangulated.preadditiveCoyoneda_homologySequenceδ_apply T n m (by omega) y).symm.trans hy⟩

/-- For a distinguished triangle `T`, composing a shifted morphism into `T.obj₁` with the shifts of
`T.mor₁` and `T.mor₂` gives zero. -/
lemma Pretriangulated.Triangle.shiftedHom_comp_mor₁_comp_mor₂ (T : Triangle 𝒯)
    (hT : T ∈ distTriang 𝒯) {A : 𝒯} {n : ℤ}
    (y : ShiftedHom A T.obj₁ n) : (y ≫ T.mor₁⟦n⟧') ≫ T.mor₂⟦n⟧' = 0 := by
  rw [assoc, ← Functor.map_comp, comp_distTriang_mor_zero₁₂ T hT, Functor.map_zero, comp_zero]

/-- For a distinguished triangle `T`, composing a shifted morphism into `T.obj₂` with the shift of
`T.mor₂` and then with `T.mor₃` gives zero. -/
lemma Pretriangulated.Triangle.shiftedHom_comp_mor₂_comp_mor₃ (T : Triangle 𝒯)
    (hT : T ∈ distTriang 𝒯) {A : 𝒯} {n m : ℤ}
    (h : 1 + n = m) (y : ShiftedHom A T.obj₂ n) :
    ShiftedHom.comp (y ≫ T.mor₂⟦n⟧' : ShiftedHom A T.obj₃ n) T.mor₃ h = 0 := by
  simp only [ShiftedHom.comp, assoc, ← Functor.map_comp_assoc, comp_distTriang_mor_zero₂₃ T hT,
    Functor.map_zero, zero_comp, comp_zero]

/-- For a distinguished triangle `T`, composing a shifted morphism into `T.obj₃` with `T.mor₃` and
then with the shift of `T.mor₁` gives zero. -/
lemma Pretriangulated.Triangle.shiftedHom_comp_mor₃_comp_mor₁ (T : Triangle 𝒯)
    (hT : T ∈ distTriang 𝒯) {A : 𝒯} {n m : ℤ}
    (h : 1 + n = m) (y : ShiftedHom A T.obj₃ n) : y.comp T.mor₃ h ≫ T.mor₁⟦m⟧' = 0 := by
  simp only [ShiftedHom.comp, assoc]
  rw [← NatTrans.naturality, Functor.comp_map, ← Functor.map_comp_assoc,
    comp_distTriang_mor_zero₃₁ T hT, Functor.map_zero, zero_comp, comp_zero]

end CategoryTheory
