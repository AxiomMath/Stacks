module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.RingCohomologyMapLocal
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsModel
public import StacksFrontier.Homology.Tor.BaseChangeIndependence.ComparisonEquations
public import StacksFrontier.Homology.KFlat.Resolution

/-!
# The comparison of Stacks 065Z at the standard and at the locally small model

For a commutative square of rings `R → A → A'`, `R → R' → A'`, the derived base change
comparison `K ⊗ᴸ_R R' ⟶ K ⊗ᴸ_A A'` of Stacks 065Z can be formed at the standard model of the
derived categories of modules or at the locally small one. The two agree under the shrinking
equivalences of `Stacks.Injectives.grothendieckModelEquiv` and the comparisons of the derived
functors involved: both are pinned on K-flat complexes by their counit equation.

## Main definitions

* `RingTheory.TorIndependence.restrictScalarsMapDerivedCategoryModelIso`: `D(restrictScalars)` at
  the two models.
* `RingTheory.TorIndependence.ringHomSquareComparisonLS`: the comparison at the locally small
  model.

## Main results

* `RingTheory.TorIndependence.ringHomSquareComparison_model`: the two comparisons agree.
* `RingTheory.TorIndependence.isIso_ringHomSquareComparisonLS_comp_iff`: invertibility of the
  comparison followed by a morphism does not depend on the model.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
attribute [local instance] ModuleCat.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace RingTheory.TorIndependence

variable {R A R' A' : Type u} [CommRing R] [CommRing A] [CommRing R'] [CommRing A']

/-- The model comparison of `D(restrictScalars i)`. -/
def restrictScalarsMapDerivedCategoryModelIso (i : R' →+* A') :
    @Functor.mapDerivedCategory _ _ _ (HasDerivedCategory.standard _) _ _ _
        (HasDerivedCategory.standard _) (ModuleCat.restrictScalars.{u} i) _ _ _ ⋙
      (Stacks.Injectives.grothendieckModelEquiv.{u} (ModuleCat.{u} R')).functor ≅
    (Stacks.Injectives.grothendieckModelEquiv.{u} (ModuleCat.{u} A')).functor ⋙
      (ModuleCat.restrictScalars.{u} i).mapDerivedCategory :=
  haveI : (@Functor.mapDerivedCategory _ _ _ (HasDerivedCategory.standard _) _ _ _
        (HasDerivedCategory.standard _) (ModuleCat.restrictScalars.{u} i)
        _ _ _).IsLeftDerivedFunctor
      (@Functor.mapDerivedCategoryFactors _ _ _ (HasDerivedCategory.standard _) _ _ _
        (HasDerivedCategory.standard _) (ModuleCat.restrictScalars.{u} i) _ _ _).hom
      (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)) :=
    Functor.isLeftDerivedFunctor_of_inverts (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)) _
      (@Functor.mapDerivedCategoryFactors _ _ _ (HasDerivedCategory.standard _) _ _ _
        (HasDerivedCategory.standard _) (ModuleCat.restrictScalars.{u} i) _ _ _)
  haveI : (ModuleCat.restrictScalars.{u} i).mapDerivedCategory.IsLeftDerivedFunctor
      (ModuleCat.restrictScalars.{u} i).mapDerivedCategoryFactors.hom
      (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)) :=
    Functor.isLeftDerivedFunctor_of_inverts (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)) _
      (ModuleCat.restrictScalars.{u} i).mapDerivedCategoryFactors
  StacksDraft.DerivedModel.leftDerivedModelIso (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
    (@Functor.mapDerivedCategoryFactors _ _ _ (HasDerivedCategory.standard _) _ _ _
        (HasDerivedCategory.standard _) (ModuleCat.restrictScalars.{u} i) _ _ _).hom
    (ModuleCat.restrictScalars.{u} i).mapDerivedCategoryFactors.hom
    (eqToIso (Stacks.Injectives.grothendieckModelEquiv_comp_Q (ModuleCat.{u} A')))
    (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _
      (eqToIso (Stacks.Injectives.grothendieckModelEquiv_comp_Q (ModuleCat.{u} R'))))

/-- If a square commutes after inserting identities, it commutes. -/
private theorem eq_of_comp_map_id_comp {C D : Type*} [Category C] [Category D] {F : C ⥤ D}
    {X : C} {W Z : D} {a : W ⟶ F.obj X} {c : F.obj X ⟶ Z} {b : W ⟶ Z} {e₁ : X ⟶ X} {e₂ : Z ⟶ Z}
    (h : a ≫ F.map e₁ ≫ c = b ≫ e₂) (h₁ : e₁ = 𝟙 _) (h₂ : e₂ = 𝟙 _) : a ≫ c = b := by
  simpa [h₁, h₂] using h

/-- The model comparison of `D(restrictScalars i)` on complexes. -/
theorem restrictScalarsMapDerivedCategoryModelIso_hom_app_factors (i : R' →+* A')
    (P : CochainComplex (ModuleCat.{u} A') ℤ) :
    (restrictScalarsMapDerivedCategoryModelIso i).hom.app
        (@DerivedCategory.Q _ _ _ (HasDerivedCategory.standard _) |>.obj P) ≫
      (ModuleCat.restrictScalars.{u} i).mapDerivedCategoryFactors.hom.app P =
    (Stacks.Injectives.grothendieckModelEquiv.{u} (ModuleCat.{u} R')).functor.map
      ((@Functor.mapDerivedCategoryFactors _ _ _ (HasDerivedCategory.standard _) _ _ _
        (HasDerivedCategory.standard _) (ModuleCat.restrictScalars.{u} i) _ _ _).hom.app P) := by
  have : (@Functor.mapDerivedCategory _ _ _ (HasDerivedCategory.standard _) _ _ _
        (HasDerivedCategory.standard _) (ModuleCat.restrictScalars.{u} i)
        _ _ _).IsLeftDerivedFunctor
      (@Functor.mapDerivedCategoryFactors _ _ _ (HasDerivedCategory.standard _) _ _ _
        (HasDerivedCategory.standard _) (ModuleCat.restrictScalars.{u} i) _ _ _).hom
      (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)) :=
    Functor.isLeftDerivedFunctor_of_inverts (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)) _
      (@Functor.mapDerivedCategoryFactors _ _ _ (HasDerivedCategory.standard _) _ _ _
        (HasDerivedCategory.standard _) (ModuleCat.restrictScalars.{u} i) _ _ _)
  have : (ModuleCat.restrictScalars.{u} i).mapDerivedCategory.IsLeftDerivedFunctor
      (ModuleCat.restrictScalars.{u} i).mapDerivedCategoryFactors.hom
      (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)) :=
    Functor.isLeftDerivedFunctor_of_inverts (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)) _
      (ModuleCat.restrictScalars.{u} i).mapDerivedCategoryFactors
  have h := StacksDraft.DerivedModel.leftDerivedModelIso_hom_app_comparison_whiskerLeft
    (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
    ((ModuleCat.restrictScalars.{u} i).mapHomologicalComplex (ComplexShape.up ℤ))
    (@Functor.mapDerivedCategoryFactors _ _ _ (HasDerivedCategory.standard _) _ _ _
        (HasDerivedCategory.standard _) (ModuleCat.restrictScalars.{u} i) _ _ _).hom
    (ModuleCat.restrictScalars.{u} i).mapDerivedCategoryFactors.hom
    (eqToIso (Stacks.Injectives.grothendieckModelEquiv_comp_Q (ModuleCat.{u} A')))
    (eqToIso (Stacks.Injectives.grothendieckModelEquiv_comp_Q (ModuleCat.{u} R'))) P
  exact eq_of_comp_map_id_comp h rfl rfl

section Chase

variable {C₀ D E Rc : Type*} [Category C₀] [Category D] [Category E] [Category Rc]

/-- Two natural families on a localization agree as soon as they agree at the images of the
objects of a class through which every object admits a resolution. -/
private theorem app_eq_of_left_resolutions (Q : C₀ ⥤ D) (W : MorphismProperty C₀)
    [Q.IsLocalization W] (Pr : ObjectProperty C₀) (hP : ∀ X : C₀, ∃ Y, Pr Y ∧ ∃ p : Y ⟶ X, W p)
    {F G : D ⥤ E} (a b : ∀ M, F.obj M ⟶ G.obj M)
    (ha : ∀ ⦃M M' : D⦄ (x : M ⟶ M'), F.map x ≫ a M' = a M ≫ G.map x)
    (hb : ∀ ⦃M M' : D⦄ (x : M ⟶ M'), F.map x ≫ b M' = b M ≫ G.map x)
    (h : ∀ X, Pr X → a (Q.obj X) = b (Q.obj X)) (M : D) : a M = b M := by
  have e := Localization.natTrans_ext (τ := (⟨a, ha⟩ : F ⟶ G)) (τ' := ⟨b, hb⟩) Q W (fun X => by
    obtain ⟨Y, hY, p, hp⟩ := hP X
    have : IsIso (Q.map p) := Localization.inverts Q W p hp
    change a (Q.obj X) = b (Q.obj X)
    rw [← cancel_epi (F.map (Q.map p)), ha, hb, h Y hY])
  exact congrArg (fun t => NatTrans.app t M) e

/-- The naturality chase for the comparison of models, first form. -/
private theorem model_naturality_chase₁ {D₁ : Type*} [Category D₁] (G : D₁ ⥤ E) (R : Rc ⥤ E)
    {X X' Y Y' : D₁} {Z Z' V V' : Rc} (p : X ⟶ X') (s : X ⟶ Y) (s' : X' ⟶ Y')
    (q : Y ⟶ Y') (m : G.obj Y ⟶ R.obj Z) (m' : G.obj Y' ⟶ R.obj Z') (r : Z ⟶ Z') (w : Z ⟶ V)
    (w' : Z' ⟶ V') (v : V ⟶ V') (h₁ : p ≫ s' = s ≫ q) (h₂ : G.map q ≫ m' = m ≫ R.map r)
    (h₃ : r ≫ w' = w ≫ v) :
    G.map p ≫ G.map s' ≫ m' ≫ R.map w' = (G.map s ≫ m ≫ R.map w) ≫ R.map v := by
  rw [← G.map_comp_assoc, h₁, G.map_comp_assoc, reassoc_of% h₂, ← R.map_comp, h₃, R.map_comp]
  simp

/-- The naturality chase for the comparison of models, second form. -/
private theorem model_naturality_chase₂ {D₁ : Type*} [Category D₁] (L : D₁ ⥤ E)
    {X X' : E} {Y Y' Z Z' : D₁} {T T' : E} (p : X ⟶ X') (μ : X ⟶ L.obj Y) (μ' : X' ⟶ L.obj Y')
    (q : Y ⟶ Y') (m : Y ⟶ Z) (m' : Y' ⟶ Z') (r : Z ⟶ Z') (t : L.obj Z ⟶ T) (t' : L.obj Z' ⟶ T')
    (v : T ⟶ T') (h₁ : p ≫ μ' = μ ≫ L.map q) (h₂ : q ≫ m' = m ≫ r) (h₃ : L.map r ≫ t' = t ≫ v) :
    p ≫ μ' ≫ L.map m' ≫ t' = (μ ≫ L.map m ≫ t) ≫ v := by
  rw [reassoc_of% h₁, ← L.map_comp_assoc, h₂, L.map_comp_assoc, h₃]
  simp

/-- The pointwise chase for the comparison of models of Stacks 065Z. -/
private theorem model_point_chase {DR' DA' DAl' DR DRl : Type*} [Category DR'] [Category DA']
    [Category DAl'] [Category DR] [Category DRl] (G : DR' ⥤ E) (Rl : DAl' ⥤ E) (G' : DA' ⥤ DAl')
    (Rs : DA' ⥤ DR') (Ll : DRl ⥤ E) (GR : DR ⥤ DRl) (Ls : DR ⥤ DR')
    {X₀ X₁ : DR} {Y₀ Y₁ : DA'} {Z₁ Z₂ : DR'} {Xl₀ : DRl} {Yl₀ : DAl'}
    (τs : Ls.obj X₀ ⟶ Rs.obj Y₀) (αhs : Y₀ ⟶ Y₁) (fis : Rs.obj Y₁ ⟶ Z₁) (ffs : X₀ ⟶ X₁)
    (αgs : Ls.obj X₁ ⟶ Z₂) (qs : Z₂ ⟶ Z₁)
    (hs : τs ≫ Rs.map αhs ≫ fis = Ls.map ffs ≫ αgs ≫ qs)
    (τl : Ll.obj Xl₀ ⟶ Rl.obj Yl₀) (αhl : Yl₀ ⟶ G'.obj Y₁) (fil : Rl.obj (G'.obj Y₁) ⟶ G.obj Z₁)
    (ffl : Xl₀ ⟶ GR.obj X₁) (αgl : Ll.obj (GR.obj X₁) ⟶ G.obj Z₂) (ql : G.obj Z₂ ⟶ G.obj Z₁)
    (hl : τl ≫ Rl.map αhl ≫ fil = Ll.map ffl ≫ αgl ≫ ql)
    (μh : G'.obj Y₀ ⟶ Yl₀) (hμh : μh ≫ αhl = G'.map αhs)
    (μg : G.obj (Ls.obj X₀) ⟶ Ll.obj (GR.obj X₀)) (μg₁ : G.obj (Ls.obj X₁) ⟶ Ll.obj (GR.obj X₁))
    (hμg : μg₁ ≫ αgl = G.map αgs) (hμgn : G.map (Ls.map ffs) ≫ μg₁ = μg ≫ Ll.map (GR.map ffs))
    (mi : G.obj (Rs.obj Y₀) ⟶ Rl.obj (G'.obj Y₀)) (mi₁ : G.obj (Rs.obj Y₁) ⟶ Rl.obj (G'.obj Y₁))
    (hmi : mi₁ ≫ fil = G.map fis) (hmin : G.map (Rs.map αhs) ≫ mi₁ = mi ≫ Rl.map (G'.map αhs))
    (mf : GR.obj X₀ ⟶ Xl₀) (hmf : mf ≫ ffl = GR.map ffs) (hq : G.map qs = ql)
    (hX : IsIso (Rl.map αhl ≫ fil)) :
    G.map τs ≫ mi ≫ Rl.map μh = μg ≫ Ll.map mf ≫ τl := by
  have := hX
  refine (cancel_mono (Rl.map αhl ≫ fil)).1 ?_
  have e₁ : (G.map τs ≫ mi ≫ Rl.map μh) ≫ Rl.map αhl ≫ fil =
      G.map (Ls.map ffs) ≫ G.map αgs ≫ G.map qs := by
    rw [Category.assoc, Category.assoc, ← Rl.map_comp_assoc, hμh, ← reassoc_of% hmin, hmi,
      ← G.map_comp, ← G.map_comp, ← Category.assoc, ← G.map_comp, Category.assoc, hs]
    simp
  have e₂ : (μg ≫ Ll.map mf ≫ τl) ≫ Rl.map αhl ≫ fil =
      G.map (Ls.map ffs) ≫ G.map αgs ≫ G.map qs := by
    rw [Category.assoc, Category.assoc, hl, ← Ll.map_comp_assoc, hmf, ← reassoc_of% hμgn,
      reassoc_of% hμg, hq]
  rw [e₁, e₂]

/-- Transfer of invertibility along the comparison of models. -/
private theorem isIso_model_iff {DR' DA' DAl' DRl : Type*} [Category DR'] [Category DA']
    [Category DAl'] [Category DRl] (G : DR' ⥤ E) [G.ReflectsIsomorphisms] (Rl : DAl' ⥤ E)
    (G' : DA' ⥤ DAl') (Rs : DA' ⥤ DR') (Ll : DRl ⥤ E)
    {X₀ : DR'} {Y₀ Y₂ : DA'} {Xl₁ : DRl} {Yl₀ : DAl'} {Z : E}
    (τs : X₀ ⟶ Rs.obj Y₀) (τl : Ll.obj Xl₁ ⟶ Rl.obj Yl₀) (μg : G.obj X₀ ⟶ Z) (mf : Z ⟶ Ll.obj Xl₁)
    (mi : G.obj (Rs.obj Y₀) ⟶ Rl.obj (G'.obj Y₀)) (mi₂ : G.obj (Rs.obj Y₂) ⟶ Rl.obj (G'.obj Y₂))
    (μh : G'.obj Y₀ ≅ Yl₀) (x : Y₀ ⟶ Y₂) (hμg : IsIso μg) (hmf : IsIso mf) (hmi₂ : IsIso mi₂)
    (hkey : G.map τs ≫ mi ≫ Rl.map μh.hom = μg ≫ mf ≫ τl)
    (hmin : G.map (Rs.map x) ≫ mi₂ = mi ≫ Rl.map (G'.map x)) :
    IsIso (τl ≫ Rl.map (μh.inv ≫ G'.map x)) ↔ IsIso (τs ≫ Rs.map x) := by
  have := hμg
  have := hmf
  have := hmi₂
  have e : τl ≫ Rl.map (μh.inv ≫ G'.map x) = inv mf ≫ inv μg ≫ G.map (τs ≫ Rs.map x) ≫ mi₂ := by
    rw [IsIso.eq_inv_comp, IsIso.eq_inv_comp, ← reassoc_of% hkey, ← Rl.map_comp,
      Iso.hom_inv_id_assoc, G.map_comp, Category.assoc, hmin]
  rw [e, isIso_comp_left_iff, isIso_comp_left_iff, isIso_comp_right_iff]
  exact ⟨fun _ => isIso_of_reflects_iso _ G, fun _ => inferInstance⟩

end Chase

section ModelsStd

attribute [local instance 10000] HasDerivedCategory.standard

variable (f : R →+* A) (g : R →+* R') (h : A →+* A') (i : R' →+* A') (sq : h.comp f = i.comp g)

/-- The data of Stacks 065Z at the standard model. -/
abbrev ringHomSquareComparisonData :=
  @derivedBaseChangeComparison.{u, u, u, u, u, u + 1, u + 1, u + 1, u + 1}
    R A R' A' _ _ _ _ _ _ _ _ f g h i sq
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} g).functor
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} h).functor
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} g).comparison
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} h).comparison
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      g).isLeftDerived
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      h).isLeftDerived

/-- The counit compatibility of Stacks 065Z at the standard model. -/
theorem ringHomSquareComparison_app_comp_counit (P : CochainComplex (ModuleCat.{u} A) ℤ) :
    (ringHomSquareComparison f g h i sq).app (DerivedCategory.Q.obj P) ≫
        (ModuleCat.restrictScalars.{u} i).mapDerivedCategory.map
          ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
            h).comparison.app P) ≫
        (ModuleCat.restrictScalars.{u} i).mapDerivedCategoryFactors.hom.app
          (((ModuleCat.extendScalars.{u, u, u} h).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P) =
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} g).functor.map
          ((ModuleCat.restrictScalars.{u} f).mapDerivedCategoryFactors.hom.app P) ≫
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          g).comparison.app
          (((ModuleCat.restrictScalars.{u} f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (ringHomSquareComparisonData f g h i sq).1 (ComplexShape.up ℤ)).app P) := by
  exact @derivedBaseChangeComparison_snd_app_comp_counit R A R' A' _ _ _ _ _ _ _ _ f g h i
    sq _ _ _ _
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      g).isLeftDerived
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      h).isLeftDerived P

end ModelsStd

section Models

variable (f : R →+* A) (g : R →+* R') (h : A →+* A') (i : R' →+* A') (sq : h.comp f = i.comp g)

/-- The data of Stacks 065Z at the locally small model. -/
abbrev ringHomSquareComparisonLSData :=
  @derivedBaseChangeComparison.{u, u, u, u, u, u, u, u, u}
    R A R' A' _ _ _ _ _ _ _ _ f g h i sq
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u, u, u} g).functor
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u, u, u} h).functor
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u, u, u}
      g).comparison
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u, u, u}
      h).comparison
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u, u, u}
      g).isLeftDerived
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u, u, u}
      h).isLeftDerived

/-- The derived base change comparison of Stacks 065Z at the locally small model. -/
abbrev ringHomSquareComparisonLS :
    (ModuleCat.restrictScalars.{u} f).mapDerivedCategory ⋙
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u, u, u}
          g).functor ⟶
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u, u, u}
        h).functor ⋙
        (ModuleCat.restrictScalars.{u} i).mapDerivedCategory :=
  (@derivedBaseChangeComparison.{u, u, u, u, u, u, u, u, u}
    R A R' A' _ _ _ _ _ _ _ _ f g h i sq
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u, u, u} g).functor
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u, u, u} h).functor
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u, u, u}
      g).comparison
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u, u, u}
      h).comparison
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u, u, u}
      g).isLeftDerived
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u, u, u}
      h).isLeftDerived).2.1

/-- The counit compatibility of Stacks 065Z at the locally small model. -/
theorem ringHomSquareComparisonLS_app_comp_counit (P : CochainComplex (ModuleCat.{u} A) ℤ) :
    (ringHomSquareComparisonLS f g h i sq).app (DerivedCategory.Q.obj P) ≫
        (ModuleCat.restrictScalars.{u} i).mapDerivedCategory.map
          ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u, u, u}
            h).comparison.app P) ≫
        (ModuleCat.restrictScalars.{u} i).mapDerivedCategoryFactors.hom.app
          (((ModuleCat.extendScalars.{u, u, u} h).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P) =
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u, u, u}
        g).functor.map
          ((ModuleCat.restrictScalars.{u} f).mapDerivedCategoryFactors.hom.app P) ≫
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u, u, u}
          g).comparison.app
          (((ModuleCat.restrictScalars.{u} f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (ringHomSquareComparisonLSData f g h i sq).1 (ComplexShape.up ℤ)).app P) := by
  exact @derivedBaseChangeComparison_snd_app_comp_counit R A R' A' _ _ _ _ _ _ _ _ f g h i
    sq _ _ _ _
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u, u, u}
      g).isLeftDerived
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u, u, u}
      h).isLeftDerived P

omit [CommRing R'] [CommRing A'] in
/-- The comparison of the two models of derived extension of scalars, on complexes. -/
theorem totalDerivedExtensionScalarsModelIso_hom_app_comparison'
    (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsModelIso f).hom.app
        (@DerivedCategory.Q _ _ _ (HasDerivedCategory.standard _) |>.obj P) ≫
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u, u, u}
        f).comparison.app P =
    (Stacks.Injectives.grothendieckModelEquiv.{u} (ModuleCat.{u} A)).functor.map
      ((@CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.comparison.{u, u, u}
        R A _ _ f (HasDerivedCategory.standard _) (HasDerivedCategory.standard _)
        (@CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          R A _ _ f (HasDerivedCategory.standard _) (HasDerivedCategory.standard _))).app P) := by
  have h :=
    CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsModelIso_hom_app_comparison
      f P
  exact eq_of_comp_map_id_comp h rfl rfl

/-- The underived comparisons of Stacks 065Z at the two models agree. -/
theorem ringHomSquareComparisonData_fst :
    (ringHomSquareComparisonData f g h i sq).1 = (ringHomSquareComparisonLSData f g h i sq).1 :=
  NatTrans.ext (funext fun M => ModuleCat.ExtendScalars.hom_ext fun m =>
    ((ringHomSquareComparisonData f g h i sq).2.2.1 M 1 m).trans
      ((ringHomSquareComparisonLSData f g h i sq).2.2.1 M 1 m).symm)

/-- **Stacks 065Z at the two models.** -/
theorem ringHomSquareComparison_model
    (M : @DerivedCategory (ModuleCat.{u} A) _ _ (HasDerivedCategory.standard _)) :
    (Stacks.Injectives.grothendieckModelEquiv.{u} (ModuleCat.{u} R')).functor.map
        ((ringHomSquareComparison f g h i sq).app M) ≫
      (restrictScalarsMapDerivedCategoryModelIso i).hom.app _ ≫
      (ModuleCat.restrictScalars.{u} i).mapDerivedCategory.map
        ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsModelIso h).hom.app
          M) =
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsModelIso g).hom.app _ ≫
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u, u, u}
        g).functor.map
        ((restrictScalarsMapDerivedCategoryModelIso f).hom.app M) ≫
      (ringHomSquareComparisonLS f g h i sq).app
        ((Stacks.Injectives.grothendieckModelEquiv.{u} (ModuleCat.{u} A)).functor.obj M) := by
  refine app_eq_of_left_resolutions (@DerivedCategory.Q _ _ _ (HasDerivedCategory.standard _))
    (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)) (fun K => CochainComplex.KFlat.{u, u} K)
    (fun X => ?_) (F := (@Functor.mapDerivedCategory _ _ _ (HasDerivedCategory.standard _) _ _ _
        (HasDerivedCategory.standard _) (ModuleCat.restrictScalars.{u} f) _ _ _) ⋙
      (@CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.functor.{u, u, u}
        R R' _ _ g (HasDerivedCategory.standard _) (HasDerivedCategory.standard _)
        (@CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} R R' _ _ g
          (HasDerivedCategory.standard _) (HasDerivedCategory.standard _))) ⋙
      (Stacks.Injectives.grothendieckModelEquiv.{u} (ModuleCat.{u} R')).functor)
    (G := (Stacks.Injectives.grothendieckModelEquiv.{u} (ModuleCat.{u} A)).functor ⋙
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u, u, u}
        h).functor ⋙
      (ModuleCat.restrictScalars.{u} i).mapDerivedCategory)
    (fun M => (Stacks.Injectives.grothendieckModelEquiv.{u} (ModuleCat.{u} R')).functor.map
        ((ringHomSquareComparison f g h i sq).app M) ≫
      (restrictScalarsMapDerivedCategoryModelIso i).hom.app _ ≫
      (ModuleCat.restrictScalars.{u} i).mapDerivedCategory.map
        ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsModelIso h).hom.app M))
    (fun M =>
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsModelIso g).hom.app _ ≫
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u, u, u}
        g).functor.map ((restrictScalarsMapDerivedCategoryModelIso f).hom.app M) ≫
      (ringHomSquareComparisonLS f g h i sq).app
        ((Stacks.Injectives.grothendieckModelEquiv.{u} (ModuleCat.{u} A)).functor.obj M))
    (fun _ _ x => model_naturality_chase₁
      (Stacks.Injectives.grothendieckModelEquiv.{u} (ModuleCat.{u} R')).functor
      (ModuleCat.restrictScalars.{u} i).mapDerivedCategory
      _ _ _ _ _ _ _ _ _ _ ((ringHomSquareComparison f g h i sq).naturality x)
      ((restrictScalarsMapDerivedCategoryModelIso i).hom.naturality _)
      ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsModelIso
        h).hom.naturality x))
    (fun _ _ x => model_naturality_chase₂
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u, u, u}
        g).functor _ _ _ _ _ _ _ _ _ _
      ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsModelIso
        g).hom.naturality _)
      ((restrictScalarsMapDerivedCategoryModelIso f).hom.naturality x)
      ((ringHomSquareComparisonLS f g h i sq).naturality _))
    (fun P hP => ?_) M
  · obtain ⟨Y, p, hY, -, hp, -⟩ := CochainComplex.KFlat.exists_kFlat_resolution.{u, u} X
    exact ⟨Y, hY, p, hp⟩
  · exact model_point_chase
      (Stacks.Injectives.grothendieckModelEquiv.{u} (ModuleCat.{u} R')).functor
      (ModuleCat.restrictScalars.{u} i).mapDerivedCategory
      (Stacks.Injectives.grothendieckModelEquiv.{u} (ModuleCat.{u} A')).functor
      (@Functor.mapDerivedCategory _ _ _ (HasDerivedCategory.standard _) _ _ _
        (HasDerivedCategory.standard _) (ModuleCat.restrictScalars.{u} i) _ _ _)
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u, u, u}
        g).functor
      (Stacks.Injectives.grothendieckModelEquiv.{u} (ModuleCat.{u} R)).functor
      (@CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.functor.{u, u, u}
        R R' _ _ g (HasDerivedCategory.standard _) (HasDerivedCategory.standard _)
        (@CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} R R' _ _ g
          (HasDerivedCategory.standard _) (HasDerivedCategory.standard _)))
      _ _ _ _ _ _ (ringHomSquareComparison_app_comp_counit f g h i sq P)
      _ _ _ _ _ _ (ringHomSquareComparisonLS_app_comp_counit f g h i sq P)
      _ (totalDerivedExtensionScalarsModelIso_hom_app_comparison' h P)
      _ _ (totalDerivedExtensionScalarsModelIso_hom_app_comparison' g _)
      ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsModelIso
        g).hom.naturality _)
      _ _ (restrictScalarsMapDerivedCategoryModelIso_hom_app_factors i _)
      ((restrictScalarsMapDerivedCategoryModelIso i).hom.naturality _)
      _ (restrictScalarsMapDerivedCategoryModelIso_hom_app_factors f P)
      (congrArg (fun t => DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex t (ComplexShape.up ℤ)).app P))
        (ringHomSquareComparisonData_fst f g h i sq))
      (@IsIso.comp_isIso _ _ _ _ _ _ _
        (@Functor.map_isIso _ _ _ _ _ _ _ _
          ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u, u, u}
            h).comparison_isIso_of_kFlat P hP))
        (((ModuleCat.restrictScalars.{u} i).mapDerivedCategoryFactors.app _).isIso_hom))


/-- **Stacks 065Z does not depend on the model**: the comparison at the locally small model
followed by a morphism transported from the standard model is invertible exactly when the
comparison at the standard model followed by that morphism is. -/
theorem isIso_ringHomSquareComparisonLS_comp_iff
    (M : @DerivedCategory (ModuleCat.{u} A) _ _ (HasDerivedCategory.standard _))
    (M' : @DerivedCategory (ModuleCat.{u} A') _ _ (HasDerivedCategory.standard _))
    (x : (@CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars.functor.{u, u, u}
        A A' _ _ h (HasDerivedCategory.standard _) (HasDerivedCategory.standard _)
        (@CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} A A' _ _ h
          (HasDerivedCategory.standard _) (HasDerivedCategory.standard _))).obj M ⟶ M') :
    IsIso ((ringHomSquareComparisonLS f g h i sq).app
        ((Stacks.Injectives.grothendieckModelEquiv.{u} (ModuleCat.{u} A)).functor.obj M) ≫
        (ModuleCat.restrictScalars.{u} i).mapDerivedCategory.map
          ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsModelIso h).inv.app
              M ≫
            (Stacks.Injectives.grothendieckModelEquiv.{u} (ModuleCat.{u} A')).functor.map x)) ↔
      IsIso ((ringHomSquareComparison f g h i sq).app M ≫
        (@Functor.mapDerivedCategory _ _ _ (HasDerivedCategory.standard _) _ _ _
          (HasDerivedCategory.standard _) (ModuleCat.restrictScalars.{u} i) _ _ _).map x) :=
  isIso_model_iff (Stacks.Injectives.grothendieckModelEquiv.{u} (ModuleCat.{u} R')).functor
    (ModuleCat.restrictScalars.{u} i).mapDerivedCategory
    (Stacks.Injectives.grothendieckModelEquiv.{u} (ModuleCat.{u} A')).functor
    (@Functor.mapDerivedCategory _ _ _ (HasDerivedCategory.standard _) _ _ _
        (HasDerivedCategory.standard _) (ModuleCat.restrictScalars.{u} i) _ _ _)
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u, u, u}
      g).functor _ _ _ _ _ _
    ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsModelIso h).app M) x
    ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsModelIso g).app
      _).isIso_hom
    ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u, u, u}
      g).functor.mapIso
      ((restrictScalarsMapDerivedCategoryModelIso f).app M)).isIso_hom
    ((restrictScalarsMapDerivedCategoryModelIso i).app _).isIso_hom
    (ringHomSquareComparison_model f g h i sq M)
    ((restrictScalarsMapDerivedCategoryModelIso i).hom.naturality x)

end Models

end RingTheory.TorIndependence
