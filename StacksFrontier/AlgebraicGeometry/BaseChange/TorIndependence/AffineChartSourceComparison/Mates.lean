module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactDerivedHomologyComposition
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsTotalComp
public import StacksFrontier.Homology.Tor.FlatDerivedExtensionScalars
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.BaseChangeTFAEAssembly
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.PointwiseStalkTransport
public import
  StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineChartTargetCornerSpellings
public import StacksFrontier.Homology.Tor.DerivedBaseChangeSquarePasting
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsCompIdentification

/-!
# Mate relations of composition isomorphisms, and the homology comparison around one

The mate relations of a composite of two left adjoints; the mate relations
`RingTheory.TorIndependence.unit_comp_map_totalDerivedExtensionScalarsComp_hom` and
`RingTheory.TorIndependence.totalDerivedExtensionScalarsComp_hom_app_comp_counit` of the composition
isomorphism of derived extension of scalars; and
`CategoryTheory.Functor.mapDerivedCategoryCompNatIso_homologyIso_hom_app`, the compatibility of the
homology comparison of an exact functor with a composition isomorphism `F ⋙ G ≅ H`.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open CochainComplex.DerivedExtensionScalars (totalDerivedExtensionScalars
  totalDerivedExtensionScalarsComp totalDerivedExtensionScalarsComp_comparison
  derivedExtensionScalarsAdjunction)
open scoped TensorProduct ChangeOfRings

universe u w v₁ v₂ v₃ u₁ u₂ u₃

/-! ### The mate relations of a composite of two left adjoints

Let `E₁ ⊣ R₁` and `E₂ ⊣ R₂` be adjunctions and let `Ψ : R₂ ⋙ R₁ ≅ Rc` merge the two right
adjoints. Then `E₁ ⋙ E₂ ⊣ Rc`, so a third adjunction `Ec ⊣ Rc` has the *same* right adjoint and
`CategoryTheory.Adjunction.leftAdjointUniq` identifies `E₁ ⋙ E₂` with `Ec`. A transformation
`γ : E₁ ⋙ E₂ ⟶ Ec` that matches the units is that identification, and its counit mate relation
is `CategoryTheory.Adjunction.leftAdjointUniq_hom_app_counit`. -/

section Mate

variable {C₀ : Type u₁} [Category.{v₁} C₀] {C₁ : Type u₂} [Category.{v₂} C₁]
  {C₂ : Type u₃} [Category.{v₃} C₂] {E₁ : C₀ ⥤ C₁} {R₁ : C₁ ⥤ C₀} {E₂ : C₁ ⥤ C₂} {R₂ : C₂ ⥤ C₁}

/-- The unit of the composite adjunction, transported along a merge of the two right adjoints. -/
private theorem ofNatIsoRight_comp_unit_app {Rc : C₂ ⥤ C₀} (adj₁ : E₁ ⊣ R₁) (adj₂ : E₂ ⊣ R₂)
    (Ψ : R₂ ⋙ R₁ ≅ Rc) (X : C₀) :
    ((adj₁.comp adj₂).ofNatIsoRight Ψ).unit.app X =
      adj₁.unit.app X ≫ R₁.map (adj₂.unit.app (E₁.obj X)) ≫
        Ψ.hom.app (E₂.obj (E₁.obj X)) := by
  simp

/-- The counit of the composite adjunction, transported along a merge of the two right
adjoints. -/
private theorem ofNatIsoRight_comp_counit_app {Rc : C₂ ⥤ C₀} (adj₁ : E₁ ⊣ R₁) (adj₂ : E₂ ⊣ R₂)
    (Ψ : R₂ ⋙ R₁ ≅ Rc) (M : C₂) :
    ((adj₁.comp adj₂).ofNatIsoRight Ψ).counit.app M =
      E₂.map (E₁.map (Ψ.inv.app M) ≫ adj₁.counit.app (R₂.obj M)) ≫ adj₂.counit.app M := by
  simp

/-- **Two left adjoints of one functor, identified by a transformation that matches the
units.** -/
private theorem eq_leftAdjointUniq_hom_of_unit {L₁ L₂ : C₀ ⥤ C₂} {R : C₂ ⥤ C₀} (adj₁ : L₁ ⊣ R)
    (adj₂ : L₂ ⊣ R) (γ : L₁ ⟶ L₂)
    (h : ∀ X, adj₁.unit.app X ≫ R.map (γ.app X) = adj₂.unit.app X) :
    γ = (Adjunction.leftAdjointUniq adj₁ adj₂).hom := by
  ext X
  refine (adj₁.homEquiv X _).injective ?_
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, h X,
    Adjunction.unit_leftAdjointUniq_hom_app]

/-- **The counit mate relation, from the unit mate relation.** -/
private theorem comp_counit_app_of_unit {Ec : C₀ ⥤ C₂} {Rc : C₂ ⥤ C₀} (adj₁ : E₁ ⊣ R₁)
    (adj₂ : E₂ ⊣ R₂) (adjc : Ec ⊣ Rc) (Ψ : R₂ ⋙ R₁ ≅ Rc) (γ : E₁ ⋙ E₂ ⟶ Ec)
    (h : ∀ X, adj₁.unit.app X ≫ R₁.map (adj₂.unit.app (E₁.obj X)) ≫
      Ψ.hom.app (E₂.obj (E₁.obj X)) ≫ Rc.map (γ.app X) = adjc.unit.app X) (M : C₂) :
    γ.app (Rc.obj M) ≫ adjc.counit.app M =
      E₂.map (E₁.map (Ψ.inv.app M) ≫ adj₁.counit.app (R₂.obj M)) ≫ adj₂.counit.app M := by
  have h' : ∀ X, ((adj₁.comp adj₂).ofNatIsoRight Ψ).unit.app X ≫ Rc.map (γ.app X) =
      adjc.unit.app X := fun X => by
    rw [ofNatIsoRight_comp_unit_app]
    simpa only [Category.assoc] using h X
  rw [eq_leftAdjointUniq_hom_of_unit ((adj₁.comp adj₂).ofNatIsoRight Ψ) adjc γ h',
    Adjunction.leftAdjointUniq_hom_app_counit]
  exact ofNatIsoRight_comp_counit_app adj₁ adj₂ Ψ M

/-- **The unit mate relation at an object**, read off the natural-transformation form. -/
private theorem unit_app_of_merge_unit {Ec : C₀ ⥤ C₂} {Rc : C₂ ⥤ C₀} (adj₁ : E₁ ⊣ R₁)
    (adj₂ : E₂ ⊣ R₂) (adjc : Ec ⊣ Rc) (Ψ : R₂ ⋙ R₁ ≅ Rc) (γ : E₁ ⋙ E₂ ⟶ Ec)
    (h : ((adj₁.comp adj₂).ofNatIsoRight Ψ).unit ≫ Functor.whiskerRight γ Rc = adjc.unit)
    (X : C₀) :
    adj₁.unit.app X ≫ R₁.map (adj₂.unit.app (E₁.obj X)) ≫
        Ψ.hom.app (E₂.obj (E₁.obj X)) ≫ Rc.map (γ.app X) = adjc.unit.app X := by
  have hX := NatTrans.congr_app h X
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, ofNatIsoRight_comp_unit_app,
    Category.assoc] at hX
  exact hX

/-- **The unit mate relation with the merge last**: the identification is applied inside the
first right adjoint and the merge closes the composite. -/
private theorem unit_app_merge_form {Ec : C₀ ⥤ C₂} {Rc : C₂ ⥤ C₀} (adj₁ : E₁ ⊣ R₁)
    (adj₂ : E₂ ⊣ R₂) (adjc : Ec ⊣ Rc) (Ψ : R₂ ⋙ R₁ ≅ Rc) (γ : E₁ ⋙ E₂ ⟶ Ec)
    (h : ((adj₁.comp adj₂).ofNatIsoRight Ψ).unit ≫ Functor.whiskerRight γ Rc = adjc.unit)
    (X : C₀) :
    adj₁.unit.app X ≫ R₁.map (adj₂.unit.app (E₁.obj X) ≫ R₂.map (γ.app X)) ≫
        Ψ.hom.app (Ec.obj X) = adjc.unit.app X := by
  have hn := Ψ.hom.naturality (γ.app X)
  dsimp only [Functor.comp_obj, Functor.comp_map] at hn
  rw [CategoryTheory.Functor.map_comp_assoc, hn]
  exact unit_app_of_merge_unit adj₁ adj₂ adjc Ψ γ h X

/-- **The unit mate relation of a composition isomorphism, descended along three localization
functors.** Every category, functor, object and morphism is a variable.

`Q₀`, `Q₁`, `Q₂` are the three localization functors, `Ef`, `Eg` the two derived left adjoints
and `Rf`, `Rg`, `Rc` the three derived right adjoints, which `Ff`, `Fg`, `Fc` factor through the
degreewise ones `resf`, `resg`, `resc` and which `Ψ` merges. `H1`, `H2`, `H3` normalize the three
units on a localized object, `H4` reads the merge there, `H6` is the characterizing factorization
of the composition isomorphism `tc`, and `H5` is the degreewise mate relation. -/
private theorem unit_merge_chase {K₀ K₁ K₂ D₀ D₁ D₂ : Type*} [Category K₀] [Category K₁]
    [Category K₂] [Category D₀] [Category D₁] [Category D₂] (Q₀ : K₀ ⥤ D₀) (Q₁ : K₁ ⥤ D₁)
    (Q₂ : K₂ ⥤ D₂) (Ef : D₀ ⥤ D₁) (Eg : D₁ ⥤ D₂) (Rf : D₁ ⥤ D₀) (Rg : D₂ ⥤ D₁) (Rc : D₂ ⥤ D₀)
    (resf : K₁ ⥤ K₀) (resg : K₂ ⥤ K₁) (resc : K₂ ⥤ K₀) (Ff : Q₁ ⋙ Rf ≅ resf ⋙ Q₀)
    (Fg : Q₂ ⋙ Rg ≅ resg ⋙ Q₁) (Fc : Q₂ ⋙ Rc ≅ resc ⋙ Q₀) (Ψ : Rg ⋙ Rf ≅ Rc)
    (ηg : 𝟭 D₁ ⟶ Eg ⋙ Rg) {P : K₀} {XF : K₁} {XH XG : K₂} {Y : D₂}
    (ηf : Q₀.obj P ⟶ Rf.obj (Ef.obj (Q₀.obj P))) (ηc : Q₀.obj P ⟶ Rc.obj Y)
    (cf : Ef.obj (Q₀.obj P) ⟶ Q₁.obj XF) (cg : Eg.obj (Q₁.obj XF) ⟶ Q₂.obj XH)
    (cc : Y ⟶ Q₂.obj XG) (tc : Eg.obj (Ef.obj (Q₀.obj P)) ⟶ Y) (c : XH ⟶ XG)
    (uf : P ⟶ resf.obj XF) (ug : XF ⟶ resg.obj XH) (uc : P ⟶ resc.obj XG)
    (ecx : resf.obj (resg.obj XG) ⟶ resc.obj XG)
    (H1 : ηg.app (Q₁.obj XF) ≫ Rg.map cg = Q₁.map ug ≫ Fg.inv.app XH)
    (H2 : ηf ≫ Rf.map cf = Q₀.map uf ≫ Ff.inv.app XF)
    (H3 : ηc ≫ Rc.map cc = Q₀.map uc ≫ Fc.inv.app XG)
    (H4 : Ψ.hom.app (Q₂.obj XG) = Rf.map (Fg.hom.app XG) ≫ Ff.hom.app (resg.obj XG) ≫
      Q₀.map ecx ≫ Fc.inv.app XG)
    (H5 : uf ≫ resf.map (ug ≫ resg.map c) ≫ ecx = uc)
    (H6 : Eg.map cf ≫ cg ≫ Q₂.map c = tc ≫ cc) :
    ηf ≫ Rf.map (ηg.app (Ef.obj (Q₀.obj P))) ≫
        Ψ.hom.app (Eg.obj (Ef.obj (Q₀.obj P))) ≫ Rc.map tc ≫ Rc.map cc =
      ηc ≫ Rc.map cc := by
  have hFg := Fg.inv.naturality c
  dsimp only [Functor.comp_obj, Functor.comp_map] at hFg
  have hFf := Ff.inv.naturality (ug ≫ resg.map c)
  dsimp only [Functor.comp_obj, Functor.comp_map] at hFf
  have hΨn := Ψ.hom.naturality (Eg.map cf ≫ cg ≫ Q₂.map c)
  dsimp only [Functor.comp_obj, Functor.comp_map] at hΨn
  have hηg := ηg.naturality cf
  dsimp only [Functor.id_obj, Functor.id_map, Functor.comp_obj, Functor.comp_map] at hηg
  have e1 : ηg.app (Ef.obj (Q₀.obj P)) ≫ Rg.map (Eg.map cf ≫ cg ≫ Q₂.map c) =
      cf ≫ Q₁.map (ug ≫ resg.map c) ≫ Fg.inv.app XG := by
    conv_lhs => rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
    rw [← reassoc_of% hηg, reassoc_of% H1, ← hFg, ← CategoryTheory.Functor.map_comp_assoc]
  have e2 : Rf.map (Fg.inv.app XG) ≫ Ψ.hom.app (Q₂.obj XG) =
      Ff.hom.app (resg.obj XG) ≫ Q₀.map ecx ≫ Fc.inv.app XG := by
    rw [H4, ← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp]
  rw [← CategoryTheory.Functor.map_comp, ← H6, ← hΨn,
    ← CategoryTheory.Functor.map_comp_assoc, e1, CategoryTheory.Functor.map_comp_assoc,
    CategoryTheory.Functor.map_comp_assoc, e2, reassoc_of% H2, ← reassoc_of% hFf,
    Iso.inv_hom_id_app_assoc, ← CategoryTheory.Functor.map_comp_assoc,
    ← CategoryTheory.Functor.map_comp_assoc, Category.assoc, H5, H3]

end Mate

namespace RingTheory.TorIndependence

/-! ### The mate relations of the composition isomorphism for derived extension of scalars -/

section CompMate

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
  [HasDerivedCategory.{u} (ModuleCat.{u} A)] [HasDerivedCategory.{u} (ModuleCat.{u} B)]
  [HasDerivedCategory.{u} (ModuleCat.{u} C)] (f : A →+* B) (g : B →+* C)

omit [HasDerivedCategory (ModuleCat A)] [HasDerivedCategory (ModuleCat B)]
  [HasDerivedCategory (ModuleCat C)] in
/-- **The unit mate relation of `ModuleCat.extendScalarsComp`, on a module.** The unit of
extension–restriction along `f`, the unit along `g` extended, the inverse scalar-tower
isomorphism of extension of scalars and the merge of the two restrictions compose to the unit
along `g ∘ f`. -/
private theorem unit_comp_extendScalarsComp_inv_app (M : ModuleCat.{u} A) :
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).unit.app M ≫
        (ModuleCat.restrictScalars.{u} f).map
            ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} g).unit.app
                ((ModuleCat.extendScalars.{u, u, u} f).obj M) ≫
              (ModuleCat.restrictScalars.{u} g).map
                ((ModuleCat.extendScalarsComp.{u, u} f g).inv.app M)) ≫
          (ModuleCat.restrictScalarsComp'.{u} f g (g.comp f) rfl).inv.app
            ((ModuleCat.extendScalars.{u, u, u} (g.comp f)).obj M) =
      (ModuleCat.extendRestrictScalarsAdj.{u, u, u} (g.comp f)).unit.app M := by
  have hM : (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).unit.app M ≫
        (ModuleCat.restrictScalars.{u} f).map
            ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} g).unit.app
              ((ModuleCat.extendScalars.{u, u, u} f).obj M)) ≫
          (ModuleCat.restrictScalarsComp'.{u} f g (g.comp f) rfl).inv.app
            ((ModuleCat.extendScalars.{u, u, u} g).obj
              ((ModuleCat.extendScalars.{u, u, u} f).obj M)) =
      (ModuleCat.extendRestrictScalarsAdj.{u, u, u} (g.comp f)).unit.app M ≫
        (ModuleCat.restrictScalars.{u} (g.comp f)).map
          ((ModuleCat.extendScalarsComp.{u, u} f g).hom.app M) :=
    (ModuleCat.homEquiv_extendScalarsComp.{u, u} f g M).symm.trans
      (Adjunction.homEquiv_unit _ _ _ _)
  have hnat := (ModuleCat.restrictScalarsComp'.{u} f g (g.comp f) rfl).inv.naturality
    ((ModuleCat.extendScalarsComp.{u, u} f g).inv.app M)
  dsimp only [Functor.comp_obj, Functor.comp_map] at hnat
  have h1 : (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).unit.app M ≫
        (ModuleCat.restrictScalars.{u} f).map
            ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} g).unit.app
                ((ModuleCat.extendScalars.{u, u, u} f).obj M) ≫
              (ModuleCat.restrictScalars.{u} g).map
                ((ModuleCat.extendScalarsComp.{u, u} f g).inv.app M)) ≫
          (ModuleCat.restrictScalarsComp'.{u} f g (g.comp f) rfl).inv.app
            ((ModuleCat.extendScalars.{u, u, u} (g.comp f)).obj M) =
      ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).unit.app M ≫
          (ModuleCat.restrictScalars.{u} f).map
              ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} g).unit.app
                ((ModuleCat.extendScalars.{u, u, u} f).obj M)) ≫
            (ModuleCat.restrictScalarsComp'.{u} f g (g.comp f) rfl).inv.app
              ((ModuleCat.extendScalars.{u, u, u} g).obj
                ((ModuleCat.extendScalars.{u, u, u} f).obj M))) ≫
        (ModuleCat.restrictScalars.{u} (g.comp f)).map
          ((ModuleCat.extendScalarsComp.{u, u} f g).inv.app M) := by
    simp only [Functor.map_comp, Category.assoc, hnat]
  rw [h1, hM, Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id]
  exact Category.comp_id _

omit [HasDerivedCategory (ModuleCat A)] [HasDerivedCategory (ModuleCat B)]
  [HasDerivedCategory (ModuleCat C)] in
/-- **The unit mate relation of `ModuleCat.extendScalarsComp`, on a cochain complex**, for the
degreewise adjunctions of `CategoryTheory.Adjunction.mapHomologicalComplex`. -/
private theorem unit_comp_extendScalarsComp_inv_app_obj
    (P : CochainComplex (ModuleCat.{u} A) ℤ) :
    ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).unit.app P ≫
        ((ModuleCat.restrictScalars.{u} f).mapHomologicalComplex (ComplexShape.up ℤ)).map
            (((ModuleCat.extendRestrictScalarsAdj.{u, u, u} g).mapHomologicalComplex
                  (ComplexShape.up ℤ)).unit.app
                (((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj P) ≫
              ((ModuleCat.restrictScalars.{u} g).mapHomologicalComplex
                  (ComplexShape.up ℤ)).map
                ((NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp.{u, u} f g)
                  (ComplexShape.up ℤ)).inv.app P)) ≫
          (Functor.mapHomologicalComplexCompIso
              (ModuleCat.restrictScalarsComp'.{u} f g (g.comp f) rfl).symm
              (ComplexShape.up ℤ)).hom.app
            (((ModuleCat.extendScalars.{u, u, u} (g.comp f)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P) =
      ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} (g.comp f)).mapHomologicalComplex
        (ComplexShape.up ℤ)).unit.app P := by
  ext i : 1
  exact unit_comp_extendScalarsComp_inv_app f g (P.X i)

private theorem unit_merge_aux
    (Ψ : (ModuleCat.restrictScalars.{u} g).mapDerivedCategory ⋙
          (ModuleCat.restrictScalars.{u} f).mapDerivedCategory ≅
        (ModuleCat.restrictScalars.{u} (g.comp f)).mapDerivedCategory)
    (hΨ : Ψ = mapDerivedCategoryCompNatIso (ModuleCat.restrictScalars.{u} g)
      (ModuleCat.restrictScalars.{u} f) (ModuleCat.restrictScalars.{u} (g.comp f))
      (ModuleCat.restrictScalarsComp'.{u} f g (g.comp f) rfl).symm) :
    (((@derivedExtensionScalarsAdjunction.{u, u, u, u, u} A B _ _ f _ _
              (totalDerivedExtensionScalars.{u, u, u} f).functor
              (totalDerivedExtensionScalars.{u, u, u} f).comparison
              (totalDerivedExtensionScalars.{u, u, u} f).isLeftDerived).comp
          (@derivedExtensionScalarsAdjunction.{u, u, u, u, u} B C _ _ g _ _
            (totalDerivedExtensionScalars.{u, u, u} g).functor
            (totalDerivedExtensionScalars.{u, u, u} g).comparison
            (totalDerivedExtensionScalars.{u, u, u} g).isLeftDerived)).ofNatIsoRight Ψ).unit ≫
        Functor.whiskerRight (totalDerivedExtensionScalarsComp.{u, u} f g).hom
          (ModuleCat.restrictScalars.{u} (g.comp f)).mapDerivedCategory =
      (@derivedExtensionScalarsAdjunction.{u, u, u, u, u} A C _ _ (g.comp f) _ _
        (totalDerivedExtensionScalars.{u, u, u} (g.comp f)).functor
        (totalDerivedExtensionScalars.{u, u, u} (g.comp f)).comparison
        (totalDerivedExtensionScalars.{u, u, u} (g.comp f)).isLeftDerived).unit := by
  let α : DerivedCategory.Q ⋙ (totalDerivedExtensionScalars.{u, u, u} (g.comp f)).functor ⟶
      CochainComplex.extendScalarsLarge.{u, u, u} (g.comp f) ⋙ DerivedCategory.Q :=
    (totalDerivedExtensionScalars.{u, u, u} (g.comp f)).comparison
  have : (totalDerivedExtensionScalars.{u, u, u} (g.comp f)).functor.IsLeftDerivedFunctor α
      (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)) :=
    (totalDerivedExtensionScalars.{u, u, u} (g.comp f)).isLeftDerived
  have :=
    CochainComplex.DerivedTensor.KFlatDerived.isLeftDerivedFunctor_extension_postcomp.{u, u, u}
      (g.comp f) (totalDerivedExtensionScalars.{u, u, u} (g.comp f)).functor α
      (ModuleCat.restrictScalars.{u} (g.comp f)).mapDerivedCategory
  refine Functor.leftDerived_ext
    ((totalDerivedExtensionScalars.{u, u, u} (g.comp f)).functor ⋙
      (ModuleCat.restrictScalars.{u} (g.comp f)).mapDerivedCategory)
    ((Functor.associator DerivedCategory.Q
          (totalDerivedExtensionScalars.{u, u, u} (g.comp f)).functor
          (ModuleCat.restrictScalars.{u} (g.comp f)).mapDerivedCategory).inv ≫
      Functor.whiskerRight α (ModuleCat.restrictScalars.{u} (g.comp f)).mapDerivedCategory)
    (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)) _ _ _ ?_
  have hα : α = (totalDerivedExtensionScalars.{u, u, u} (g.comp f)).comparison := rfl
  ext P
  simp only [hα, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    ofNatIsoRight_comp_unit_app, Functor.associator_inv_app, Category.id_comp, Category.assoc]
  exact unit_merge_chase DerivedCategory.Q DerivedCategory.Q DerivedCategory.Q
    (totalDerivedExtensionScalars.{u, u, u} f).functor
    (totalDerivedExtensionScalars.{u, u, u} g).functor
    (ModuleCat.restrictScalars.{u} f).mapDerivedCategory
    (ModuleCat.restrictScalars.{u} g).mapDerivedCategory
    (ModuleCat.restrictScalars.{u} (g.comp f)).mapDerivedCategory
    ((ModuleCat.restrictScalars.{u} f).mapHomologicalComplex (ComplexShape.up ℤ))
    ((ModuleCat.restrictScalars.{u} g).mapHomologicalComplex (ComplexShape.up ℤ))
    ((ModuleCat.restrictScalars.{u} (g.comp f)).mapHomologicalComplex (ComplexShape.up ℤ))
    (ModuleCat.restrictScalars.{u} f).mapDerivedCategoryFactors
    (ModuleCat.restrictScalars.{u} g).mapDerivedCategoryFactors
    (ModuleCat.restrictScalars.{u} (g.comp f)).mapDerivedCategoryFactors Ψ
    (@derivedExtensionScalarsAdjunction.{u, u, u, u, u} B C _ _ g _ _
      (totalDerivedExtensionScalars.{u, u, u} g).functor
      (totalDerivedExtensionScalars.{u, u, u} g).comparison
      (totalDerivedExtensionScalars.{u, u, u} g).isLeftDerived).unit _ _ _ _ _ _ _ _ _ _ _
    (@CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction_unit_app.{u, u, u,
        u, u} B C _ _ g _ _ (totalDerivedExtensionScalars.{u, u, u} g).functor
      (totalDerivedExtensionScalars.{u, u, u} g).comparison
      (totalDerivedExtensionScalars.{u, u, u} g).isLeftDerived
      (((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P))
    (@CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction_unit_app.{u, u, u,
        u, u} A B _ _ f _ _ (totalDerivedExtensionScalars.{u, u, u} f).functor
      (totalDerivedExtensionScalars.{u, u, u} f).comparison
      (totalDerivedExtensionScalars.{u, u, u} f).isLeftDerived P)
    (@CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction_unit_app.{u, u, u,
        u, u} A C _ _ (g.comp f) _ _
      (totalDerivedExtensionScalars.{u, u, u} (g.comp f)).functor
      (totalDerivedExtensionScalars.{u, u, u} (g.comp f)).comparison
      (totalDerivedExtensionScalars.{u, u, u} (g.comp f)).isLeftDerived P)
    (by
      rw [hΨ]
      exact mapDerivedCategoryCompNatIso_hom_app_Q (ModuleCat.restrictScalars.{u} g)
        (ModuleCat.restrictScalars.{u} f) (ModuleCat.restrictScalars.{u} (g.comp f))
        (ModuleCat.restrictScalarsComp'.{u} f g (g.comp f) rfl).symm
        (((ModuleCat.extendScalars.{u, u, u} (g.comp f)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P))
    (unit_comp_extendScalarsComp_inv_app_obj f g P)
    (totalDerivedExtensionScalarsComp_comparison.{u, u} f g P)

/-- **The unit form of the mate relation of the composition isomorphism for derived extension of
scalars.** The unit of the derived change-of-rings adjunction along `f`, then — restricted along
`f` — the unit along `g` followed by the composition isomorphism
`CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp` restricted along `g`,
and finally the merge `Ψ` of the two restrictions of scalars, is the unit along `g ∘ f`.

Derived extension along `f` and then along `g` is left adjoint to derived restriction along `g`
and then along `f`, which `Ψ` identifies with derived restriction along `g ∘ f`; so that
composite adjunction and the adjunction along `g ∘ f` have the same right adjoint, and this says
that the composition isomorphism is the identification of their left adjoints given by
`CategoryTheory.Adjunction.leftAdjointUniq`. -/
public theorem unit_comp_map_totalDerivedExtensionScalarsComp_hom
    (Ψ : (ModuleCat.restrictScalars.{u} g).mapDerivedCategory ⋙
          (ModuleCat.restrictScalars.{u} f).mapDerivedCategory ≅
        (ModuleCat.restrictScalars.{u} (g.comp f)).mapDerivedCategory)
    (hΨ : Ψ = mapDerivedCategoryCompNatIso (ModuleCat.restrictScalars.{u} g)
      (ModuleCat.restrictScalars.{u} f) (ModuleCat.restrictScalars.{u} (g.comp f))
      (ModuleCat.restrictScalarsComp'.{u} f g (g.comp f) rfl).symm)
    (P : DerivedCategory (ModuleCat.{u} A)) :
    (@derivedExtensionScalarsAdjunction.{u, u, u, u, u} A B _ _ f _ _
            (totalDerivedExtensionScalars.{u, u, u} f).functor
            (totalDerivedExtensionScalars.{u, u, u} f).comparison
            (totalDerivedExtensionScalars.{u, u, u} f).isLeftDerived).unit.app P ≫
        (ModuleCat.restrictScalars.{u} f).mapDerivedCategory.map
            ((@derivedExtensionScalarsAdjunction.{u, u, u, u, u} B C _ _ g _ _
                    (totalDerivedExtensionScalars.{u, u, u} g).functor
                    (totalDerivedExtensionScalars.{u, u, u} g).comparison
                    (totalDerivedExtensionScalars.{u, u, u} g).isLeftDerived).unit.app
                  ((totalDerivedExtensionScalars.{u, u, u} f).functor.obj P) ≫
                (ModuleCat.restrictScalars.{u} g).mapDerivedCategory.map
                  ((totalDerivedExtensionScalarsComp.{u, u} f g).hom.app P)) ≫
          Ψ.hom.app ((totalDerivedExtensionScalars.{u, u, u} (g.comp f)).functor.obj P) =
      (@derivedExtensionScalarsAdjunction.{u, u, u, u, u} A C _ _ (g.comp f) _ _
        (totalDerivedExtensionScalars.{u, u, u} (g.comp f)).functor
        (totalDerivedExtensionScalars.{u, u, u} (g.comp f)).comparison
        (totalDerivedExtensionScalars.{u, u, u} (g.comp f)).isLeftDerived).unit.app P :=
  unit_app_merge_form _ _ _ Ψ (totalDerivedExtensionScalarsComp.{u, u} f g).hom
    (unit_merge_aux f g Ψ hΨ) P

/-- **The counit form of the mate relation of the composition isomorphism for derived extension
of scalars.** The composition isomorphism at the restriction of `M` along `g ∘ f`, followed by
the counit along `g ∘ f`, is the merge `Ψ` read backwards and extended twice, then the counit
along `f` extended along `g`, then the counit along `g`. -/
public theorem totalDerivedExtensionScalarsComp_hom_app_comp_counit
    (Ψ : (ModuleCat.restrictScalars.{u} g).mapDerivedCategory ⋙
          (ModuleCat.restrictScalars.{u} f).mapDerivedCategory ≅
        (ModuleCat.restrictScalars.{u} (g.comp f)).mapDerivedCategory)
    (hΨ : Ψ = mapDerivedCategoryCompNatIso (ModuleCat.restrictScalars.{u} g)
      (ModuleCat.restrictScalars.{u} f) (ModuleCat.restrictScalars.{u} (g.comp f))
      (ModuleCat.restrictScalarsComp'.{u} f g (g.comp f) rfl).symm)
    (M : DerivedCategory (ModuleCat.{u} C)) :
    (totalDerivedExtensionScalarsComp.{u, u} f g).hom.app
          ((ModuleCat.restrictScalars.{u} (g.comp f)).mapDerivedCategory.obj M) ≫
        (@derivedExtensionScalarsAdjunction.{u, u, u, u, u} A C _ _ (g.comp f) _ _
          (totalDerivedExtensionScalars.{u, u, u} (g.comp f)).functor
          (totalDerivedExtensionScalars.{u, u, u} (g.comp f)).comparison
          (totalDerivedExtensionScalars.{u, u, u} (g.comp f)).isLeftDerived).counit.app M =
      (totalDerivedExtensionScalars.{u, u, u} g).functor.map
          ((totalDerivedExtensionScalars.{u, u, u} f).functor.map (Ψ.inv.app M) ≫
            (@derivedExtensionScalarsAdjunction.{u, u, u, u, u} A B _ _ f _ _
                (totalDerivedExtensionScalars.{u, u, u} f).functor
                (totalDerivedExtensionScalars.{u, u, u} f).comparison
                (totalDerivedExtensionScalars.{u, u, u} f).isLeftDerived).counit.app
              ((ModuleCat.restrictScalars.{u} g).mapDerivedCategory.obj M)) ≫
        (@derivedExtensionScalarsAdjunction.{u, u, u, u, u} B C _ _ g _ _
          (totalDerivedExtensionScalars.{u, u, u} g).functor
          (totalDerivedExtensionScalars.{u, u, u} g).comparison
          (totalDerivedExtensionScalars.{u, u, u} g).isLeftDerived).counit.app M :=
  comp_counit_app_of_unit _ _ _ Ψ (totalDerivedExtensionScalarsComp.{u, u} f g).hom
    (fun X => unit_app_of_merge_unit _ _ _ Ψ _ (unit_merge_aux f g Ψ hΨ) X) M

end CompMate

end RingTheory.TorIndependence

/-! ### The homology comparison of an exact functor, around a composition isomorphism -/

section HomologyComposition

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂]
  {C₃ : Type u₃} [Category.{v₃} C₃] [Abelian C₃]

/-- **The homology comparison of an exact functor is compatible with a composition isomorphism,
on a short complex.** The comparison for `G` at `S.map F`, followed by `G` applied to the
comparison for `F` and then by `e`, is the homology map of `e` followed by the comparison
for `H`. -/
private theorem mapHomologyIso_compNatIso_hom (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃) (H : C₁ ⥤ C₃)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (e : F ⋙ G ≅ H) (S : ShortComplex C₁) :
    ((S.map F).mapHomologyIso G).hom ≫ G.map (S.mapHomologyIso F).hom ≫
        e.hom.app S.homology =
      ShortComplex.homologyMap (S.mapNatTrans e.hom) ≫ (S.mapHomologyIso H).hom := by
  rw [ShortComplex.homologyMap_mapNatTrans, ← Stacks.Homology.mapHomologyIso_comp_hom F G S]
  simp

/-- **`mapHomologyIso_compNatIso_hom` on cochain complexes**, at the component of
`CategoryTheory.Functor.mapHomologicalComplexHomologyIso` at `K` in degree `n`. -/
private theorem mapHomologicalComplexHomologyIso_compNatIso_hom_app
    (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃) (H : C₁ ⥤ C₃)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (e : F ⋙ G ≅ H) (n : ℤ) (K : CochainComplex C₁ ℤ) :
    (G.mapHomologicalComplexHomologyIso (ComplexShape.up ℤ) n).hom.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        G.map ((F.mapHomologicalComplexHomologyIso (ComplexShape.up ℤ) n).hom.app K) ≫
          e.hom.app ((HomologicalComplex.homologyFunctor C₁ (ComplexShape.up ℤ) n).obj K) =
      (HomologicalComplex.homologyFunctor C₃ (ComplexShape.up ℤ) n).map
          ((Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ)).hom.app K) ≫
        (H.mapHomologicalComplexHomologyIso (ComplexShape.up ℤ) n).hom.app K :=
  mapHomologyIso_compNatIso_hom F G H e (K.sc n)

section Derived

variable [HasDerivedCategory.{w} C₁] [HasDerivedCategory.{w} C₂] [HasDerivedCategory.{w} C₃]

/-- **The component of `CategoryTheory.Functor.mapDerivedCategoryHomologyIso` on the image of the
localization.** It is the comparison on complexes, conjugated by the factorizations of the
degreewise action of `F` and of the homology functors through the category of complexes. -/
private theorem mapDerivedCategoryHomologyIso_hom_app_Q (F : C₁ ⥤ C₂) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (n : ℤ) (K : CochainComplex C₁ ℤ) :
    (F.mapDerivedCategoryHomologyIso n).hom.app (DerivedCategory.Q.obj K) =
      (DerivedCategory.homologyFunctor C₂ n).map (F.mapDerivedCategoryFactors.hom.app K) ≫
        (DerivedCategory.homologyFunctorFactors C₂ n).hom.app
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
          (F.mapHomologicalComplexHomologyIso (ComplexShape.up ℤ) n).hom.app K ≫
            F.map ((DerivedCategory.homologyFunctorFactors C₁ n).inv.app K) := by
  simp only [Functor.mapDerivedCategoryHomologyIso, Functor.mapDerivedCategoryHomologyIsoAux,
    Localization.liftNatIso_hom, Localization.liftNatTrans_app,
    Localization.Lifting.compLeft_iso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Iso.refl_inv, NatTrans.id_app,
    Category.id_comp, Category.comp_id, Localization.Lifting.compRight_iso]
  rfl

variable (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃) (H : C₁ ⥤ C₃)
  [F.Additive] [G.Additive] [H.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]

/-- **The composition law of `CategoryTheory.Functor.mapDerivedCategoryHomologyIso` on the image
of the localization.** -/
private theorem mapDerivedCategoryCompNatIso_homologyIso_hom_app_Q
    (e : F ⋙ G ≅ H) (n : ℤ) (K : CochainComplex C₁ ℤ) :
    (G.mapDerivedCategoryHomologyIso n).hom.app
          (F.mapDerivedCategory.obj (DerivedCategory.Q.obj K)) ≫
        G.map ((F.mapDerivedCategoryHomologyIso n).hom.app (DerivedCategory.Q.obj K)) ≫
          e.hom.app ((DerivedCategory.homologyFunctor C₁ n).obj (DerivedCategory.Q.obj K)) =
      (DerivedCategory.homologyFunctor C₃ n).map
          ((RingTheory.TorIndependence.mapDerivedCategoryCompNatIso F G H e).hom.app
            (DerivedCategory.Q.obj K)) ≫
        (H.mapDerivedCategoryHomologyIso n).hom.app (DerivedCategory.Q.obj K) := by
  have N1 := (G.mapDerivedCategoryHomologyIso n).hom.naturality
    (F.mapDerivedCategoryFactors.hom.app K)
  rw [mapDerivedCategoryHomologyIso_hom_app_Q F n K,
    mapDerivedCategoryHomologyIso_hom_app_Q H n K,
    RingTheory.TorIndependence.mapDerivedCategoryCompNatIso_hom_app_Q F G H e K]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [← reassoc_of% N1, mapDerivedCategoryHomologyIso_hom_app_Q G n
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)]
  simp only [Category.assoc]
  erw [Iso.inv_hom_id_map_assoc (H.mapDerivedCategoryFactors.app K)
      (DerivedCategory.homologyFunctor C₃ n),
    Iso.inv_hom_id_map_assoc ((DerivedCategory.homologyFunctorFactors C₂ n).app _) G]
  have hnat_e := e.hom.naturality ((DerivedCategory.homologyFunctorFactors C₁ n).inv.app K)
  have hnat_ff := (DerivedCategory.homologyFunctorFactors C₃ n).hom.naturality
    ((Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ)).hom.app K)
  simp only [Functor.comp_map, Functor.comp_obj] at hnat_e hnat_ff
  rw [reassoc_of% hnat_ff, hnat_e,
    reassoc_of% mapHomologicalComplexHomologyIso_compNatIso_hom_app F G H e n K]

/-- **The homology comparison of an exact functor is compatible with a composition isomorphism
`F ⋙ G ≅ H`, on the derived category.** The comparison for `G`, followed by `G` of the
comparison for `F` and then by `e`, is the cohomology of
`RingTheory.TorIndependence.mapDerivedCategoryCompNatIso` followed by the comparison for `H`. -/
public theorem mapDerivedCategoryCompNatIso_homologyIso_hom_app
    (e : F ⋙ G ≅ H) (n : ℤ) (X : DerivedCategory C₁) :
    (G.mapDerivedCategoryHomologyIso n).hom.app (F.mapDerivedCategory.obj X) ≫
        G.map ((F.mapDerivedCategoryHomologyIso n).hom.app X) ≫
          e.hom.app ((DerivedCategory.homologyFunctor C₁ n).obj X) =
      (DerivedCategory.homologyFunctor C₃ n).map
          ((RingTheory.TorIndependence.mapDerivedCategoryCompNatIso F G H e).hom.app X) ≫
        (H.mapDerivedCategoryHomologyIso n).hom.app X := by
  have key : Functor.whiskerLeft F.mapDerivedCategory
          (G.mapDerivedCategoryHomologyIso n).hom ≫
        Functor.whiskerRight (F.mapDerivedCategoryHomologyIso n).hom G ≫
          Functor.whiskerLeft (DerivedCategory.homologyFunctor C₁ n) e.hom =
      Functor.whiskerRight
          (RingTheory.TorIndependence.mapDerivedCategoryCompNatIso F G H e).hom
          (DerivedCategory.homologyFunctor C₃ n) ≫
        (H.mapDerivedCategoryHomologyIso n).hom := by
    refine Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ)) (fun K => ?_)
    dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    exact mapDerivedCategoryCompNatIso_homologyIso_hom_app_Q F G H e n K
  exact NatTrans.congr_app key X

end Derived

end HomologyComposition

end
