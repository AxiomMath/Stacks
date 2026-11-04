module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineChartSourceComparison
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.Limits.PseudoCoherent

/-!
# The composition isomorphism of derived extension of scalars, conjugated

For ring maps `f : A →+* B` and `g : B →+* C`, derived extension of scalars along `f` and then
`g` is identified with derived extension along `g ∘ f` by
`CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp`, and derived restriction
along `g` and then `f` with derived restriction along `g ∘ f` by
`StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp`, the localization of the degreewise
identity. This file shows that the second is the conjugate of the inverse of the first, under the
derived change-of-rings adjunctions: the two identifications correspond under adjunction.

This is what lets the composition law of base change maps of derived global sections, stated
with `totalDerivedExtensionScalarsComp`, be read against the transitions of a tower restricted
along a tower of rings, as in [Stacks, Tag 0CQF], which are stated with
`derivedRestrictScalarsComp`.

## Main results

* `RingTheory.TorIndependence.unit_comp_map_totalDerivedExtensionScalarsComp_hom_ofModel`: the
  unit form of the mate relation of `totalDerivedExtensionScalarsComp`, as
  `RingTheory.TorIndependence.unit_comp_map_totalDerivedExtensionScalarsComp_hom`, for derived
  categories of modules in any universe. Its proof is that one, with the private auxiliary
  lemmas of that file as local steps.

* `StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp_eq_mapDerivedCategoryCompNatIso`
* `StacksDraft.DerivedInverseLimit.conjugateEquiv_totalDerivedExtensionScalarsComp_inv`
-/

@[expose] public noncomputable section

section CopiedMate


open CategoryTheory CategoryTheory.Limits
open CochainComplex.DerivedExtensionScalars (totalDerivedExtensionScalars
  totalDerivedExtensionScalarsComp totalDerivedExtensionScalarsComp_comparison
  derivedExtensionScalarsAdjunction)
open scoped TensorProduct ChangeOfRings

universe u w v₁ v₂ v₃ u₁ u₂ u₃


namespace RingTheory.TorIndependence

/-! ### The mate relations of the composition isomorphism for derived extension of scalars -/

section CompMateUniverse

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
  [HasDerivedCategory.{w} (ModuleCat.{u} A)] [HasDerivedCategory.{w} (ModuleCat.{u} B)]
  [HasDerivedCategory.{w} (ModuleCat.{u} C)] (f : A →+* B) (g : B →+* C)

/-- The unit mate relation of the composition isomorphism, as an equality of transformations:
the composite adjunction transported along `Ψ`, then the composition isomorphism, has the unit of
the adjunction along `g ∘ f`. The proof is that of the case `w = u` in
`StacksFrontier/AlgebraicGeometry/BaseChange/TorIndependence/AffineChartSourceComparison.lean`, with
its auxiliary lemmas as local steps. -/
private theorem unit_merge_aux
    (Ψ : (ModuleCat.restrictScalars.{u} g).mapDerivedCategory ⋙
          (ModuleCat.restrictScalars.{u} f).mapDerivedCategory ≅
        (ModuleCat.restrictScalars.{u} (g.comp f)).mapDerivedCategory)
    (hΨ : Ψ = mapDerivedCategoryCompNatIso (ModuleCat.restrictScalars.{u} g)
      (ModuleCat.restrictScalars.{u} f) (ModuleCat.restrictScalars.{u} (g.comp f))
      (ModuleCat.restrictScalarsComp'.{u} f g (g.comp f) rfl).symm) :
    (((@derivedExtensionScalarsAdjunction.{u, u, u, w, w} A B _ _ f _ _
              (totalDerivedExtensionScalars.{u, u, u} f).functor
              (totalDerivedExtensionScalars.{u, u, u} f).comparison
              (totalDerivedExtensionScalars.{u, u, u} f).isLeftDerived).comp
          (@derivedExtensionScalarsAdjunction.{u, u, u, w, w} B C _ _ g _ _
            (totalDerivedExtensionScalars.{u, u, u} g).functor
            (totalDerivedExtensionScalars.{u, u, u} g).comparison
            (totalDerivedExtensionScalars.{u, u, u} g).isLeftDerived)).ofNatIsoRight Ψ).unit ≫
        Functor.whiskerRight (totalDerivedExtensionScalarsComp.{u, u} f g).hom
          (ModuleCat.restrictScalars.{u} (g.comp f)).mapDerivedCategory =
      (@derivedExtensionScalarsAdjunction.{u, u, u, w, w} A C _ _ (g.comp f) _ _
        (totalDerivedExtensionScalars.{u, u, u} (g.comp f)).functor
        (totalDerivedExtensionScalars.{u, u, u} (g.comp f)).comparison
        (totalDerivedExtensionScalars.{u, u, u} (g.comp f)).isLeftDerived).unit := by
  -- the chase of the unit mate relation through the three localizations
  have chase : ∀ {K₀ K₁ K₂ D₀ D₁ D₂ : Type (u + 1)} [Category.{u} K₀] [Category.{u} K₁]
        [Category.{u} K₂] [Category.{w} D₀] [Category.{w} D₁] [Category.{w} D₂]
        (Q₀ : K₀ ⥤ D₀) (Q₁ : K₁ ⥤ D₁)
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
        (H6 : Eg.map cf ≫ cg ≫ Q₂.map c = tc ≫ cc),
        ηf ≫ Rf.map (ηg.app (Ef.obj (Q₀.obj P))) ≫
            Ψ.hom.app (Eg.obj (Ef.obj (Q₀.obj P))) ≫ Rc.map tc ≫ Rc.map cc =
          ηc ≫ Rc.map cc := by
    intro K₀ K₁ K₂ D₀ D₁ D₂ _ _ _ _ _ _ Q₀ Q₁ Q₂ Ef Eg Rf Rg Rc resf resg resc Ff Fg Fc Ψ ηg P XF XH
      XG Y ηf ηc cf cg cc tc c uf ug uc ecx H1 H2 H3 H4 H5 H6
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
  -- the unit mate relation of `ModuleCat.extendScalarsComp`, on a module and on a complex
  have hmod : ∀ M : ModuleCat.{u} A,
      (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).unit.app M ≫
          (ModuleCat.restrictScalars.{u} f).map
              ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} g).unit.app
                  ((ModuleCat.extendScalars.{u, u, u} f).obj M) ≫
                (ModuleCat.restrictScalars.{u} g).map
                  ((ModuleCat.extendScalarsComp.{u, u} f g).inv.app M)) ≫
            (ModuleCat.restrictScalarsComp'.{u} f g (g.comp f) rfl).inv.app
              ((ModuleCat.extendScalars.{u, u, u} (g.comp f)).obj M) =
        (ModuleCat.extendRestrictScalarsAdj.{u, u, u} (g.comp f)).unit.app M := by
    intro M
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
    simp only [Functor.map_comp, Category.assoc, hnat]
    rw [reassoc_of% hM, ← Functor.map_comp, Iso.hom_inv_id_app,
      CategoryTheory.Functor.map_id, Category.comp_id]
  have hobj : ∀ P : CochainComplex (ModuleCat.{u} A) ℤ,
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
    intro P
    ext i : 1
    exact hmod (P.X i)
  -- the unit of the composite adjunction, transported along the merge
  have hU : ∀ {C₀ C₁ C₂ : Type (u + 1)} [Category.{w} C₀] [Category.{w} C₁] [Category.{w} C₂]
      {E₁ : C₀ ⥤ C₁} {R₁ : C₁ ⥤ C₀} {E₂ : C₁ ⥤ C₂} {R₂ : C₂ ⥤ C₁} {Rc : C₂ ⥤ C₀}
      (adj₁ : E₁ ⊣ R₁) (adj₂ : E₂ ⊣ R₂) (Ψ : R₂ ⋙ R₁ ≅ Rc) (X : C₀),
      ((adj₁.comp adj₂).ofNatIsoRight Ψ).unit.app X =
        adj₁.unit.app X ≫ R₁.map (adj₂.unit.app (E₁.obj X)) ≫
          Ψ.hom.app (E₂.obj (E₁.obj X)) := by
    intros
    simp
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
    hU, Functor.associator_inv_app, Category.id_comp, Category.assoc]
  exact chase DerivedCategory.Q DerivedCategory.Q DerivedCategory.Q
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
    (@derivedExtensionScalarsAdjunction.{u, u, u, w, w} B C _ _ g _ _
      (totalDerivedExtensionScalars.{u, u, u} g).functor
      (totalDerivedExtensionScalars.{u, u, u} g).comparison
      (totalDerivedExtensionScalars.{u, u, u} g).isLeftDerived).unit _ _ _ _ _ _ _ _ _ _ _
    (@CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction_unit_app.{u, u, u,
        w, w} B C _ _ g _ _ (totalDerivedExtensionScalars.{u, u, u} g).functor
      (totalDerivedExtensionScalars.{u, u, u} g).comparison
      (totalDerivedExtensionScalars.{u, u, u} g).isLeftDerived
      (((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P))
    (@CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction_unit_app.{u, u, u,
        w, w} A B _ _ f _ _ (totalDerivedExtensionScalars.{u, u, u} f).functor
      (totalDerivedExtensionScalars.{u, u, u} f).comparison
      (totalDerivedExtensionScalars.{u, u, u} f).isLeftDerived P)
    (@CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction_unit_app.{u, u, u,
        w, w} A C _ _ (g.comp f) _ _
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
    (hobj P)
    (totalDerivedExtensionScalarsComp_comparison.{u, u} f g P)

/-- **The unit form of the mate relation of the composition isomorphism for derived extension of
scalars**, for derived categories of modules in any universe `w` (in particular at
`HasDerivedCategory.standard`); `unit_comp_map_totalDerivedExtensionScalarsComp_hom` is the case
`w = u`. The unit of the derived change-of-rings adjunction along `f`, then — restricted along
`f` — the unit along `g` followed by the composition isomorphism
`CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp` restricted along `g`,
and finally the merge `Ψ` of the two restrictions of scalars, is the unit along `g ∘ f`.

Derived extension along `f` and then along `g` is left adjoint to derived restriction along `g`
and then along `f`, which `Ψ` identifies with derived restriction along `g ∘ f`; so that
composite adjunction and the adjunction along `g ∘ f` have the same right adjoint, and this says
that the composition isomorphism is the identification of their left adjoints given by
`CategoryTheory.Adjunction.leftAdjointUniq`. -/
public theorem unit_comp_map_totalDerivedExtensionScalarsComp_hom_ofModel
    (Ψ : (ModuleCat.restrictScalars.{u} g).mapDerivedCategory ⋙
          (ModuleCat.restrictScalars.{u} f).mapDerivedCategory ≅
        (ModuleCat.restrictScalars.{u} (g.comp f)).mapDerivedCategory)
    (hΨ : Ψ = mapDerivedCategoryCompNatIso (ModuleCat.restrictScalars.{u} g)
      (ModuleCat.restrictScalars.{u} f) (ModuleCat.restrictScalars.{u} (g.comp f))
      (ModuleCat.restrictScalarsComp'.{u} f g (g.comp f) rfl).symm)
    (P : DerivedCategory (ModuleCat.{u} A)) :
    (@derivedExtensionScalarsAdjunction.{u, u, u, w, w} A B _ _ f _ _
            (totalDerivedExtensionScalars.{u, u, u} f).functor
            (totalDerivedExtensionScalars.{u, u, u} f).comparison
            (totalDerivedExtensionScalars.{u, u, u} f).isLeftDerived).unit.app P ≫
        (ModuleCat.restrictScalars.{u} f).mapDerivedCategory.map
            ((@derivedExtensionScalarsAdjunction.{u, u, u, w, w} B C _ _ g _ _
                    (totalDerivedExtensionScalars.{u, u, u} g).functor
                    (totalDerivedExtensionScalars.{u, u, u} g).comparison
                    (totalDerivedExtensionScalars.{u, u, u} g).isLeftDerived).unit.app
                  ((totalDerivedExtensionScalars.{u, u, u} f).functor.obj P) ≫
                (ModuleCat.restrictScalars.{u} g).mapDerivedCategory.map
                  ((totalDerivedExtensionScalarsComp.{u, u} f g).hom.app P)) ≫
          Ψ.hom.app ((totalDerivedExtensionScalars.{u, u, u} (g.comp f)).functor.obj P) =
      (@derivedExtensionScalarsAdjunction.{u, u, u, w, w} A C _ _ (g.comp f) _ _
        (totalDerivedExtensionScalars.{u, u, u} (g.comp f)).functor
        (totalDerivedExtensionScalars.{u, u, u} (g.comp f)).comparison
        (totalDerivedExtensionScalars.{u, u, u} (g.comp f)).isLeftDerived).unit.app P := by
  have hU : ∀ {C₀ C₁ C₂ : Type (u + 1)} [Category.{w} C₀] [Category.{w} C₁] [Category.{w} C₂]
      {E₁ : C₀ ⥤ C₁} {R₁ : C₁ ⥤ C₀} {E₂ : C₁ ⥤ C₂} {R₂ : C₂ ⥤ C₁} {Ec : C₀ ⥤ C₂} {Rc : C₂ ⥤ C₀}
      (adj₁ : E₁ ⊣ R₁) (adj₂ : E₂ ⊣ R₂) (adjc : Ec ⊣ Rc) (Ψ : R₂ ⋙ R₁ ≅ Rc)
      (γ : E₁ ⋙ E₂ ⟶ Ec)
      (h : ((adj₁.comp adj₂).ofNatIsoRight Ψ).unit ≫ Functor.whiskerRight γ Rc = adjc.unit)
      (X : C₀), adj₁.unit.app X ≫ R₁.map (adj₂.unit.app (E₁.obj X) ≫ R₂.map (γ.app X)) ≫
        Ψ.hom.app (Ec.obj X) = adjc.unit.app X := by
    intro C₀ C₁ C₂ _ _ _ E₁ R₁ E₂ R₂ Ec Rc adj₁ adj₂ adjc Ψ γ h X
    have hn := Ψ.hom.naturality (γ.app X)
    dsimp only [Functor.comp_obj, Functor.comp_map] at hn
    rw [CategoryTheory.Functor.map_comp_assoc, hn]
    have hX := NatTrans.congr_app h X
    simp only [NatTrans.comp_app, Functor.whiskerRight_app] at hX
    simpa using hX
  exact hU _ _ _ Ψ (totalDerivedExtensionScalarsComp.{u, u} f g).hom (unit_merge_aux f g Ψ hΨ) P

end CompMateUniverse

end RingTheory.TorIndependence

end CopiedMate


open CategoryTheory

open CochainComplex.DerivedExtensionScalars (totalDerivedExtensionScalars
  totalDerivedExtensionScalarsComp derivedExtensionScalarsAdjunction)

namespace StacksDraft.DerivedInverseLimit

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C)

/-- `derivedRestrictScalarsComp` is `mapDerivedCategoryCompNatIso` of the degreewise identity. -/
theorem derivedRestrictScalarsComp_eq_mapDerivedCategoryCompNatIso :
    derivedRestrictScalarsComp.{u, u} f g (g.comp f) rfl =
      RingTheory.TorIndependence.mapDerivedCategoryCompNatIso (ModuleCat.restrictScalars.{u} g)
        (ModuleCat.restrictScalars.{u} f) (ModuleCat.restrictScalars.{u} (g.comp f))
        (ModuleCat.restrictScalarsComp'.{u} f g (g.comp f) rfl).symm := by
  ext1
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u} C) (ComplexShape.up ℤ)) fun P => ?_
  rw [RingTheory.TorIndependence.mapDerivedCategoryCompNatIso_hom_app_Q]
  simp [derivedRestrictScalarsComp, Localization.liftNatIso_hom,
    Localization.liftNatTrans_app]

/-- **The conjugate of the composition isomorphism of derived extension of scalars** under the
derived change-of-rings adjunctions is `derivedRestrictScalarsComp`. -/
theorem conjugateEquiv_totalDerivedExtensionScalarsComp_inv :
    conjugateEquiv ((@derivedExtensionScalarsAdjunction A B _ _ f _ _
          (totalDerivedExtensionScalars.{u, u, u} f).functor
          (totalDerivedExtensionScalars.{u, u, u} f).comparison
          (totalDerivedExtensionScalars.{u, u, u} f).isLeftDerived).comp
        (@derivedExtensionScalarsAdjunction B C _ _ g _ _
          (totalDerivedExtensionScalars.{u, u, u} g).functor
          (totalDerivedExtensionScalars.{u, u, u} g).comparison
          (totalDerivedExtensionScalars.{u, u, u} g).isLeftDerived))
      (@derivedExtensionScalarsAdjunction A C _ _ (g.comp f) _ _
          (totalDerivedExtensionScalars.{u, u, u} (g.comp f)).functor
          (totalDerivedExtensionScalars.{u, u, u} (g.comp f)).comparison
          (totalDerivedExtensionScalars.{u, u, u} (g.comp f)).isLeftDerived)
      (totalDerivedExtensionScalarsComp.{u, u} f g).inv =
      (derivedRestrictScalarsComp.{u, u} f g (g.comp f) rfl).hom := by
  rw [derivedRestrictScalarsComp_eq_mapDerivedCategoryCompNatIso]
  set Ψ := RingTheory.TorIndependence.mapDerivedCategoryCompNatIso
    (ModuleCat.restrictScalars.{u} g) (ModuleCat.restrictScalars.{u} f)
    (ModuleCat.restrictScalars.{u} (g.comp f))
    (ModuleCat.restrictScalarsComp'.{u} f g (g.comp f) rfl).symm with hΨ
  have hu :=
    RingTheory.TorIndependence.unit_comp_map_totalDerivedExtensionScalarsComp_hom_ofModel f g Ψ hΨ
  have key : (conjugateEquiv ((@derivedExtensionScalarsAdjunction A B _ _ f _ _
          (totalDerivedExtensionScalars.{u, u, u} f).functor
          (totalDerivedExtensionScalars.{u, u, u} f).comparison
          (totalDerivedExtensionScalars.{u, u, u} f).isLeftDerived).comp
        (@derivedExtensionScalarsAdjunction B C _ _ g _ _
          (totalDerivedExtensionScalars.{u, u, u} g).functor
          (totalDerivedExtensionScalars.{u, u, u} g).comparison
          (totalDerivedExtensionScalars.{u, u, u} g).isLeftDerived))
      (@derivedExtensionScalarsAdjunction A C _ _ (g.comp f) _ _
          (totalDerivedExtensionScalars.{u, u, u} (g.comp f)).functor
          (totalDerivedExtensionScalars.{u, u, u} (g.comp f)).comparison
          (totalDerivedExtensionScalars.{u, u, u} (g.comp f)).isLeftDerived)).symm Ψ.hom =
      (totalDerivedExtensionScalarsComp.{u, u} f g).inv := by
    ext P
    apply ((@derivedExtensionScalarsAdjunction A C _ _ (g.comp f) _ _
          (totalDerivedExtensionScalars.{u, u, u} (g.comp f)).functor
          (totalDerivedExtensionScalars.{u, u, u} (g.comp f)).comparison
          (totalDerivedExtensionScalars.{u, u, u} (g.comp f)).isLeftDerived).homEquiv _ _).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, ← unit_conjugateEquiv_symm,
      Adjunction.comp_unit_app, ← hu P]
    have hn := Ψ.hom.naturality
      ((totalDerivedExtensionScalarsComp.{u, u} f g).hom.app P)
    simp only [Functor.comp_map] at hn
    simp only [Functor.map_comp, Category.assoc]
    rw [reassoc_of% hn, ← Functor.map_comp, Iso.hom_inv_id_app]
    refine (congrArg (fun t => _ ≫ _ ≫ t) ?_).symm
    exact (congrArg (_ ≫ ·) (CategoryTheory.Functor.map_id _ _)).trans (Category.comp_id _)
  rw [← key, Equiv.apply_symm_apply]

end StacksDraft.DerivedInverseLimit
