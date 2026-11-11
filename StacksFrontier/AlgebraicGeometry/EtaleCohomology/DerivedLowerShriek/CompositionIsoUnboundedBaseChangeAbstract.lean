module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived

/-!
# Comparisons of right derived functors and base change, for abstract categories

The identities of transformations of functors on derived categories that the compatibility of
the isomorphism `R(g ∘ f)_! ≅ Rg_! ∘ Rf_!` of [Stacks, Tag 0F7J] with base change, on
unbounded derived categories, reduces to. Each is stated for abstract categories and functors, so
that the kernel never reduces the functors of étale sheaves they are applied to.

A *comparison* of a right derived functor `RP` of `P` with base change is a transformation
`b : RP ⋙ GD ⟶ GD' ⋙ RP'` determined, through the universal property of `RP`, by a comparison
`c : P ⋙ G ⟶ G' ⋙ P'` of the underlying functors: its value after the derived-functor unit of
`RP` is `c`, read through the derived-functor unit of `RP'` and the comparisons `Φ` of the
localizations.

## Main results

* `Stacks.EtaleCohomology.DerivedComparisonPaste.comparison_comp`: comparisons of right derived
  functors compose.
* `Stacks.EtaleCohomology.DerivedComparisonPaste.comparison_rightDerivedUnique`: comparisons are
  compatible with the identification of two right derived functors of isomorphic functors.
* `Stacks.EtaleCohomology.DerivedComparisonPaste.mapDerivedCategoryCube_inv_app_Q`: the
  identification `G ∘ F' ≅ F ∘ Φ` of functors induced on derived categories by an isomorphism of
  exact functors, at the image of a complex.
* `Stacks.EtaleCohomology.DerivedComparisonPaste.mapDerivedCategoryCube_comp`: these
  identifications paste along composites of exact functors.
* `Stacks.EtaleCohomology.DerivedComparisonPaste.restrictBase_baseChange_unbounded_abstract`: the
  assembly of the compatibility of `Rf̄_* (b ∘ a)_! ≅ i_! Rf'_* a_!` with base change.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.EtaleCohomology.DerivedComparisonPaste

/-! ### Comparisons of right derived functors -/

section Unique

variable {CA CB CA' CB' DA DB DA' DB' : Type*} [Category* CA] [Category* CB] [Category* CA']
  [Category* CB'] [Category* DA] [Category* DB] [Category* DA'] [Category* DB']
  {QA : CA ⥤ DA} {QB : CB ⥤ DB} {QA' : CA' ⥤ DA'} {QB' : CB' ⥤ DB'}
  {P₁ P₂ : CA ⥤ CB} {P₁' P₂' : CA' ⥤ CB'} {R₁ R₂ : DA ⥤ DB} {R₁' R₂' : DA' ⥤ DB'}
  {GA : CA ⥤ CA'} {GB : CB ⥤ CB'} {GDA : DA ⥤ DA'} {GDB : DB ⥤ DB'}

/-- **Comparisons are compatible with the identification of right derived functors**, for
abstract categories. Let `β : R₂ ≅ R₁` and `β' : R₂' ≅ R₁'` identify two right derived functors
of isomorphic functors `P₁ ≅ P₂` (the hypotheses `hβ`, `hβ'`), and let `b₁`, `b₂` be the
comparisons of `R₁`, `R₂` with base change induced by comparisons `c₁`, `c₂` of the underlying
functors (`hb₁`, `hb₂`). If `c₁` is `c₂` read through `P₁ ≅ P₂` (`hc`), then `b₁` is `b₂` read
through `β` and `β'`. -/
theorem comparison_rightDerivedUnique (W : MorphismProperty CA) [QA.IsLocalization W]
    (u₁ : P₁ ⋙ QB ⟶ QA ⋙ R₁) (u₂ : P₂ ⋙ QB ⟶ QA ⋙ R₂)
    (u₁' : P₁' ⋙ QB' ⟶ QA' ⋙ R₁') (u₂' : P₂' ⋙ QB' ⟶ QA' ⋙ R₂')
    [(R₁ ⋙ GDB).IsRightDerivedFunctor
      (Functor.whiskerRight u₁ GDB ≫ (Functor.associator _ _ _).hom) W]
    (ι : P₁ ≅ P₂) (ι' : P₁' ≅ P₂') (β : R₂ ≅ R₁) (β' : R₂' ≅ R₁')
    (hβ : ∀ K, QB.map (ι.hom.app K) ≫ u₂.app K ≫ β.hom.app (QA.obj K) = u₁.app K)
    (hβ' : ∀ K, QB'.map (ι'.hom.app K) ≫ u₂'.app K ≫ β'.hom.app (QA'.obj K) = u₁'.app K)
    (ΦA : QA ⋙ GDA ≅ GA ⋙ QA') (ΦB : QB ⋙ GDB ≅ GB ⋙ QB')
    (c₁ : P₁ ⋙ GB ⟶ GA ⋙ P₁') (c₂ : P₂ ⋙ GB ⟶ GA ⋙ P₂')
    (b₁ : R₁ ⋙ GDB ⟶ GDA ⋙ R₁') (b₂ : R₂ ⋙ GDB ⟶ GDA ⋙ R₂')
    (hb₁ : ∀ K, GDB.map (u₁.app K) ≫ b₁.app (QA.obj K) =
      ΦB.hom.app (P₁.obj K) ≫ QB'.map (c₁.app K) ≫ u₁'.app (GA.obj K) ≫
        R₁'.map (ΦA.inv.app K))
    (hb₂ : ∀ K, GDB.map (u₂.app K) ≫ b₂.app (QA.obj K) =
      ΦB.hom.app (P₂.obj K) ≫ QB'.map (c₂.app K) ≫ u₂'.app (GA.obj K) ≫
        R₂'.map (ΦA.inv.app K))
    (hc : ∀ K, c₁.app K = GB.map (ι.hom.app K) ≫ c₂.app K ≫ ι'.inv.app (GA.obj K))
    (L : DA) :
    GDB.map (β.hom.app L) ≫ b₁.app L = b₂.app L ≫ β'.hom.app (GDA.obj L) := by
  have key : b₁ = Functor.whiskerRight β.inv GDB ≫ b₂ ≫ Functor.whiskerLeft GDA β'.hom := by
    refine Functor.rightDerived_ext (R₁ ⋙ GDB)
      (Functor.whiskerRight u₁ GDB ≫ (Functor.associator _ _ _).hom) W _ _ _
      (NatTrans.ext (funext fun K => ?_))
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Category.id_comp, Category.assoc, Functor.comp_obj]
    have e1 : u₁.app K ≫ β.inv.app (QA.obj K) = QB.map (ι.hom.app K) ≫ u₂.app K := by
      rw [← hβ K]
      simp
    have e2 : u₂'.app (GA.obj K) ≫ β'.hom.app (QA'.obj (GA.obj K)) =
        QB'.map (ι'.inv.app (GA.obj K)) ≫ u₁'.app (GA.obj K) := by
      rw [← hβ' (GA.obj K), ← QB'.map_comp_assoc, Iso.inv_hom_id_app,
        CategoryTheory.Functor.map_id, Category.id_comp]
    have nβ' := β'.hom.naturality (ΦA.inv.app K)
    have nΦ := ΦB.hom.naturality (ι.hom.app K)
    simp only [Functor.comp_map, Functor.comp_obj] at nβ' nΦ
    rw [hb₁, ← GDB.map_comp_assoc, e1, GDB.map_comp_assoc, reassoc_of% hb₂, nβ',
      reassoc_of% e2, reassoc_of% nΦ, hc]
    simp only [Functor.map_comp, Category.assoc]
  have h := NatTrans.congr_app key L
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at h
  rw [h, ← GDB.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp]

end Unique

section Comp

variable {CA CB CC CA' CB' CC' DA DB DC DA' DB' DC' : Type*} [Category* CA] [Category* CB]
  [Category* CC] [Category* CA'] [Category* CB'] [Category* CC'] [Category* DA] [Category* DB]
  [Category* DC] [Category* DA'] [Category* DB'] [Category* DC']
  {QA : CA ⥤ DA} {QB : CB ⥤ DB} {QC : CC ⥤ DC} {QA' : CA' ⥤ DA'} {QB' : CB' ⥤ DB'}
  {QC' : CC' ⥤ DC'}
  {P : CA ⥤ CB} {Qt : CB ⥤ CC} {PQ : CA ⥤ CC} {P' : CA' ⥤ CB'} {Qt' : CB' ⥤ CC'}
  {PQ' : CA' ⥤ CC'} {GA : CA ⥤ CA'} {GB : CB ⥤ CB'} {GC : CC ⥤ CC'}
  {RP : DA ⥤ DB} {RQ : DB ⥤ DC} {RP' : DA' ⥤ DB'} {RQ' : DB' ⥤ DC'}
  {GDA : DA ⥤ DA'} {GDB : DB ⥤ DB'} {GDC : DC ⥤ DC'}

/-- **Comparisons of right derived functors compose**, for abstract categories: if `bP` and `bQ`
are the comparisons of `RP` and `RQ` with base change induced by comparisons `cP` and `cQ` of the
underlying functors, the composite comparison of `RP ⋙ RQ` is induced by the composite `cPQ` of
`cP` and `cQ` (the hypothesis `hc`), for the composite derived-functor units `uPQ`, `uPQ'`. -/
theorem comparison_comp
    (uP : P ⋙ QB ⟶ QA ⋙ RP) (uQ : Qt ⋙ QC ⟶ QB ⋙ RQ) (uPQ : PQ ⋙ QC ⟶ QA ⋙ (RP ⋙ RQ))
    (uP' : P' ⋙ QB' ⟶ QA' ⋙ RP') (uQ' : Qt' ⋙ QC' ⟶ QB' ⋙ RQ')
    (uPQ' : PQ' ⋙ QC' ⟶ QA' ⋙ (RP' ⋙ RQ'))
    (ΦA : QA ⋙ GDA ≅ GA ⋙ QA') (ΦB : QB ⋙ GDB ≅ GB ⋙ QB') (ΦC : QC ⋙ GDC ≅ GC ⋙ QC')
    (cP : P ⋙ GB ⟶ GA ⋙ P') (cQ : Qt ⋙ GC ⟶ GB ⋙ Qt') (cPQ : PQ ⋙ GC ⟶ GA ⋙ PQ')
    (bP : RP ⋙ GDB ⟶ GDA ⋙ RP') (bQ : RQ ⋙ GDC ⟶ GDB ⋙ RQ')
    (e : P ⋙ Qt ≅ PQ) (e' : P' ⋙ Qt' ≅ PQ')
    (hbP : ∀ K, GDB.map (uP.app K) ≫ bP.app (QA.obj K) =
      ΦB.hom.app (P.obj K) ≫ QB'.map (cP.app K) ≫ uP'.app (GA.obj K) ≫
        RP'.map (ΦA.inv.app K))
    (hbQ : ∀ K, GDC.map (uQ.app K) ≫ bQ.app (QB.obj K) =
      ΦC.hom.app (Qt.obj K) ≫ QC'.map (cQ.app K) ≫ uQ'.app (GB.obj K) ≫
        RQ'.map (ΦB.inv.app K))
    (huPQ : ∀ K, uPQ.app K = QC.map (e.inv.app K) ≫ uQ.app (P.obj K) ≫ RQ.map (uP.app K))
    (huPQ' : ∀ K, uPQ'.app K =
      QC'.map (e'.inv.app K) ≫ uQ'.app (P'.obj K) ≫ RQ'.map (uP'.app K))
    (hc : ∀ K, cPQ.app K ≫ e'.inv.app (GA.obj K) =
      GC.map (e.inv.app K) ≫ cQ.app (P.obj K) ≫ Qt'.map (cP.app K))
    (K : CA) :
    GDC.map (uPQ.app K) ≫ ((Functor.associator _ _ _).hom ≫ Functor.whiskerLeft RP bQ ≫
        (Functor.associator _ _ _).inv ≫ Functor.whiskerRight bP RQ' ≫
        (Functor.associator _ _ _).hom).app (QA.obj K) =
      ΦC.hom.app (PQ.obj K) ≫ QC'.map (cPQ.app K) ≫ uPQ'.app (GA.obj K) ≫
        (RP' ⋙ RQ').map (ΦA.inv.app K) := by
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp, Category.comp_id,
    Functor.comp_map, Functor.comp_obj]
  have nb := bQ.naturality (uP.app K)
  have nu := uQ'.naturality (cP.app K)
  have nΦ := ΦC.hom.naturality (e.inv.app K)
  simp only [Functor.comp_map, Functor.comp_obj] at nb nu nΦ
  have hP' : ΦB.inv.app (P.obj K) ≫ GDB.map (uP.app K) ≫ bP.app (QA.obj K) =
      QB'.map (cP.app K) ≫ uP'.app (GA.obj K) ≫ RP'.map (ΦA.inv.app K) := by
    rw [hbP, Iso.inv_hom_id_app_assoc]
  rw [huPQ, huPQ']
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% nb, reassoc_of% hbQ, ← RQ'.map_comp (GDB.map (uP.app K)),
    ← RQ'.map_comp (ΦB.inv.app (P.obj K)), hP', RQ'.map_comp (QB'.map (cP.app K)),
    RQ'.map_comp (uP'.app (GA.obj K)), ← reassoc_of% nu, reassoc_of% nΦ,
    ← QC'.map_comp_assoc (cPQ.app K), hc]
  simp only [Functor.map_comp, Category.assoc]

end Comp

/-! ### Isomorphisms of exact functors on derived categories -/

section MapDerived

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

variable {C₁ C₂ C₁' C₂' : Type*} [Category C₁] [Category C₂] [Category C₁'] [Category C₂']
  [Abelian C₁] [Abelian C₂] [Abelian C₁'] [Abelian C₂'] [HasDerivedCategory C₁]
  [HasDerivedCategory C₂] [HasDerivedCategory C₁'] [HasDerivedCategory C₂']
  (G : C₁ ⥤ C₁') (F' : C₁' ⥤ C₂') (F : C₁ ⥤ C₂) (Φ : C₂ ⥤ C₂')
  [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [F'.Additive] [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
  [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [Φ.Additive] [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ]

/-- The identification `G ∘ F' ≅ F ∘ Φ` of the functors induced on derived categories by an
isomorphism `η : G ⋙ F' ≅ F ⋙ Φ` of exact functors. -/
abbrev mapDerivedCategoryCube (η : G ⋙ F' ≅ F ⋙ Φ) :
    G.mapDerivedCategory ⋙ F'.mapDerivedCategory ≅ F.mapDerivedCategory ⋙ Φ.mapDerivedCategory :=
  (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso G F').symm ≪≫
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _ η ≪≫
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso F Φ

omit [HasDerivedCategory C₁] [HasDerivedCategory C₂] [HasDerivedCategory C₁']
  [HasDerivedCategory C₂'] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits F'] [PreservesFiniteColimits F'] [PreservesFiniteLimits F]
  [PreservesFiniteColimits F] [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ] in
/-- The degreewise comparison attached to an isomorphism of additive functors is the inverse of
the degreewise isomorphism. -/
lemma mapHomologicalComplex_comparison_eq (η : G ⋙ F' ≅ F ⋙ Φ)
    (K : CochainComplex C₁ ℤ) :
    ((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ Φ)) (ComplexShape.up ℤ)).hom ≫
        NatTrans.mapHomologicalComplex η.inv (ComplexShape.up ℤ) ≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (G ⋙ F')) (ComplexShape.up ℤ)).inv).app
          K =
      (NatIso.mapHomologicalComplex η (ComplexShape.up ℤ)).inv.app K := by
  ext n
  simp

/-- **The identification `G ∘ F' ≅ F ∘ Φ` induced by an isomorphism of exact functors, at the
image of a complex**: it is the degreewise isomorphism, read through the canonical
factorizations. -/
theorem mapDerivedCategoryCube_inv_app_Q (η : G ⋙ F' ≅ F ⋙ Φ) (K : CochainComplex C₁ ℤ) :
    (mapDerivedCategoryCube G F' F Φ η).inv.app (DerivedCategory.Q.obj K) =
      Φ.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
        Φ.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Q.map
          (((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ Φ)) (ComplexShape.up ℤ)).hom ≫
            NatTrans.mapHomologicalComplex η.inv (ComplexShape.up ℤ) ≫
            (Functor.mapHomologicalComplexCompIso (Iso.refl (G ⋙ F'))
              (ComplexShape.up ℤ)).inv).app K) ≫
        F'.mapDerivedCategoryFactors.inv.app ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        F'.mapDerivedCategory.map (G.mapDerivedCategoryFactors.inv.app K) := by
  rw [mapHomologicalComplex_comparison_eq]
  simp only [mapDerivedCategoryCube, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso_inv_app_Q,
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso_inv_app_Q,
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso_hom_app_Q, Category.assoc,
    Iso.inv_hom_id_app_assoc]

/-- `Stacks.EtaleCohomology.DerivedComparisonPaste.mapDerivedCategoryCube_inv_app_Q` in the form
of a comparison of functors on derived categories: after the canonical factorization of `F`. -/
theorem mapDerivedCategoryCube_comparison (η : G ⋙ F' ≅ F ⋙ Φ) (K : CochainComplex C₁ ℤ) :
    Φ.mapDerivedCategory.map (F.mapDerivedCategoryFactors.inv.app K) ≫
        (mapDerivedCategoryCube G F' F Φ η).inv.app (DerivedCategory.Q.obj K) =
      Φ.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Q.map
          (((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ Φ)) (ComplexShape.up ℤ)).hom ≫
            NatTrans.mapHomologicalComplex η.inv (ComplexShape.up ℤ) ≫
            (Functor.mapHomologicalComplexCompIso (Iso.refl (G ⋙ F'))
              (ComplexShape.up ℤ)).inv).app K) ≫
        F'.mapDerivedCategoryFactors.inv.app ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        F'.mapDerivedCategory.map (G.mapDerivedCategoryFactors.inv.app K) := by
  rw [mapDerivedCategoryCube_inv_app_Q, ← Φ.mapDerivedCategory.map_comp_assoc,
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]

end MapDerived

section Cancel

variable {C D E E' : Type*} [Category* C] [Category* D] [Category* E] [Category* E']

/-- `H(e⁻¹) ≫ H(e) = 𝟙`, with a tail, for a natural isomorphism `e`. -/
@[reassoc]
lemma map_inv_hom_app {F G : C ⥤ D} (e : F ≅ G) (H : D ⥤ E) (X : C) :
    H.map (e.inv.app X) ≫ H.map (e.hom.app X) = 𝟙 _ := by
  rw [← H.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]

/-- `H'(H(e⁻¹)) ≫ H'(H(e)) = 𝟙`, with a tail, for a natural isomorphism `e`. -/
@[reassoc]
lemma map_map_inv_hom_app {F G : C ⥤ D} (e : F ≅ G) (H : D ⥤ E) (H' : E ⥤ E') (X : C) :
    H'.map (H.map (e.inv.app X)) ≫ H'.map (H.map (e.hom.app X)) = 𝟙 _ := by
  rw [← H'.map_comp, ← H.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_id]

end Cancel

section Composite

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

variable {C Cu Cb C' Cu' Cb' : Type*} [Category C] [Category Cu] [Category Cb] [Category C']
  [Category Cu'] [Category Cb'] [Abelian C] [Abelian Cu] [Abelian Cb] [Abelian C'] [Abelian Cu']
  [Abelian Cb'] [HasDerivedCategory C] [HasDerivedCategory Cu] [HasDerivedCategory Cb]
  [HasDerivedCategory C'] [HasDerivedCategory Cu'] [HasDerivedCategory Cb']
  {A : C ⥤ Cu} {B : Cu ⥤ Cb} {AB : C ⥤ Cb} {A' : C' ⥤ Cu'} {B' : Cu' ⥤ Cb'} {AB' : C' ⥤ Cb'}
  {GX : C ⥤ C'} {GU : Cu ⥤ Cu'} {GXb : Cb ⥤ Cb'}
  [A.Additive] [PreservesFiniteLimits A] [PreservesFiniteColimits A]
  [B.Additive] [PreservesFiniteLimits B] [PreservesFiniteColimits B]
  [AB.Additive] [PreservesFiniteLimits AB] [PreservesFiniteColimits AB]
  [A'.Additive] [PreservesFiniteLimits A'] [PreservesFiniteColimits A']
  [B'.Additive] [PreservesFiniteLimits B'] [PreservesFiniteColimits B']
  [AB'.Additive] [PreservesFiniteLimits AB'] [PreservesFiniteColimits AB']
  [GX.Additive] [PreservesFiniteLimits GX] [PreservesFiniteColimits GX]
  [GU.Additive] [PreservesFiniteLimits GU] [PreservesFiniteColimits GU]
  [GXb.Additive] [PreservesFiniteLimits GXb] [PreservesFiniteColimits GXb]

/-- **The identifications induced by isomorphisms of exact functors paste along composites**: if
`ηAB : GX ⋙ AB' ≅ AB ⋙ GXb` is the pasting of `ηA` and `ηB` through `e : AB ≅ A ⋙ B` and
`e' : AB' ≅ A' ⋙ B'` (the hypothesis `h`), so are the induced identifications on derived
categories, through identifications `c`, `c'` induced by `e`, `e'` (the hypotheses `hc`,
`hc'`). -/
theorem mapDerivedCategoryCube_comp (ηA : GX ⋙ A' ≅ A ⋙ GU) (ηB : GU ⋙ B' ≅ B ⋙ GXb)
    (ηAB : GX ⋙ AB' ≅ AB ⋙ GXb) (e : AB ≅ A ⋙ B) (e' : AB' ≅ A' ⋙ B')
    (c : AB.mapDerivedCategory ≅ A.mapDerivedCategory ⋙ B.mapDerivedCategory)
    (c' : AB'.mapDerivedCategory ≅ A'.mapDerivedCategory ⋙ B'.mapDerivedCategory)
    (hc : ∀ N, AB.mapDerivedCategoryFactors.inv.app N ≫ c.hom.app (DerivedCategory.Q.obj N) =
      DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso e.symm (ComplexShape.up ℤ)).inv.app N) ≫
        B.mapDerivedCategoryFactors.inv.app ((A.mapHomologicalComplex (ComplexShape.up ℤ)).obj N) ≫
        B.mapDerivedCategory.map (A.mapDerivedCategoryFactors.inv.app N))
    (hc' : ∀ N, AB'.mapDerivedCategoryFactors.inv.app N ≫ c'.hom.app (DerivedCategory.Q.obj N) =
      DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso e'.symm (ComplexShape.up ℤ)).inv.app N) ≫
        B'.mapDerivedCategoryFactors.inv.app
          ((A'.mapHomologicalComplex (ComplexShape.up ℤ)).obj N) ≫
        B'.mapDerivedCategory.map (A'.mapDerivedCategoryFactors.inv.app N))
    (h : ∀ F, ηAB.inv.app F ≫ e'.hom.app (GX.obj F) =
      GXb.map (e.hom.app F) ≫ ηB.inv.app (A.obj F) ≫ B'.map (ηA.inv.app F))
    (K : DerivedCategory C) :
    (mapDerivedCategoryCube GX AB' AB GXb ηAB).inv.app K ≫
        c'.hom.app (GX.mapDerivedCategory.obj K) =
      GXb.mapDerivedCategory.map (c.hom.app K) ≫
        (mapDerivedCategoryCube GU B' B GXb ηB).inv.app (A.mapDerivedCategory.obj K) ≫
        B'.mapDerivedCategory.map ((mapDerivedCategoryCube GX A' A GU ηA).inv.app K) := by
  suffices hnat : (mapDerivedCategoryCube GX AB' AB GXb ηAB).inv ≫
      Functor.whiskerLeft GX.mapDerivedCategory c'.hom =
      Functor.whiskerRight c.hom GXb.mapDerivedCategory ≫ (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft A.mapDerivedCategory (mapDerivedCategoryCube GU B' B GXb ηB).inv ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (mapDerivedCategoryCube GX A' A GU ηA).inv B'.mapDerivedCategory ≫
        (Functor.associator _ _ _).hom by
    have h' := NatTrans.congr_app hnat K
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
      Category.comp_id, Functor.comp_obj] at h'
    exact h'
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) (fun N => ?_)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.comp_id, Functor.comp_obj]
  have hc0 : ∀ N, c.hom.app (DerivedCategory.Q.obj N) = AB.mapDerivedCategoryFactors.hom.app N ≫
      DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso e.symm (ComplexShape.up ℤ)).inv.app N) ≫
        B.mapDerivedCategoryFactors.inv.app ((A.mapHomologicalComplex (ComplexShape.up ℤ)).obj N) ≫
        B.mapDerivedCategory.map (A.mapDerivedCategoryFactors.inv.app N) := fun N => by
    rw [← hc N, Iso.hom_inv_id_app_assoc]
  have hc0' : ∀ N, c'.hom.app (DerivedCategory.Q.obj N) =
      AB'.mapDerivedCategoryFactors.hom.app N ≫
      DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso e'.symm (ComplexShape.up ℤ)).inv.app N) ≫
        B'.mapDerivedCategoryFactors.inv.app
          ((A'.mapHomologicalComplex (ComplexShape.up ℤ)).obj N) ≫
        B'.mapDerivedCategory.map (A'.mapDerivedCategoryFactors.inv.app N) := fun N => by
    rw [← hc' N, Iso.hom_inv_id_app_assoc]
  have n1 := c'.hom.naturality (GX.mapDerivedCategoryFactors.inv.app N)
  have n2 := (mapDerivedCategoryCube GU B' B GXb ηB).inv.naturality
    (A.mapDerivedCategoryFactors.inv.app N)
  have n3 := GXb.mapDerivedCategoryFactors.hom.naturality
    ((Functor.mapHomologicalComplexCompIso e.symm (ComplexShape.up ℤ)).inv.app N)
  have n4 := B'.mapDerivedCategoryFactors.inv.naturality
    (((Functor.mapHomologicalComplexCompIso (Iso.refl (A ⋙ GU)) (ComplexShape.up ℤ)).hom ≫
      NatTrans.mapHomologicalComplex ηA.inv (ComplexShape.up ℤ) ≫
      (Functor.mapHomologicalComplexCompIso (Iso.refl (GX ⋙ A'))
        (ComplexShape.up ℤ)).inv).app N)
  simp only [Functor.comp_map, Functor.comp_obj] at n1 n2 n3 n4
  have hdeg : ((Functor.mapHomologicalComplexCompIso (Iso.refl (AB ⋙ GXb))
        (ComplexShape.up ℤ)).hom ≫
      NatTrans.mapHomologicalComplex ηAB.inv (ComplexShape.up ℤ) ≫
      (Functor.mapHomologicalComplexCompIso (Iso.refl (GX ⋙ AB'))
        (ComplexShape.up ℤ)).inv).app N ≫
      (Functor.mapHomologicalComplexCompIso e'.symm (ComplexShape.up ℤ)).inv.app
        ((GX.mapHomologicalComplex (ComplexShape.up ℤ)).obj N) =
      (GXb.mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((Functor.mapHomologicalComplexCompIso e.symm (ComplexShape.up ℤ)).inv.app N) ≫
        ((Functor.mapHomologicalComplexCompIso (Iso.refl (B ⋙ GXb)) (ComplexShape.up ℤ)).hom ≫
          NatTrans.mapHomologicalComplex ηB.inv (ComplexShape.up ℤ) ≫
          (Functor.mapHomologicalComplexCompIso (Iso.refl (GU ⋙ B'))
            (ComplexShape.up ℤ)).inv).app ((A.mapHomologicalComplex (ComplexShape.up ℤ)).obj N) ≫
        (B'.mapHomologicalComplex (ComplexShape.up ℤ)).map
          (((Functor.mapHomologicalComplexCompIso (Iso.refl (A ⋙ GU)) (ComplexShape.up ℤ)).hom ≫
            NatTrans.mapHomologicalComplex ηA.inv (ComplexShape.up ℤ) ≫
            (Functor.mapHomologicalComplexCompIso (Iso.refl (GX ⋙ A'))
              (ComplexShape.up ℤ)).inv).app N) := by
    ext n
    simpa using h (N.X n)
  have hQ := congrArg DerivedCategory.Q.map hdeg
  simp only [Functor.map_comp] at hQ
  rw [mapDerivedCategoryCube_inv_app_Q, mapDerivedCategoryCube_inv_app_Q, hc0]
  simp only [Functor.map_comp, Category.assoc]
  rw [n1, hc0']
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [reassoc_of% n2, mapDerivedCategoryCube_inv_app_Q]
  simp only [Category.assoc, map_inv_hom_app_assoc, map_map_inv_hom_app_assoc]
  rw [reassoc_of% n3, ← reassoc_of% n4, reassoc_of% hQ]

end Composite

/-! ### Degreewise comparisons -/

section Paste

variable {VA VB VC VA' VB' VC' : Type*} [Category* VA] [Category* VB] [Category* VC]
  [Category* VA'] [Category* VB'] [Category* VC']

/-- The pasting of a comparison `αA : A ⋙ GB ⟶ GA ⋙ A'` with a comparison
`αB : B ⋙ GC ⟶ GB ⋙ B'`: the comparison `(A ⋙ B) ⋙ GC ⟶ GA ⋙ (A' ⋙ B')` of the composites. -/
abbrev pasteComparison {A : VA ⥤ VB} {B : VB ⥤ VC} {A' : VA' ⥤ VB'} {B' : VB' ⥤ VC'}
    {GA : VA ⥤ VA'} {GB : VB ⥤ VB'} {GC : VC ⥤ VC'} (αA : A ⋙ GB ⟶ GA ⋙ A')
    (αB : B ⋙ GC ⟶ GB ⋙ B') : (A ⋙ B) ⋙ GC ⟶ GA ⋙ (A' ⋙ B') :=
  (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft A αB ≫ (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight αA B' ≫ (Functor.associator _ _ _).hom

/-- The components of `Stacks.EtaleCohomology.DerivedComparisonPaste.pasteComparison`. -/
theorem pasteComparison_app {A : VA ⥤ VB} {B : VB ⥤ VC} {A' : VA' ⥤ VB'} {B' : VB' ⥤ VC'}
    {GA : VA ⥤ VA'} {GB : VB ⥤ VB'} {GC : VC ⥤ VC'} (αA : A ⋙ GB ⟶ GA ⋙ A')
    (αB : B ⋙ GC ⟶ GB ⋙ B') (F : VA) :
    (pasteComparison αA αB).app F = αB.app (A.obj F) ≫ B'.map (αA.app F) := by
  simp only [pasteComparison, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.id_comp, Category.comp_id]

end Paste

section DegreewiseComponents

variable {ι : Type*} {c : ComplexShape ι} {VA VB VC VA' VB' VC' : Type*} {cVA : Category VA}
  {cVB : Category VB} {cVC : Category VC} {cVA' : Category VA'} {cVB' : Category VB'}
  {cVC' : Category VC'} {zVA : HasZeroMorphisms VA} {zVB : HasZeroMorphisms VB}
  {zVC : HasZeroMorphisms VC} {zVA' : HasZeroMorphisms VA'} {zVB' : HasZeroMorphisms VB'}
  {zVC' : HasZeroMorphisms VC'}

/-- **Degreewise comparisons compose**, for comparisons given by their components: if `γP`,
`γQ`, `γPQ` are, degree by degree, `αP`, `αQ` and their composite, and `e`, `e'` are, degree by
degree, identities, then `γPQ` is the composite of `γQ` and `γP` read through `e` and `e'`. -/
theorem mapHomologicalComplex_comparison_comp_of_components {P : VA ⥤ VB} {Q : VB ⥤ VC}
    {P' : VA' ⥤ VB'} {Q' : VB' ⥤ VC'} {GA : VA ⥤ VA'} {GB : VB ⥤ VB'} {GC : VC ⥤ VC'}
    [P.PreservesZeroMorphisms] [Q.PreservesZeroMorphisms] [P'.PreservesZeroMorphisms]
    [Q'.PreservesZeroMorphisms] [GA.PreservesZeroMorphisms] [GB.PreservesZeroMorphisms]
    [GC.PreservesZeroMorphisms]
    (αP : P ⋙ GB ⟶ GA ⋙ P') (αQ : Q ⋙ GC ⟶ GB ⋙ Q')
    (γP : P.mapHomologicalComplex c ⋙ GB.mapHomologicalComplex c ⟶
      GA.mapHomologicalComplex c ⋙ P'.mapHomologicalComplex c)
    (hγP : ∀ K i, (γP.app K).f i = αP.app (K.X i))
    (γQ : Q.mapHomologicalComplex c ⋙ GC.mapHomologicalComplex c ⟶
      GB.mapHomologicalComplex c ⋙ Q'.mapHomologicalComplex c)
    (hγQ : ∀ K i, (γQ.app K).f i = αQ.app (K.X i))
    (γPQ : (P ⋙ Q).mapHomologicalComplex c ⋙ GC.mapHomologicalComplex c ⟶
      GA.mapHomologicalComplex c ⋙ (P' ⋙ Q').mapHomologicalComplex c)
    (hγPQ : ∀ K i, (γPQ.app K).f i = αQ.app (P.obj (K.X i)) ≫ Q'.map (αP.app (K.X i)))
    (e : P.mapHomologicalComplex c ⋙ Q.mapHomologicalComplex c ≅ (P ⋙ Q).mapHomologicalComplex c)
    (he : ∀ K i, (e.inv.app K).f i = 𝟙 ((P ⋙ Q).obj (K.X i)))
    (e' : P'.mapHomologicalComplex c ⋙ Q'.mapHomologicalComplex c ≅
      (P' ⋙ Q').mapHomologicalComplex c)
    (he' : ∀ K i, (e'.inv.app K).f i = 𝟙 ((P' ⋙ Q').obj (K.X i)))
    (K : HomologicalComplex VA c) :
    γPQ.app K ≫ e'.inv.app ((GA.mapHomologicalComplex c).obj K) =
      (GC.mapHomologicalComplex c).map (e.inv.app K) ≫
        γQ.app ((P.mapHomologicalComplex c).obj K) ≫
        (Q'.mapHomologicalComplex c).map (γP.app K) := by
  refine HomologicalComplex.hom_ext _ _ (fun i => ?_)
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f, hγP, hγQ, hγPQ,
    he, he']
  dsimp only [Functor.comp_obj, Functor.mapHomologicalComplex_obj_X]
  simp only [Category.comp_id, CategoryTheory.Functor.map_id, Category.id_comp]

/-- The components of `Stacks.EtaleCohomology.DerivedComparisonPaste.pasteComparison` applied
degreewise. -/
theorem mapHomologicalComplex_pasteComparison_app_f {A : VA ⥤ VB} {B : VB ⥤ VC}
    {A' : VA' ⥤ VB'} {B' : VB' ⥤ VC'} {GA : VA ⥤ VA'} {GB : VB ⥤ VB'} {GC : VC ⥤ VC'}
    [A.PreservesZeroMorphisms] [B.PreservesZeroMorphisms] [A'.PreservesZeroMorphisms]
    [B'.PreservesZeroMorphisms] [GA.PreservesZeroMorphisms] [GC.PreservesZeroMorphisms]
    (αA : A ⋙ GB ⟶ GA ⋙ A') (αB : B ⋙ GC ⟶ GB ⋙ B') (K : HomologicalComplex VA c) (i : ι) :
    ((NatTrans.mapHomologicalComplex (pasteComparison αA αB) c).app K).f i =
      αB.app (A.obj (K.X i)) ≫ B'.map (αA.app (K.X i)) := by
  rw [NatTrans.mapHomologicalComplex_app_f, pasteComparison_app]

/-- **Degreewise pasted comparisons are compatible with isomorphisms of functors**, for
comparisons given by their components: if the pasted comparisons `γ₁`, `γ₂` are, degree by degree,
`Stacks.EtaleCohomology.DerivedComparisonPaste.pasteComparison` of `αA₁, αB₁` and of `αA₂, αB₂`,
and these correspond under `e`, `e'` (the hypothesis `h`), then `γ₁` is `γ₂` read through the
degreewise isomorphisms `ι`, `ι'`. -/
theorem mapHomologicalComplex_pasteComparison_conj_of_components {VM₁ VM₂ VM₁' VM₂' : Type*}
    {cVM₁ : Category VM₁} {cVM₂ : Category VM₂} {cVM₁' : Category VM₁'} {cVM₂' : Category VM₂'}
    {A₁ : VA ⥤ VM₁} {B₁ : VM₁ ⥤ VB} {A₂ : VA ⥤ VM₂} {B₂ : VM₂ ⥤ VB}
    {A₁' : VA' ⥤ VM₁'} {B₁' : VM₁' ⥤ VB'} {A₂' : VA' ⥤ VM₂'} {B₂' : VM₂' ⥤ VB'}
    {GA : VA ⥤ VA'} {GM₁ : VM₁ ⥤ VM₁'} {GM₂ : VM₂ ⥤ VM₂'} {GB : VB ⥤ VB'}
    [(A₁ ⋙ B₁).PreservesZeroMorphisms] [(A₂ ⋙ B₂).PreservesZeroMorphisms]
    [(A₁' ⋙ B₁').PreservesZeroMorphisms] [(A₂' ⋙ B₂').PreservesZeroMorphisms]
    [GA.PreservesZeroMorphisms] [GB.PreservesZeroMorphisms]
    (e : A₁ ⋙ B₁ ≅ A₂ ⋙ B₂) (e' : A₁' ⋙ B₁' ≅ A₂' ⋙ B₂')
    (αA₁ : A₁ ⋙ GM₁ ⟶ GA ⋙ A₁') (αB₁ : B₁ ⋙ GB ⟶ GM₁ ⋙ B₁')
    (αA₂ : A₂ ⋙ GM₂ ⟶ GA ⋙ A₂') (αB₂ : B₂ ⋙ GB ⟶ GM₂ ⋙ B₂')
    (h : ∀ F, αB₁.app (A₁.obj F) ≫ B₁'.map (αA₁.app F) =
      GB.map (e.hom.app F) ≫ αB₂.app (A₂.obj F) ≫ B₂'.map (αA₂.app F) ≫
        e'.inv.app (GA.obj F))
    (γ₁ : (A₁ ⋙ B₁).mapHomologicalComplex c ⋙ GB.mapHomologicalComplex c ⟶
      GA.mapHomologicalComplex c ⋙ (A₁' ⋙ B₁').mapHomologicalComplex c)
    (hγ₁ : ∀ K i, (γ₁.app K).f i = αB₁.app (A₁.obj (K.X i)) ≫ B₁'.map (αA₁.app (K.X i)))
    (γ₂ : (A₂ ⋙ B₂).mapHomologicalComplex c ⋙ GB.mapHomologicalComplex c ⟶
      GA.mapHomologicalComplex c ⋙ (A₂' ⋙ B₂').mapHomologicalComplex c)
    (hγ₂ : ∀ K i, (γ₂.app K).f i = αB₂.app (A₂.obj (K.X i)) ≫ B₂'.map (αA₂.app (K.X i)))
    (ι : (A₁ ⋙ B₁).mapHomologicalComplex c ≅ (A₂ ⋙ B₂).mapHomologicalComplex c)
    (hι : ∀ K i, (ι.hom.app K).f i = e.hom.app (K.X i))
    (ι' : (A₁' ⋙ B₁').mapHomologicalComplex c ≅ (A₂' ⋙ B₂').mapHomologicalComplex c)
    (hι' : ∀ K i, (ι'.inv.app K).f i = e'.inv.app (K.X i)) (K : HomologicalComplex VA c) :
    γ₁.app K = (GB.mapHomologicalComplex c).map (ι.hom.app K) ≫ γ₂.app K ≫
      ι'.inv.app ((GA.mapHomologicalComplex c).obj K) := by
  refine HomologicalComplex.hom_ext _ _ (fun i => ?_)
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f, hγ₁, hγ₂, hι, hι',
    Category.assoc]
  exact h (K.X i)

end DegreewiseComponents

/-! ### The assembly -/

section Assembly

variable {DX DU DXb DY DYb DX' DU' DXb' DY' DYb' : Type*} [Category* DX] [Category* DU]
  [Category* DXb] [Category* DY] [Category* DYb] [Category* DX'] [Category* DU']
  [Category* DXb'] [Category* DY'] [Category* DYb']
  {RA Ea : DX ⥤ DU} {Rab Eab : DX ⥤ DXb} {Eb : DU ⥤ DXb} {Rfb : DXb ⥤ DYb} {Rf : DU ⥤ DY}
  {RI Ei : DY ⥤ DYb}
  {RA' Ea' : DX' ⥤ DU'} {Rab' Eab' : DX' ⥤ DXb'} {Eb' : DU' ⥤ DXb'} {Rfb' : DXb' ⥤ DYb'}
  {Rf' : DU' ⥤ DY'} {RI' Ei' : DY' ⥤ DYb'}
  {GX : DX ⥤ DX'} {GU : DU ⥤ DU'} {GXb : DXb ⥤ DXb'} {GY : DY ⥤ DY'} {GYb : DYb ⥤ DYb'}

/-- **The assembly of the compatibility of `Rf̄_* (b ∘ a)_! ≅ i_! Rf'_* a_!` with base change**, for
abstract categories. The isomorphism is `Rf̄_* (b ∘ a)_! ≅ Rf̄_* b_! a_! ≅ i_! Rf'_* a_!`, through
`(b ∘ a)_! ≅ b_! ∘ a_!` (`eAB`, `c`) and the open immersion case `β` of [Stacks, Tag 0F7B], with
the extensions by zero `RA`, `RI` identified with exact functors `Ea`, `Ei`. The base change maps
are built from the base change maps `bcF`, `bcFb` of direct images and the identifications
`cubeA`, `cubeAB`, `cubeI` of extensions by zero with inverse images. The inputs are the
compatibility `hii` of `c` with these identifications and the compatibility `hiii` of `β` with
base change. -/
theorem restrictBase_baseChange_unbounded_abstract
    (eA : RA ≅ Ea) (eA' : RA' ≅ Ea') (eAB : Rab ≅ Eab) (eAB' : Rab' ≅ Eab')
    (eI : RI ≅ Ei) (eI' : RI' ≅ Ei') (c : Eab ≅ Ea ⋙ Eb) (c' : Eab' ≅ Ea' ⋙ Eb')
    (β : Eb ⋙ Rfb ≅ Rf ⋙ Ei) (β' : Eb' ⋙ Rfb' ≅ Rf' ⋙ Ei')
    (cmdA : GX ⋙ Ea' ≅ Ea ⋙ GU) (cmdB : GU ⋙ Eb' ≅ Eb ⋙ GXb) (cmdAB : GX ⋙ Eab' ≅ Eab ⋙ GXb)
    (cmdI : GY ⋙ Ei' ≅ Ei ⋙ GYb) (bcF : Rf ⋙ GY ⟶ GU ⋙ Rf') (bcFb : Rfb ⋙ GYb ⟶ GXb ⋙ Rfb')
    (cubeA : GX ⋙ RA' ≅ RA ⋙ GU)
    (hcubeA : cubeA = Functor.isoWhiskerLeft GX eA' ≪≫ cmdA ≪≫ Functor.isoWhiskerRight eA.symm GU)
    (cubeAB : GX ⋙ Rab' ≅ Rab ⋙ GXb)
    (hcubeAB : cubeAB = Functor.isoWhiskerLeft GX eAB' ≪≫ cmdAB ≪≫
      Functor.isoWhiskerRight eAB.symm GXb)
    (cubeI : GY ⋙ RI' ≅ RI ⋙ GYb)
    (hcubeI : cubeI = Functor.isoWhiskerLeft GY eI' ≪≫ cmdI ≪≫ Functor.isoWhiskerRight eI.symm GYb)
    (hii : ∀ K, cmdAB.inv.app K ≫ c'.hom.app (GX.obj K) =
      GXb.map (c.hom.app K) ≫ cmdB.inv.app (Ea.obj K) ≫ Eb'.map (cmdA.inv.app K))
    (hiii : ∀ L, GYb.map (β.hom.app L) ≫ ((Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft Rf cmdI.inv ≫ (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight bcF Ei' ≫ (Functor.associator _ _ _).hom).app L =
      ((Functor.associator _ _ _).hom ≫ Functor.whiskerLeft Eb bcFb ≫
        (Functor.associator _ _ _).inv ≫ Functor.whiskerRight cmdB.inv Rfb' ≫
        (Functor.associator _ _ _).hom).app L ≫ β'.hom.app (GU.obj L))
    (K : DX) :
    GYb.map (Rfb.map ((eAB ≪≫ c).hom.app K) ≫ β.hom.app (Ea.obj K) ≫
          Ei.map (Rf.map (eA.inv.app K)) ≫ eI.inv.app (Rf.obj (RA.obj K))) ≫
        cubeI.inv.app (Rf.obj (RA.obj K)) ≫
        RI'.map (bcF.app (RA.obj K) ≫ Rf'.map (cubeA.inv.app K)) =
      (bcFb.app (Rab.obj K) ≫ Rfb'.map (cubeAB.inv.app K)) ≫
        Rfb'.map ((eAB' ≪≫ c').hom.app (GX.obj K)) ≫ β'.hom.app (Ea'.obj (GX.obj K)) ≫
          Ei'.map (Rf'.map (eA'.inv.app (GX.obj K))) ≫
          eI'.inv.app (Rf'.obj (RA'.obj (GX.obj K))) := by
  have hiii' : ∀ L, GYb.map (β.hom.app L) ≫ cmdI.inv.app (Rf.obj L) ≫ Ei'.map (bcF.app L) =
      bcFb.app (Eb.obj L) ≫ Rfb'.map (cmdB.inv.app L) ≫ β'.hom.app (GU.obj L) := fun L => by
    simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp, Category.comp_id,
      Functor.comp_obj, Category.assoc] using hiii L
  subst hcubeA hcubeAB hcubeI
  simp only [Iso.trans_inv, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.symm_inv,
    Functor.map_comp, Category.assoc, Functor.comp_obj]
  rw [← GYb.map_comp_assoc (eI.inv.app (Rf.obj (RA.obj K))), Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp,
    ← Rfb'.map_comp_assoc (eAB'.inv.app (GX.obj K)), Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  have nbc := bcFb.naturality (eAB.hom.app K)
  have nbc2 := bcFb.naturality (c.hom.app K)
  have ncmd := cmdI.inv.naturality (Rf.map (eA.inv.app K))
  have nbcF := bcF.naturality (eA.inv.app K)
  have nβ' := β'.hom.naturality (cmdA.inv.app K)
  simp only [Functor.comp_map, Functor.comp_obj] at nbc nbc2 ncmd nbcF nβ'
  rw [← reassoc_of% nbc, cancel_epi,
    ← RI'.map_comp (Rf'.map (cmdA.inv.app K)), ← RI'.map_comp (Rf'.map (GU.map (eA.hom.app K))),
    ← RI'.map_comp (bcF.app (RA.obj K)), ← eI'.inv.naturality]
  simp only [← Category.assoc]
  rw [cancel_mono]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% ncmd, ← Ei'.map_comp_assoc (GY.map (Rf.map (eA.inv.app K))), nbcF,
    Ei'.map_comp_assoc, ← Ei'.map_comp_assoc (Rf'.map (GU.map (eA.inv.app K))),
    ← Rf'.map_comp, ← GU.map_comp, Iso.inv_hom_id_app]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [reassoc_of% (hiii' (Ea.obj K)), ← reassoc_of% nβ', reassoc_of% nbc2,
    ← Rfb'.map_comp_assoc (cmdAB.inv.app K), hii]
  simp only [Functor.map_comp, Category.assoc]

end Assembly

/-! ### Identities on sheaves, for abstract categories -/

section Sheaves

/-- **The inclusions `j_! ⟶ j_*` decide identities between maps into `j_!`**, for abstract
categories: the comparisons `φ⁻¹ ∘ j_! ≅ j'_! ∘ g'⁻¹` paste along a composite `b ∘ a`, read
through `(b ∘ a)_! ≅ b_! ∘ a_!`, as soon as the inclusions `εa`, `εb`, `εab` compose (`e`, `e'`),
commute with base change (`ma`, `mb`, `mab`), and the base change maps of the direct images paste
(`pv`), the inclusion `εab'` being a monomorphism. -/
theorem extensionByZero_comp_baseChange_abstract
    {CX CU CT CX' CU' CT' : Type*} [Category* CX] [Category* CU] [Category* CT]
    [Category* CX'] [Category* CU'] [Category* CT']
    {aS aD : CX ⥤ CU} {bS bD : CU ⥤ CT} {abS abD : CX ⥤ CT}
    {aS' aD' : CX' ⥤ CU'} {bS' bD' : CU' ⥤ CT'} {abS' abD' : CX' ⥤ CT'}
    {GX : CX ⥤ CX'} {GU : CU ⥤ CU'} {GT : CT ⥤ CT'}
    (εa : aS ⟶ aD) (εb : bS ⟶ bD) (εab : abS ⟶ abD)
    (εa' : aS' ⟶ aD') (εb' : bS' ⟶ bD') (εab' : abS' ⟶ abD')
    (c : abS ≅ aS ⋙ bS) (c' : abS' ≅ aS' ⋙ bS') (d : aD ⋙ bD ≅ abD) (d' : aD' ⋙ bD' ≅ abD')
    (isoA : GX ⋙ aS' ≅ aS ⋙ GU) (isoB : GU ⋙ bS' ≅ bS ⋙ GT)
    (isoAB : GX ⋙ abS' ≅ abS ⋙ GT)
    (bcA : aD ⋙ GU ⟶ GX ⋙ aD') (bcB : bD ⋙ GT ⟶ GU ⋙ bD') (bcAB : abD ⋙ GT ⟶ GX ⋙ abD')
    (e : ∀ F, c.hom.app F ≫ bS.map (εa.app F) ≫ εb.app (aD.obj F) ≫ d.hom.app F = εab.app F)
    (e' : ∀ F, c'.hom.app F ≫ bS'.map (εa'.app F) ≫ εb'.app (aD'.obj F) ≫ d'.hom.app F =
      εab'.app F)
    (ma : ∀ F, GU.map (εa.app F) ≫ bcA.app F = isoA.inv.app F ≫ εa'.app (GX.obj F))
    (mb : ∀ M, GT.map (εb.app M) ≫ bcB.app M = isoB.inv.app M ≫ εb'.app (GU.obj M))
    (mab : ∀ F, GT.map (εab.app F) ≫ bcAB.app F = isoAB.inv.app F ≫ εab'.app (GX.obj F))
    (pvN : Functor.whiskerRight d.hom GT ≫ bcAB =
      ((Functor.associator _ _ _).hom ≫ Functor.whiskerLeft aD bcB ≫
        (Functor.associator _ _ _).inv ≫ Functor.whiskerRight bcA bD' ≫
        (Functor.associator _ _ _).hom) ≫ Functor.whiskerLeft GX d'.hom)
    (hm : ∀ G, Mono (εab'.app G)) (F : CX) :
    isoAB.inv.app F ≫ c'.hom.app (GX.obj F) =
      GT.map (c.hom.app F) ≫ isoB.inv.app (aS.obj F) ≫ bS'.map (isoA.inv.app F) := by
  have pv : ∀ F, GT.map (d.hom.app F) ≫ bcAB.app F =
      bcB.app (aD.obj F) ≫ bD'.map (bcA.app F) ≫ d'.hom.app (GX.obj F) := fun F => by
    simpa using NatTrans.congr_app pvN F
  have := hm (GX.obj F)
  refine (cancel_mono (c'.inv.app (GX.obj F) ≫ εab'.app (GX.obj F))).1 ?_
  have nB := isoB.inv.naturality (εa.app F)
  have nε := εb'.naturality (bcA.app F)
  simp only [Functor.comp_map, Functor.comp_obj] at nB nε
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [← mab, ← e, ← e' (GX.obj F)]
  simp only [Iso.inv_hom_id_app_assoc]
  rw [← bS'.map_comp_assoc, ← ma, bS'.map_comp_assoc, ← reassoc_of% nB, reassoc_of% nε,
    ← reassoc_of% mb, ← pv]
  simp only [Functor.map_comp, Category.assoc]

/-- **The open immersion case of [Stacks, Tag 0F7B] on sheaves commutes with base change**, for
abstract categories: the identification `ι : i_! ∘ f'_* ≅ f̄_* ∘ b_!` is compatible with the base
change maps, as soon as it is compatible with the inclusions `j_! ⟶ j_*` (`h0`, `h0'`), these
commute with base change (`mi`, `mb`), the base change maps of the direct images paste (`pv1`,
`pv2`), and `f̄'_* (b'_! ⟶ b'_*)` is a monomorphism (`hm`). -/
theorem directImageExtensionByZero_baseChange_abstract
    {CP CT CU CY CP' CT' CU' CY' : Type*} [Category* CP] [Category* CT] [Category* CU]
    [Category* CY] [Category* CP'] [Category* CT'] [Category* CU'] [Category* CY']
    {fs : CP ⥤ CY} {iS iD : CY ⥤ CU} {bS bD : CP ⥤ CT} {fbD : CT ⥤ CU} {compD : CP ⥤ CU}
    {fs' : CP' ⥤ CY'} {iS' iD' : CY' ⥤ CU'} {bS' bD' : CP' ⥤ CT'} {fbD' : CT' ⥤ CU'}
    {compD' : CP' ⥤ CU'} {GP : CP ⥤ CP'} {GT : CT ⥤ CT'} {GU : CU ⥤ CU'} {GY : CY ⥤ CY'}
    (εi : iS ⟶ iD) (εb : bS ⟶ bD) (εi' : iS' ⟶ iD') (εb' : bS' ⟶ bD')
    (ι : fs ⋙ iS ≅ bS ⋙ fbD) (ι' : fs' ⋙ iS' ≅ bS' ⋙ fbD')
    (dFI : fs ⋙ iD ≅ compD) (dBF : bD ⋙ fbD ≅ compD) (dFI' : fs' ⋙ iD' ≅ compD')
    (dBF' : bD' ⋙ fbD' ≅ compD') (isoI : GY ⋙ iS' ≅ iS ⋙ GU) (isoB : GP ⋙ bS' ≅ bS ⋙ GT)
    (bcF : fs ⋙ GY ⟶ GP ⋙ fs') (bcI : iD ⋙ GU ⟶ GY ⋙ iD') (bcB : bD ⋙ GT ⟶ GP ⋙ bD')
    (bcFb : fbD ⋙ GU ⟶ GT ⋙ fbD') (bcC : compD ⋙ GU ⟶ GP ⋙ compD')
    (h0 : ∀ F, ι.hom.app F ≫ fbD.map (εb.app F) ≫ dBF.hom.app F =
      εi.app (fs.obj F) ≫ dFI.hom.app F)
    (h0' : ∀ F, ι'.hom.app F ≫ fbD'.map (εb'.app F) ≫ dBF'.hom.app F =
      εi'.app (fs'.obj F) ≫ dFI'.hom.app F)
    (mi : ∀ M, GU.map (εi.app M) ≫ bcI.app M = isoI.inv.app M ≫ εi'.app (GY.obj M))
    (mb : ∀ F, GT.map (εb.app F) ≫ bcB.app F = isoB.inv.app F ≫ εb'.app (GP.obj F))
    (pvN1 : Functor.whiskerRight dFI.hom GU ≫ bcC =
      ((Functor.associator _ _ _).hom ≫ Functor.whiskerLeft fs bcI ≫
        (Functor.associator _ _ _).inv ≫ Functor.whiskerRight bcF iD' ≫
        (Functor.associator _ _ _).hom) ≫ Functor.whiskerLeft GP dFI'.hom)
    (pvN2 : Functor.whiskerRight dBF.hom GU ≫ bcC =
      ((Functor.associator _ _ _).hom ≫ Functor.whiskerLeft bD bcFb ≫
        (Functor.associator _ _ _).inv ≫ Functor.whiskerRight bcB fbD' ≫
        (Functor.associator _ _ _).hom) ≫ Functor.whiskerLeft GP dBF'.hom)
    (hm : ∀ G, Mono (fbD'.map (εb'.app G))) (F : CP) :
    isoI.inv.app (fs.obj F) ≫ iS'.map (bcF.app F) =
      GU.map (ι.hom.app F) ≫ bcFb.app (bS.obj F) ≫ fbD'.map (isoB.inv.app F) ≫
        ι'.inv.app (GP.obj F) := by
  have pv1 : ∀ F, GU.map (dFI.hom.app F) ≫ bcC.app F =
      bcI.app (fs.obj F) ≫ iD'.map (bcF.app F) ≫ dFI'.hom.app (GP.obj F) := fun F => by
    simpa using NatTrans.congr_app pvN1 F
  have pv2 : ∀ F, GU.map (dBF.hom.app F) ≫ bcC.app F =
      bcFb.app (bD.obj F) ≫ fbD'.map (bcB.app F) ≫ dBF'.hom.app (GP.obj F) := fun F => by
    simpa using NatTrans.congr_app pvN2 F
  have := hm (GP.obj F)
  refine (cancel_mono (ι'.hom.app (GP.obj F) ≫ fbD'.map (εb'.app (GP.obj F)) ≫
    dBF'.hom.app (GP.obj F))).1 ?_
  have nεi := εi'.naturality (bcF.app F)
  have nbc := bcFb.naturality (εb.app F)
  have h0'' := congrArg GU.map (h0 F)
  simp only [Functor.comp_map, Functor.comp_obj] at nεi nbc
  simp only [Functor.map_comp] at h0''
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [h0', reassoc_of% nεi, ← reassoc_of% (mi (fs.obj F)), ← pv1, ← fbD'.map_comp_assoc, ← mb,
    fbD'.map_comp_assoc, ← reassoc_of% nbc, ← pv2, reassoc_of% h0'']

end Sheaves

/-! ### Right derived functors identified through an isomorphism -/

section RightDerivedUnique

variable {C D H : Type*} [Category* C] [Category* D] [Category* H]

/-- The identification of two right derived functors, after the derived-functor unit of the first
written as `ι ≫ ν₀`: the derived-functor unit of the second. -/
theorem rightDerivedUnique_hom_fac (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
    {F F₀ : C ⥤ H} {RF RF' : D ⥤ H} (ι : F ⟶ F₀) (ν₀ : F₀ ⟶ L ⋙ RF) (ν' : F ⟶ L ⋙ RF)
    (hν' : ν' = ι ≫ ν₀) (ν : F ⟶ L ⋙ RF') [RF.IsRightDerivedFunctor ν' W]
    [RF'.IsRightDerivedFunctor ν W] (K : C) :
    ι.app K ≫ ν₀.app K ≫ (Functor.rightDerivedUnique RF RF' ν' ν W).hom.app (L.obj K) =
      ν.app K := by
  subst hν'
  have h := Functor.rightDerivedNatTrans_app RF RF' (ι ≫ ν₀) ν W (Iso.refl F).hom K
  simp only [NatTrans.comp_app, Category.assoc, Iso.refl_hom, NatTrans.id_app,
    Category.id_comp] at h
  exact h

end RightDerivedUnique

/-! ### The component of `R(g ∘ f)_! ≅ Rg_! ∘ Rf_!` -/

section CompOverIso

variable {DX DU DXb DY DYb DZ : Type*} [Category* DX] [Category* DU] [Category* DXb]
  [Category* DY] [Category* DYb] [Category* DZ]
  {RA Ea : DX ⥤ DU} {Rab : DX ⥤ DXb} {Eb : DU ⥤ DXb} {Rfb : DXb ⥤ DYb} {Rgb : DYb ⥤ DZ}
  {Rfg : DXb ⥤ DZ} {Rf : DU ⥤ DY} {RI Ei : DY ⥤ DYb}

/-- **The component of the isomorphism `R(g ∘ f)_! ≅ Rg_! ∘ Rf_!` through the auxiliary
compactification**, for abstract categories: the Leray isomorphism `e₂`, followed by `Rḡ_*` of
`Rf̄_* (b ∘ a)_! ≅ Rf̄_* b_! a_! ≅ i_! Rf'_* a_!`. -/
theorem compOverIso_hom_app_abstract (e₁ : Rab ≅ Ea ⋙ Eb) (e₂ : Rfg ≅ Rfb ⋙ Rgb)
    (β : Eb ⋙ Rfb ≅ Rf ⋙ Ei) (eA : RA ≅ Ea) (eI : RI ≅ Ei) (K : DX) :
    ((Functor.isoWhiskerRight e₁ Rfg ≪≫ Functor.isoWhiskerLeft _ e₂ :
        Rab ⋙ Rfg ≅ Ea ⋙ ((Eb ⋙ Rfb) ⋙ Rgb)) ≪≫
      Functor.isoWhiskerLeft Ea (Functor.isoWhiskerRight β Rgb) ≪≫
      (Functor.isoWhiskerRight eA.symm ((Rf ⋙ Ei) ⋙ Rgb) ≪≫
        Functor.isoWhiskerLeft (RA ⋙ Rf) (Functor.isoWhiskerRight eI.symm Rgb) :
        Ea ⋙ ((Rf ⋙ Ei) ⋙ Rgb) ≅ (RA ⋙ Rf) ⋙ (RI ⋙ Rgb))).hom.app K =
      e₂.hom.app (Rab.obj K) ≫ Rgb.map (Rfb.map (e₁.hom.app K) ≫ β.hom.app (Ea.obj K) ≫
        Ei.map (Rf.map (eA.inv.app K)) ≫ eI.inv.app (Rf.obj (RA.obj K))) := by
  have n := e₂.hom.naturality (e₁.hom.app K)
  simp only [Functor.comp_map, Functor.comp_obj] at n
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app, Iso.symm_hom,
    Functor.comp_map, Functor.comp_obj, Functor.map_comp, Category.assoc]
  rw [reassoc_of% n]

end CompOverIso

end Stacks.EtaleCohomology.DerivedComparisonPaste

end
