module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.ExtensionByZeroRestrict
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedSquareTransComposition

/-!
# The counit `i^{-1} i_! ≅ 𝟭` and base change

For a cartesian square of schemes
```
Y' --i'--> Ȳ'
|hY        |h
Y  --i-->  Ȳ
```
with `i`, `i'` open immersions, the counit `i'^{-1} i'_! ≅ 𝟭`, precomposed with `i'^{-1}` of the
isomorphism `h^{-1} i_! ≅ i'_! hY^{-1}` of [Stacks, Tag 03S6], is `hY^{-1}` of the counit
`i^{-1} i_! ≅ 𝟭`, read through the composition isomorphisms of inverse images.

## Main results

* `Stacks.EtaleCohomology.etaleModuleInverseImageExtensionByZeroIso_inv_counit`: on sheaves.
* `Stacks.EtaleCohomology.etaleModuleDerivedExtensionByZeroCubeIso_inv_counit`: on `D⁺`, and
  `Stacks.EtaleCohomology.etaleModuleDerivedExtensionByZeroCubeIso_inv_counit_app` at an object.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Cohomology.DerivedBaseChangePlus

universe u

namespace Stacks.EtaleCohomology

open Stacks.CategoryTheory.LeftAdjointUniqPasting

variable (Λ : Type) [Ring Λ]

variable {Y Y' Yb Yb' : Scheme.{u}} {hY : Y' ⟶ Y} {i' : Y' ⟶ Yb'} {i : Y ⟶ Yb} {hYb : Yb' ⟶ Yb}
  [IsOpenImmersion i] [IsOpenImmersion i'] (sq : IsPullback hY i' i hYb)

omit [IsOpenImmersion i] in
/-- A morphism into `((V ×_Y Y') ⟶ Ȳ') ×_{Ȳ'} Y'` of the small étale site of `Y'` is determined
by its component to `V`. -/
lemma baseChange_compose_baseChange_hom_ext {V : Y.Etale} {A : Y'.Etale}
    {p q : A ⟶ (smallEtaleBaseChange i').obj
      ((Etale.smallEtaleCompose i').obj ((smallEtaleBaseChange hY).obj V))}
    (hpq : p.left ≫ pullback.fst _ _ ≫ pullback.fst V.hom hY =
      q.left ≫ pullback.fst _ _ ≫ pullback.fst V.hom hY) : p = q := by
  have h2 := (MorphismProperty.Over.w p).trans (MorphismProperty.Over.w q).symm
  refine MorphismProperty.Over.Hom.ext (pullback.hom_ext (pullback.hom_ext ?_ ?_) h2)
  · exact (Category.assoc _ _ _).trans (hpq.trans (Category.assoc _ _ _).symm)
  · rw [← cancel_mono i']
    have hc : pullback.fst
          ((Etale.smallEtaleCompose i').obj ((smallEtaleBaseChange hY).obj V)).hom i' ≫
        pullback.snd V.hom hY ≫ i' =
        pullback.snd
          ((Etale.smallEtaleCompose i').obj ((smallEtaleBaseChange hY).obj V)).hom i' ≫ i' :=
      pullback.condition
    exact (Category.assoc _ _ _).trans ((Category.assoc _ _ _).trans
      ((congrArg (fun z => p.left ≫ z) hc).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun z => z ≫ i') h2).trans ((Category.assoc _ _ _).trans
          ((congrArg (fun z => q.left ≫ z) hc.symm).trans
            ((Category.assoc _ _ _).symm.trans (Category.assoc _ _ _).symm)))))))

/-- On small étale sites, the unit of the adjunction between composition with `i'` and base
change along `i'`, at the base change of `V` along `hY`, is the base change along `hY` of the
unit for `i` at `V`, followed by the comparison isomorphisms of iterated base change and the base
change isomorphism of the cartesian square `sq`. -/
lemma smallEtale_unit_baseChange_eq (V : Y.Etale) :
    (Etale.smallEtaleComposeBaseChangeAdj i').unit.app ((smallEtaleBaseChange hY).obj V) =
      (smallEtaleBaseChange hY).map ((Etale.smallEtaleComposeBaseChangeAdj i).unit.app V) ≫
        (smallEtaleBaseChangeComp' hY i (i' ≫ hYb) sq.w.symm).inv.app
          ((Etale.smallEtaleCompose i).obj V) ≫
        (smallEtaleBaseChangeComp' i' hYb (i' ≫ hYb) rfl).hom.app
          ((Etale.smallEtaleCompose i).obj V) ≫
        (smallEtaleBaseChange i').map
          ((Etale.smallEtaleComposeBaseChangeIsoOfIsPullback sq).hom.app V) := by
  refine baseChange_compose_baseChange_hom_ext ?_
  refine (ExtensionByZeroPasting.smallEtaleComposeBaseChangeAdj_unit_app_left_fst_assoc i'
    ((smallEtaleBaseChange hY).obj V) _).trans ?_
  refine Eq.symm ((congrArg (fun z => z ≫ _)
    (ExtensionByZeroPasting.comp_comp_comp_left _ _ _ _)).trans ?_)
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun z => _ ≫ z) (Category.assoc _ _ _)).trans ?_
  refine (congrArg (fun z => _ ≫ _ ≫ z) (Category.assoc _ _ _)).trans ?_
  refine (congrArg (fun z => _ ≫ _ ≫ _ ≫ z)
    (ExtensionByZeroPasting.smallEtaleBaseChange_map_left_fst_assoc
      i' ((Etale.smallEtaleComposeBaseChangeIsoOfIsPullback sq).hom.app V) _)).trans ?_
  refine (congrArg (fun z => _ ≫ _ ≫ _ ≫ _ ≫ z)
    (ExtensionByZeroPasting.smallEtaleComposeBaseChangeIsoOfIsPullback_hom_app_left_fst
      sq V)).trans ?_
  refine (congrArg (fun z => _ ≫ _ ≫ z) (smallEtaleBaseChangeComp'_fst_fst i' hYb (i' ≫ hYb) rfl
    ((Etale.smallEtaleCompose i).obj V))).trans ?_
  refine (congrArg (fun z => _ ≫ z) (smallEtaleBaseChangeComp'_inv_fst hY i (i' ≫ hYb) sq.w.symm
    ((Etale.smallEtaleCompose i).obj V))).trans ?_
  refine (ExtensionByZeroPasting.smallEtaleBaseChange_map_left_fst_assoc hY
    ((Etale.smallEtaleComposeBaseChangeAdj i).unit.app V) _).trans ?_
  exact (congrArg (fun z => _ ≫ z)
    (ExtensionByZeroPasting.smallEtaleComposeBaseChangeAdj_unit_app_left_fst i V)).trans
    (Category.comp_id _)

/-- **The counit `i'^{-1} i'_! ≅ 𝟭` after the isomorphism of [Stacks, Tag 03S6] is `hY^{-1}` of
the counit `i^{-1} i_! ≅ 𝟭`**, on sheaves of `Λ`-modules. -/
theorem etaleModuleInverseImageExtensionByZeroIso_inv_counit :
    Functor.whiskerRight (etaleModuleInverseImageExtensionByZeroIso.{u, 0} Λ sq).inv
        (etaleModuleInverseImage.{u, 0} Λ i') ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (etaleModuleInverseImage.{u, 0} Λ hY)
        (etaleModuleExtensionByZeroInverseImageIso Λ i').hom ≫
      (Functor.rightUnitor _).hom =
    (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (etaleModuleExtensionByZero.{u, 0} Λ i)
        ((etaleModuleInverseImageCompIso.{u, 0} Λ i' hYb).inv ≫
          eqToHom (congrArg (fun m => etaleModuleInverseImage.{u, 0} Λ m) sq.w.symm) ≫
          (etaleModuleInverseImageCompIso.{u, 0} Λ hY i).hom) ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (etaleModuleExtensionByZeroInverseImageIso Λ i).hom
        (etaleModuleInverseImage.{u, 0} Λ hY) ≫
      (Functor.leftUnitor _).hom := by
  apply (conjugateEquiv (etaleModuleInverseImageAdj.{u, 0} Λ hY)
    (((etaleModuleExtensionByZeroAdj.{u, 0} Λ i).comp
      (etaleModuleInverseImageAdj.{u, 0} Λ hYb)).comp
        (etaleModuleInverseImageAdj.{u, 0} Λ i'))).injective
  rw [← conjugateEquiv_comp _
      (((etaleModuleInverseImageAdj.{u, 0} Λ hY).comp
        (etaleModuleExtensionByZeroAdj.{u, 0} Λ i')).comp
          (etaleModuleInverseImageAdj.{u, 0} Λ i')),
    ← conjugateEquiv_comp _
      ((etaleModuleInverseImageAdj.{u, 0} Λ hY).comp
        ((etaleModuleExtensionByZeroAdj.{u, 0} Λ i').comp
          (etaleModuleInverseImageAdj.{u, 0} Λ i'))),
    ← conjugateEquiv_comp _
      ((etaleModuleInverseImageAdj.{u, 0} Λ hY).comp Adjunction.id),
    ← conjugateEquiv_comp _
      ((etaleModuleExtensionByZeroAdj.{u, 0} Λ i).comp
        ((etaleModuleInverseImageAdj.{u, 0} Λ hYb).comp
          (etaleModuleInverseImageAdj.{u, 0} Λ i'))),
    ← conjugateEquiv_comp _
      ((etaleModuleExtensionByZeroAdj.{u, 0} Λ i).comp
        ((etaleModuleInverseImageAdj.{u, 0} Λ i).comp
          (etaleModuleInverseImageAdj.{u, 0} Λ hY))),
    ← conjugateEquiv_comp _
      (((etaleModuleExtensionByZeroAdj.{u, 0} Λ i).comp
        (etaleModuleInverseImageAdj.{u, 0} Λ i)).comp
          (etaleModuleInverseImageAdj.{u, 0} Λ hY)),
    ← conjugateEquiv_comp _
      (Adjunction.id.comp (etaleModuleInverseImageAdj.{u, 0} Λ hY))]
  simp only [Category.assoc]
  rw [conjugateEquiv_rightUnitor_hom, conjugateEquiv_whiskerLeft,
    conjugateEquiv_associator_hom, conjugateEquiv_whiskerRight, conjugateEquiv_leftUnitor_hom,
    conjugateEquiv_whiskerRight, conjugateEquiv_associator_inv, conjugateEquiv_whiskerLeft,
    conjugateEquiv_associator_hom]
  rw [← conjugateEquiv_comp _ (etaleModuleInverseImageAdj.{u, 0} Λ (i' ≫ hYb)) _,
    ExtensionByZeroPasting.conjugateEquiv_eqToHom_comp_etaleModuleInverseImageCompIso_hom Λ hY i
      (i' ≫ hYb) sq.w.symm,
    conjugateEquiv_etaleModuleInverseImageCompIso_inv]
  simp only [etaleModuleInverseImageExtensionByZeroIso,
    Stacks.CategoryTheory.LeftAdjointUniqPasting.conjugateEquiv_leftAdjointUniq_inv]
  refine NatTrans.ext (funext fun F => ?_)
  have hσ := congrArg (fun t => NatTrans.app t F)
    (conjugateEquiv_etaleModuleExtensionByZeroInverseImageIso_hom_comp_counit Λ i')
  have hσ' := congrArg (fun t => NatTrans.app t ((etaleModuleDirectImage.{u, 0} Λ hY).obj F))
    (conjugateEquiv_etaleModuleExtensionByZeroInverseImageIso_hom_comp_counit Λ i)
  simp only [NatTrans.comp_app, NatTrans.id_app] at hσ hσ'
  replace hσ := IsIso.eq_inv_of_inv_hom_id hσ
  replace hσ' := IsIso.eq_inv_of_inv_hom_id hσ'
  simp only [NatTrans.comp_app, Functor.leftUnitor_inv_app, Functor.rightUnitor_inv_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, hσ, hσ', Functor.map_inv, IsIso.inv_comp_eq,
    Category.comp_id]
  have hR : (etaleModuleRestriction.{u, 0} Λ i).map
      ((etaleModuleDirectImageComp Λ hY i (i' ≫ hYb) sq.w.symm).hom.app F ≫
        (etaleModuleDirectImageComp Λ i' hYb (i' ≫ hYb) rfl).inv.app F) ≫
      (etaleModuleRestriction.{u, 0} Λ i).map
        ((etaleModuleDirectImageComp Λ i' hYb (i' ≫ hYb) rfl).hom.app F ≫
          (etaleModuleDirectImageComp Λ hY i (i' ≫ hYb) sq.w.symm).inv.app F) = 𝟙 _ := by
    rw [← Functor.map_comp, Category.assoc, Iso.inv_hom_id_app_assoc, Iso.hom_inv_id_app,
      CategoryTheory.Functor.map_id]
  have : IsIso ((etaleModuleRestrictionDirectImageAdj.{u, 0} Λ i).counit.app
      ((etaleModuleDirectImage.{u, 0} Λ hY).obj F)) := inferInstance
  have : IsIso ((etaleModuleRestriction.{u, 0} Λ i).map
        ((etaleModuleDirectImageComp Λ i' hYb (i' ≫ hYb) rfl).hom.app F ≫
          (etaleModuleDirectImageComp Λ hY i (i' ≫ hYb) sq.w.symm).inv.app F)) :=
    Functor.map_isIso _ _
  refine (@cancel_mono _ _ _ _ _ ((etaleModuleRestriction.{u, 0} Λ i).map
        ((etaleModuleDirectImageComp Λ i' hYb (i' ≫ hYb) rfl).hom.app F ≫
          (etaleModuleDirectImageComp Λ hY i (i' ≫ hYb) sq.w.symm).inv.app F) ≫
      (etaleModuleRestrictionDirectImageAdj.{u, 0} Λ i).counit.app
        ((etaleModuleDirectImage.{u, 0} Λ hY).obj F)) (IsIso.mono_of_iso _) _ _).1 ?_
  simp only [Category.assoc, reassoc_of% hR, IsIso.inv_hom_id, Category.comp_id]
  refine Sheaf.hom_ext (NatTrans.ext (funext fun V => ?_))
  simp only [NatTrans.comp_app, ObjectProperty.FullSubcategory.comp_hom, Iso.symm_inv,
    ExtensionByZeroPasting.etaleRestrictionPushforwardIsoOfIsPullback_hom_app_hom_app,
    ExtensionByZeroPasting.etaleModuleRestrictionDirectImageAdj_counit_app_hom_app]
  simp only [Functor.sheafPushforwardContinuous_map_hom_app, NatTrans.comp_app,
    ObjectProperty.FullSubcategory.comp_hom, etaleModuleDirectImageComp_hom_app_hom_app,
    ExtensionByZeroPasting.etaleModuleDirectImageComp_inv_app_hom_app,
    ExtensionByZeroPasting.etaleModuleRestrictionDirectImageAdj_counit_app_hom_app]
  have key := congrArg (fun z => F.obj.map (Quiver.Hom.op z))
    (smallEtale_unit_baseChange_eq sq V.unop)
  simp only [op_comp, Functor.map_comp] at key
  exact key.symm

section Derived

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

omit [IsOpenImmersion i] [IsOpenImmersion i'] in
/-- For isomorphisms `A`, `B`, `Cc`, `D` and morphisms `n`, `n'` with `n ≫ n' = 𝟙 _`, the
identity `A.inv ≫ B.inv ≫ Cc.hom = n ≫ D.inv` implies `Cc.inv ≫ B.hom ≫ A.hom = D.hom ≫ n'`. -/
lemma inv_chain_of_comp_eq {C : Type*} [Category* C] {X₀ X₁ X₂ W V : C} (A : X₁ ≅ X₀)
    (B : X₂ ≅ X₁) (Cc : X₂ ≅ W) (D : W ≅ V) (n : X₀ ⟶ V) (n' : V ⟶ X₀) (hn : n ≫ n' = 𝟙 _)
    (h : A.inv ≫ B.inv ≫ Cc.hom = n ≫ D.inv) : Cc.inv ≫ B.hom ≫ A.hom = D.hom ≫ n' := by
  have e : B.hom ≫ A.hom = Cc.hom ≫ D.hom ≫ n' := by
    calc B.hom ≫ A.hom = B.hom ≫ A.hom ≫ (n ≫ D.inv) ≫ D.hom ≫ n' := by simp [hn]
      _ = B.hom ≫ A.hom ≫ (A.inv ≫ B.inv ≫ Cc.hom) ≫ D.hom ≫ n' := by rw [h]
      _ = Cc.hom ≫ D.hom ≫ n' := by simp
  rw [Iso.inv_comp_eq, e]

omit [IsOpenImmersion i] [IsOpenImmersion i'] in
/-- The inverse of `Functor.mapDerivedCategoryPlusCompIsoh e` at the image of a bounded below
complex `L` is compatible with the factorization isomorphisms
`Functor.mapDerivedCategoryPlusFactorsh` and the action of `e.inv` on homotopy categories. -/
lemma mapDerivedCategoryPlusCompIsoh_inv_compatible {M₀ M₁ M₂ : Type*} [Category* M₀]
    [Abelian M₀] [Category* M₁] [Abelian M₁] [Category* M₂] [Abelian M₂]
    {r₂ : M₂ ⥤ M₁} {r₁ : M₁ ⥤ M₀} {r : M₂ ⥤ M₀} [r₁.Additive] [r₂.Additive] [r.Additive]
    [PreservesFiniteLimits r₁] [PreservesFiniteColimits r₁] [PreservesFiniteLimits r₂]
    [PreservesFiniteColimits r₂] [PreservesFiniteLimits r] [PreservesFiniteColimits r]
    (e : r₂ ⋙ r₁ ≅ r) (L : HomotopyCategory.Plus M₂) :
    (Functor.mapDerivedCategoryPlusCompIsoh e).inv.app (DerivedCategory.Plus.Qh.obj L) ≫
        r₁.mapDerivedCategoryPlus.map (r₂.mapDerivedCategoryPlusFactorsh.hom.app L) ≫
        r₁.mapDerivedCategoryPlusFactorsh.hom.app (r₂.mapHomotopyCategoryPlus.obj L) =
      r.mapDerivedCategoryPlusFactorsh.hom.app L ≫
        DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusNatTrans e.inv).app L) := by
  have h := Functor.mapDerivedCategoryPlusCompIsoh_compatible e L
  have hi : (Functor.mapHomotopyCategoryPlusNatTrans e.hom).app L ≫
      (Functor.mapHomotopyCategoryPlusNatTrans e.inv).app L = 𝟙 _ := by
    ext
    show (NatTrans.mapHomotopyCategory e.hom _).app L.obj ≫
      (NatTrans.mapHomotopyCategory e.inv _).app L.obj = 𝟙 _
    rw [← NatTrans.comp_app, ← NatTrans.mapHomotopyCategory_comp, e.hom_inv_id,
      NatTrans.mapHomotopyCategory_id]
    rfl
  have hn : DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusNatTrans e.hom).app L) ≫
      DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusNatTrans e.inv).app L) =
        𝟙 _ := by
    rw [← Functor.map_comp, hi, CategoryTheory.Functor.map_id]
  exact inv_chain_of_comp_eq
    (r₁.mapDerivedCategoryPlusFactorsh.app (r₂.mapHomotopyCategoryPlus.obj L))
    (r₁.mapDerivedCategoryPlus.mapIso (r₂.mapDerivedCategoryPlusFactorsh.app L))
    ((Functor.mapDerivedCategoryPlusCompIsoh e).app (DerivedCategory.Plus.Qh.obj L))
    (r.mapDerivedCategoryPlusFactorsh.app L) _ _ hn h

omit [IsOpenImmersion i] [IsOpenImmersion i'] in
/-- If `a ≫ b ≫ c.hom = d ≫ e` for an isomorphism `c`, then `a ≫ b = d ≫ e ≫ c.inv`. -/
lemma comp_eq_comp_inv_of_comp_hom_eq {C : Type*} [Category* C] {X₀ X₁ X₂ X₃ Y₁ : C}
    (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂) (c : X₂ ≅ X₃) (d : X₀ ⟶ Y₁) (e : Y₁ ⟶ X₃)
    (h : a ≫ b ≫ c.hom = d ≫ e) : a ≫ b = d ≫ e ≫ c.inv := by
  rw [← reassoc_of% h, Iso.hom_inv_id, Category.comp_id]

omit [IsOpenImmersion i] [IsOpenImmersion i'] in
/-- Six commuting squares `n1`, …, `n6` compose to
`a ≫ g ≫ c ≫ ε ≫ 𝟙 _ = F ≫ z ≫ y ≫ x ≫ t`. -/
lemma counit_chain_left {C : Type*} [Category* C] {X₀ X₁ X₂ X₃ X₄ P₁ P₂ P₃ P₄ Q₁ Q₂ Q₃ Q₄ : C}
    (a : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (g' : X₀ ⟶ P₁) (b : P₁ ⟶ X₂) (c : X₂ ⟶ X₃) (ε : X₃ ⟶ X₄)
    (p : P₁ ⟶ P₂) (q : P₂ ⟶ P₃) (r : P₃ ⟶ P₄) (s' : P₄ ⟶ X₃) (ε₀ : P₄ ⟶ Q₃) (t : Q₃ ⟶ X₄)
    (f' : P₃ ⟶ Q₂) (x : Q₂ ⟶ Q₃) (f'' : P₂ ⟶ Q₁) (y : Q₁ ⟶ Q₂) (F : X₀ ⟶ Q₄) (z : Q₄ ⟶ Q₁)
    (n1 : a ≫ g = g' ≫ b) (n2 : b ≫ c = p ≫ q ≫ r ≫ s') (n3 : s' ≫ ε = ε₀ ≫ t)
    (n4 : r ≫ ε₀ = f' ≫ x) (n5 : q ≫ f' = f'' ≫ y) (n6 : g' ≫ p ≫ f'' = F ≫ z) :
    a ≫ g ≫ c ≫ ε ≫ 𝟙 _ = F ≫ z ≫ y ≫ x ≫ t := by
  rw [Category.comp_id, reassoc_of% n1, reassoc_of% n2, n3, reassoc_of% n4, reassoc_of% n5,
    reassoc_of% n6]

omit [IsOpenImmersion i] [IsOpenImmersion i'] in
/-- An identity of natural transformations of the shape of
`Stacks.EtaleCohomology.etaleModuleInverseImageExtensionByZeroIso_inv_counit`, with the
associators and unitors removed and the composition isomorphisms `c₁`, `c₂` moved to the left. -/
lemma counit_whisker_rearrange {A A' B B' : Type*} [Category* A] [Category* A'] [Category* B]
    [Category* B'] {E : A ⥤ B} {E' : A' ⥤ B'} {Ii : B ⥤ A} {Ii' : B' ⥤ A'} {IhY : A ⥤ A'}
    {IhYb : B ⥤ B'} {Ik Ik₂ : B ⥤ A'} (U : IhY ⋙ E' ≅ E ⋙ IhYb) (εi : E ⋙ Ii ≅ 𝟭 A)
    (εi' : E' ⋙ Ii' ≅ 𝟭 A') (c₁ : Ik ≅ IhYb ⋙ Ii') (c₂ : Ik₂ ≅ Ii ⋙ IhY) (hk : Ik₂ = Ik)
    (h : Functor.whiskerRight U.inv Ii' ≫ (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft IhY εi'.hom ≫ (Functor.rightUnitor _).hom =
      (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft E (c₁.inv ≫ eqToHom hk.symm ≫ c₂.hom) ≫
        (Functor.associator _ _ _).inv ≫ Functor.whiskerRight εi.hom IhY ≫
        (Functor.leftUnitor _).hom) :
    Functor.whiskerLeft E c₁.symm.inv ≫ Functor.whiskerRight U.inv Ii' ≫
        Functor.whiskerLeft IhY εi'.hom =
      Functor.whiskerLeft E (c₂.symm ≪≫ eqToIso hk).inv ≫ Functor.whiskerRight εi.hom IhY := by
  subst hk
  refine NatTrans.ext (funext fun M => ?_)
  have hM := congrArg (fun t => NatTrans.app t M) h
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.rightUnitor_hom_app,
    Functor.leftUnitor_hom_app, Category.id_comp, eqToHom_refl] at hM
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Iso.trans_inv, Iso.symm_inv, eqToIso_refl, Iso.refl_inv, Category.id_comp]
  rw [← cancel_epi (c₁.inv.app (E.obj M)), Iso.inv_hom_id_app_assoc]
  simpa using hM

omit [IsOpenImmersion i] [IsOpenImmersion i'] in
/-- The action of an isomorphism of additive functors on bounded below homotopy categories, at an
object, is the action of its forward half. -/
lemma mapHomotopyCategoryPlusNatIso_hom_app_eq {A B : Type*} [Category* A] [Preadditive A]
    [Category* B] [Preadditive B] {F G : A ⥤ B} [F.Additive] [G.Additive] (e : F ≅ G)
    (K : HomotopyCategory.Plus A) :
    (Functor.mapHomotopyCategoryPlusNatIso e).hom.app K =
      (Functor.mapHomotopyCategoryPlusNatTrans e.hom).app K := by
  ext
  rfl

omit [IsOpenImmersion i] [IsOpenImmersion i'] in
/-- Four commuting squares `m2`, …, `m5` compose to `a ≫ dh ≫ ε = F ≫ m ≫ v ≫ fhinv'`. -/
lemma counit_chain_value {C : Type*} [Category* C] {X₀ X₁ X₄ X₅ P₂ Q₁ Q₃ Q₄ R₁ : C}
    (a : X₀ ⟶ X₁) (dh : X₁ ⟶ X₄) (ε : X₄ ⟶ X₅) (dh₀ : X₀ ⟶ P₂) (a₃ : P₂ ⟶ X₄)
    (fi : P₂ ⟶ Q₁) (w : Q₁ ⟶ X₅) (F : X₀ ⟶ R₁) (m : R₁ ⟶ Q₃) (fhinv : Q₃ ⟶ Q₁)
    (v : Q₃ ⟶ Q₄) {fhinv' : Q₄ ⟶ X₅}
    (m2 : a ≫ dh = dh₀ ≫ a₃) (m3 : a₃ ≫ ε = fi ≫ w) (m4 : dh₀ ≫ fi = F ≫ m ≫ fhinv)
    (m5 : fhinv ≫ w = v ≫ fhinv') :
    a ≫ dh ≫ ε = F ≫ m ≫ v ≫ fhinv' := by
  rw [reassoc_of% m2, m3, reassoc_of% m4, m5]

omit [IsOpenImmersion i] [IsOpenImmersion i'] in
/-- If `gi ≫ gh = 𝟙 _`, then `a ≫ gi ≫ (gh ≫ dh) ≫ ε ≫ 𝟙 _ = a ≫ dh ≫ ε`. -/
lemma cancel_inv_hom_whisker {C : Type*} [Category* C] {X₀ X₁ X₂ X₄ X₅ : C}
    (a : X₀ ⟶ X₁) (gi : X₁ ⟶ X₂) (gh : X₂ ⟶ X₁) (dh : X₁ ⟶ X₄) (ε : X₄ ⟶ X₅)
    (hg : gi ≫ gh = 𝟙 _) : a ≫ gi ≫ (gh ≫ dh) ≫ ε ≫ 𝟙 _ = a ≫ dh ≫ ε := by
  simp only [Category.comp_id, Category.assoc, reassoc_of% hg]

omit [IsOpenImmersion i] [IsOpenImmersion i'] in
/-- The value at the image of a complex of `g^{-1}` of the counit `c^{-1} c_! ≅ 𝟭`, read through a
composition isomorphism `c^{-1} ⋙ g^{-1} ≅ k^{-1}`. -/
lemma etaleModuleDerivedExtensionByZeroCompInverseImagePlusIso_whisker_value {W V Vb : Scheme.{u}}
    (c : V ⟶ Vb) [IsOpenImmersion c] (g : W ⟶ V) (k : W ⟶ Vb)
    (e : etaleModuleInverseImage.{u, 0} Λ c ⋙ etaleModuleInverseImage.{u, 0} Λ g ≅
      etaleModuleInverseImage.{u, 0} Λ k)
    (K : HomotopyCategory.Plus (EtaleModules.{u, 0} Λ V)) :
    (etaleModuleInverseImage.{u, 0} Λ k).mapDerivedCategoryPlus.map
        ((etaleModuleExtensionByZero.{u, 0} Λ c).rightDerivedFunctorPlusUnit.app K) ≫
      (Functor.mapDerivedCategoryPlusCompIsoh e).inv.app
        ((etaleModuleDerivedExtensionByZero.{u, 0} Λ c).obj (DerivedCategory.Plus.Qh.obj K)) ≫
      (etaleModuleDerivedInverseImagePlus.{u, 0} Λ g).map
        ((etaleModuleDerivedExtensionByZeroCompInverseImagePlusIso Λ c).hom.app
          (DerivedCategory.Plus.Qh.obj K)) =
    (etaleModuleInverseImage.{u, 0} Λ k).mapDerivedCategoryPlusFactorsh.hom.app
        ((etaleModuleExtensionByZero.{u, 0} Λ c).mapHomotopyCategoryPlus.obj K) ≫
      DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusNatTrans e.inv).app
          ((etaleModuleExtensionByZero.{u, 0} Λ c).mapHomotopyCategoryPlus.obj K) :
        _ ⟶ (etaleModuleInverseImage.{u, 0} Λ g).mapHomotopyCategoryPlus.obj
          ((etaleModuleInverseImage.{u, 0} Λ c).mapHomotopyCategoryPlus.obj
            ((etaleModuleExtensionByZero.{u, 0} Λ c).mapHomotopyCategoryPlus.obj K))) ≫
      DerivedCategory.Plus.Qh.map ((etaleModuleInverseImage.{u, 0} Λ g).mapHomotopyCategoryPlus.map
        ((Functor.mapHomotopyCategoryPlusNatIso
          (etaleModuleExtensionByZeroInverseImageIso Λ c)).hom.app K :
            (etaleModuleInverseImage.{u, 0} Λ c).mapHomotopyCategoryPlus.obj
              ((etaleModuleExtensionByZero.{u, 0} Λ c).mapHomotopyCategoryPlus.obj K) ⟶ K)) ≫
      (etaleModuleInverseImage.{u, 0} Λ g).mapDerivedCategoryPlusFactorsh.inv.app K := by
  have m2 := (Functor.mapDerivedCategoryPlusCompIsoh e).inv.naturality
    ((etaleModuleExtensionByZero.{u, 0} Λ c).rightDerivedFunctorPlusUnit.app K)
  have m3 : (etaleModuleDerivedInverseImagePlus.{u, 0} Λ g).map
        ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ c).map
          ((etaleModuleExtensionByZero.{u, 0} Λ c).rightDerivedFunctorPlusUnit.app K)) ≫
      (etaleModuleDerivedInverseImagePlus.{u, 0} Λ g).map
        ((etaleModuleDerivedExtensionByZeroCompInverseImagePlusIso Λ c).hom.app
          (DerivedCategory.Plus.Qh.obj K)) =
      (etaleModuleDerivedInverseImagePlus.{u, 0} Λ g).map
          ((etaleModuleInverseImage.{u, 0} Λ c).mapDerivedCategoryPlusFactorsh.hom.app
            ((etaleModuleExtensionByZero.{u, 0} Λ c).mapHomotopyCategoryPlus.obj K)) ≫
        (etaleModuleDerivedInverseImagePlus.{u, 0} Λ g).map (DerivedCategory.Plus.Qh.map
          ((Functor.mapHomotopyCategoryPlusNatIso
            (etaleModuleExtensionByZeroInverseImageIso Λ c)).hom.app K :
              (etaleModuleInverseImage.{u, 0} Λ c).mapHomotopyCategoryPlus.obj
                ((etaleModuleExtensionByZero.{u, 0} Λ c).mapHomotopyCategoryPlus.obj K) ⟶ K)) := by
    rw [← Functor.map_comp, ← Functor.map_comp,
      etaleModuleDerivedExtensionByZeroCompInverseImagePlusIso_hom_app_Qh]
    rfl
  have m4 := comp_eq_comp_inv_of_comp_hom_eq _ _
      ((etaleModuleInverseImage.{u, 0} Λ g).mapDerivedCategoryPlusFactorsh.app
        ((etaleModuleInverseImage.{u, 0} Λ c).mapHomotopyCategoryPlus.obj
          ((etaleModuleExtensionByZero.{u, 0} Λ c).mapHomotopyCategoryPlus.obj K))) _ _
      (mapDerivedCategoryPlusCompIsoh_inv_compatible e
        ((etaleModuleExtensionByZero.{u, 0} Λ c).mapHomotopyCategoryPlus.obj K))
  have m5 : DerivedCategory.Plus.Qh.map
        ((etaleModuleInverseImage.{u, 0} Λ g).mapHomotopyCategoryPlus.map
        ((Functor.mapHomotopyCategoryPlusNatIso
          (etaleModuleExtensionByZeroInverseImageIso Λ c)).hom.app K :
            (etaleModuleInverseImage.{u, 0} Λ c).mapHomotopyCategoryPlus.obj
              ((etaleModuleExtensionByZero.{u, 0} Λ c).mapHomotopyCategoryPlus.obj K) ⟶ K)) ≫
      (etaleModuleInverseImage.{u, 0} Λ g).mapDerivedCategoryPlusFactorsh.inv.app K =
      (etaleModuleInverseImage.{u, 0} Λ g).mapDerivedCategoryPlusFactorsh.inv.app
          ((etaleModuleInverseImage.{u, 0} Λ c).mapHomotopyCategoryPlus.obj
            ((etaleModuleExtensionByZero.{u, 0} Λ c).mapHomotopyCategoryPlus.obj K)) ≫
        (etaleModuleDerivedInverseImagePlus.{u, 0} Λ g).map (DerivedCategory.Plus.Qh.map
          ((Functor.mapHomotopyCategoryPlusNatIso
            (etaleModuleExtensionByZeroInverseImageIso Λ c)).hom.app K :
              (etaleModuleInverseImage.{u, 0} Λ c).mapHomotopyCategoryPlus.obj
                ((etaleModuleExtensionByZero.{u, 0} Λ c).mapHomotopyCategoryPlus.obj K) ⟶ K)) :=
    (etaleModuleInverseImage.{u, 0} Λ g).mapDerivedCategoryPlusFactorsh.inv.naturality _
  exact counit_chain_value _ _ _ _ _ _ _ _ _ _ _ m2 m3 m4 m5.symm

/-- `Stacks.EtaleCohomology.etaleModuleInverseImageExtensionByZeroIso_inv_counit` on bounded
below homotopy categories, at a complex `K`. -/
lemma etaleModuleExtensionByZeroCubeIso_inv_counit_homotopy
    (K : HomotopyCategory.Plus (EtaleModules.{u, 0} Λ Y)) :
    (Functor.mapHomotopyCategoryPlusNatTrans
        (etaleModuleInverseImageCompIso.{u, 0} Λ i' hYb).symm.inv).app
          ((etaleModuleExtensionByZero.{u, 0} Λ i).mapHomotopyCategoryPlus.obj K) ≫
      (etaleModuleInverseImage.{u, 0} Λ i').mapHomotopyCategoryPlus.map
        (hmap (etaleModuleInverseImage.{u, 0} Λ hYb) (etaleModuleInverseImage.{u, 0} Λ hY)
          (etaleModuleInverseImageExtensionByZeroIso.{u, 0} Λ sq).inv K) ≫
      (Functor.mapHomotopyCategoryPlusNatTrans
        (etaleModuleExtensionByZeroInverseImageIso Λ i').hom).app
        ((etaleModuleInverseImage.{u, 0} Λ hY).mapHomotopyCategoryPlus.obj K) =
      (Functor.mapHomotopyCategoryPlusNatTrans
        ((etaleModuleInverseImageCompIso.{u, 0} Λ hY i).symm ≪≫
          eqToIso (congrArg (fun m => etaleModuleInverseImage.{u, 0} Λ m) sq.w)).inv).app
          ((etaleModuleExtensionByZero.{u, 0} Λ i).mapHomotopyCategoryPlus.obj K) ≫
        (etaleModuleInverseImage.{u, 0} Λ hY).mapHomotopyCategoryPlus.map
          ((Functor.mapHomotopyCategoryPlusNatIso
            (etaleModuleExtensionByZeroInverseImageIso Λ i)).hom.app K :
              (etaleModuleInverseImage.{u, 0} Λ i).mapHomotopyCategoryPlus.obj
                ((etaleModuleExtensionByZero.{u, 0} Λ i).mapHomotopyCategoryPlus.obj K) ⟶ K) := by
  have key : Functor.whiskerLeft (etaleModuleExtensionByZero.{u, 0} Λ i)
        (etaleModuleInverseImageCompIso.{u, 0} Λ i' hYb).symm.inv ≫
      Functor.whiskerRight (etaleModuleInverseImageExtensionByZeroIso.{u, 0} Λ sq).inv
        (etaleModuleInverseImage.{u, 0} Λ i') ≫
      Functor.whiskerLeft (etaleModuleInverseImage.{u, 0} Λ hY)
        (etaleModuleExtensionByZeroInverseImageIso Λ i').hom =
      Functor.whiskerLeft (etaleModuleExtensionByZero.{u, 0} Λ i)
        ((etaleModuleInverseImageCompIso.{u, 0} Λ hY i).symm ≪≫
          eqToIso (congrArg (fun m => etaleModuleInverseImage.{u, 0} Λ m) sq.w)).inv ≫
        Functor.whiskerRight (etaleModuleExtensionByZeroInverseImageIso Λ i).hom
          (etaleModuleInverseImage.{u, 0} Λ hY) :=
    counit_whisker_rearrange _ _ _ _ _ _
      (etaleModuleInverseImageExtensionByZeroIso_inv_counit Λ sq)
  have h := congrArg (fun t => (Functor.mapHomotopyCategoryPlusNatTrans t).app K) key
  simp only [Functor.mapHomotopyCategoryPlusNatTrans_comp_app,
    Functor.mapHomotopyCategoryPlusNatTrans_whiskerLeft_app,
    Functor.mapHomotopyCategoryPlusNatTrans_whiskerRight_app] at h
  rwa [mapHomotopyCategoryPlusNatIso_hom_app_eq]

/-- **The counit `i'^{-1} i'_! ≅ 𝟭` after the isomorphism of [Stacks, Tag 03S6] is `hY^{-1}` of
the counit `i^{-1} i_! ≅ 𝟭`**, on `D⁺`. -/
theorem etaleModuleDerivedExtensionByZeroCubeIso_inv_counit :
    Functor.whiskerRight (etaleModuleDerivedExtensionByZeroCubeIso Λ sq).inv
        (etaleModuleDerivedInverseImagePlus.{u, 0} Λ i') ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (etaleModuleDerivedInverseImagePlus.{u, 0} Λ hY)
        (etaleModuleDerivedExtensionByZeroCompInverseImagePlusIso Λ i').hom ≫
      (Functor.rightUnitor _).hom =
    (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (etaleModuleDerivedExtensionByZero.{u, 0} Λ i)
        ((Functor.mapDerivedCategoryPlusCompIsoh
            (etaleModuleInverseImageCompIso.{u, 0} Λ i' hYb).symm).hom ≫
          (Functor.mapDerivedCategoryPlusCompIsoh
            ((etaleModuleInverseImageCompIso.{u, 0} Λ hY i).symm ≪≫
              eqToIso (congrArg (fun m => etaleModuleInverseImage.{u, 0} Λ m) sq.w))).inv) ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (etaleModuleDerivedExtensionByZeroCompInverseImagePlusIso Λ i).hom
        (etaleModuleDerivedInverseImagePlus.{u, 0} Λ hY) ≫
      (Functor.leftUnitor _).hom := by
  let T := Functor.whiskerLeft (etaleModuleDerivedExtensionByZero.{u, 0} Λ i)
      (Functor.mapDerivedCategoryPlusCompIsoh
        (etaleModuleInverseImageCompIso.{u, 0} Λ i' hYb).symm).inv ≫
    (Functor.associator _ _ _).inv
  have : IsIso T := by dsimp only [T]; infer_instance
  rw [← cancel_epi T]
  refine ((etaleModuleExtensionByZero.{u, 0} Λ i).rightDerivedFunctorPlus ⋙
    (etaleModuleInverseImage.{u, 0} Λ (i' ≫ hYb)).mapDerivedCategoryPlus).rightDerived_ext
    (derivedBaseChangePlusUnit _ _) (HomotopyCategory.Plus.quasiIso _) _ _ _
    (NatTrans.ext (funext fun K => ?_))
  simp only [T, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.leftUnitor_hom_app, Functor.rightUnitor_hom_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.comp_id, Category.id_comp]
  let E := etaleModuleExtensionByZero.{u, 0} Λ i
  let E' := etaleModuleExtensionByZero.{u, 0} Λ i'
  let uK := E.rightDerivedFunctorPlusUnit.app K
  let α₀ := (etaleModuleInverseImageExtensionByZeroIso.{u, 0} Λ sq).inv
  have n1 := (Functor.mapDerivedCategoryPlusCompIsoh
    (etaleModuleInverseImageCompIso.{u, 0} Λ i' hYb).symm).inv.naturality uK
  have dfac := derivedBaseChangePlus_fac E E' (etaleModuleInverseImage.{u, 0} Λ hYb)
    (etaleModuleInverseImage.{u, 0} Λ hY) α₀ K
  rw [derivedBaseChangePlusAux_app'] at dfac
  have n2 : (etaleModuleDerivedInverseImagePlus.{u, 0} Λ i').map
        ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ hYb).map uK) ≫
      (etaleModuleDerivedInverseImagePlus.{u, 0} Λ i').map
        ((etaleModuleDerivedExtensionByZeroCubeIso Λ sq).inv.app (DerivedCategory.Plus.Qh.obj K)) =
      (etaleModuleDerivedInverseImagePlus.{u, 0} Λ i').map
          ((etaleModuleInverseImage.{u, 0} Λ hYb).mapDerivedCategoryPlusFactorsh.hom.app
            (E.mapHomotopyCategoryPlus.obj K)) ≫
        (etaleModuleDerivedInverseImagePlus.{u, 0} Λ i').map (DerivedCategory.Plus.Qh.map
          (hmap (etaleModuleInverseImage.{u, 0} Λ hYb) (etaleModuleInverseImage.{u, 0} Λ hY)
            α₀ K)) ≫
        (etaleModuleDerivedInverseImagePlus.{u, 0} Λ i').map (E'.rightDerivedFunctorPlusUnit.app
          ((etaleModuleInverseImage.{u, 0} Λ hY).mapHomotopyCategoryPlus.obj K)) ≫
        (etaleModuleDerivedInverseImagePlus.{u, 0} Λ i').map (E'.rightDerivedFunctorPlus.map
          ((etaleModuleInverseImage.{u, 0} Λ hY).mapDerivedCategoryPlusFactorsh.inv.app K)) := by
    rw [← Functor.map_comp, etaleModuleDerivedExtensionByZeroCubeIso_inv, dfac]
    simp only [Functor.map_comp]
  have n3 := (etaleModuleDerivedExtensionByZeroCompInverseImagePlusIso Λ i').hom.naturality
    ((etaleModuleInverseImage.{u, 0} Λ hY).mapDerivedCategoryPlusFactorsh.inv.app K)
  simp only [Functor.comp_map, Functor.id_map] at n3
  have n4 := etaleModuleDerivedExtensionByZeroCompInverseImagePlusIso_hom_app_Qh Λ i'
    ((etaleModuleInverseImage.{u, 0} Λ hY).mapHomotopyCategoryPlus.obj K)
  have n5 := (etaleModuleInverseImage.{u, 0} Λ i').mapDerivedCategoryPlusFactorsh.hom.naturality
    (hmap (etaleModuleInverseImage.{u, 0} Λ hYb) (etaleModuleInverseImage.{u, 0} Λ hY) α₀ K)
  simp only [Functor.comp_map] at n5
  have n6 := mapDerivedCategoryPlusCompIsoh_inv_compatible
    (etaleModuleInverseImageCompIso.{u, 0} Λ i' hYb).symm (E.mapHomotopyCategoryPlus.obj K)
  have L := counit_chain_left _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ n1 n2 n3 n4 n5 n6
  have hg := (Functor.mapDerivedCategoryPlusCompIsoh
    (etaleModuleInverseImageCompIso.{u, 0} Λ i' hYb).symm).inv_hom_id_app
      ((etaleModuleDerivedExtensionByZero.{u, 0} Λ i).obj (DerivedCategory.Plus.Qh.obj K))
  have R0 := cancel_inv_hom_whisker
    ((etaleModuleInverseImage.{u, 0} Λ (i' ≫ hYb)).mapDerivedCategoryPlus.map uK) _ _
    ((Functor.mapDerivedCategoryPlusCompIsoh
      ((etaleModuleInverseImageCompIso.{u, 0} Λ hY i).symm ≪≫
        eqToIso (congrArg (fun m => etaleModuleInverseImage.{u, 0} Λ m) sq.w))).inv.app
      ((etaleModuleDerivedExtensionByZero.{u, 0} Λ i).obj (DerivedCategory.Plus.Qh.obj K)))
    ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ hY).map
      ((etaleModuleDerivedExtensionByZeroCompInverseImagePlusIso Λ i).hom.app
        (DerivedCategory.Plus.Qh.obj K))) hg
  have R := R0.trans (etaleModuleDerivedExtensionByZeroCompInverseImagePlusIso_whisker_value Λ i hY
    (i' ≫ hYb) ((etaleModuleInverseImageCompIso.{u, 0} Λ hY i).symm ≪≫
      eqToIso (congrArg (fun m => etaleModuleInverseImage.{u, 0} Λ m) sq.w)) K)
  have H := etaleModuleExtensionByZeroCubeIso_inv_counit_homotopy Λ sq K
  rw [← mapHomotopyCategoryPlusNatIso_hom_app_eq] at H
  have H' := (whisker_eq _ (DerivedCategory.Plus.Qh.map_comp _ _).symm).trans
    ((DerivedCategory.Plus.Qh.map_comp _ _).symm.trans
      ((congrArg (fun t => DerivedCategory.Plus.Qh.map t) H).trans
        (DerivedCategory.Plus.Qh.map_comp _ _)))
  have H'' := whisker_eq
    ((etaleModuleInverseImage.{u, 0} Λ (i' ≫ hYb)).mapDerivedCategoryPlusFactorsh.hom.app
      (E.mapHomotopyCategoryPlus.obj K))
    ((reassoc_of% H')
      ((etaleModuleInverseImage.{u, 0} Λ hY).mapDerivedCategoryPlusFactorsh.inv.app K))
  exact L.trans (H''.trans R.symm)

omit [IsOpenImmersion i] [IsOpenImmersion i'] in
/-- If `a ≫ b ≫ 𝟙 X = (c ≫ d) ≫ e ≫ 𝟙 X`, then `a ≫ b = c ≫ d ≫ e`. -/
lemma comp_id_clean {C : Type*} [Category* C] {A B B' B'' X : C} {a : A ⟶ B} {b : B ⟶ X}
    {c : A ⟶ B'} {d : B' ⟶ B''} {e : B'' ⟶ X} (h : a ≫ b ≫ 𝟙 X = (c ≫ d) ≫ e ≫ 𝟙 X) :
    a ≫ b = c ≫ d ≫ e := by
  simpa only [Category.comp_id, Category.assoc] using h

/-- The comparison `h^{-1} ⋙ i'^{-1} ⟶ i^{-1} ⋙ hY^{-1}` of derived inverse images around the
cartesian square `sq`, through the composition isomorphisms. -/
def etaleModuleDerivedInverseImagePlusSquareComparison :
    etaleModuleDerivedInverseImagePlus.{u, 0} Λ hYb ⋙
        etaleModuleDerivedInverseImagePlus.{u, 0} Λ i' ⟶
      etaleModuleDerivedInverseImagePlus.{u, 0} Λ i ⋙
        etaleModuleDerivedInverseImagePlus.{u, 0} Λ hY :=
  (Functor.mapDerivedCategoryPlusCompIsoh
      (etaleModuleInverseImageCompIso.{u, 0} Λ i' hYb).symm).hom ≫
    (Functor.mapDerivedCategoryPlusCompIsoh
      ((etaleModuleInverseImageCompIso.{u, 0} Λ hY i).symm ≪≫
        eqToIso (congrArg (fun m => etaleModuleInverseImage.{u, 0} Λ m) sq.w))).inv

/-- `Stacks.EtaleCohomology.etaleModuleDerivedExtensionByZeroCubeIso_inv_counit` at an object,
through `Stacks.EtaleCohomology.etaleModuleDerivedInverseImagePlusSquareComparison`. -/
theorem etaleModuleDerivedExtensionByZeroCubeIso_inv_counit_app
    (M : DerivedCategory.Plus (EtaleModules.{u, 0} Λ Y)) :
    (etaleModuleDerivedInverseImagePlus.{u, 0} Λ i').map
        ((etaleModuleDerivedExtensionByZeroCubeIso Λ sq).inv.app M) ≫
      (etaleModuleDerivedExtensionByZeroCompInverseImagePlusIso Λ i').hom.app
        ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ hY).obj M) =
    (etaleModuleDerivedInverseImagePlusSquareComparison Λ sq).app
        ((etaleModuleDerivedExtensionByZero.{u, 0} Λ i).obj M) ≫
      (etaleModuleDerivedInverseImagePlus.{u, 0} Λ hY).map
        ((etaleModuleDerivedExtensionByZeroCompInverseImagePlusIso Λ i).hom.app M) := by
  have h := NatTrans.congr_app (etaleModuleDerivedExtensionByZeroCubeIso_inv_counit Λ sq) M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.rightUnitor_hom_app,
    Functor.leftUnitor_hom_app, Category.id_comp] at h
  simp only [etaleModuleDerivedInverseImagePlusSquareComparison, NatTrans.comp_app, Category.assoc]
  exact comp_id_clean h

end Derived

end Stacks.EtaleCohomology
