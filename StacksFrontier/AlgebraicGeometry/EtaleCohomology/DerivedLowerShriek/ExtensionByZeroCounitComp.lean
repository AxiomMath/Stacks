module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.UnderivedExtensionByZeroPasting
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.ExtensionByZeroValues

/-!
# The counit of extension by zero along a composite of open immersions

For open immersions `a : X ⟶ U` and `b : U ⟶ V` the comparison `(b ∘ a)^{-1} (b ∘ a)_! ≅ 𝟭`
is the composite of the comparisons for `a` and for `b`, read through the composition
isomorphisms `(b ∘ a)_! ≅ b_! ∘ a_!` and `(b ∘ a)^{-1} ≅ a^{-1} ∘ b^{-1}`. This file proves it
for sheaves of modules and on `D⁺`.

## Main results

* `AlgebraicGeometry.Scheme.Etale.smallEtaleComposeBaseChangeAdj_counit_comp`: the counit of
  composition against base change along a composite, on small étale sites.
* `Stacks.EtaleCohomology.etaleModuleRestrictionDirectImageAdj_unit_comp`: the unit of restriction
  against direct image along a composite.
* `Stacks.EtaleCohomology.etaleModuleExtensionByZeroInverseImageIso_comp`: the counit
  `j^{-1} j_! ≅ 𝟭` along a composite of open immersions, on sheaves of modules.
* `Stacks.EtaleCohomology.etaleModuleDerivedExtensionByZeroCompInverseImagePlusIso_comp`: the
  counit `j^{-1} Rj_! ≅ 𝟭` along a composite of open immersions, on `D⁺`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale

universe u r

attribute [local instance] AlgebraicGeometry.Etale.isStableUnderComposition

namespace AlgebraicGeometry.Scheme.Etale

variable {X U V : Scheme.{u}} (a : X ⟶ U) (b : U ⟶ V) [Etale a] [Etale b]

/-- The counit of composition against base change along a composite is the composite of the
counits, read through `smallEtaleComposeCompIso` and the composition of base changes. -/
theorem smallEtaleComposeBaseChangeAdj_counit_comp (W : V.Etale) :
    (smallEtaleComposeBaseChangeAdj (a ≫ b)).counit.app W =
      (Stacks.EtaleCohomology.smallEtaleComposeCompIso a b).hom.app
          ((Stacks.EtaleCohomology.smallEtaleBaseChange (a ≫ b)).obj W) ≫
        (smallEtaleCompose b).map ((smallEtaleCompose a).map
          ((Stacks.EtaleCohomology.smallEtaleBaseChangeComp' a b (a ≫ b) rfl).hom.app W)) ≫
        (smallEtaleCompose b).map ((smallEtaleComposeBaseChangeAdj a).counit.app
          ((Stacks.EtaleCohomology.smallEtaleBaseChange b).obj W)) ≫
        (smallEtaleComposeBaseChangeAdj b).counit.app W := by
  refine MorphismProperty.Over.Hom.ext ?_
  change pullback.fst W.hom (a ≫ b) = 𝟙 _ ≫
    ((Stacks.EtaleCohomology.smallEtaleBaseChangeComp' a b (a ≫ b) rfl).hom.app W).left ≫
      pullback.fst ((Stacks.EtaleCohomology.smallEtaleBaseChange b).obj W).hom a ≫
        pullback.fst W.hom b
  rw [Category.id_comp]
  exact (Stacks.EtaleCohomology.smallEtaleBaseChangeComp'_fst_fst a b (a ≫ b) rfl W).symm

end AlgebraicGeometry.Scheme.Etale

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [Ring Λ]

section Unit

/-- On sections, the unit of restriction against direct image along an étale `j` is restriction
along the counit of composition against base change. -/
lemma etaleModuleRestrictionDirectImageAdj_unit_app_hom_app {U X : Scheme.{u}} (j : U ⟶ X)
    [Etale j] (M : EtaleModules.{u, r} Λ X) (W : X.Etaleᵒᵖ) :
    ((etaleModuleRestrictionDirectImageAdj.{u, r} Λ j).unit.app M).hom.app W =
      M.obj.map ((smallEtaleComposeBaseChangeAdj j).counit.app W.unop).op := by
  rfl

variable {X U V : Scheme.{u}} (a : X ⟶ U) (b : U ⟶ V) [Etale a] [Etale b]

/-- The unit of restriction against direct image along a composite is the composite of the units,
read through the composition isomorphisms of restrictions and of direct images. -/
theorem etaleModuleRestrictionDirectImageAdj_unit_comp (M : EtaleModules.{u, r} Λ V) :
    (etaleModuleRestrictionDirectImageAdj.{u, r} Λ (a ≫ b)).unit.app M =
      (etaleModuleRestrictionDirectImageAdj.{u, r} Λ b).unit.app M ≫
        (etaleModuleDirectImage.{u, r} Λ b).map
          ((etaleModuleRestrictionDirectImageAdj.{u, r} Λ a).unit.app
            ((etaleModuleRestriction.{u, r} Λ b).obj M)) ≫
        (etaleModuleDirectImageComp.{u, r} Λ a b (a ≫ b) rfl).hom.app _ ≫
        (etaleModuleDirectImage.{u, r} Λ (a ≫ b)).map
          ((etaleModuleRestrictionCompIso.{u, r} Λ a b).hom.app M) := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun W ↦ ?_))
  have key := congrArg (fun z ↦ M.obj.map (Quiver.Hom.op z))
    (smallEtaleComposeBaseChangeAdj_counit_comp a b W.unop)
  simp only [op_comp, Functor.map_comp] at key
  simp only [etaleModuleRestrictionDirectImageAdj_unit_app_hom_app, NatTrans.comp_app,
    ObjectProperty.FullSubcategory.comp_hom, etaleModuleDirectImageComp_hom_app_hom_app,
    etaleModuleRestrictionCompIso]
  rw [key]
  simp only [Category.assoc]
  rfl

/-- An identity between two composites of morphisms in `D` that follows from the commutation
relations `hU`, `hb`, `ha`, `nu`, `nd` and `nd'`. -/
lemma ir_comp_chain {C D : Type*} [Category* C] [Category* D] (G : C ⥤ D) {M A₂ A₃ : D} {A₁ : C}
    {P₁ P₂ P₃ P₄ : C} {Q₁ Q₂ Q₃ : D} (iUab : M ⟶ Q₁) (mInvComp : Q₁ ⟶ Q₂)
    (iUb : M ⟶ G.obj P₁) (iUaInv : P₁ ⟶ P₂) (dInv : G.obj P₂ ⟶ Q₂) (irB : P₁ ⟶ P₃)
    (iUaRes : P₃ ⟶ P₄) (aIrB : P₂ ⟶ P₄) (dA : G.obj P₄ ⟶ Q₃) (mAIrB : Q₂ ⟶ Q₃)
    (rUb : M ⟶ G.obj P₃) (rUa : P₃ ⟶ A₁) (irA : P₄ ⟶ A₁) (dRes : G.obj A₁ ⟶ A₂)
    (mIrA : Q₃ ⟶ A₂) (rc : A₂ ⟶ A₃)
    (hU : iUab ≫ mInvComp = iUb ≫ G.map iUaInv ≫ dInv) (hb : iUb ≫ G.map irB = rUb)
    (ha : iUaRes ≫ irA = rUa) (nu : irB ≫ iUaRes = iUaInv ≫ aIrB)
    (nd : G.map aIrB ≫ dA = dInv ≫ mAIrB) (nd' : G.map irA ≫ dRes = dA ≫ mIrA) :
    rUb ≫ G.map rUa ≫ dRes ≫ rc = iUab ≫ mInvComp ≫ mAIrB ≫ mIrA ≫ rc := by
  rw [reassoc_of% hU, ← reassoc_of% nd, ← reassoc_of% nd', ← hb, ← ha, ← G.map_comp_assoc,
    ← G.map_comp_assoc, ← nu]
  simp only [G.map_comp, Category.assoc]

/-- The unit of a composite adjunction, transported along an isomorphism of right adjoints. -/
private lemma comp_ofNatIsoRight_unit_app {C D E : Type*} [Category* C] [Category* D]
    [Category* E] {F : C ⥤ D} {G : D ⥤ C} {F' : D ⥤ E} {G' : E ⥤ D} {R : E ⥤ C}
    (adj₁ : F ⊣ G) (adj₂ : F' ⊣ G') (iso : G' ⋙ G ≅ R) (X : C) :
    ((adj₁.comp adj₂).ofNatIsoRight iso).unit.app X =
      adj₁.unit.app X ≫ G.map (adj₂.unit.app (F.obj X)) ≫ iso.hom.app _ := by
  rw [← Adjunction.homEquiv_id, Adjunction.homEquiv_ofNatIsoRight_apply,
    Adjunction.homEquiv_unit, CategoryTheory.Functor.map_id]
  simp only [Adjunction.comp_unit_app, Category.assoc]
  erw [Category.id_comp]
  rfl

omit [Etale a] [Etale b] in
/-- The unit of the composite adjunction `b^{-1} ∘ a^{-1} ⊣ (b ∘ a)_*` defining
`etaleModuleInverseImageCompIso`, read through the inverse image along the composite. -/
lemma etaleModuleInverseImageAdj_unit_comp (M : EtaleModules.{u, r} Λ V) :
    (etaleModuleInverseImageAdj.{u, r} Λ (a ≫ b)).unit.app M ≫
        (etaleModuleDirectImage.{u, r} Λ (a ≫ b)).map
          ((etaleModuleInverseImageCompIso.{u, r} Λ a b).hom.app M) =
      (etaleModuleInverseImageAdj.{u, r} Λ b).unit.app M ≫
        (etaleModuleDirectImage.{u, r} Λ b).map
          ((etaleModuleInverseImageAdj.{u, r} Λ a).unit.app
            ((etaleModuleInverseImage.{u, r} Λ b).obj M)) ≫
        (etaleModuleDirectImageComp.{u, r} Λ a b (a ≫ b) rfl).hom.app _ := by
  refine (Adjunction.unit_leftAdjointUniq_hom_app _ _ M).trans ?_
  exact comp_ofNatIsoRight_unit_app _ _ _ M

/-- The comparison of inverse image with restriction is compatible with composition:
`(b ∘ a)^{-1} ≅ res_{b ∘ a}` is the composite of the comparisons for `a` and for `b`, read through
the composition isomorphisms of inverse images and of restrictions. -/
theorem etaleModuleInverseImageRestrictionIso_comp (M : EtaleModules.{u, r} Λ V) :
    (etaleModuleInverseImageRestrictionIso.{u, r} Λ (a ≫ b)).hom.app M =
      (etaleModuleInverseImageCompIso.{u, r} Λ a b).hom.app M ≫
        (etaleModuleInverseImage.{u, r} Λ a).map
          ((etaleModuleInverseImageRestrictionIso.{u, r} Λ b).hom.app M) ≫
        (etaleModuleInverseImageRestrictionIso.{u, r} Λ a).hom.app
          ((etaleModuleRestriction.{u, r} Λ b).obj M) ≫
        (etaleModuleRestrictionCompIso.{u, r} Λ a b).hom.app M := by
  apply ((etaleModuleInverseImageAdj.{u, r} Λ (a ≫ b)).homEquiv _ _).injective
  rw [etaleModuleInverseImageRestrictionIso, Adjunction.homEquiv_leftAdjointUniq_hom_app,
    etaleModuleRestrictionDirectImageAdj_unit_comp, Adjunction.homEquiv_unit]
  have hb := Adjunction.unit_leftAdjointUniq_hom_app (etaleModuleInverseImageAdj.{u, r} Λ b)
    (etaleModuleRestrictionDirectImageAdj.{u, r} Λ b) M
  have ha := Adjunction.unit_leftAdjointUniq_hom_app (etaleModuleInverseImageAdj.{u, r} Λ a)
    (etaleModuleRestrictionDirectImageAdj.{u, r} Λ a) ((etaleModuleRestriction.{u, r} Λ b).obj M)
  have nu := (etaleModuleInverseImageAdj.{u, r} Λ a).unit.naturality
    ((etaleModuleInverseImageRestrictionIso.{u, r} Λ b).hom.app M)
  have nd := (etaleModuleDirectImageComp.{u, r} Λ a b (a ≫ b) rfl).hom.naturality
    ((etaleModuleInverseImage.{u, r} Λ a).map
      ((etaleModuleInverseImageRestrictionIso.{u, r} Λ b).hom.app M))
  have nd' := (etaleModuleDirectImageComp.{u, r} Λ a b (a ≫ b) rfl).hom.naturality
    ((etaleModuleInverseImageRestrictionIso.{u, r} Λ a).hom.app
      ((etaleModuleRestriction.{u, r} Λ b).obj M))
  simp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj] at nu nd nd'
  simp only [Functor.map_comp]
  exact ir_comp_chain (etaleModuleDirectImage.{u, r} Λ b)
    (rc := (etaleModuleDirectImage.{u, r} Λ (a ≫ b)).map
      ((etaleModuleRestrictionCompIso.{u, r} Λ a b).hom.app M))
    (hU := etaleModuleInverseImageAdj_unit_comp Λ a b M) (hb := hb) (ha := ha) (nu := nu) (nd := nd)
    (nd' := nd')

end Unit

/-! ### The counit `j^{-1} j_! ≅ 𝟭` along a composite, on sheaves -/

section Counit

variable (Λ₀ : Type) [Ring Λ₀] {X U V : Scheme.{u}} (a : X ⟶ U) (b : U ⟶ V)

/-- The unit of extension by zero against restriction along a composite is the composite of the
units, read through the composition isomorphisms of extensions by zero and of restrictions. -/
lemma etaleModuleExtensionByZeroAdj_unit_comp [Etale a] [Etale b]
    (F : EtaleModules.{u, r} Λ X) :
    (etaleModuleExtensionByZeroAdj.{u, r} Λ (a ≫ b)).unit.app F =
      (etaleModuleExtensionByZeroAdj.{u, r} Λ a).unit.app F ≫
        (etaleModuleRestriction.{u, r} Λ a).map
          ((etaleModuleExtensionByZeroAdj.{u, r} Λ b).unit.app
            ((etaleModuleExtensionByZero.{u, r} Λ a).obj F)) ≫
        (etaleModuleRestriction.{u, r} Λ a).map ((etaleModuleRestriction.{u, r} Λ b).map
          ((etaleModuleExtensionByZeroCompIso.{u, r} Λ a b).inv.app F)) ≫
        (etaleModuleRestrictionCompIso.{u, r} Λ a b).hom.app
          ((etaleModuleExtensionByZero.{u, r} Λ (a ≫ b)).obj F) := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    (etaleModuleExtensionByZeroAdj.{u, r} Λ (a ≫ b))
    (((etaleModuleExtensionByZeroAdj.{u, r} Λ a).comp
      (etaleModuleExtensionByZeroAdj.{u, r} Λ b)).ofNatIsoRight
        (etaleModuleRestrictionCompIso.{u, r} Λ a b)) F
  rw [comp_ofNatIsoRight_unit_app] at h
  have n := (etaleModuleRestrictionCompIso.{u, r} Λ a b).hom.naturality
    ((etaleModuleExtensionByZeroCompIso.{u, r} Λ a b).inv.app F)
  simp only [Functor.comp_map] at n
  rw [n]
  simp only [Functor.comp_obj]
  rw [← reassoc_of% h, ← Functor.map_comp]
  refine (Category.comp_id _).symm.trans (whisker_eq _ ?_)
  exact ((etaleModuleRestriction.{u, r} Λ (a ≫ b)).map_id _).symm.trans
    (congrArg (etaleModuleRestriction.{u, r} Λ (a ≫ b)).map
      ((etaleModuleExtensionByZeroCompIso.{u, r} Λ a b).hom_inv_id_app F).symm)

/-- An identity between two composites of morphisms in `C` that follows from the commutation
relations `hr`, `n1`, `n2` and `n3`. -/
lemma counit_comp_chain {C : Type*} [Category* C] {P₀ Q₀ Q₁ Q₂ Q₃ F Q₀' Q₁' Q₂' Q₄ Q₅ : C}
    (iC : P₀ ⟶ Q₀) (A1 : Q₀ ⟶ Q₁) (A2 : Q₁ ⟶ Q₂) (rC : Q₂ ⟶ Q₃) (iu : Q₃ ⟶ F)
    (B1 : Q₀ ⟶ Q₀') (B2 : Q₀' ⟶ Q₁') (B3 : Q₁' ⟶ Q₄) (B4 : Q₄ ⟶ Q₅) (B5 : Q₅ ⟶ F)
    (C1 : Q₁ ⟶ Q₁') (A2' : Q₁' ⟶ Q₂') (D1 : Q₂ ⟶ Q₂') (D2 : Q₂' ⟶ Q₅)
    (hr : rC ≫ iu = D1 ≫ D2 ≫ B5) (n1 : B1 ≫ B2 = A1 ≫ C1) (n2 : C1 ≫ A2' = A2 ≫ D1)
    (n3 : B3 ≫ B4 = A2' ≫ D2) :
    iC ≫ A1 ≫ A2 ≫ rC ≫ iu = iC ≫ B1 ≫ B2 ≫ B3 ≫ B4 ≫ B5 := by
  rw [hr, ← reassoc_of% n2, ← reassoc_of% n1, reassoc_of% n3]

/-- An identity between two composites of morphisms in `C₂` that follows from the given commutation
relations and the inverse pairs `i1`, `i2`, `i3` and `i4`. -/
lemma derived_counit_chain {C₀ C₁ C₂ : Type*} [Category* C₀] [Category* C₁] [Category* C₂]
    (G1 : C₁ ⥤ C₂) (G2 : C₀ ⥤ C₁) {n0 n1 n2 n3 n4 : C₀} {m2 m3 m4 m5 : C₁}
    {P S0 S1 S2 S3 T : C₂}
    (ic : P ⟶ G1.obj (G2.obj n0)) (u : n0 ⟶ n1) (e : n1 ⟶ n2) (eb : G2.obj n2 ⟶ m2)
    (ea : G1.obj m2 ⟶ T) (q : n0 ⟶ n3) (ub : n3 ⟶ n4) (rbua : n4 ⟶ n2)
    (eb₁ : G2.obj n4 ⟶ m3) (ua : m3 ⟶ m2) (fb : G2.obj n3 ⟶ m4) (dbQ : m4 ⟶ m3)
    (fa : G1.obj m3 ⟶ S3) (daQ : S3 ⟶ T) (fb₂ : G2.obj n0 ⟶ m5) (ibq : m5 ⟶ m4)
    (fa₂ : G1.obj m4 ⟶ S2) (iadb : S2 ⟶ S3) (fa₃ : G1.obj m5 ⟶ S1) (iaibq : S1 ⟶ S2)
    (fab : P ⟶ S0) (dabQ : S0 ⟶ T) (fai : S1 ⟶ G1.obj m5) (fbi : m5 ⟶ G2.obj n0)
    (ich : G1.obj (G2.obj n0) ⟶ P) (cQ : S1 ⟶ S0) (fabi : S0 ⟶ P)
    (F1 : u ≫ e = q ≫ ub ≫ rbua) (nεb : G2.map rbua ≫ eb = eb₁ ≫ ua)
    (F2 : G2.map ub ≫ eb₁ = fb ≫ dbQ) (F3 : G1.map ua ≫ ea = fa ≫ daQ)
    (nfb : G2.map q ≫ fb = fb₂ ≫ ibq) (nfa : G1.map dbQ ≫ fa = fa₂ ≫ iadb)
    (nfa2 : G1.map ibq ≫ fa₂ = fa₃ ≫ iaibq) (F5 : fai ≫ G1.map fbi ≫ ich = cQ ≫ fabi)
    (i1 : fa₃ ≫ fai = 𝟙 _) (i2 : fb₂ ≫ fbi = 𝟙 _) (i3 : ic ≫ ich = 𝟙 _)
    (i4 : fabi ≫ fab = 𝟙 _) (H : cQ ≫ dabQ = iaibq ≫ iadb ≫ daQ) :
    fab ≫ dabQ = ic ≫ G1.map (G2.map u) ≫ G1.map (G2.map e) ≫ 𝟙 _ ≫ G1.map eb ≫ 𝟙 _ ≫ ea := by
  have hfab : fab = ic ≫ G1.map fb₂ ≫ fa₃ ≫ cQ := by
    calc fab = ic ≫ ich ≫ fab := by rw [reassoc_of% i3]
      _ = ic ≫ G1.map fb₂ ≫ fa₃ ≫ fai ≫ G1.map fbi ≫ ich ≫ fab := by
        rw [reassoc_of% i1, ← G1.map_comp_assoc, i2, G1.map_id, Category.id_comp]
      _ = ic ≫ G1.map fb₂ ≫ fa₃ ≫ cQ := by
        rw [reassoc_of% F5, i4, Category.comp_id]
  simp only [Category.id_comp]
  symm
  calc ic ≫ G1.map (G2.map u) ≫ G1.map (G2.map e) ≫ G1.map eb ≫ ea
      = ic ≫ G1.map (G2.map (u ≫ e) ≫ eb) ≫ ea := by simp
    _ = ic ≫ G1.map (G2.map q ≫ G2.map ub ≫ G2.map rbua ≫ eb) ≫ ea := by rw [F1]; simp
    _ = ic ≫ G1.map (G2.map q ≫ fb ≫ dbQ ≫ ua) ≫ ea := by rw [nεb, reassoc_of% F2]
    _ = ic ≫ G1.map fb₂ ≫ G1.map ibq ≫ G1.map dbQ ≫ G1.map ua ≫ ea := by
        rw [reassoc_of% nfb]; simp
    _ = ic ≫ G1.map fb₂ ≫ fa₃ ≫ iaibq ≫ iadb ≫ daQ := by
        rw [F3, reassoc_of% nfa, reassoc_of% nfa2]
    _ = fab ≫ dabQ := by rw [← H, hfab]; simp

variable [IsOpenImmersion a] [IsOpenImmersion b]

/-- The comparison `j^{-1} j_! ≅ 𝟭` is the comparison of inverse image with restriction followed
by the inverse of the unit. -/
lemma etaleModuleExtensionByZeroInverseImageIso_hom_app {U' X' : Scheme.{u}} (j : U' ⟶ X')
    [IsOpenImmersion j] (G : EtaleModules.{u, 0} Λ₀ U') :
    (etaleModuleExtensionByZeroInverseImageIso Λ₀ j).hom.app G =
      (etaleModuleInverseImageRestrictionIso.{u, 0} Λ₀ j).hom.app
          ((etaleModuleExtensionByZero.{u, 0} Λ₀ j).obj G) ≫
        inv ((etaleModuleExtensionByZeroAdj.{u, 0} Λ₀ j).unit.app G) := by
  simp [etaleModuleExtensionByZeroInverseImageIso, NatIso.isIso_inv_app]

/-- The counit `j^{-1} j_! ≅ 𝟭` along a composite of open immersions, on sheaves of modules: the
comparison for `b ∘ a` is that of `b` followed by that of `a`, read through
`(b ∘ a)^{-1} ≅ a^{-1} ∘ b^{-1}` and `(b ∘ a)_! ≅ b_! ∘ a_!`. -/
theorem etaleModuleExtensionByZeroInverseImageIso_comp (F : EtaleModules.{u, 0} Λ₀ X) :
    (etaleModuleExtensionByZeroInverseImageIso Λ₀ (a ≫ b)).hom.app F =
      (etaleModuleInverseImageCompIso.{u, 0} Λ₀ a b).hom.app
          ((etaleModuleExtensionByZero.{u, 0} Λ₀ (a ≫ b)).obj F) ≫
        (etaleModuleInverseImage.{u, 0} Λ₀ a).map ((etaleModuleInverseImage.{u, 0} Λ₀ b).map
          ((etaleModuleExtensionByZeroCompIso.{u, 0} Λ₀ a b).hom.app F)) ≫
        (etaleModuleInverseImage.{u, 0} Λ₀ a).map
          ((etaleModuleExtensionByZeroInverseImageIso Λ₀ b).hom.app
            ((etaleModuleExtensionByZero.{u, 0} Λ₀ a).obj F)) ≫
        (etaleModuleExtensionByZeroInverseImageIso Λ₀ a).hom.app F := by
  rw [etaleModuleExtensionByZeroInverseImageIso_hom_app,
    etaleModuleExtensionByZeroInverseImageIso_hom_app,
    etaleModuleExtensionByZeroInverseImageIso_hom_app, etaleModuleInverseImageRestrictionIso_comp,
    Functor.map_comp]
  have hr : (etaleModuleRestrictionCompIso.{u, 0} Λ₀ a b).hom.app
        ((etaleModuleExtensionByZero.{u, 0} Λ₀ (a ≫ b)).obj F) ≫
      inv ((etaleModuleExtensionByZeroAdj.{u, 0} Λ₀ (a ≫ b)).unit.app F) =
      (etaleModuleRestriction.{u, 0} Λ₀ a).map ((etaleModuleRestriction.{u, 0} Λ₀ b).map
          ((etaleModuleExtensionByZeroCompIso.{u, 0} Λ₀ a b).hom.app F)) ≫
        (etaleModuleRestriction.{u, 0} Λ₀ a).map
          (inv ((etaleModuleExtensionByZeroAdj.{u, 0} Λ₀ b).unit.app
            ((etaleModuleExtensionByZero.{u, 0} Λ₀ a).obj F))) ≫
        inv ((etaleModuleExtensionByZeroAdj.{u, 0} Λ₀ a).unit.app F) := by
    rw [IsIso.comp_inv_eq, etaleModuleExtensionByZeroAdj_unit_comp]
    simp only [Category.assoc, IsIso.inv_hom_id_assoc]
    rw [← (etaleModuleRestriction.{u, 0} Λ₀ a).map_comp_assoc (inv _), IsIso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp,
      ← (etaleModuleRestriction.{u, 0} Λ₀ a).map_comp_assoc,
      ← (etaleModuleRestriction.{u, 0} Λ₀ b).map_comp, Iso.hom_inv_id_app,
      CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp]
  have n1 := congrArg (etaleModuleInverseImage.{u, 0} Λ₀ a).map
    ((etaleModuleInverseImageRestrictionIso.{u, 0} Λ₀ b).hom.naturality
      ((etaleModuleExtensionByZeroCompIso.{u, 0} Λ₀ a b).hom.app F))
  have n2 := (etaleModuleInverseImageRestrictionIso.{u, 0} Λ₀ a).hom.naturality
    ((etaleModuleRestriction.{u, 0} Λ₀ b).map
      ((etaleModuleExtensionByZeroCompIso.{u, 0} Λ₀ a b).hom.app F))
  have n3 := (etaleModuleInverseImageRestrictionIso.{u, 0} Λ₀ a).hom.naturality
    (inv ((etaleModuleExtensionByZeroAdj.{u, 0} Λ₀ b).unit.app
      ((etaleModuleExtensionByZero.{u, 0} Λ₀ a).obj F)))
  simp only [Functor.map_comp] at n1
  exact counit_comp_chain _ _ _ _ _ _ _ _ _ _ _ _ _ _ hr n1 n2 n3

end Counit

/-! ### The counit `j^{-1} Rj_! ≅ 𝟭` along a composite, on `D⁺` -/

section DerivedCounit

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

variable (Λ₀ : Type) [Ring Λ₀] {X U V : Scheme.{u}} (a : X ⟶ U) (b : U ⟶ V)
  [IsOpenImmersion a] [IsOpenImmersion b]

/-- The composition isomorphism `R(b ∘ a)_! ≅ Ra_! ∘ Rb_!` of derived extensions by zero. -/
abbrev etaleModuleDerivedExtensionByZeroCompIso :
    etaleModuleDerivedExtensionByZero.{u, 0} Λ₀ (a ≫ b) ≅
      etaleModuleDerivedExtensionByZero.{u, 0} Λ₀ a ⋙
        etaleModuleDerivedExtensionByZero.{u, 0} Λ₀ b :=
  (Functor.rightDerivedFunctorPlusCompIsoOfExact
    (etaleModuleExtensionByZero.{u, 0} Λ₀ a) (etaleModuleExtensionByZero.{u, 0} Λ₀ b)
    (etaleModuleExtensionByZero.{u, 0} Λ₀ (a ≫ b))
    (etaleModuleExtensionByZeroCompIso.{u, 0} Λ₀ a b).symm).symm

/-- The composition isomorphism `(b ∘ a)^{-1} ≅ a^{-1} ∘ b^{-1}` of derived inverse images. -/
abbrev etaleModuleDerivedInverseImagePlusCompIso :
    etaleModuleDerivedInverseImagePlus.{u, 0} Λ₀ b ⋙
        etaleModuleDerivedInverseImagePlus.{u, 0} Λ₀ a ≅
      etaleModuleDerivedInverseImagePlus.{u, 0} Λ₀ (a ≫ b) :=
  Functor.mapDerivedCategoryPlusCompIsoh (etaleModuleInverseImageCompIso.{u, 0} Λ₀ a b).symm

/-- The composite `R(b ∘ a)_! ⋙ (b ∘ a)^{-1} ⟶ 𝟭` through `a` and `b`. -/
def etaleModuleDerivedExtensionByZeroCompInverseImagePlusThrough :
    etaleModuleDerivedExtensionByZero.{u, 0} Λ₀ (a ≫ b) ⋙
        etaleModuleDerivedInverseImagePlus.{u, 0} Λ₀ (a ≫ b) ⟶ 𝟭 _ :=
  Functor.whiskerLeft _ (etaleModuleDerivedInverseImagePlusCompIso Λ₀ a b).inv ≫
    Functor.whiskerRight (etaleModuleDerivedExtensionByZeroCompIso Λ₀ a b).hom _ ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _ (Functor.associator _ _ _).inv ≫
    Functor.whiskerLeft _ (Functor.whiskerRight
      (etaleModuleDerivedExtensionByZeroCompInverseImagePlusIso Λ₀ b).hom _) ≫
    Functor.whiskerLeft _ (Functor.leftUnitor _).hom ≫
    (etaleModuleDerivedExtensionByZeroCompInverseImagePlusIso Λ₀ a).hom

/-- The composition law `etaleModuleExtensionByZeroInverseImageIso_comp` of the counit
`j^{-1} j_! ≅ 𝟭`, on the homotopy category of bounded below complexes. -/
lemma etaleModuleExtensionByZeroInverseImageIso_comp_mapHomotopyCategoryPlus
    (K : HomotopyCategory.Plus (EtaleModules.{u, 0} Λ₀ X)) :
    (Functor.mapHomotopyCategoryPlusNatTrans
        (etaleModuleInverseImageCompIso.{u, 0} Λ₀ a b).symm.hom).app
        ((etaleModuleExtensionByZero.{u, 0} Λ₀ (a ≫ b)).mapHomotopyCategoryPlus.obj K) ≫
      ((Functor.mapHomotopyCategoryPlusNatIso
        (etaleModuleExtensionByZeroInverseImageIso Λ₀ (a ≫ b))).hom.app K :
          (etaleModuleInverseImage.{u, 0} Λ₀ (a ≫ b)).mapHomotopyCategoryPlus.obj
            ((etaleModuleExtensionByZero.{u, 0} Λ₀ (a ≫ b)).mapHomotopyCategoryPlus.obj K) ⟶ K) =
    (etaleModuleInverseImage.{u, 0} Λ₀ a).mapHomotopyCategoryPlus.map
        ((etaleModuleInverseImage.{u, 0} Λ₀ b).mapHomotopyCategoryPlus.map
          ((Functor.mapHomotopyCategoryPlusCompIso
            (etaleModuleExtensionByZeroCompIso.{u, 0} Λ₀ a b).symm).inv.app K :
              (etaleModuleExtensionByZero.{u, 0} Λ₀ (a ≫ b)).mapHomotopyCategoryPlus.obj K ⟶
                (etaleModuleExtensionByZero.{u, 0} Λ₀ b).mapHomotopyCategoryPlus.obj
                  ((etaleModuleExtensionByZero.{u, 0} Λ₀ a).mapHomotopyCategoryPlus.obj K))) ≫
      (etaleModuleInverseImage.{u, 0} Λ₀ a).mapHomotopyCategoryPlus.map
        ((Functor.mapHomotopyCategoryPlusNatIso
          (etaleModuleExtensionByZeroInverseImageIso Λ₀ b)).hom.app
          ((etaleModuleExtensionByZero.{u, 0} Λ₀ a).mapHomotopyCategoryPlus.obj K) :
            (etaleModuleInverseImage.{u, 0} Λ₀ b).mapHomotopyCategoryPlus.obj
              ((etaleModuleExtensionByZero.{u, 0} Λ₀ b).mapHomotopyCategoryPlus.obj
                ((etaleModuleExtensionByZero.{u, 0} Λ₀ a).mapHomotopyCategoryPlus.obj K)) ⟶
              (etaleModuleExtensionByZero.{u, 0} Λ₀ a).mapHomotopyCategoryPlus.obj K) ≫
      ((Functor.mapHomotopyCategoryPlusNatIso
          (etaleModuleExtensionByZeroInverseImageIso Λ₀ a)).hom.app K :
        (etaleModuleInverseImage.{u, 0} Λ₀ a).mapHomotopyCategoryPlus.obj
          ((etaleModuleExtensionByZero.{u, 0} Λ₀ a).mapHomotopyCategoryPlus.obj K) ⟶ K) := by
  let Ea := etaleModuleExtensionByZero.{u, 0} Λ₀ a
  let Eab := etaleModuleExtensionByZero.{u, 0} Λ₀ (a ≫ b)
  let Ia := etaleModuleInverseImage.{u, 0} Λ₀ a
  let Ib := etaleModuleInverseImage.{u, 0} Λ₀ b
  apply (HomotopyCategory.Plus.ι _).map_injective
  change (NatTrans.mapHomotopyCategory (etaleModuleInverseImageCompIso.{u, 0} Λ₀ a b).symm.hom
        (ComplexShape.up ℤ)).app ((Eab.mapHomotopyCategory (ComplexShape.up ℤ)).obj K.obj) ≫
      (NatTrans.mapHomotopyCategory (etaleModuleExtensionByZeroInverseImageIso Λ₀ (a ≫ b)).hom
        (ComplexShape.up ℤ)).app K.obj =
    (Ia.mapHomotopyCategory (ComplexShape.up ℤ)).map
      ((Ib.mapHomotopyCategory (ComplexShape.up ℤ)).map
        ((Functor.mapHomotopyCategoryCompIso (etaleModuleExtensionByZeroCompIso.{u, 0} Λ₀ a b).symm
          (ComplexShape.up ℤ)).inv.app K.obj)) ≫
      (Ia.mapHomotopyCategory (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomotopyCategory (etaleModuleExtensionByZeroInverseImageIso Λ₀ b).hom
          (ComplexShape.up ℤ)).app ((Ea.mapHomotopyCategory (ComplexShape.up ℤ)).obj K.obj)) ≫
      (NatTrans.mapHomotopyCategory (etaleModuleExtensionByZeroInverseImageIso Λ₀ a).hom
        (ComplexShape.up ℤ)).app K.obj
  obtain ⟨K₀⟩ := K.obj
  change (HomotopyCategory.quotient _ _).map
      ((NatTrans.mapHomologicalComplex (etaleModuleInverseImageCompIso.{u, 0} Λ₀ a b).symm.hom
        (ComplexShape.up ℤ)).app ((Eab.mapHomologicalComplex (ComplexShape.up ℤ)).obj K₀)) ≫
      (HomotopyCategory.quotient _ _).map
      ((NatTrans.mapHomologicalComplex (etaleModuleExtensionByZeroInverseImageIso Λ₀ (a ≫ b)).hom
        (ComplexShape.up ℤ)).app K₀) =
    (HomotopyCategory.quotient _ _).map ((Ia.mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((Ib.mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((Functor.mapHomologicalComplexCompIso
          (etaleModuleExtensionByZeroCompIso.{u, 0} Λ₀ a b).symm
          (ComplexShape.up ℤ)).inv.app K₀))) ≫
      (HomotopyCategory.quotient _ _).map ((Ia.mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex (etaleModuleExtensionByZeroInverseImageIso Λ₀ b).hom
          (ComplexShape.up ℤ)).app ((Ea.mapHomologicalComplex (ComplexShape.up ℤ)).obj K₀))) ≫
      (HomotopyCategory.quotient _ _).map
        ((NatTrans.mapHomologicalComplex (etaleModuleExtensionByZeroInverseImageIso Λ₀ a).hom
          (ComplexShape.up ℤ)).app K₀)
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
  congr 1
  ext n
  simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
    Functor.mapHomologicalComplex_map_f, Functor.mapHomologicalComplexCompIso_inv_app_f,
    Iso.symm_hom, Iso.symm_inv, Functor.mapHomologicalComplex_obj_X]
  rw [etaleModuleExtensionByZeroInverseImageIso_comp, Iso.inv_hom_id_app_assoc]

/-- The counit `j^{-1} Rj_! ≅ 𝟭` along a composite of open immersions, on `D⁺`: the comparison for
`b ∘ a` is that of `b` followed by that of `a`, read through `(b ∘ a)^{-1} ≅ a^{-1} ∘ b^{-1}` and
`R(b ∘ a)_! ≅ Rb_! ∘ Ra_!`. -/
theorem etaleModuleDerivedExtensionByZeroCompInverseImagePlusIso_comp :
    (etaleModuleDerivedExtensionByZeroCompInverseImagePlusIso Λ₀ (a ≫ b)).hom =
      etaleModuleDerivedExtensionByZeroCompInverseImagePlusThrough Λ₀ a b := by
  refine ((etaleModuleExtensionByZero.{u, 0} Λ₀ (a ≫ b)).rightDerivedFunctorPlus ⋙
    (etaleModuleInverseImage.{u, 0} Λ₀ (a ≫ b)).mapDerivedCategoryPlus).rightDerived_ext
    (Stacks.Cohomology.DerivedBaseChangePlus.derivedBaseChangePlusUnit _ _)
    (HomotopyCategory.Plus.quasiIso _) _ _ _ (NatTrans.ext (funext fun K ↦ ?_))
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    etaleModuleDerivedExtensionByZeroCompInverseImagePlusThrough, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.leftUnitor_hom_app, Category.id_comp]
  let Ea := etaleModuleExtensionByZero.{u, 0} Λ₀ a
  let Eb := etaleModuleExtensionByZero.{u, 0} Λ₀ b
  let Eab := etaleModuleExtensionByZero.{u, 0} Λ₀ (a ≫ b)
  let Ia := etaleModuleInverseImage.{u, 0} Λ₀ a
  let Ib := etaleModuleInverseImage.{u, 0} Λ₀ b
  let Iab := etaleModuleInverseImage.{u, 0} Λ₀ (a ≫ b)
  let N := Eab.mapHomotopyCategoryPlus.obj K
  let Ka := Ea.mapHomotopyCategoryPlus.obj K
  let CId := (Functor.mapHomotopyCategoryPlusCompIso
    (etaleModuleExtensionByZeroCompIso.{u, 0} Λ₀ a b).symm).inv.app K
  let RCO := Functor.rightDerivedFunctorPlusCompIsoOfExact Ea Eb Eab
    (etaleModuleExtensionByZeroCompIso.{u, 0} Λ₀ a b).symm
  have f1 := Functor.rightDerivedFunctorPlusCompIsoOfExact_fac Ea Eb Eab
    (etaleModuleExtensionByZeroCompIso.{u, 0} Λ₀ a b).symm K
  have F1 : Eab.rightDerivedFunctorPlusUnit.app K ≫ RCO.inv.app (DerivedCategory.Plus.Qh.obj K) =
      DerivedCategory.Plus.Qh.map CId ≫ Eb.rightDerivedFunctorPlusUnit.app Ka ≫
        Eb.rightDerivedFunctorPlus.map (Ea.rightDerivedFunctorPlusUnit.app K) := by
    rw [← cancel_epi (DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusCompIso
          (etaleModuleExtensionByZeroCompIso.{u, 0} Λ₀ a b).symm).hom.app K)),
      ← Category.assoc, ← f1]
    simp [RCO, CId, Ka]
  have F2 := etaleModuleDerivedExtensionByZeroCompInverseImagePlusIso_hom_app_Qh Λ₀ b Ka
  have F3 := etaleModuleDerivedExtensionByZeroCompInverseImagePlusIso_hom_app_Qh Λ₀ a K
  have F4 := etaleModuleDerivedExtensionByZeroCompInverseImagePlusIso_hom_app_Qh Λ₀ (a ≫ b) K
  have F5 := Functor.mapDerivedCategoryPlusCompIsoh_compatible
    (etaleModuleInverseImageCompIso.{u, 0} Λ₀ a b).symm N
  have nic := (etaleModuleDerivedInverseImagePlusCompIso Λ₀ a b).inv.naturality
    (Eab.rightDerivedFunctorPlusUnit.app K)
  have nεb := (etaleModuleDerivedExtensionByZeroCompInverseImagePlusIso Λ₀ b).hom.naturality
    (Ea.rightDerivedFunctorPlusUnit.app K)
  simp only [Functor.comp_map, Functor.id_map] at nic nεb ⊢
  rw [F4, reassoc_of% nic]
  let c := (Functor.mapHomotopyCategoryPlusNatTrans
    (etaleModuleInverseImageCompIso.{u, 0} Λ₀ a b).symm.hom).app N
  let dab : Iab.mapHomotopyCategoryPlus.obj N ⟶ K := (Functor.mapHomotopyCategoryPlusNatIso
    (etaleModuleExtensionByZeroInverseImageIso Λ₀ (a ≫ b))).hom.app K
  let db : Ib.mapHomotopyCategoryPlus.obj (Eb.mapHomotopyCategoryPlus.obj Ka) ⟶ Ka :=
    (Functor.mapHomotopyCategoryPlusNatIso
      (etaleModuleExtensionByZeroInverseImageIso Λ₀ b)).hom.app Ka
  let da : Ia.mapHomotopyCategoryPlus.obj Ka ⟶ K :=
    (Functor.mapHomotopyCategoryPlusNatIso
      (etaleModuleExtensionByZeroInverseImageIso Λ₀ a)).hom.app K
  let CId' : N ⟶ Eb.mapHomotopyCategoryPlus.obj Ka := CId
  have Hd : c ≫ dab = Ia.mapHomotopyCategoryPlus.map (Ib.mapHomotopyCategoryPlus.map CId') ≫
      Ia.mapHomotopyCategoryPlus.map db ≫ da :=
    etaleModuleExtensionByZeroInverseImageIso_comp_mapHomotopyCategoryPlus Λ₀ a b K
  have H : DerivedCategory.Plus.Qh.map c ≫ DerivedCategory.Plus.Qh.map dab =
      DerivedCategory.Plus.Qh.map
          (Ia.mapHomotopyCategoryPlus.map (Ib.mapHomotopyCategoryPlus.map CId')) ≫
        DerivedCategory.Plus.Qh.map (Ia.mapHomotopyCategoryPlus.map db) ≫
        DerivedCategory.Plus.Qh.map da := by
    rw [← Functor.map_comp, Hd]
    exact (DerivedCategory.Plus.Qh.map_comp _ _).trans
      (whisker_eq _ (DerivedCategory.Plus.Qh.map_comp _ _))
  have nfb := Ib.mapDerivedCategoryPlusFactorsh.hom.naturality CId'
  have nfa := Ia.mapDerivedCategoryPlusFactorsh.hom.naturality db
  have nfa2 :=
    Ia.mapDerivedCategoryPlusFactorsh.hom.naturality (Ib.mapHomotopyCategoryPlus.map CId')
  simp only [Functor.comp_map] at nfb nfa nfa2
  exact derived_counit_chain (etaleModuleDerivedInverseImagePlus.{u, 0} Λ₀ a)
    (etaleModuleDerivedInverseImagePlus.{u, 0} Λ₀ b) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ F1 nεb F2 F3 nfb nfa nfa2 F5 (Iso.hom_inv_id_app _ _) (Iso.hom_inv_id_app _ _)
    (Iso.inv_hom_id_app _ _) (Iso.inv_hom_id_app _ _) H

end DerivedCounit

end Stacks.EtaleCohomology

end
