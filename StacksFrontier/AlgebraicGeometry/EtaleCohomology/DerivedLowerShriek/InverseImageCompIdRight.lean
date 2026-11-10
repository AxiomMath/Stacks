module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.ExtensionByZeroCounitCube

/-!
# The right unit law for the composition isomorphisms of inverse images

For `c : X ⟶ Y`, the composition isomorphism `(c ≫ 𝟙_Y)^{-1} ≅ c^{-1} ∘ (𝟙_Y)^{-1}` of inverse
images of étale sheaves of modules is `c^{-1}` of the identification `(𝟙_Y)^{-1} ≅ 𝟭`, on sheaves
and on `D⁺`. The left unit law is
`Stacks.EtaleCohomology.etaleModuleInverseImageCompIso_id_left_hom_app`.

## Main results

* `Stacks.EtaleCohomology.etaleModuleInverseImageCompIso_id_right_hom_app`.
* `Stacks.EtaleCohomology.etaleModuleDerivedInverseImagePlusCompIso_id_right_hom_app`.
* `Stacks.EtaleCohomology.etaleModuleDerivedInverseImagePlusCompIso_id_comp_hom_app`: the left unit
  law for an arbitrary (not necessarily étale) morphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

variable (Λ : Type) [Ring Λ] {X Y : Scheme.{u}} (c : X ⟶ Y)

/-- **The right unit law for the composition of base changes on small étale sites**: the
comparison for `c ≫ 𝟙_Y` is base change along `c` of the inverse of the identification of base
change along `𝟙_Y`. -/
theorem smallEtaleBaseChangeComp'_id_right_hom_app (U : Y.Etale) :
    (smallEtaleBaseChangeComp' c (𝟙 Y) (c ≫ 𝟙 Y) rfl).hom.app U =
      (smallEtaleBaseChange c).map ((smallEtaleBaseChangeId Y).inv.app U) := by
  have hf : ((smallEtaleBaseChangeComp' c (𝟙 Y) (c ≫ 𝟙 Y) rfl).hom.app U).left ≫
      pullback.fst ((smallEtaleBaseChange (𝟙 Y)).obj U).hom c ≫ pullback.fst U.hom (𝟙 Y) =
      ((smallEtaleBaseChange c).map ((smallEtaleBaseChangeId Y).inv.app U)).left ≫
        pullback.fst ((smallEtaleBaseChange (𝟙 Y)).obj U).hom c ≫ pullback.fst U.hom (𝟙 Y) :=
    (smallEtaleBaseChangeComp'_fst_fst c (𝟙 Y) (c ≫ 𝟙 Y) rfl U).trans
      (((ExtensionByZeroPasting.smallEtaleBaseChange_map_left_fst_assoc c _ _).trans
        ((congrArg (fun z => _ ≫ z) (smallEtaleBaseChangeId_inv_app_left_fst Y U)).trans
          (Category.comp_id _))).symm)
  have hs : pullback.snd U.hom (𝟙 Y) = pullback.fst U.hom (𝟙 Y) ≫ U.hom :=
    ((Category.comp_id _).symm.trans pullback.condition.symm)
  refine smallEtaleBaseChange_hom_ext c (pullback.hom_ext ?_ ?_)
  · exact (Category.assoc _ _ _).trans (hf.trans (Category.assoc _ _ _).symm)
  · rw [hs]
    have := congrArg (fun z => z ≫ U.hom) hf
    simp only [Category.assoc] at this ⊢
    exact this

/-- The identification `(𝟙_Y)_* ≅ 𝟭` at `c_* N`, followed by the composition isomorphism of direct
images along `c ≫ 𝟙_Y`, is the identity. -/
lemma pushforwardId_inv_app_comp_etaleModuleDirectImageComp_id_right
    (N : EtaleModules.{u, 0} Λ X) :
    (Functor.sheafPushforwardContinuousId' (smallEtaleBaseChangeId Y) _ _ :
        etaleModuleDirectImage.{u, 0} Λ (𝟙 Y) ≅ 𝟭 _).inv.app
          ((etaleModuleDirectImage.{u, 0} Λ c).obj N) ≫
      (etaleModuleDirectImageComp.{u, 0} Λ c (𝟙 Y) (c ≫ 𝟙 Y) rfl).hom.app N = 𝟙 _ := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun U => ?_))
  change N.obj.map ((smallEtaleBaseChange c).map
      ((smallEtaleBaseChangeId Y).hom.app U.unop)).op ≫
    N.obj.map ((smallEtaleBaseChangeComp' c (𝟙 Y) (c ≫ 𝟙 Y) rfl).hom.app U.unop).op = 𝟙 _
  rw [← Functor.map_comp, ← op_comp, smallEtaleBaseChangeComp'_id_right_hom_app]
  have hab : (smallEtaleBaseChange c).map ((smallEtaleBaseChangeId Y).inv.app U.unop) ≫
      (smallEtaleBaseChange c).map ((smallEtaleBaseChangeId Y).hom.app U.unop) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  exact (congrArg (fun z => N.obj.map z.op) hab).trans (N.obj.map_id _)

/-- The unit of the composite adjunction defining `etaleModuleInverseImageCompIso`, read through
the inverse image along the composite, for arbitrary morphisms (compare
`Stacks.EtaleCohomology.etaleModuleInverseImageAdj_unit_comp`, stated for étale ones). -/
lemma unit_comp_etaleModuleInverseImageCompIso {W V : Scheme.{u}} (a : W ⟶ X) (b : X ⟶ V)
    (M : EtaleModules.{u, 0} Λ V) :
    (etaleModuleInverseImageAdj.{u, 0} Λ (a ≫ b)).unit.app M ≫
        (etaleModuleDirectImage.{u, 0} Λ (a ≫ b)).map
          ((etaleModuleInverseImageCompIso.{u, 0} Λ a b).hom.app M) =
      (etaleModuleInverseImageAdj.{u, 0} Λ b).unit.app M ≫
        (etaleModuleDirectImage.{u, 0} Λ b).map
          ((etaleModuleInverseImageAdj.{u, 0} Λ a).unit.app
            ((etaleModuleInverseImage.{u, 0} Λ b).obj M)) ≫
        (etaleModuleDirectImageComp.{u, 0} Λ a b (a ≫ b) rfl).hom.app _ := by
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app
    (etaleModuleInverseImageAdj.{u, 0} Λ (a ≫ b))
    (((etaleModuleInverseImageAdj.{u, 0} Λ b).comp
      (etaleModuleInverseImageAdj.{u, 0} Λ a)).ofNatIsoRight
        (etaleModuleDirectImageComp.{u, 0} Λ a b (a ≫ b) rfl)) M
  rw [Adjunction.homEquiv_unit] at h
  refine h.trans ?_
  rw [← Adjunction.homEquiv_id, Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.homEquiv_unit,
    CategoryTheory.Functor.map_id]
  simp only [Adjunction.comp_unit_app, Category.assoc]
  rfl

/-- The unit of `(𝟙_Y)^{-1} ⊣ (𝟙_Y)_*` through the identifications of both functors with `𝟭`. -/
lemma etaleModuleInverseImageAdj_id_unit_app (G : EtaleModules.{u, 0} Λ Y) :
    (etaleModuleInverseImageAdj.{u, 0} Λ (𝟙 Y)).unit.app G =
      (Functor.sheafPushforwardContinuousId' (smallEtaleBaseChangeId Y) _ _ :
          etaleModuleDirectImage.{u, 0} Λ (𝟙 Y) ≅ 𝟭 _).inv.app G ≫
        (etaleModuleDirectImage.{u, 0} Λ (𝟙 Y)).map
          ((etaleModuleInverseImageIdIso.{u, 0} Λ Y).inv.app G) := by
  let e : etaleModuleDirectImage.{u, 0} Λ (𝟙 Y) ≅ 𝟭 _ :=
    Functor.sheafPushforwardContinuousId' (smallEtaleBaseChangeId Y) _ _
  have U2 := Adjunction.unit_leftAdjointUniq_hom_app (etaleModuleInverseImageAdj.{u, 0} Λ (𝟙 Y))
    (Adjunction.id.ofNatIsoRight e.symm) G
  have hU2 : (Adjunction.id.ofNatIsoRight e.symm).unit.app G = e.inv.app G := by
    rw [← Adjunction.homEquiv_id, Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.homEquiv_id]
    exact Category.id_comp _
  calc (etaleModuleInverseImageAdj.{u, 0} Λ (𝟙 Y)).unit.app G
      = (etaleModuleInverseImageAdj.{u, 0} Λ (𝟙 Y)).unit.app G ≫
          (etaleModuleDirectImage.{u, 0} Λ (𝟙 Y)).map
            ((etaleModuleInverseImageIdIso.{u, 0} Λ Y).hom.app G ≫
              (etaleModuleInverseImageIdIso.{u, 0} Λ Y).inv.app G) := by
        rw [Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
        exact (Category.comp_id _).symm
    _ = ((etaleModuleInverseImageAdj.{u, 0} Λ (𝟙 Y)).unit.app G ≫
          (etaleModuleDirectImage.{u, 0} Λ (𝟙 Y)).map
            ((etaleModuleInverseImageIdIso.{u, 0} Λ Y).hom.app G)) ≫
          (etaleModuleDirectImage.{u, 0} Λ (𝟙 Y)).map
            ((etaleModuleInverseImageIdIso.{u, 0} Λ Y).inv.app G) := by
        rw [Functor.map_comp, Category.assoc]
    _ = _ := congrArg (fun t => t ≫ _) (U2.trans hU2)

/-- The cancellation pattern of
`Stacks.EtaleCohomology.etaleModuleInverseImageCompIso_id_right_hom_app`, over plain objects. -/
lemma id_right_chain {C : Type*} [Category* C] {G₀ G₁ G₂ G₃ : C} (ei : G₀ ⟶ G₁)
    (m₁ : G₁ ⟶ G₂) (m₂ : G₁ ⟶ G₂) (dc : G₂ ⟶ G₃) (q : G₀ ⟶ G₃) (ei' : G₃ ⟶ G₂)
    (hm : m₁ = m₂) (hn : ei ≫ m₂ = q ≫ ei') (hs : ei' ≫ dc = 𝟙 _) :
    ei ≫ m₁ ≫ dc = q := by
  rw [hm, ← Category.assoc, hn, Category.assoc, hs, Category.comp_id]

/-- **The composition isomorphism of inverse images along `c ≫ 𝟙_Y` is `c^{-1}` of the
identification of the inverse image along `𝟙_Y`**, on sheaves of modules. -/
theorem etaleModuleInverseImageCompIso_id_right_hom_app (G : EtaleModules.{u, 0} Λ Y) :
    (etaleModuleInverseImageCompIso.{u, 0} Λ c (𝟙 Y)).hom.app G =
      (etaleModuleInverseImage.{u, 0} Λ c).map
        ((etaleModuleInverseImageIdIso.{u, 0} Λ Y).inv.app G) := by
  apply ((etaleModuleInverseImageAdj.{u, 0} Λ (c ≫ 𝟙 Y)).homEquiv _ _).injective
  change (etaleModuleInverseImageAdj.{u, 0} Λ (c ≫ 𝟙 Y)).unit.app G ≫
      (etaleModuleDirectImage.{u, 0} Λ (c ≫ 𝟙 Y)).map
        ((etaleModuleInverseImageCompIso.{u, 0} Λ c (𝟙 Y)).hom.app G) =
    (etaleModuleInverseImageAdj.{u, 0} Λ c).unit.app G ≫
      (etaleModuleDirectImage.{u, 0} Λ c).map ((etaleModuleInverseImage.{u, 0} Λ c).map
        ((etaleModuleInverseImageIdIso.{u, 0} Λ Y).inv.app G))
  rw [unit_comp_etaleModuleInverseImageCompIso, etaleModuleInverseImageAdj_id_unit_app,
    Category.assoc, ← Functor.map_comp_assoc]
  have nu := (etaleModuleInverseImageAdj.{u, 0} Λ c).unit.naturality
    ((etaleModuleInverseImageIdIso.{u, 0} Λ Y).inv.app G)
  simp only [Functor.id_map, Functor.comp_map] at nu
  have ne := (Functor.sheafPushforwardContinuousId' (smallEtaleBaseChangeId Y) _ _ :
      etaleModuleDirectImage.{u, 0} Λ (𝟙 Y) ≅ 𝟭 _).inv.naturality
    ((etaleModuleInverseImageAdj.{u, 0} Λ c).unit.app G ≫ (etaleModuleDirectImage.{u, 0} Λ c).map
      ((etaleModuleInverseImage.{u, 0} Λ c).map
        ((etaleModuleInverseImageIdIso.{u, 0} Λ Y).inv.app G)))
  simp only [Functor.id_map] at ne
  exact id_right_chain _ _ _ _ _ _ (congrArg (etaleModuleDirectImage.{u, 0} Λ (𝟙 Y)).map nu)
    ne.symm (pushforwardId_inv_app_comp_etaleModuleDirectImageComp_id_right Λ c _)

/-- `Stacks.EtaleCohomology.etaleModuleInverseImageCompIso_id_right_hom_app`, for the inverse. -/
theorem etaleModuleInverseImageCompIso_id_right_inv_app (G : EtaleModules.{u, 0} Λ Y) :
    (etaleModuleInverseImageCompIso.{u, 0} Λ c (𝟙 Y)).inv.app G =
      (etaleModuleInverseImage.{u, 0} Λ c).map
        ((etaleModuleInverseImageIdIso.{u, 0} Λ Y).hom.app G) :=
  Iso.inv_ext (f := (etaleModuleInverseImageCompIso.{u, 0} Λ c (𝟙 Y)).app G)
    ((congrArg (fun t => t ≫ _) (etaleModuleInverseImageCompIso_id_right_hom_app Λ c G)).trans
      ((Functor.map_comp _ _ _).symm.trans
        ((congrArg (etaleModuleInverseImage.{u, 0} Λ c).map
          (Iso.inv_hom_id_app (etaleModuleInverseImageIdIso.{u, 0} Λ Y) G)).trans
            (CategoryTheory.Functor.map_id _ _))))

/-- The cancellation pattern of
`Stacks.EtaleCohomology.etaleModuleDerivedInverseImagePlusCompIso_id_right_hom_app`, over plain
objects. -/
lemma id_right_derived_chain {C : Type*} [Category* C] {A₀ A₁ A₂ B₀ T : C} (y : A₀ ⟶ A₁)
    (Gx : A₁ ⟶ A₂) (ch : A₂ ⟶ T) (ι₂ : A₂ ⟶ T) (qt : A₀ ⟶ B₀) (z : B₀ ⟶ T) (dq : A₁ ⟶ T)
    [IsIso y] [IsIso Gx]
    (F5 : y ≫ Gx ≫ ch = qt ≫ z) (vθ : Gx ≫ ι₂ = dq) (nf : y ≫ dq = qt ≫ z) : ch = ι₂ := by
  rw [← cancel_epi (y ≫ Gx), Category.assoc, F5, Category.assoc, vθ, nf]

/-- **The composition isomorphism of derived inverse images along `c ≫ 𝟙_Y` is `c^{-1}` of the
identification of the derived inverse image along `𝟙_Y`**, on `D⁺`. -/
theorem etaleModuleDerivedInverseImagePlusCompIso_id_right_hom_app
    (N : DerivedCategory.Plus (EtaleModules.{u, 0} Λ Y)) :
    (etaleModuleDerivedInverseImagePlusCompIso Λ c (𝟙 Y)).hom.app N =
      (etaleModuleDerivedInverseImagePlus.{u, 0} Λ c).map
        ((etaleModuleDerivedInverseImagePlusIdIso Λ Y).hom.app N) := by
  have key : (etaleModuleDerivedInverseImagePlusCompIso Λ c (𝟙 Y)).hom =
      Functor.whiskerRight (etaleModuleDerivedInverseImagePlusIdIso Λ Y).hom
        (etaleModuleDerivedInverseImagePlus.{u, 0} Λ c) := by
    refine Localization.natTrans_ext DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso _)
      (fun K => ?_)
    have F5 := Functor.mapDerivedCategoryPlusCompIsoh_compatible
      (etaleModuleInverseImageCompIso.{u, 0} Λ c (𝟙 Y)).symm K
    have vθ := congrArg (etaleModuleDerivedInverseImagePlus.{u, 0} Λ c).map
      (etaleModuleDerivedInverseImagePlusIdIso_hom_app_Qh Λ Y K)
    simp only [Functor.map_comp] at vθ
    have nf := (etaleModuleInverseImage.{u, 0} Λ c).mapDerivedCategoryPlusFactorsh.inv.naturality
      ((Functor.mapHomotopyCategoryPlusNatIso (etaleModuleInverseImageIdIso.{u, 0} Λ Y)).hom.app K)
    simp only [Functor.comp_map] at nf
    have ht : (Functor.mapHomotopyCategoryPlusNatTrans
        (etaleModuleInverseImageCompIso.{u, 0} Λ c (𝟙 Y)).symm.hom).app K =
        (etaleModuleInverseImage.{u, 0} Λ c).mapHomotopyCategoryPlus.map
          ((Functor.mapHomotopyCategoryPlusNatIso
            (etaleModuleInverseImageIdIso.{u, 0} Λ Y)).hom.app K) := by
      apply (HomotopyCategory.Plus.ι _).map_injective
      change (NatTrans.mapHomotopyCategory
          (etaleModuleInverseImageCompIso.{u, 0} Λ c (𝟙 Y)).symm.hom
          (ComplexShape.up ℤ)).app K.obj =
        ((etaleModuleInverseImage.{u, 0} Λ c).mapHomotopyCategory (ComplexShape.up ℤ)).map
          ((NatTrans.mapHomotopyCategory (etaleModuleInverseImageIdIso.{u, 0} Λ Y).hom
            (ComplexShape.up ℤ)).app K.obj)
      obtain ⟨K₀⟩ := K.obj
      change (HomotopyCategory.quotient _ _).map
          ((NatTrans.mapHomologicalComplex
            (etaleModuleInverseImageCompIso.{u, 0} Λ c (𝟙 Y)).symm.hom
            (ComplexShape.up ℤ)).app K₀) =
        (HomotopyCategory.quotient _ _).map
          (((etaleModuleInverseImage.{u, 0} Λ c).mapHomologicalComplex (ComplexShape.up ℤ)).map
            ((NatTrans.mapHomologicalComplex (etaleModuleInverseImageIdIso.{u, 0} Λ Y).hom
              (ComplexShape.up ℤ)).app K₀))
      congr 1
      refine HomologicalComplex.hom_ext _ _ (fun n => ?_)
      exact etaleModuleInverseImageCompIso_id_right_inv_app Λ c (K₀.X n)
    exact id_right_derived_chain _ _ _ _ _ _ _ F5 vθ
      (nf.symm.trans (congrArg (fun t => DerivedCategory.Plus.Qh.map t ≫
        (etaleModuleInverseImage.{u, 0} Λ c).mapDerivedCategoryPlusFactorsh.inv.app _) ht.symm))
  exact NatTrans.congr_app key N

section IdComp

variable {W : Scheme.{u}} (d : W ⟶ X)

/-- **The composition isomorphism of inverse images along `𝟙_W ≫ d` is the identification of the
inverse image along `𝟙_W`**, on sheaves of modules, for an arbitrary morphism `d` (compare
`Stacks.EtaleCohomology.etaleModuleInverseImageCompIso_id_left_hom_app`, for étale ones). -/
theorem etaleModuleInverseImageCompIso_id_comp_hom_app (G : EtaleModules.{u, 0} Λ X) :
    (etaleModuleInverseImageCompIso.{u, 0} Λ (𝟙 W) d).hom.app G =
      (etaleModuleInverseImageIdIso.{u, 0} Λ W).inv.app
        ((etaleModuleInverseImage.{u, 0} Λ d).obj G) := by
  let N := (etaleModuleInverseImage.{u, 0} Λ d).obj G
  apply ((etaleModuleInverseImageAdj.{u, 0} Λ (𝟙 W ≫ d)).homEquiv _ _).injective
  change (etaleModuleInverseImageAdj.{u, 0} Λ (𝟙 W ≫ d)).unit.app G ≫
      (etaleModuleDirectImage.{u, 0} Λ (𝟙 W ≫ d)).map
        ((etaleModuleInverseImageCompIso.{u, 0} Λ (𝟙 W) d).hom.app G) =
    (etaleModuleInverseImageAdj.{u, 0} Λ d).unit.app G ≫
      (etaleModuleDirectImage.{u, 0} Λ d).map ((etaleModuleInverseImageIdIso.{u, 0} Λ W).inv.app N)
  rw [unit_comp_etaleModuleInverseImageCompIso, etaleModuleInverseImageAdj_id_unit_app,
    Functor.map_comp, Category.assoc]
  have nD := (etaleModuleDirectImageComp.{u, 0} Λ (𝟙 W) d d rfl).hom.naturality
    ((etaleModuleInverseImageIdIso.{u, 0} Λ W).inv.app N)
  simp only [Functor.comp_map] at nD
  exact id_left_chain _ _ _ _ _ _ nD (etaleModuleDirectImage_map_pushforwardId_inv_comp Λ d N)

/-- `Stacks.EtaleCohomology.etaleModuleInverseImageCompIso_id_comp_hom_app`, for the inverse. -/
theorem etaleModuleInverseImageCompIso_id_comp_inv_app (G : EtaleModules.{u, 0} Λ X) :
    (etaleModuleInverseImageCompIso.{u, 0} Λ (𝟙 W) d).inv.app G =
      (etaleModuleInverseImageIdIso.{u, 0} Λ W).hom.app
        ((etaleModuleInverseImage.{u, 0} Λ d).obj G) :=
  Iso.inv_ext (f := (etaleModuleInverseImageCompIso.{u, 0} Λ (𝟙 W) d).app G)
    ((congrArg (fun t => t ≫ _) (etaleModuleInverseImageCompIso_id_comp_hom_app Λ d G)).trans
      (Iso.inv_hom_id_app _ _))

/-- **The composition isomorphism of derived inverse images along `𝟙_W ≫ d` is the
identification of the derived inverse image along `𝟙_W`**, on `D⁺`, for an arbitrary morphism. -/
theorem etaleModuleDerivedInverseImagePlusCompIso_id_comp_hom_app
    (N : DerivedCategory.Plus (EtaleModules.{u, 0} Λ X)) :
    (etaleModuleDerivedInverseImagePlusCompIso Λ (𝟙 W) d).hom.app N =
      (etaleModuleDerivedInverseImagePlusIdIso Λ W).hom.app
        ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ d).obj N) := by
  have key : (etaleModuleDerivedInverseImagePlusCompIso Λ (𝟙 W) d).hom =
      Functor.whiskerLeft (etaleModuleDerivedInverseImagePlus.{u, 0} Λ d)
        (etaleModuleDerivedInverseImagePlusIdIso Λ W).hom := by
    refine Localization.natTrans_ext DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso _)
      (fun K => ?_)
    have F5 := Functor.mapDerivedCategoryPlusCompIsoh_compatible
      (etaleModuleInverseImageCompIso.{u, 0} Λ (𝟙 W) d).symm K
    have vι := etaleModuleDerivedInverseImagePlusIdIso_hom_app_Qh Λ W
      ((etaleModuleInverseImage.{u, 0} Λ d).mapHomotopyCategoryPlus.obj K)
    have nι := (etaleModuleDerivedInverseImagePlusIdIso Λ W).hom.naturality
      ((etaleModuleInverseImage.{u, 0} Λ d).mapDerivedCategoryPlusFactorsh.inv.app K)
    simp only [Functor.id_map] at nι
    have ht : (Functor.mapHomotopyCategoryPlusNatTrans
        (etaleModuleInverseImageCompIso.{u, 0} Λ (𝟙 W) d).symm.hom).app K =
        (Functor.mapHomotopyCategoryPlusNatIso (etaleModuleInverseImageIdIso.{u, 0} Λ W)).hom.app
          ((etaleModuleInverseImage.{u, 0} Λ d).mapHomotopyCategoryPlus.obj K) := by
      apply (HomotopyCategory.Plus.ι _).map_injective
      change (NatTrans.mapHomotopyCategory
          (etaleModuleInverseImageCompIso.{u, 0} Λ (𝟙 W) d).symm.hom
          (ComplexShape.up ℤ)).app K.obj =
        (NatTrans.mapHomotopyCategory (etaleModuleInverseImageIdIso.{u, 0} Λ W).hom
          (ComplexShape.up ℤ)).app (((etaleModuleInverseImage.{u, 0} Λ d).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj K.obj)
      obtain ⟨K₀⟩ := K.obj
      change (HomotopyCategory.quotient _ _).map
          ((NatTrans.mapHomologicalComplex
            (etaleModuleInverseImageCompIso.{u, 0} Λ (𝟙 W) d).symm.hom
            (ComplexShape.up ℤ)).app K₀) =
        (HomotopyCategory.quotient _ _).map
          ((NatTrans.mapHomologicalComplex (etaleModuleInverseImageIdIso.{u, 0} Λ W).hom
            (ComplexShape.up ℤ)).app (((etaleModuleInverseImage.{u, 0} Λ d).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K₀))
      congr 1
      refine HomologicalComplex.hom_ext _ _ (fun n => ?_)
      exact etaleModuleInverseImageCompIso_id_comp_inv_app Λ d (K₀.X n)
    exact id_left_derived_chain _ _ _ _ _ _ _ _ _ F5 vι nι
      (congrArg (fun t => DerivedCategory.Plus.Qh.map t ≫
        (etaleModuleInverseImage.{u, 0} Λ d).mapDerivedCategoryPlusFactorsh.inv.app K) ht)
  exact NatTrans.congr_app key N

end IdComp

end Stacks.EtaleCohomology
