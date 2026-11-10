module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.ExtensionByZeroCounitComp
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.ExtensionByZeroRestrict

/-!
# The counit `j^{-1} Rj_! ≅ 𝟭` along a composite, through the base change isomorphism

For open immersions `a : X ⟶ U` and `b : U ⟶ V`, the comparison `(b ∘ a)^{-1} R(b ∘ a)_! ≅ 𝟭` on
`D⁺` is `a^{-1}` of the isomorphism `b^{-1} R(b ∘ a)_! ≅ Ra_! (𝟙_X)^{-1}` of [Stacks, Tag 03S6] for
the cartesian square `X = X ×_V U`, followed by the comparison for `a` and `(𝟙_X)^{-1} ≅ 𝟭`.

## Main results

* `Stacks.EtaleCohomology.etaleModuleDerivedExtensionByZeroCompInverseImagePlusIso_comp_cube`:
  the counit along a composite through the isomorphism of [Stacks, Tag 03S6].
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

variable (Λ : Type) [Ring Λ] {X U V : Scheme.{u}} (a : X ⟶ U) (b : U ⟶ V)
  [IsOpenImmersion a] [IsOpenImmersion b]

/-- The cancellation pattern of
`Stacks.EtaleCohomology.etaleModuleDerivedExtensionByZeroCompInverseImagePlusIso_comp_cube`, over
plain objects. -/
lemma counit_cube_chain {C D : Type*} [Category* C] [Category* D] (G : C ⥤ D) {P : D}
    {A₁ A₂ A₃ A₄ : C} {T₁ T₂ : D} (ic : P ⟶ G.obj A₁) (e : A₁ ⟶ A₂) (εb : A₂ ⟶ A₃)
    (cubeInv : A₁ ⟶ A₄) (rι : A₄ ⟶ A₃) (εa : G.obj A₃ ⟶ T₂) (εa' : G.obj A₄ ⟶ T₁)
    (ι : T₁ ⟶ T₂) (h2 : e ≫ εb ≫ 𝟙 _ = cubeInv ≫ rι ≫ 𝟙 _) (n : G.map rι ≫ εa = εa' ≫ ι) :
    ic ≫ G.map e ≫ 𝟙 _ ≫ G.map εb ≫ 𝟙 _ ≫ εa = ic ≫ G.map cubeInv ≫ εa' ≫ ι := by
  simp only [Category.comp_id] at h2
  rw [Category.id_comp, Category.id_comp, ← G.map_comp_assoc, h2, G.map_comp_assoc, n]

/-- **The counit along a composite through the isomorphism of [Stacks, Tag 03S6]**: for the
cartesian square `X = X ×_V U` of the open immersions `a`, `b ∘ a` and `b`, the comparison
`(b ∘ a)^{-1} R(b ∘ a)_! ≅ 𝟭` is `(b ∘ a)^{-1} ≅ a^{-1} ∘ b^{-1}`, then `a^{-1}` of
`b^{-1} R(b ∘ a)_! ≅ Ra_! (𝟙_X)^{-1}`, then the comparison for `a` and `(𝟙_X)^{-1} ≅ 𝟭`. -/
theorem etaleModuleDerivedExtensionByZeroCompInverseImagePlusIso_comp_cube
    (hc : IsPullback (𝟙 X) a (a ≫ b) b) (B : DerivedCategory.Plus (EtaleModules.{u, 0} Λ X)) :
    (etaleModuleDerivedExtensionByZeroCompInverseImagePlusIso Λ (a ≫ b)).hom.app B =
      (etaleModuleDerivedInverseImagePlusCompIso Λ a b).inv.app
          ((etaleModuleDerivedExtensionByZero.{u, 0} Λ (a ≫ b)).obj B) ≫
        (etaleModuleDerivedInverseImagePlus.{u, 0} Λ a).map
          ((etaleModuleDerivedExtensionByZeroCubeIso Λ hc).inv.app B) ≫
        (etaleModuleDerivedExtensionByZeroCompInverseImagePlusIso Λ a).hom.app
          ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ (𝟙 X)).obj B) ≫
        (etaleModuleDerivedInverseImagePlusIdIso Λ X).hom.app B := by
  have h1 :=
    NatTrans.congr_app (etaleModuleDerivedExtensionByZeroCompInverseImagePlusIso_comp Λ a b) B
  have h2 := NatTrans.congr_app (etaleModuleDerivedExtensionByZeroRestrictIso_hom Λ a b hc) B
  simp only [etaleModuleDerivedExtensionByZeroCompInverseImagePlusThrough, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.leftUnitor_hom_app, Category.id_comp,
    Functor.comp_map] at h1
  simp only [etaleModuleDerivedExtensionByZeroRestrictIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.rightUnitor_hom_app,
    Functor.leftUnitor_hom_app, Category.id_comp] at h2
  have n := (etaleModuleDerivedExtensionByZeroCompInverseImagePlusIso Λ a).hom.naturality
    ((etaleModuleDerivedInverseImagePlusIdIso Λ X).hom.app B)
  simp only [Functor.comp_map, Functor.id_map] at n
  rw [h1]
  exact counit_cube_chain (etaleModuleDerivedInverseImagePlus.{u, 0} Λ a) _ _ _ _ _ _ _ _ h2 n

/-! ### The composition isomorphism of inverse images along `𝟙 ≫ c` -/

section IdComp

omit [IsOpenImmersion a] [IsOpenImmersion b] in
/-- **The left unit law for the composition of base changes on small étale sites**: the
comparison for `𝟙_X ≫ c` is the inverse of the identification of base change along `𝟙_X`. -/
theorem smallEtaleBaseChangeComp'_id_left_hom_app_eq_id_inv {Y : Scheme.{u}} (c : X ⟶ Y)
    (U : Y.Etale) :
    (smallEtaleBaseChangeComp' (𝟙 X) c c rfl).hom.app U =
      (smallEtaleBaseChangeId X).inv.app ((smallEtaleBaseChange c).obj U) := by
  refine smallEtaleBaseChange_hom_ext (𝟙 X) ?_
  rw [smallEtaleBaseChangeId_inv_app_left_fst]
  have h := smallEtaleBaseChangeComp'_fst_fst (𝟙 X) c c rfl U
  refine pullback.hom_ext ((Category.assoc _ _ _).trans (h.trans (Category.id_comp _).symm)) ?_
  have w := MorphismProperty.Over.w ((smallEtaleBaseChangeComp' (𝟙 X) c c rfl).hom.app U)
  have hc := pullback.condition (f := ((smallEtaleBaseChange c).obj U).hom) (g := 𝟙 X)
  exact (Category.assoc _ _ _).trans ((whisker_eq _ (hc.trans (Category.comp_id _))).trans
    (w.trans (Category.id_comp _).symm))

omit [IsOpenImmersion a] [IsOpenImmersion b] in
/-- `c_*` of the identification `𝟙_* ≅ 𝟭` followed by the composition isomorphism of direct
images along `𝟙_X ≫ c` is the identity. -/
lemma etaleModuleDirectImage_map_pushforwardId_inv_comp {Y : Scheme.{u}} (c : X ⟶ Y)
    (N : EtaleModules.{u, 0} Λ X) :
    (etaleModuleDirectImage.{u, 0} Λ c).map
        ((Functor.sheafPushforwardContinuousId' (smallEtaleBaseChangeId X) _ _ :
          etaleModuleDirectImage.{u, 0} Λ (𝟙 X) ≅ 𝟭 _).inv.app N) ≫
      (etaleModuleDirectImageComp.{u, 0} Λ (𝟙 X) c c rfl).hom.app N = 𝟙 _ := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun U => ?_))
  change N.obj.map ((smallEtaleBaseChangeId X).hom.app ((smallEtaleBaseChange c).obj U.unop)).op ≫
      N.obj.map ((smallEtaleBaseChangeComp' (𝟙 X) c c rfl).hom.app U.unop).op = 𝟙 _
  rw [← Functor.map_comp, ← op_comp, smallEtaleBaseChangeComp'_id_left_hom_app_eq_id_inv,
    Iso.inv_hom_id_app]
  exact N.obj.map_id _

/-- The cancellation pattern of
`Stacks.EtaleCohomology.etaleModuleInverseImageCompIso_id_left_hom_app`, over plain objects. -/
lemma id_left_chain {C : Type*} [Category* C] {P Q₀ Q₁ Q₂ Q₃ : C} (uc : P ⟶ Q₀)
    (A1 : Q₀ ⟶ Q₁) (A2 : Q₁ ⟶ Q₂) (D' : Q₂ ⟶ Q₃) (D : Q₁ ⟶ Q₀) (B : Q₀ ⟶ Q₃)
    (nD : A2 ≫ D' = D ≫ B) (S : A1 ≫ D = 𝟙 _) : uc ≫ A1 ≫ A2 ≫ D' = uc ≫ B := by
  rw [nD, reassoc_of% S]

omit [IsOpenImmersion a] [IsOpenImmersion b] in
/-- **The composition isomorphism of inverse images along `𝟙_X ≫ c` is the identification of the
inverse image along `𝟙_X`**, on sheaves of modules. -/
theorem etaleModuleInverseImageCompIso_id_left_hom_app {Y : Scheme.{u}} (c : X ⟶ Y) [Etale c]
    (G : EtaleModules.{u, 0} Λ Y) :
    (etaleModuleInverseImageCompIso.{u, 0} Λ (𝟙 X) c).hom.app G =
      (etaleModuleInverseImageIdIso.{u, 0} Λ X).inv.app
        ((etaleModuleInverseImage.{u, 0} Λ c).obj G) := by
  let N := (etaleModuleInverseImage.{u, 0} Λ c).obj G
  apply ((etaleModuleInverseImageAdj.{u, 0} Λ (𝟙 X ≫ c)).homEquiv _ _).injective
  change (etaleModuleInverseImageAdj.{u, 0} Λ (𝟙 X ≫ c)).unit.app G ≫
      (etaleModuleDirectImage.{u, 0} Λ (𝟙 X ≫ c)).map
        ((etaleModuleInverseImageCompIso.{u, 0} Λ (𝟙 X) c).hom.app G) =
    (etaleModuleInverseImageAdj.{u, 0} Λ c).unit.app G ≫
      (etaleModuleDirectImage.{u, 0} Λ c).map ((etaleModuleInverseImageIdIso.{u, 0} Λ X).inv.app N)
  rw [etaleModuleInverseImageAdj_unit_comp]
  let e : etaleModuleDirectImage.{u, 0} Λ (𝟙 X) ≅ 𝟭 _ :=
    Functor.sheafPushforwardContinuousId' (smallEtaleBaseChangeId X) _ _
  have U2 := Adjunction.unit_leftAdjointUniq_hom_app (etaleModuleInverseImageAdj.{u, 0} Λ (𝟙 X))
    (Adjunction.id.ofNatIsoRight e.symm) N
  have hU2 : (Adjunction.id.ofNatIsoRight e.symm).unit.app N = e.inv.app N := by
    rw [← Adjunction.homEquiv_id, Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.homEquiv_id]
    exact Category.id_comp _
  have hu : (etaleModuleInverseImageAdj.{u, 0} Λ (𝟙 X)).unit.app N =
      e.inv.app N ≫ (etaleModuleDirectImage.{u, 0} Λ (𝟙 X)).map
        ((etaleModuleInverseImageIdIso.{u, 0} Λ X).inv.app N) := by
    calc (etaleModuleInverseImageAdj.{u, 0} Λ (𝟙 X)).unit.app N
        = (etaleModuleInverseImageAdj.{u, 0} Λ (𝟙 X)).unit.app N ≫
            (etaleModuleDirectImage.{u, 0} Λ (𝟙 X)).map
              ((etaleModuleInverseImageIdIso.{u, 0} Λ X).hom.app N ≫
                (etaleModuleInverseImageIdIso.{u, 0} Λ X).inv.app N) := by
          rw [Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
          exact (Category.comp_id _).symm
      _ = ((etaleModuleInverseImageAdj.{u, 0} Λ (𝟙 X)).unit.app N ≫
            (etaleModuleDirectImage.{u, 0} Λ (𝟙 X)).map
              ((etaleModuleInverseImageIdIso.{u, 0} Λ X).hom.app N)) ≫
            (etaleModuleDirectImage.{u, 0} Λ (𝟙 X)).map
              ((etaleModuleInverseImageIdIso.{u, 0} Λ X).inv.app N) := by
          rw [Functor.map_comp, Category.assoc]
      _ = _ := congrArg (fun t => t ≫ _) (U2.trans hU2)
  have nD := (etaleModuleDirectImageComp.{u, 0} Λ (𝟙 X) c c rfl).hom.naturality
    ((etaleModuleInverseImageIdIso.{u, 0} Λ X).inv.app N)
  simp only [Functor.comp_map] at nD
  rw [hu, Functor.map_comp, Category.assoc]
  exact id_left_chain _ _ _ _ _ _ nD (etaleModuleDirectImage_map_pushforwardId_inv_comp Λ c N)

omit [IsOpenImmersion a] [IsOpenImmersion b] in
/-- `Stacks.EtaleCohomology.etaleModuleInverseImageCompIso_id_left_hom_app`, for the inverse. -/
theorem etaleModuleInverseImageCompIso_id_left_inv_app {Y : Scheme.{u}} (c : X ⟶ Y) [Etale c]
    (G : EtaleModules.{u, 0} Λ Y) :
    (etaleModuleInverseImageCompIso.{u, 0} Λ (𝟙 X) c).inv.app G =
      (etaleModuleInverseImageIdIso.{u, 0} Λ X).hom.app
        ((etaleModuleInverseImage.{u, 0} Λ c).obj G) :=
  Iso.inv_ext (f := (etaleModuleInverseImageCompIso.{u, 0} Λ (𝟙 X) c).app G)
    ((congrArg (fun t => t ≫ _) (etaleModuleInverseImageCompIso_id_left_hom_app Λ c G)).trans
      (Iso.inv_hom_id_app _ _))

/-- The cancellation pattern of
`Stacks.EtaleCohomology.etaleModuleDerivedInverseImagePlusCompIso_id_left_hom_app`, over plain
objects. -/
lemma id_left_derived_chain {C : Type*} [Category* C] {A₀ A₁ A₂ B₀ B₁ T : C} (y : A₀ ⟶ A₁)
    (Gx : A₁ ⟶ A₂) (ch : A₂ ⟶ T) (ι₂ : A₂ ⟶ T) (qt : A₀ ⟶ B₀) (z : B₀ ⟶ T) (ι₁ : A₁ ⟶ B₁)
    (qi : A₀ ⟶ B₁) (x : B₁ ⟶ T) [IsIso y] [IsIso Gx]
    (F5 : y ≫ Gx ≫ ch = qt ≫ z) (vι : y ≫ ι₁ = qi) (nι : Gx ≫ ι₂ = ι₁ ≫ x)
    (H : qt ≫ z = qi ≫ x) : ch = ι₂ := by
  rw [← cancel_epi (y ≫ Gx), Category.assoc, F5, H, ← vι, Category.assoc, ← nι, Category.assoc]

omit [IsOpenImmersion a] [IsOpenImmersion b] in
/-- **The composition isomorphism of derived inverse images along `𝟙_X ≫ c` is the
identification of the derived inverse image along `𝟙_X`**, on `D⁺`. -/
theorem etaleModuleDerivedInverseImagePlusCompIso_id_left_hom_app {Y : Scheme.{u}} (c : X ⟶ Y)
    [Etale c] (N : DerivedCategory.Plus (EtaleModules.{u, 0} Λ Y)) :
    (etaleModuleDerivedInverseImagePlusCompIso Λ (𝟙 X) c).hom.app N =
      (etaleModuleDerivedInverseImagePlusIdIso Λ X).hom.app
        ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ c).obj N) := by
  have key : (etaleModuleDerivedInverseImagePlusCompIso Λ (𝟙 X) c).hom =
      Functor.whiskerLeft (etaleModuleDerivedInverseImagePlus.{u, 0} Λ c)
        (etaleModuleDerivedInverseImagePlusIdIso Λ X).hom := by
    refine Localization.natTrans_ext DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso _)
      (fun K => ?_)
    have F5 := Functor.mapDerivedCategoryPlusCompIsoh_compatible
      (etaleModuleInverseImageCompIso.{u, 0} Λ (𝟙 X) c).symm K
    have vι := etaleModuleDerivedInverseImagePlusIdIso_hom_app_Qh Λ X
      ((etaleModuleInverseImage.{u, 0} Λ c).mapHomotopyCategoryPlus.obj K)
    have nι := (etaleModuleDerivedInverseImagePlusIdIso Λ X).hom.naturality
      ((etaleModuleInverseImage.{u, 0} Λ c).mapDerivedCategoryPlusFactorsh.inv.app K)
    simp only [Functor.id_map] at nι
    have ht : (Functor.mapHomotopyCategoryPlusNatTrans
        (etaleModuleInverseImageCompIso.{u, 0} Λ (𝟙 X) c).symm.hom).app K =
        (Functor.mapHomotopyCategoryPlusNatIso (etaleModuleInverseImageIdIso.{u, 0} Λ X)).hom.app
          ((etaleModuleInverseImage.{u, 0} Λ c).mapHomotopyCategoryPlus.obj K) := by
      apply (HomotopyCategory.Plus.ι _).map_injective
      change (NatTrans.mapHomotopyCategory
          (etaleModuleInverseImageCompIso.{u, 0} Λ (𝟙 X) c).symm.hom
          (ComplexShape.up ℤ)).app K.obj =
        (NatTrans.mapHomotopyCategory (etaleModuleInverseImageIdIso.{u, 0} Λ X).hom
          (ComplexShape.up ℤ)).app (((etaleModuleInverseImage.{u, 0} Λ c).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj K.obj)
      obtain ⟨K₀⟩ := K.obj
      change (HomotopyCategory.quotient _ _).map
          ((NatTrans.mapHomologicalComplex
            (etaleModuleInverseImageCompIso.{u, 0} Λ (𝟙 X) c).symm.hom
            (ComplexShape.up ℤ)).app K₀) =
        (HomotopyCategory.quotient _ _).map
          ((NatTrans.mapHomologicalComplex (etaleModuleInverseImageIdIso.{u, 0} Λ X).hom
            (ComplexShape.up ℤ)).app (((etaleModuleInverseImage.{u, 0} Λ c).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K₀))
      congr 1
      refine HomologicalComplex.hom_ext _ _ (fun n => ?_)
      exact etaleModuleInverseImageCompIso_id_left_inv_app Λ c (K₀.X n)
    exact id_left_derived_chain _ _ _ _ _ _ _ _ _ F5 vι nι
      (congrArg (fun t => DerivedCategory.Plus.Qh.map t ≫
        (etaleModuleInverseImage.{u, 0} Λ c).mapDerivedCategoryPlusFactorsh.inv.app K) ht)
  exact NatTrans.congr_app key N

end IdComp


/-! ### The counit through the base change isomorphism of the trivial square -/

section CounitTrivial

/-- The cancellation pattern of
`Stacks.EtaleCohomology.etaleModuleDerivedExtensionByZeroCompInverseImagePlusIso_hom_app_eq_cube`,
over plain objects. -/
lemma counit_trivial_chain {C : Type*} [Category* C] {A₀ A₁ A₂ A₃ A₄ A₅ : C} (E : A₀ ⟶ A₅)
    (ci : A₀ ⟶ A₁) (G : A₁ ⟶ A₂) (e1 : A₂ ⟶ A₄) (e2 : A₄ ⟶ A₅) (i' : A₀ ⟶ A₁) (q : A₀ ⟶ A₃)
    (ii : A₃ ⟶ A₂) (h : E = ci ≫ G ≫ e1 ≫ e2) (hι : ci = i') (n : q ≫ ii = i' ≫ G) :
    E = q ≫ ii ≫ e1 ≫ e2 := by
  rw [h, hι, ← reassoc_of% n]

omit [IsOpenImmersion a] [IsOpenImmersion b] in
/-- **The comparison `c^{-1} Rc_! ≅ 𝟭` through the isomorphism of [Stacks, Tag 03S6] for the
square `X = X ×_V X`**: it is that isomorphism `c^{-1} Rc_! ≅ R(𝟙_X)_! (𝟙_X)^{-1}` followed by a
comparison `R(𝟙_X)_! (𝟙_X)^{-1} ≅ 𝟭` that does not depend on `c`. -/
theorem etaleModuleDerivedExtensionByZeroCompInverseImagePlusIso_hom_app_eq_cube (c : X ⟶ V)
    [IsOpenImmersion c] (hc : IsPullback (𝟙 X) (𝟙 X) c c)
    (B : DerivedCategory.Plus (EtaleModules.{u, 0} Λ X)) :
    (etaleModuleDerivedExtensionByZeroCompInverseImagePlusIso Λ c).hom.app B =
      (etaleModuleDerivedExtensionByZeroCubeIso Λ hc).inv.app B ≫
        (etaleModuleDerivedInverseImagePlusIdIso Λ X).inv.app
          ((etaleModuleDerivedExtensionByZero.{u, 0} Λ (𝟙 X)).obj
            ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ (𝟙 X)).obj B)) ≫
        (etaleModuleDerivedExtensionByZeroCompInverseImagePlusIso Λ (𝟙 X)).hom.app
          ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ (𝟙 X)).obj B) ≫
        (etaleModuleDerivedInverseImagePlusIdIso Λ X).hom.app B := by
  have h := etaleModuleDerivedExtensionByZeroCompInverseImagePlusIso_comp_cube Λ (𝟙 X) c hc B
  have hι : (etaleModuleDerivedInverseImagePlusCompIso Λ (𝟙 X) c).inv.app
      ((etaleModuleDerivedExtensionByZero.{u, 0} Λ c).obj B) =
      (etaleModuleDerivedInverseImagePlusIdIso Λ X).inv.app
        ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ c).obj
          ((etaleModuleDerivedExtensionByZero.{u, 0} Λ c).obj B)) :=
    (Iso.inv_eq_inv ((etaleModuleDerivedInverseImagePlusCompIso Λ (𝟙 X) c).app _)
      ((etaleModuleDerivedInverseImagePlusIdIso Λ X).app _)).mpr
        (etaleModuleDerivedInverseImagePlusCompIso_id_left_hom_app Λ c _)
  have n := (etaleModuleDerivedInverseImagePlusIdIso Λ X).inv.naturality
    ((etaleModuleDerivedExtensionByZeroCubeIso Λ hc).inv.app B)
  simp only [Functor.id_map] at n
  exact counit_trivial_chain _ _ _ _ _ _ _ _ h hι n

end CounitTrivial

end Stacks.EtaleCohomology

end
