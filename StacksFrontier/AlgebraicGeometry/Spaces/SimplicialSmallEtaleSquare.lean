module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardCocontinuousSquare
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposTwoMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSmallEtaleExchange
public import StacksFrontier.CategoryTheory.Sites.Localization.AndMorphismsTwoSquare

/-!
# The square of an augmented morphism of simplicial algebraic spaces

Let `h : X ⟶ Y` be a morphism of simplicial algebraic spaces with augmentations `a : X → X₋₁`,
`b : Y → Y₋₁` and `h₋₁ : X₋₁ ⟶ Y₋₁` compatible with them (Stacks 0DE7). This file shows that the
square of morphisms of ringed topoi `h₋₁ ∘ a ≅ b ∘ h_étale` commutes up to a canonical
2-isomorphism.

## Main definitions

* `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.pullbackFunctorSquareIso`: for a commutative
  square `p ≫ q = p' ≫ q'` of simplicial algebraic spaces, the two iterated base changes agree.
* `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.pastedPushforwardIso`: for abstract sites, a
  square of continuous functors pasted with a Guitart exact square of cocontinuous ones.
* `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.augmentationSquareTwoIso`: **the
  2-isomorphism `h₋₁ ∘ a ≅ b ∘ h_étale` of morphisms of ringed topoi.**

## Main results

* `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.pastedPushforwardIso_commutes`: structure maps
  that agree after restriction along the two squares paste to compatible structure maps of the
  two composites.
-/

@[expose] public section

open CategoryTheory Opposite CategoryTheory.Limits Simplicial

universe u

namespace AlgebraicGeometry.Space.SimplicialSpacesEtaleSite

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Square

variable {X Y Y' W : SimplicialObject (AlgebraicSpaces B S hS)} (p : X ⟶ Y) (q : Y ⟶ W)
  (p' : X ⟶ Y') (q' : Y' ⟶ W) (w : p ≫ q = p' ≫ q')

include w in
/-- The two maps `(A ×_{W_n} Y_n) ×_{Y_n} X_n ⟶ W_n`, through `A` and through `Y'_n`, are
equal. -/
theorem squareMap_aux {n : SimplexCategoryᵒᵖ} {A : AlgebraicSpaces B S hS} (a : A ⟶ W.obj n) :
    (pullback.fst (pullback.snd a (q.app n)) (p.app n) ≫ pullback.fst a (q.app n)) ≫ a =
      (pullback.snd (pullback.snd a (q.app n)) (p.app n) ≫ p'.app n) ≫ q'.app n := by
  rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition, Category.assoc,
    Category.assoc, ← NatTrans.comp_app, w, NatTrans.comp_app]

/-- The comparison `(A ×_{W_n} Y_n) ×_{Y_n} X_n ⟶ (A ×_{W_n} Y'_n) ×_{Y'_n} X_n` of iterated fibre
products along a commutative square. -/
noncomputable def squareMap {n : SimplexCategoryᵒᵖ} {A : AlgebraicSpaces B S hS}
    (a : A ⟶ W.obj n) :
    pullback (pullback.snd a (q.app n)) (p.app n) ⟶
      pullback (pullback.snd a (q'.app n)) (p'.app n) :=
  pullback.lift (pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _) (pullback.snd _ _ ≫ p'.app n)
    (squareMap_aux p q p' q' w a)) (pullback.snd _ _) (pullback.lift_snd _ _ _)

/-- `squareMap` commutes with the projections to `X_n`. -/
@[reassoc (attr := simp)]
theorem squareMap_snd {n : SimplexCategoryᵒᵖ} {A : AlgebraicSpaces B S hS} (a : A ⟶ W.obj n) :
    squareMap p q p' q' w a ≫ pullback.snd _ _ = pullback.snd _ _ :=
  pullback.lift_snd _ _ _

/-- `squareMap` commutes with the projections to `A`. -/
@[reassoc (attr := simp)]
theorem squareMap_fst_fst {n : SimplexCategoryᵒᵖ} {A : AlgebraicSpaces B S hS}
    (a : A ⟶ W.obj n) :
    squareMap p q p' q' w a ≫ pullback.fst _ _ ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ pullback.fst _ _ :=
  (Category.assoc _ _ _).symm.trans ((eq_whisker (pullback.lift_fst _ _ _) _).trans
    (pullback.lift_fst _ _ _))

/-- The projection of `squareMap` to `Y'_n` is the projection to `X_n` followed by `p'_n`. -/
@[reassoc (attr := simp)]
theorem squareMap_fst_snd {n : SimplexCategoryᵒᵖ} {A : AlgebraicSpaces B S hS}
    (a : A ⟶ W.obj n) :
    squareMap p q p' q' w a ≫ pullback.fst _ _ ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ p'.app n :=
  (Category.assoc _ _ _).symm.trans ((eq_whisker (pullback.lift_fst _ _ _) _).trans
    (pullback.lift_snd _ _ _))

/-- The comparison maps for a square and for its transpose are mutually inverse. -/
@[reassoc (attr := simp)]
theorem squareMap_comp_squareMap {n : SimplexCategoryᵒᵖ} {A : AlgebraicSpaces B S hS}
    (a : A ⟶ W.obj n) :
    squareMap p q p' q' w a ≫ squareMap p' q' p q w.symm a = 𝟙 _ := by
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simp only [Category.assoc, squareMap_fst_fst, Category.id_comp]
    · simp only [Category.assoc, squareMap_fst_snd, squareMap_snd_assoc, Category.id_comp]
      exact pullback.condition.symm
  · simp only [Category.assoc, squareMap_snd, Category.id_comp]

/-- `squareMap` is natural in the object `a : A ⟶ W_n` and in the simplicial degree. -/
theorem squareMap_natural {n m : SimplexCategoryᵒᵖ} {A A' : AlgebraicSpaces B S hS}
    (a : A ⟶ W.obj n) (a' : A' ⟶ W.obj m) (f : A ⟶ A') (φ : n ⟶ m)
    (hf : f ≫ a' = a ≫ W.map φ) (e₁ e₁' e₂ e₂') :
    pullback.map _ _ _ _ (pullback.map a (q.app n) a' (q.app m) f (Y.map φ) (W.map φ) hf.symm
        (q.naturality φ).symm) (X.map φ) (Y.map φ) e₁ e₂ ≫ squareMap p q p' q' w a' =
      squareMap p q p' q' w a ≫ pullback.map _ _ _ _ (pullback.map a (q'.app n) a' (q'.app m) f
        (Y'.map φ) (W.map φ) hf.symm (q'.naturality φ).symm) (X.map φ) (Y'.map φ) e₁' e₂' := by
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simp only [Category.assoc, squareMap_fst_fst, pullback.map, pullback.lift_fst,
        pullback.lift_fst_assoc, squareMap_fst_fst_assoc]
    · simp only [Category.assoc, squareMap_fst_snd, pullback.map, pullback.lift_fst,
        squareMap_fst_snd_assoc, pullback.lift_snd,
        pullback.lift_snd_assoc]
      rw [p'.naturality φ]
  · simp only [Category.assoc, squareMap_snd, pullback.map, pullback.lift_snd, squareMap_snd_assoc]

/-- The comparison of the two iterated base changes of an object along a commutative square. -/
noncomputable def squareHom (V : SimplicialSpacesEtaleSite B S hS W) :
    (pullbackFunctor p).obj ((pullbackFunctor q).obj V) ⟶
      (pullbackFunctor p').obj ((pullbackFunctor q').obj V) :=
  ⟨𝟙 _, squareMap p q p' q' w (n := op V.degree) V.obj.1.hom,
    (squareMap_snd p q p' q' w _).trans ((Category.comp_id _).symm.trans
      (whisker_eq _ (X.map_id _).symm))⟩

/-- The comparisons for a square and for its transpose are mutually inverse. -/
theorem squareHom_comp_squareHom (V : SimplicialSpacesEtaleSite B S hS W) :
    squareHom p q p' q' w V ≫ squareHom p' q' p q w.symm V = 𝟙 _ :=
  Hom.ext (Category.comp_id _) (squareMap_comp_squareMap p q p' q' w _)

/-- `squareHom` is natural in the object of the site. -/
theorem squareHom_naturality {V V' : SimplicialSpacesEtaleSite B S hS W} (g : V ⟶ V') :
    (pullbackFunctor p).map ((pullbackFunctor q).map g) ≫ squareHom p q p' q' w V' =
      squareHom p q p' q' w V ≫ (pullbackFunctor p').map ((pullbackFunctor q').map g) :=
  Hom.ext ((Category.id_comp _).trans (Category.comp_id _).symm)
    (squareMap_natural p q p' q' w V.obj.1.hom V'.obj.1.hom g.hom g.base.op g.w
      (pullback.lift_snd _ _ _).symm (pullback.lift_snd _ _ _).symm (p.naturality _).symm
      (p'.naturality _).symm)

/-- **Stacks 0DE7.** For a commutative square `p ≫ q = p' ≫ q'` of simplicial algebraic spaces,
the two iterated base changes of the spaces-étale sites are canonically isomorphic. -/
noncomputable def pullbackFunctorSquareIso :
    pullbackFunctor q ⋙ pullbackFunctor p ≅ pullbackFunctor q' ⋙ pullbackFunctor p' :=
  NatIso.ofComponents (fun V ↦
    { hom := squareHom p q p' q' w V
      inv := squareHom p' q' p q w.symm V
      hom_inv_id := squareHom_comp_squareHom p q p' q' w V
      inv_hom_id := squareHom_comp_squareHom p' q' p q w.symm V })
    (fun g ↦ squareHom_naturality p q p' q' w g)

end Square


/-! ### Pasting the exchange with a square of continuous functors -/

section Generic

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆ w₁ w₂

variable {A : Type w₂} [Category.{w₁} A]
  {𝒳 : Type u₁} [Category.{v₁} 𝒳] {𝒴 : Type u₂} [Category.{v₂} 𝒴]
  {C₁ : Type u₃} [Category.{v₃} C₁] {C₂ : Type u₄} [Category.{v₄} C₂]
  {D₁ : Type u₅} [Category.{v₅} D₁] {D₂ : Type u₆} [Category.{v₆} D₂]
  {JX : GrothendieckTopology 𝒳} {JY : GrothendieckTopology 𝒴}
  {J₁ : GrothendieckTopology C₁} {J₂ : GrothendieckTopology C₂}
  {K₁ : GrothendieckTopology D₁} {K₂ : GrothendieckTopology D₂}
  {uh : 𝒴 ⥤ 𝒳} {ua : C₁ ⥤ 𝒳} {ub : C₂ ⥤ 𝒴} {uc : C₂ ⥤ C₁} {uf : D₂ ⥤ D₁}
  {q₁ : C₁ ⥤ D₁} {q₂ : C₂ ⥤ D₂}
  [uh.IsContinuous JY JX] [ua.IsContinuous J₁ JX] [ub.IsContinuous J₂ JY]
  [uc.IsContinuous J₂ J₁] [uf.IsContinuous K₂ K₁]
  [q₁.IsCocontinuous J₁ K₁] [q₂.IsCocontinuous J₂ K₂]
  [∀ F : C₁ᵒᵖ ⥤ A, q₁.op.HasPointwiseRightKanExtension F]
  [∀ F : C₂ᵒᵖ ⥤ A, q₂.op.HasPointwiseRightKanExtension F]
  (w : TwoSquare uc q₂ q₁ uf) [w.GuitartExact] (sq : ub ⋙ uh ≅ uc ⋙ ua)

/-- The two composites of a square of sites
`ua ∘ uc ≅ uh ∘ ub` pasted with a Guitart exact square `w` of cocontinuous functors `q₁`, `q₂`:
`f⁻¹ ∘ q₁,* ∘ ua⁻¹ ≅ q₂,* ∘ ub⁻¹ ∘ uh⁻¹`. -/
noncomputable def pastedPushforwardIso :
    (ua.sheafPushforwardContinuous A J₁ JX ⋙ q₁.sheafPushforwardCocontinuous A J₁ K₁) ⋙
        uf.sheafPushforwardContinuous A K₂ K₁ ≅
      uh.sheafPushforwardContinuous A JY JX ⋙
        (ub.sheafPushforwardContinuous A J₂ JY ⋙ q₂.sheafPushforwardCocontinuous A J₂ K₂) :=
  haveI := Functor.isContinuous_comp uc ua J₂ J₁ JX
  haveI := Functor.isContinuous_comp ub uh J₂ JY JX
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (Stacks.Sites.CocontinuousExchange.sheafIsoOfTwoSquareAndMorphismsTwoSquare
        A J₂ J₁ K₂ K₁ w).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.sheafPushforwardContinuousComp uc ua A J₂ J₁ JX ≪≫
      (Functor.sheafPushforwardContinuousIso sq A J₂ JX).symm ≪≫
      (Functor.sheafPushforwardContinuousComp ub uh A J₂ JY JX).symm) _ ≪≫
    Functor.associator _ _ _

/-- On underlying presheaves, `pastedPushforwardIso` is the base change of right Kan extensions
followed by right Kan extension of the square. -/
theorem pastedPushforwardIso_hom_app_hom (M : Sheaf JX A) :
    ((pastedPushforwardIso (A := A) (JX := JX) (JY := JY) (J₁ := J₁) (J₂ := J₂) (K₁ := K₁)
        (K₂ := K₂) w sq).hom.app
        M).hom =
      w.op.ranBaseChange.app (ua.op ⋙ M.obj) ≫
        q₂.op.ran.map (Functor.whiskerRight (NatTrans.op sq.hom) M.obj) := by
  have := Functor.isContinuous_comp uc ua J₂ J₁ JX
  have := Functor.isContinuous_comp ub uh J₂ JY JX
  have h₁ : (uc.sheafPushforwardContinuousComp ua A J₂ J₁ JX).hom.app M = 𝟙 _ := rfl
  have h₂ : (ub.sheafPushforwardContinuousComp uh A J₂ JY JX).inv.app M = 𝟙 _ := rfl
  simp only [pastedPushforwardIso, Iso.trans_hom, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.symm_hom,
    Functor.sheafPushforwardContinuousIso_inv, h₁, h₂,
    Category.id_comp, Category.comp_id]
  exact congrArg₂ (· ≫ ·)
    (Stacks.Sites.CocontinuousExchange.sheafIsoOfTwoSquare_inv_app_hom_andMorphismsTwoSquare
      A J₂ J₁ K₂ K₁ w _)
    (congrArg (fun k ↦ q₂.op.ran.map k) ((Category.id_comp _).trans (Category.comp_id _)))

omit [∀ F : C₁ᵒᵖ ⥤ A, q₁.op.HasPointwiseRightKanExtension F]
  [∀ F : C₂ᵒᵖ ⥤ A, q₂.op.HasPointwiseRightKanExtension F] in
/-- Naturality of the counit of a right Kan extension, componentwise. -/
@[reassoc]
theorem ran_map_app_ranCounit_app {C D : Type*} [Category* C] [Category* D] (L : C ⥤ D)
    [∀ F : C ⥤ A, L.HasRightKanExtension F] {F G : C ⥤ A} (φ : F ⟶ G) (X : C) :
    (L.ran.map φ).app (L.obj X) ≫ (L.ranCounit.app G).app X =
      (L.ranCounit.app F).app X ≫ φ.app X :=
  congr_app (L.ranCounit.naturality φ) X

omit [w.GuitartExact] in
/-- On presheaves: the structure maps paste across `pastedPushforwardIso` as soon as they do
after restriction to `C₂`, where the right Kan extensions disappear. -/
theorem pasted_ran_comp_eq {P₁ : D₁ᵒᵖ ⥤ A} {P₂ : D₂ᵒᵖ ⥤ A} {PX : 𝒳ᵒᵖ ⥤ A} {PY : 𝒴ᵒᵖ ⥤ A}
    (φf : P₂ ⟶ uf.op ⋙ P₁) (φa : q₁.op ⋙ P₁ ⟶ ua.op ⋙ PX) (φb : q₂.op ⋙ P₂ ⟶ ub.op ⋙ PY)
    (φh : PY ⟶ uh.op ⋙ PX)
    (H : ∀ U : C₂ᵒᵖ, φf.app (q₂.op.obj U) ≫ P₁.map (w.app U.unop).op ≫ φa.app (uc.op.obj U) ≫
      PX.map (sq.hom.app U.unop).op = φb.app U ≫ φh.app (ub.op.obj U)) :
    φf ≫ Functor.whiskerLeft uf.op ((q₁.op.ranAdjunction A).unit.app P₁ ≫ q₁.op.ran.map φa) ≫
        w.op.ranBaseChange.app (ua.op ⋙ PX) ≫
          q₂.op.ran.map (Functor.whiskerRight (NatTrans.op sq.hom) PX) =
      (q₂.op.ranAdjunction A).unit.app P₂ ≫ q₂.op.ran.map φb ≫
        q₂.op.ran.map (Functor.whiskerLeft ub.op φh) := by
  refine Functor.hom_ext_of_isRightKanExtension _ (q₂.op.ranCounit.app _) _ _ ?_
  ext U
  have fac := Stacks.SheafOfModules.ranBaseChange_fac w.op (ua.op ⋙ PX) U
  have u₁ := ((q₁.op.ranAdjunction A).unit.app P₁).naturality (w.op.app U)
  have n₁ := (q₁.op.ran.map φa).naturality (w.op.app U)
  dsimp only [Functor.id_obj, Functor.comp_obj, Functor.whiskeringLeft_obj_obj] at u₁
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Category.assoc,
    ran_map_app_ranCounit_app]
  rw [ran_map_app_ranCounit_app q₂.op (G := (ub ⋙ uh).op ⋙ PX)
    (Functor.whiskerLeft ub.op φh : _ ⟶ (ub ⋙ uh).op ⋙ PX) U, ran_map_app_ranCounit_app_assoc]
  simp only [Functor.whiskeringLeft_obj_obj]
  rw [Functor.ranCounit_app_app_ranAdjunction_unit_app_app_assoc, reassoc_of% fac,
    ← reassoc_of% n₁, ← reassoc_of% u₁]
  simp only [Functor.comp_obj]
  rw [ran_map_app_ranCounit_app_assoc q₁.op φa (uc.op.obj U),
    Functor.ranCounit_app_app_ranAdjunction_unit_app_app_assoc]
  exact H U

/-- **The structure maps paste.** Let `q₁, q₂` be continuous and cocontinuous, and let structure
maps `fS : O₂ ⟶ f_*O₁`, `aS : q₁⁻¹O₁ ⟶ ua⁻¹O_X`, `bS : q₂⁻¹O₂ ⟶ ub⁻¹O_Y`, `hS : O_Y ⟶ uh⁻¹O_X`
agree after restriction to `C₂` along the two squares. Then the composite structure maps of
`f ∘ q₁,* ∘ ua⁻¹` and of `q₂,* ∘ ub⁻¹ ∘ uh⁻¹` correspond under `pastedPushforwardIso`. -/
theorem pastedPushforwardIso_commutes [q₁.IsContinuous J₁ K₁] [q₂.IsContinuous J₂ K₂]
    {O₁ : Sheaf K₁ A} {O₂ : Sheaf K₂ A} {OX : Sheaf JX A} {OY : Sheaf JY A}
    (fS : O₂ ⟶ (uf.sheafPushforwardContinuous A K₂ K₁).obj O₁)
    (aS : (q₁.sheafPushforwardContinuous A J₁ K₁).obj O₁ ⟶
      (ua.sheafPushforwardContinuous A J₁ JX).obj OX)
    (bS : (q₂.sheafPushforwardContinuous A J₂ K₂).obj O₂ ⟶
      (ub.sheafPushforwardContinuous A J₂ JY).obj OY)
    (hS : OY ⟶ (uh.sheafPushforwardContinuous A JY JX).obj OX)
    (H : ∀ U : C₂ᵒᵖ, fS.hom.app (q₂.op.obj U) ≫ O₁.obj.map (w.app U.unop).op ≫
      aS.hom.app (uc.op.obj U) ≫ OX.obj.map (sq.hom.app U.unop).op =
        bS.hom.app U ≫ hS.hom.app (ub.op.obj U)) :
    fS ≫ (uf.sheafPushforwardContinuous A K₂ K₁).map
        ((q₁.sheafAdjunctionCocontinuous A J₁ K₁).unit.app O₁ ≫
          (q₁.sheafPushforwardCocontinuous A J₁ K₁).map aS) ≫
        (pastedPushforwardIso (A := A) (JX := JX) (JY := JY) (J₁ := J₁) (J₂ := J₂) (K₁ := K₁)
          (K₂ := K₂) w sq).hom.app OX =
      ((q₂.sheafAdjunctionCocontinuous A J₂ K₂).unit.app O₂ ≫
          (q₂.sheafPushforwardCocontinuous A J₂ K₂).map bS) ≫
        (q₂.sheafPushforwardCocontinuous A J₂ K₂).map
          ((ub.sheafPushforwardContinuous A J₂ JY).map hS) := by
  refine ObjectProperty.hom_ext _ ?_
  change fS.hom ≫ Functor.whiskerLeft uf.op
      (((q₁.sheafAdjunctionCocontinuous A J₁ K₁).unit.app O₁).hom ≫ q₁.op.ran.map aS.hom) ≫
        ((pastedPushforwardIso (A := A) (JX := JX) (JY := JY) (J₁ := J₁) (J₂ := J₂) (K₁ := K₁)
          (K₂ := K₂) w sq).hom.app OX).hom =
    (((q₂.sheafAdjunctionCocontinuous A J₂ K₂).unit.app O₂).hom ≫ q₂.op.ran.map bS.hom) ≫
      q₂.op.ran.map (Functor.whiskerLeft ub.op hS.hom)
  rw [Functor.sheafAdjunctionCocontinuous_unit_app_hom,
    Functor.sheafAdjunctionCocontinuous_unit_app_hom, pastedPushforwardIso_hom_app_hom]
  exact (pasted_ran_comp_eq w sq fS.hom aS.hom bS.hom hS.hom H).trans (Category.assoc _ _ _).symm

end Generic

/-! ### The commutative square of ringed topoi -/

section TwoIso

open RingedToposHom Stacks.Sheaves.ToposPushforward

variable {X Y : SimplicialObject (AlgebraicSpaces B S hS)} {Z₁ Z₂ : AlgebraicSpaces B S hS}
  (h : X ⟶ Y) (a : X ⟶ (Functor.const _).obj Z₁) (b : Y ⟶ (Functor.const _).obj Z₂)
  (f : Z₁ ⟶ Z₂) (w : h ≫ b = a ≫ (Functor.const _).map f)

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for the pointwise right Kan extension along `constForget Z`
/-- Right Kan extensions along forgetting the degree exist (cached: instance search for it is
slow). -/
instance hasPointwiseRightKanExtension_constForget_simplicialSmallEtaleSquare
    (Z : AlgebraicSpaces B S hS)
    (G : (SimplicialSpacesEtaleSite B S hS ((Functor.const _).obj Z))ᵒᵖ ⥤ Type (u + 1)) :
    (constForget Z).op.HasPointwiseRightKanExtension G := inferInstance

/-- The structure map of forgetting the degree is the unit of the adjunction `ε⁻¹ ⊣ ε_*`. -/
theorem forgetFSharp_constRingedToposHom (Z : AlgebraicSpaces B S hS) :
    forgetFSharp (constRingedToposHom Z) =
      (constToposHom Z).adj.unit.app
        ((spacesEtaleRingedTopos B S hS Z).forgetRing.obj
          (SpacesEtale.structureSheaf B S hS Z)) := by
  refine (forget_map_commRingImageAdjunction_homEquiv (constToposHom Z) _ _ _).trans ?_
  exact (congrArg ((constToposHom Z).adj.homEquiv _ _)
      (Stacks.Sheaves.ToposPullback.restrictionCommRingIso_hom_forget
        (topology ((Functor.const _).obj Z)) (SpacesEtale.topology B S hS Z) (constForget Z)
        (SpacesEtale.structureSheaf B S hS Z))).trans
    (((constToposHom Z).adj.homEquiv_unit _ _ _).trans
      ((whisker_eq _ ((constToposHom Z).pushforward.map_id _)).trans (Category.comp_id _)))

/-- The underlying structure map of `spacesEtaleRingedToposHom f` at `V` is restriction of
global functions along the projection of the base change of `V` along `f`. -/
theorem forgetFSharp_spacesEtaleRingedToposHom_app (V : (SpacesEtale B S hS Z₂)ᵒᵖ) :
    (spacesEtaleRingedToposHom f).forgetFSharp.hom.app V =
      (forget CommRingCat.{u + 1}).map ((globalFunctionsPresheaf B S hS).map
        ((spacesBaseChange B S hS f).projection.app V.unop).op) := rfl

/-- The underlying structure map of `ringedToposHom h` at `V` is restriction of global functions
along the projection of the base change of `V` along `h`. -/
theorem forgetFSharp_ringedToposHom_app (V : (SimplicialSpacesEtaleSite B S hS Y)ᵒᵖ) :
    (ringedToposHom h).forgetFSharp.hom.app V =
      (forget CommRingCat.{u + 1}).map ((globalFunctionsPresheaf B S hS).map
        ((pullbackFunctorProjection h).app V.unop).op) := rfl

/-- The restriction maps of the underlying sheaf of the structure sheaf on `Z_spaces,étale` are
restriction of global functions. -/
theorem spacesEtale_forgetRing_map (Z : AlgebraicSpaces B S hS) {V W : (SpacesEtale B S hS Z)ᵒᵖ}
    (k : V ⟶ W) :
    ((spacesEtaleRingedTopos B S hS Z).forgetRing.obj
        (spacesEtaleRingedTopos B S hS Z).O).obj.map k =
      (forget CommRingCat.{u + 1}).map ((globalFunctionsPresheaf B S hS).map
        ((SpacesEtale.toSpaces B S hS Z).map k.unop).op) := rfl

/-- The restriction maps of the underlying sheaf of the structure sheaf on `X_spaces,étale` are
restriction of global functions. -/
theorem ringedTopos_forgetRing_map {V W : (SimplicialSpacesEtaleSite B S hS X)ᵒᵖ} (k : V ⟶ W) :
    ((ringedTopos X).forgetRing.obj (ringedTopos X).O).obj.map k =
      (forget CommRingCat.{u + 1}).map ((globalFunctionsPresheaf B S hS).map
        ((toSpaces X).map k.unop).op) := rfl

/-- Four morphisms composed contravariantly through a functor out of an opposite category. -/
theorem map_op_comp_eq {C E : Type*} [Category* C] [Category* E] (G : Cᵒᵖ ⥤ E)
    {X₀ X₁ X₂ X₃ X₄ Y₁ : C} {x₁ : X₁ ⟶ X₀} {x₂ : X₂ ⟶ X₁} {x₃ : X₃ ⟶ X₂} {x₄ : X₄ ⟶ X₃}
    {y₁ : Y₁ ⟶ X₀} {y₂ : X₄ ⟶ Y₁} (h : x₄ ≫ x₃ ≫ x₂ ≫ x₁ = y₂ ≫ y₁) :
    G.map x₁.op ≫ G.map x₂.op ≫ G.map x₃.op ≫ G.map x₄.op = G.map y₁.op ≫ G.map y₂.op := by
  conv_rhs => rw [← G.map_comp, ← op_comp, ← h]
  simp only [op_comp, Functor.map_comp, Category.assoc]

/-- The projections of the two iterated base changes of an object `V/Y₋₁` of the square agree. -/
theorem augmentationSquare_projection_comp
    (V : SimplicialSpacesEtaleSite B S hS ((Functor.const _).obj Z₂)) :
    (toSpaces X).map ((pullbackFunctorSquareIso h b a ((Functor.const _).map f) w).hom.app V) ≫
        (pullbackFunctorProjection a).app ((pullbackFunctor ((Functor.const _).map f)).obj V) ≫
          (SpacesEtale.toSpaces B S hS Z₁).map ((constForgetTwoSquare f).app V) ≫
            (spacesBaseChange B S hS f).projection.app ((constForget Z₂).obj V) =
      (pullbackFunctorProjection h).app ((pullbackFunctor b).obj V) ≫
        (pullbackFunctorProjection b).app V := by
  have hw : (SpacesEtale.toSpaces B S hS Z₁).map ((constForgetTwoSquare f).app V) = 𝟙 _ :=
    (SpacesEtale.toSpaces B S hS Z₁).map_id _
  refine (whisker_eq _ (whisker_eq _ ((eq_whisker hw _).trans (Category.id_comp _)))).trans ?_
  exact squareMap_fst_fst h b a ((Functor.const _).map f) w V.obj.1.hom

/-- An augmentation, restricted along a map `n ⟶ [0]`, is its component at `n`. -/
private theorem map_comp_app_zero {T : SimplicialObject (AlgebraicSpaces B S hS)}
    {Z : AlgebraicSpaces B S hS} (c : T ⟶ (Functor.const _).obj Z) {n : SimplexCategoryᵒᵖ}
    (φ : n ⟶ op ⦋0⦌) : T.map φ ≫ c.app (op ⦋0⦌) = c.app n :=
  (c.naturality φ).trans (Category.comp_id _)

/-- The square of augmentations commutes in every degree as soon as it commutes in degree `0`:
`h₋₁ ∘ a₀ = b₀ ∘ h₀` implies `b ∘ h = const(h₋₁) ∘ a`. -/
theorem comp_eq_of_app_zero
    (w₀ : h.app (op ⦋0⦌) ≫ b.app (op ⦋0⦌) = a.app (op ⦋0⦌) ≫ f) :
    h ≫ b = a ≫ (Functor.const _).map f := by
  refine NatTrans.ext (funext fun n ↦ ?_)
  let φ : n ⟶ op ⦋0⦌ := (SimplexCategory.const ⦋0⦌ n.unop 0).op
  calc (h ≫ b).app n = h.app n ≫ Y.map φ ≫ b.app (op ⦋0⦌) := by rw [map_comp_app_zero b]; rfl
    _ = X.map φ ≫ h.app (op ⦋0⦌) ≫ b.app (op ⦋0⦌) := by
        rw [← Category.assoc, ← h.naturality φ, Category.assoc]
    _ = X.map φ ≫ a.app (op ⦋0⦌) ≫ f := by rw [w₀]
    _ = (a ≫ (Functor.const _).map f).app n := by rw [← Category.assoc, map_comp_app_zero a]; rfl

set_option maxHeartbeats 400000 in
-- the `commutes` proof rewrites through large composites of ringed topos morphisms
/-- **Stacks 0DE7.** For a morphism `h : X ⟶ Y` of simplicial algebraic spaces with
augmentations `a : X → X₋₁`, `b : Y → Y₋₁` and a morphism `h₋₁ : X₋₁ ⟶ Y₋₁` with
`h₋₁ ∘ a₀ = b₀ ∘ h₀`, the square of morphisms of ringed topoi commutes:
`h₋₁ ∘ a ≅ b ∘ h_étale` as morphisms `(Sh(X_étale), 𝒪_X) ⟶ (Sh(Y₋₁,étale), 𝒪_{Y₋₁})`. -/
noncomputable def augmentationSquareTwoIso
    (w₀ : h.app (op ⦋0⦌) ≫ b.app (op ⦋0⦌) = a.app (op ⦋0⦌) ≫ f) :
    TwoIso (A := ringedTopos X) (B := spacesEtaleRingedTopos B S hS Z₂)
      (RingedToposHom.comp (X := ringedTopos X) (Y := spacesEtaleRingedTopos B S hS Z₁)
        (Z := spacesEtaleRingedTopos B S hS Z₂) (spacesEtaleRingedToposHom f)
        (augmentationRingedToposHom a))
      (RingedToposHom.comp (X := ringedTopos X) (Y := ringedTopos Y)
        (Z := spacesEtaleRingedTopos B S hS Z₂) (augmentationRingedToposHom b)
        (ringedToposHom h)) where
  e := pastedPushforwardIso (A := Type (u + 1)) (JX := topology X) (JY := topology Y)
    (J₁ := topology ((Functor.const _).obj Z₁)) (J₂ := topology ((Functor.const _).obj Z₂))
    (K₁ := SpacesEtale.topology B S hS Z₁) (K₂ := SpacesEtale.topology B S hS Z₂)
    (constForgetTwoSquare f)
    (pullbackFunctorSquareIso h b a ((Functor.const _).map f) (comp_eq_of_app_zero h a b f w₀))
  commutes := by
    have ha : forgetFSharp (augmentationRingedToposHom a) =
        forgetFSharp (constRingedToposHom Z₁) ≫ (constRingedToposHom Z₁).toToposHom.pushforward.map
          (forgetFSharp (ringedToposHom a)) :=
        forgetFSharp_comp.{u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1} _ _
    have hb : forgetFSharp (augmentationRingedToposHom b) =
        forgetFSharp (constRingedToposHom Z₂) ≫ (constRingedToposHom Z₂).toToposHom.pushforward.map
          (forgetFSharp (ringedToposHom b)) :=
        forgetFSharp_comp.{u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1} _ _
    refine (eq_whisker
      (forgetFSharp_comp.{u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1}
        (spacesEtaleRingedToposHom f) (augmentationRingedToposHom a)) _).trans
      (Eq.trans ?_
        (forgetFSharp_comp.{u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1}
          (augmentationRingedToposHom b) (ringedToposHom h)).symm)
    rw [ha, hb, forgetFSharp_constRingedToposHom, forgetFSharp_constRingedToposHom]
    refine (Category.assoc _ _ _).trans (pastedPushforwardIso_commutes _ _ _ _ _ _ (fun U ↦ ?_))
    rw [forgetFSharp_spacesEtaleRingedToposHom_app, forgetFSharp_ringedToposHom_app,
      forgetFSharp_ringedToposHom_app, forgetFSharp_ringedToposHom_app, spacesEtale_forgetRing_map,
      ringedTopos_forgetRing_map]
    exact map_op_comp_eq (globalFunctionsPresheaf B S hS ⋙ forget CommRingCat.{u + 1})
      (augmentationSquare_projection_comp h a b f (comp_eq_of_app_zero h a b f w₀) U.unop)

end TwoIso

end AlgebraicGeometry.Space.SimplicialSpacesEtaleSite
