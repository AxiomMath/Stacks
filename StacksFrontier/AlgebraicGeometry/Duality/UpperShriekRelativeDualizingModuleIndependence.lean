module

public import StacksFrontier.AlgebraicGeometry.Duality.FiniteTwistedTraceRestriction

/-!
# Independence of the chart identifications of `H⁰(f^!𝒪_Y)` from the finite factorization

Let `f : X ⟶ Y` be a quasi-finite morphism of `FTS_S` factoring as `X ⟶ T₁ ⟶ Y` (open immersion,
then finite), and let `h : T ⟶ T₁` be finite with `i ≫ h = i₁` cartesian over `𝟙 X`. The
identifications `H⁰(f^!𝒪_Y) ≅ H⁰(a 𝒪_Y)|_X` computed through `T₁` and through `T` differ by the
trace of `h`, so the chart identifications with `ω_{B/A}` of [Stacks, Tag 0BUL] agree.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory DerivedCategory

universe u

namespace Stacks.Duality

open Stacks.Discriminant DerivedPushforward

variable {S : Scheme.{u}} [IsNoetherian S] {X Y : FTS S} {f : X ⟶ Y} [LocallyQuasiFinite f.left]

omit [LocallyQuasiFinite f.left] in
/-- The identification `H⁰(f^!𝒪_Y) ≅ H⁰(a 𝒪_Y)|_X`, unfolded. -/
theorem upperShriekStructureSheafZerothIso_hom (F : OpenFiniteFactorization f)
    (j : CompactificationOf (Over.mk f.left)) :
    (upperShriekStructureSheafZerothIso F j).hom =
      (homologyFunctor X.left.Modules 0).map
          (((DominatingCompactification.upperShriekPlusIso f j F.compactification).hom.app
              (structurePlus Y)).hom.hom ≫
            ((restrictedDerivedRestrictAdjointIso F.immersion).inv.app
              ((FiniteTrace.twisted F.toBase).obj (derivedStructureSheaf Y.left))).hom) ≫
        (((Scheme.Modules.restrictFunctor F.immersion).mapDerivedCategoryHomologyIso 0).app
          ((FiniteTrace.twisted F.toBase).obj (derivedStructureSheaf Y.left)).obj).hom :=
  rfl

omit [LocallyQuasiFinite f.left] in
/-- The inverse identification `H⁰(a 𝒪_Y)|_X ≅ H⁰(f^!𝒪_Y)`, unfolded. -/
theorem upperShriekStructureSheafZerothIso_inv (F : OpenFiniteFactorization f)
    (j : CompactificationOf (Over.mk f.left)) :
    (upperShriekStructureSheafZerothIso F j).inv =
      (((Scheme.Modules.restrictFunctor F.immersion).mapDerivedCategoryHomologyIso 0).app
          ((FiniteTrace.twisted F.toBase).obj (derivedStructureSheaf Y.left)).obj).inv ≫
        (homologyFunctor X.left.Modules 0).map
          (((restrictedDerivedRestrictAdjointIso F.immersion).hom.app
              ((FiniteTrace.twisted F.toBase).obj (derivedStructureSheaf Y.left))).hom ≫
            ((DominatingCompactification.upperShriekPlusIso f j F.compactification).inv.app
              (structurePlus Y)).hom.hom) :=
  rfl

omit [AlgebraicGeometry.IsNoetherian S] [LocallyQuasiFinite f.left] in
/-- Cancelling an isomorphism natural against `lφ` and an isomorphism followed by its inverse. -/
theorem comp_cancel_aux {C : Type*} [Category C] {P Q Q' R R' W W' : C} (a : P ⟶ Q)
    (lφ : Q ⟶ Q') (ai : Q' ⟶ R) (γ : R ⟶ R') (id' : R' ⟶ W) (a₁ : W ⟶ W') (a₁i : W' ⟶ W)
    (rφ : P ⟶ R) (a' : R ⟶ Q') (hnat : a ≫ lφ = rφ ≫ a') (h₀ : a' ≫ ai = 𝟙 _)
    (h₁ : a₁ ≫ a₁i = 𝟙 _) :
    a ≫ (((lφ ≫ ai ≫ 𝟙 _) ≫ γ ≫ (id' ≫ 𝟙 _ ≫ a₁)) ≫ a₁i) = rφ ≫ γ ≫ id' := by
  simp only [Category.assoc, Category.id_comp, h₁, Category.comp_id]
  rw [reassoc_of% hnat, reassoc_of% h₀]

omit [LocallyQuasiFinite f.left] in
/-- At the compactification of `F₃ = F₁.ofMap i h`, the two identifications differ by
`i^*(a_{h ≫ π₁} ≅ a_h a_{π₁})`, the map of Tag 0A9L for `h` and `a_{𝟙} ≅ 𝟭`, on `H⁰`. -/
theorem upperShriekStructureSheafZerothIso_inv_comp_hom_ofMap_compactification
    (F₁ : OpenFiniteFactorization f) {T : Scheme.{u}} [CompactSpace T] [QuasiSeparatedSpace T]
    (i : X.left ⟶ T) [IsOpenImmersion i] (h : T ⟶ F₁.space) [IsFinite h]
    (sq : IsPullback i (𝟙 X.left) h F₁.immersion) :
    (upperShriekStructureSheafZerothIso (F₁.ofMap i h (sq.w.trans (Category.id_comp _)))
        (F₁.ofMap i h (sq.w.trans (Category.id_comp _))).compactification).inv ≫
      (upperShriekStructureSheafZerothIso F₁
        (F₁.ofMap i h (sq.w.trans (Category.id_comp _))).compactification).hom =
      (((Scheme.Modules.restrictFunctor i).mapDerivedCategoryHomologyIso 0).app
          ((FiniteTrace.twisted (h ≫ F₁.toBase)).obj (derivedStructureSheaf Y.left)).obj).inv ≫
        (homologyFunctor X.left.Modules 0).map
          ((OpenImmersion.restrictedDerivedRestrict i).map
              ((FiniteTrace.twistedCompIso h F₁.toBase).hom.app (derivedStructureSheaf Y.left)) ≫
            (compactificationRestrictionMap f
              (F₁.ofMap i h (sq.w.trans (Category.id_comp _))).compactification
              F₁.compactification h sq).app
                ((FiniteTrace.twisted F₁.toBase).obj (derivedStructureSheaf Y.left)) ≫
            (twistedInverseImageIdIsoOfComp X.left).hom.app
              ((OpenImmersion.restrictedDerivedRestrict F₁.immersion).obj
                ((FiniteTrace.twisted F₁.toBase).obj (derivedStructureSheaf Y.left)))).hom ≫
        (((Scheme.Modules.restrictFunctor F₁.immersion).mapDerivedCategoryHomologyIso 0).app
          ((FiniteTrace.twisted F₁.toBase).obj (derivedStructureSheaf Y.left)).obj).hom := by
  have : IsProper (X := (F₁.ofMap i h (sq.w.trans (Category.id_comp _))).compactification.space)
      (Y := F₁.compactification.space) h := (inferInstance : IsProper h)
  rw [upperShriekStructureSheafZerothIso_inv, upperShriekStructureSheafZerothIso_hom,
    upperShriekPlusIso_refl,
    upperShriekPlusIso_eq_upperShriekCompactificationIso f _ F₁.compactification h rfl sq]
  have key : ((restrictedDerivedRestrictAdjointIso i).hom.app
        ((FiniteTrace.twisted (h ≫ F₁.toBase)).obj (derivedStructureSheaf Y.left))).hom ≫
      ((Iso.refl (upperShriekPlus f
          (F₁.ofMap i h (sq.w.trans (Category.id_comp _))).compactification)).inv.app
        (structurePlus Y)).hom.hom ≫
      ((upperShriekCompactificationIso f
        (F₁.ofMap i h (sq.w.trans (Category.id_comp _))).compactification
        F₁.compactification h rfl sq).hom.app (structurePlus Y)).hom.hom ≫
      ((restrictedDerivedRestrictAdjointIso F₁.immersion).inv.app
        ((FiniteTrace.twisted F₁.toBase).obj (derivedStructureSheaf Y.left))).hom =
      ((OpenImmersion.restrictedDerivedRestrict i).map
              ((FiniteTrace.twistedCompIso h F₁.toBase).hom.app (derivedStructureSheaf Y.left)) ≫
            (compactificationRestrictionMap f
              (F₁.ofMap i h (sq.w.trans (Category.id_comp _))).compactification
              F₁.compactification h sq).app
                ((FiniteTrace.twisted F₁.toBase).obj (derivedStructureSheaf Y.left)) ≫
            (twistedInverseImageIdIsoOfComp X.left).hom.app
              ((OpenImmersion.restrictedDerivedRestrict F₁.immersion).obj
                ((FiniteTrace.twisted F₁.toBase).obj (derivedStructureSheaf Y.left)))).hom := by
    have k2 : (restrictedDerivedRestrictAdjointIso i).hom.app
          ((FiniteTrace.twisted (h ≫ F₁.toBase)).obj (derivedStructureSheaf Y.left)) ≫
        (upperShriekCompactificationMap f
          (F₁.ofMap i h (sq.w.trans (Category.id_comp _))).compactification
          F₁.compactification h rfl sq).app (derivedStructureSheaf Y.left) ≫
        (restrictedDerivedRestrictAdjointIso F₁.immersion).inv.app
          ((FiniteTrace.twisted F₁.toBase).obj (derivedStructureSheaf Y.left)) =
      (OpenImmersion.restrictedDerivedRestrict i).map
              ((FiniteTrace.twistedCompIso h F₁.toBase).hom.app (derivedStructureSheaf Y.left)) ≫
            (compactificationRestrictionMap f
              (F₁.ofMap i h (sq.w.trans (Category.id_comp _))).compactification
              F₁.compactification h sq).app
                ((FiniteTrace.twisted F₁.toBase).obj (derivedStructureSheaf Y.left)) ≫
            (twistedInverseImageIdIsoOfComp X.left).hom.app
              ((OpenImmersion.restrictedDerivedRestrict F₁.immersion).obj
                ((FiniteTrace.twisted F₁.toBase).obj (derivedStructureSheaf Y.left))) :=
      comp_cancel_aux _ _ _ _ _ _ _ _ _
        (((restrictedDerivedRestrictAdjointIso i).hom.naturality
          (𝟙 _ ≫ (FiniteTrace.twistedCompIso h F₁.toBase).hom.app
            (derivedStructureSheaf Y.left))).symm.trans
          (congrArg (· ≫ _) (congrArg (OpenImmersion.restrictedDerivedRestrict i).map
            (Category.id_comp _))))
        (Iso.hom_inv_id_app _ _) (Iso.hom_inv_id_app _ _)
    exact (congrArg (_ ≫ ·) (Category.id_comp _)).trans (congrArg (ObjectProperty.ι _).map k2)
  exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ((Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ _) (((homologyFunctor X.left.Modules 0).map_comp _ _).symm.trans
      (congrArg (homologyFunctor X.left.Modules 0).map
        ((Category.assoc _ _ _).trans key))))))

omit [AlgebraicGeometry.IsNoetherian S] [LocallyQuasiFinite f.left] in
/-- The diagram chase of `upperShriekStructureSheafZerothIso_inv_comp_hom_ofMap`. -/
theorem ofMap_chase {E : Type*} [Category E] {A B C D Z A₂ P₃ P' : E} (Rii3 : A ⟶ B) (HL : B ⟶ C)
    (Hγ : C ⟶ D) (R1h : D ⟶ Z) (rc : A ⟶ A₂) (Rii' : A₂ ⟶ C) (hn : rc ≫ Rii' = Rii3 ≫ HL)
    (β'i : A₂ ⟶ P') (rt : P' ⟶ Z) (hC : Rii' ≫ Hγ ≫ R1h = β'i ≫ rt) (β3i : A ⟶ P₃)
    (rhc : P₃ ⟶ P') (hβ : rc ≫ β'i = β3i ≫ rhc) (rmt : P₃ ⟶ Z) (hmt : rmt = rhc ≫ rt) :
    Rii3 ≫ (HL ≫ Hγ) ≫ R1h = β3i ≫ rmt := by
  rw [hmt, ← reassoc_of% hβ, ← hC, Category.assoc, ← reassoc_of% hn]

omit [LocallyQuasiFinite f.left] in
/-- **The identifications `H⁰(f^!𝒪_Y) ≅ H⁰(a 𝒪_Y)|_X` for `F₁` and `F₃ = F₁.ofMap i h` differ
by the trace of `h`**: `e₃⁻¹ ≫ e₁ = ((h_*M₃)|_X ≅ M₃|_X)⁻¹ ≫ (τ_h)|_X`. -/
theorem upperShriekStructureSheafZerothIso_inv_comp_hom_ofMap (F₁ : OpenFiniteFactorization f)
    {T : Scheme.{u}} [CompactSpace T] [QuasiSeparatedSpace T]
    (i : X.left ⟶ T) [IsOpenImmersion i] (h : T ⟶ F₁.space) [IsFinite h]
    (sq : IsPullback i (𝟙 X.left) h F₁.immersion) (j : CompactificationOf (Over.mk f.left)) :
    (upperShriekStructureSheafZerothIso (F₁.ofMap i h (sq.w.trans (Category.id_comp _))) j).inv ≫
      (upperShriekStructureSheafZerothIso F₁ j).hom =
    (restrictPushforwardIsoApp sq
        (finiteZeroTwisted (F₁.ofMap i h (sq.w.trans (Category.id_comp _))))).inv ≫
      (Scheme.Modules.restrictFunctor F₁.immersion).map
        (F₁.mapTrace h (sq.w.trans (Category.id_comp _))) := by
  rw [upperShriekStructureSheafZerothIso_eq_trans _ j
      (F₁.ofMap i h (sq.w.trans (Category.id_comp _))).compactification,
    upperShriekStructureSheafZerothIso_eq_trans F₁ j
      (F₁.ofMap i h (sq.w.trans (Category.id_comp _))).compactification,
    Iso.trans_inv, Iso.trans_hom, Category.assoc, Iso.inv_hom_id_assoc,
    upperShriekStructureSheafZerothIso_inv_comp_hom_ofMap_compactification F₁ i h sq]
  have := isGE_twisted_twisted F₁ h (sq.w.trans (Category.id_comp _))
  have hC := homology_map_twistedInverseImageRestrictionMap_eq_trace sq
    ((FiniteTrace.twisted F₁.toBase).obj (derivedStructureSheaf Y.left))
  have hn := natTrans_naturality_comp
    ((Scheme.Modules.restrictFunctor i).mapDerivedCategoryHomologyIso 0).inv
    ((FiniteTrace.twistedCompIso h F₁.toBase).hom.app (derivedStructureSheaf Y.left)).hom
  have hβ := (restrictPushforwardIsoOfIsPullback sq).inv.naturality
    ((homologyFunctor T.Modules 0).map
      ((FiniteTrace.twistedCompIso h F₁.toBase).hom.app (derivedStructureSheaf Y.left)).hom)
  rw [ObjectProperty.FullSubcategory.comp_hom, (homologyFunctor X.left.Modules 0).map_comp]
  exact ofMap_chase _ _ _ _ _ _ hn _ _ hC _ _ hβ _
    ((congrArg (Scheme.Modules.restrictFunctor F₁.immersion).map rfl).trans
      ((Scheme.Modules.restrictFunctor F₁.immersion).map_comp _ _))

omit [LocallyQuasiFinite f.left] in
/-- On sections, the chart identification of `F₁` after the trace of `h` is that of
`F₃ = F₁.ofMap i h`. -/
theorem chartRestrict_mapTrace_ofMap (F₁ : OpenFiniteFactorization f)
    {T : Scheme.{u}} [CompactSpace T] [QuasiSeparatedSpace T]
    (i : X.left ⟶ T) [IsOpenImmersion i] (h : T ⟶ F₁.space) [IsFinite h]
    (sq : IsPullback i (𝟙 X.left) h F₁.immersion) (j : CompactificationOf (Over.mk f.left))
    (W : F₁.space.Opens) (V : X.left.Opens) (hV : V ≤ F₁.immersion ⁻¹ᵁ W)
    (s : Γ(finiteZeroTwisted (F₁.ofMap i h (sq.w.trans (Category.id_comp _))), h ⁻¹ᵁ W)) :
    chartRestrict (finiteZeroTwisted F₁) (upperShriekStructureSheafZerothIso F₁ j) hV
        ((F₁.mapTrace h (sq.w.trans (Category.id_comp _))).app W s) =
      chartRestrict (finiteZeroTwisted (F₁.ofMap i h (sq.w.trans (Category.id_comp _))))
        (upperShriekStructureSheafZerothIso (F₁.ofMap i h (sq.w.trans (Category.id_comp _))) j)
        (le_preimage_of_map h (sq.w.trans (Category.id_comp _)) hV) s := by
  have hE : (upperShriekStructureSheafZerothIso
      (F₁.ofMap i h (sq.w.trans (Category.id_comp _))) j).inv =
      ((restrictPushforwardIsoApp sq
        (finiteZeroTwisted (F₁.ofMap i h (sq.w.trans (Category.id_comp _))))).inv ≫
        (Scheme.Modules.restrictFunctor F₁.immersion).map
          (F₁.mapTrace h (sq.w.trans (Category.id_comp _)))) ≫
        (upperShriekStructureSheafZerothIso F₁ j).inv := by
    rw [← upperShriekStructureSheafZerothIso_inv_comp_hom_ofMap F₁ i h sq j, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  rw [chartRestrict_apply, chartRestrict_apply, hE]
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
  refine congrArg (ConcreteCategory.hom
    (Scheme.Modules.Hom.app (upperShriekStructureSheafZerothIso F₁ j).inv V)) ?_
  have hτ := ConcreteCategory.congr_hom
    ((F₁.mapTrace h (sq.w.trans (Category.id_comp _))).mapPresheaf.naturality
      (homOfLE (image_le_of_le_preimage hV)).op) s
  refine hτ.symm.trans ?_
  refine congrArg (ConcreteCategory.hom (Scheme.Modules.Hom.app
    (F₁.mapTrace h (sq.w.trans (Category.id_comp _))) (F₁.immersion ''ᵁ V))) ?_
  have hle : h ⁻¹ᵁ (F₁.immersion ''ᵁ V) ≤ h ⁻¹ᵁ W :=
    (TopologicalSpace.Opens.map h.base).monotone (image_le_of_le_preimage hV)
  refine Eq.trans
    (b := (finiteZeroTwisted (F₁.ofMap i h (sq.w.trans (Category.id_comp _)))).presheaf.map
      (homOfLE hle).op s) rfl ?_
  refine Eq.trans ?_ (Eq.trans (b := (finiteZeroTwisted
      (F₁.ofMap i h (sq.w.trans (Category.id_comp _)))).presheaf.map
    (homOfLE (show h ⁻¹ᵁ (F₁.immersion ''ᵁ V) ≤ i ''ᵁ V from
      (IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback sq.flip V).ge)).op
      ((finiteZeroTwisted (F₁.ofMap i h (sq.w.trans (Category.id_comp _)))).presheaf.map
        (homOfLE (image_le_of_le_preimage
          (le_preimage_of_map h (sq.w.trans (Category.id_comp _)) hV))).op s))
    rfl rfl)
  rw [← ConcreteCategory.comp_apply, ← CategoryTheory.Functor.map_comp]
  exact congrArg (fun φ => ConcreteCategory.hom
    ((finiteZeroTwisted (F₁.ofMap i h (sq.w.trans (Category.id_comp _)))).presheaf.map φ) s)
    (Subsingleton.elim _ _)

/-- **The chart identifications of `F₁` and of `F₁.ofMap i h` agree**, for `h : T ⟶ T₁` finite
with `i ≫ h = i₁` cartesian over `𝟙 X`. -/
theorem OpenFiniteFactorization.localEquiv_relativeDualizingModuleData_ofMap
    (F₁ : OpenFiniteFactorization f) {T : Scheme.{u}} [CompactSpace T] [QuasiSeparatedSpace T]
    (i : X.left ⟶ T) [IsOpenImmersion i] (h : T ⟶ F₁.space) [IsFinite h]
    (sq : IsPullback i (𝟙 X.left) h F₁.immersion) (j : CompactificationOf (Over.mk f.left))
    (U : Y.left.affineOpens) (V : X.left.affineOpens) (hVU : V.1 ≤ f.left ⁻¹ᵁ U.1) :
    letI : Algebra Γ(Y.left, U.1) Γ(X.left, V.1) := (f.left.appLE U V hVU).hom.toAlgebra
    ∀ G : FiniteOpenFactorization.{u, u, u} Γ(Y.left, U.1) Γ(X.left, V.1),
      ((F₁.ofMap i h (sq.w.trans (Category.id_comp _))).relativeDualizingModuleData j).localEquiv
          U V hVU G = (F₁.relativeDualizingModuleData j).localEquiv U V hVU G :=
  F₁.localEquiv_relativeDualizingModuleData_ofMap_of_chartRestrict i h sq j
    (chartRestrict_mapTrace_ofMap F₁ i h sq j) U V hVU

omit [AlgebraicGeometry.IsNoetherian S] [LocallyQuasiFinite f.left] in
/-- The projection of the dominating compactification of two finite factorizations to the first
one is finite: a closed immersion followed by a base change of the finite `T₂ ⟶ Y`. -/
theorem isFinite_dominatingFst (F₁ F₂ : OpenFiniteFactorization f) :
    IsFinite (DominatingCompactification.fst f F₁.compactification F₂.compactification) := by
  have : IsFinite F₂.compactification.toBase := inferInstanceAs (IsFinite F₂.toBase)
  dsimp only [DominatingCompactification.fst, GraphClosure.closureFst]
  infer_instance

omit [AlgebraicGeometry.IsNoetherian S] [LocallyQuasiFinite f.left] in
/-- The projection of the dominating compactification of two finite factorizations to the second
one is finite. -/
theorem isFinite_dominatingSnd (F₁ F₂ : OpenFiniteFactorization f) :
    IsFinite (DominatingCompactification.snd f F₁.compactification F₂.compactification) := by
  have : IsFinite F₁.compactification.toBase := inferInstanceAs (IsFinite F₁.toBase)
  dsimp only [DominatingCompactification.snd, GraphClosure.closureSnd]
  infer_instance

/-- **The chart identifications of `H⁰(f^!𝒪_Y)` with `ω_{B/A}` do not depend on the finite
factorization**: for two factorizations `X ⟶ T₁ ⟶ Y`, `X ⟶ T₂ ⟶ Y`, compare both with the
closure of `X` in `T₁ ×_Y T₂`, which is finite over each. -/
theorem OpenFiniteFactorization.localEquiv_relativeDualizingModuleData_eq
    (F₁ F₂ : OpenFiniteFactorization f) (j : CompactificationOf (Over.mk f.left))
    (U : Y.left.affineOpens) (V : X.left.affineOpens) (hVU : V.1 ≤ f.left ⁻¹ᵁ U.1) :
    letI : Algebra Γ(Y.left, U.1) Γ(X.left, V.1) := (f.left.appLE U V hVU).hom.toAlgebra
    ∀ G : FiniteOpenFactorization.{u, u, u} Γ(Y.left, U.1) Γ(X.left, V.1),
      (F₁.relativeDualizingModuleData j).localEquiv U V hVU G =
        (F₂.relativeDualizingModuleData j).localEquiv U V hVU G := by
  intro G
  have : IsFinite (X := DominatingCompactification.space f F₁.compactification F₂.compactification)
      (Y := F₁.space) (DominatingCompactification.fst f F₁.compactification F₂.compactification) :=
    isFinite_dominatingFst F₁ F₂
  have : IsFinite (X := DominatingCompactification.space f F₁.compactification F₂.compactification)
      (Y := F₂.space) (DominatingCompactification.snd f F₁.compactification F₂.compactification) :=
    isFinite_dominatingSnd F₁ F₂
  have e₁ := F₁.localEquiv_relativeDualizingModuleData_ofMap
    (DominatingCompactification.immersion f F₁.compactification F₂.compactification)
    (DominatingCompactification.fst f F₁.compactification F₂.compactification)
    (DominatingCompactification.isPullback_fst f F₁.compactification F₂.compactification) j
    U V hVU G
  have e₂ := F₂.localEquiv_relativeDualizingModuleData_ofMap
    (DominatingCompactification.immersion f F₁.compactification F₂.compactification)
    (DominatingCompactification.snd f F₁.compactification F₂.compactification)
    (DominatingCompactification.isPullback_snd f F₁.compactification F₂.compactification) j
    U V hVU G
  have hF : F₁.ofMap
        (DominatingCompactification.immersion f F₁.compactification F₂.compactification)
        (DominatingCompactification.fst f F₁.compactification F₂.compactification)
        ((DominatingCompactification.isPullback_fst f F₁.compactification
          F₂.compactification).w.trans (Category.id_comp _)) =
      F₂.ofMap (DominatingCompactification.immersion f F₁.compactification F₂.compactification)
        (DominatingCompactification.snd f F₁.compactification F₂.compactification)
        ((DominatingCompactification.isPullback_snd f F₁.compactification
          F₂.compactification).w.trans (Category.id_comp _)) := by
    simp only [OpenFiniteFactorization.ofMap, OpenFiniteFactorization.mk.injEq, heq_eq_eq,
      true_and]
    exact DominatingCompactification.fst_comp_toBase f F₁.compactification F₂.compactification
  rw [← e₁, ← e₂, hF]

end Stacks.Duality
