module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrisCohomologyBound07QAModule
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.FrobeniusTwistArrows
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LowerShriekCounitPullback
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.VanishingTransfer
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ModuleUnitMono07QA
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.UnderivedLerayCoherence

/-!
# The underived comparison behind arrow 2 of [Stacks, Tag 07N5]

Arrow 2 of the proof of [Stacks, Tag 07N5] is built on the big crystalline site with module
coefficients, from the underived comparison `...changeBaseBigBaseGlobalSectionsTrans`; the map of
[Stacks, Tag 07QA] is built on the small crystalline site with abelian coefficients, from the
unit of `f_cris^{-1} ⊣ f_{cris, *}` and `...SmallSite.crisGlobalSectionsIso`.  This file sets up
the functors and transformations that compare the two, and proves that the two underived
comparisons agree.

## Main definitions

* `bigRestrictToAbelian` — `N ↦ i^{-1}N` read as an abelian sheaf on `Cris(X/S)`.
* `bigSectionsIsoAbelian` — `Γ(CRIS(X/S), N) ≅ Γ(Cris(X/S), i^{-1}N)` as abelian groups.
* `lowerShriekCounitPullback` — `f_cris^*(i^{-1}N) ⟶ i^{-1}f_CRIS^*N`, from the counit of
  `i_! ⊣ i^{-1}`.
* `crisComparisonTrans` — `f_cris^{-1}(i^{-1}N) ⟶ i^{-1}f_CRIS^*N` on abelian sheaves.

## Main results

* `changeBaseBigBaseGlobalSectionsTrans_comp_bigSectionsIsoAbelian` — the two underived
  comparisons agree.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable (S : GlobalCrystallineSituation.{u})

/-- `N ↦ i^{-1}N`, read as an abelian sheaf on the small crystalline site. -/
abbrev bigRestrictToAbelian : BigModuleSheaf S ⥤ Sheaf (smallTopology S) AddCommGrpCat.{u + 1} :=
  moduleRestrictι S ⋙ toAbelianSheaf S

/-- The value at an object of `CRIS(X/S)` of a global section of a sheaf of modules, as a map of
abelian groups. -/
def bigSectionsEval (M : BigModuleSheaf S) (U : (Thickening S)ᵒᵖ) :
    (bigBaseModuleGlobalSections S ⋙ forgetBaseAction S).obj M ⟶
      ((SheafOfModules.toSheaf.{u + 1} (crystallineStructureSheaf S)).obj M).obj.obj U :=
  AddCommGrpCat.ofHom
    { toFun := fun s => s.val U
      map_zero' := rfl
      map_add' := fun _ _ => rfl }

/-- The global sections of a sheaf of modules on `CRIS(X/S)`, as a cone over the underlying
abelian presheaf. -/
def bigSectionsCone (M : BigModuleSheaf S) :
    Cone ((SheafOfModules.toSheaf.{u + 1} (crystallineStructureSheaf S)).obj M).obj where
  pt := (bigBaseModuleGlobalSections S ⋙ forgetBaseAction S).obj M
  π :=
    { app := fun U => bigSectionsEval S M U
      naturality := fun _ _ f => by
        ext s
        exact (s.property f).symm }

/-- **`Γ(CRIS(X/S), N)` of a sheaf of modules is the global sections of its underlying abelian
sheaf**, as an isomorphism of abelian groups: a compatible family of sections is a cone over the
underlying abelian presheaf. -/
def bigSectionsIsoΓ (M : BigModuleSheaf S) :
    (bigBaseModuleGlobalSections S ⋙ forgetBaseAction S).obj M ≅
      (bigGlobalSections S).obj ((SheafOfModules.toSheaf.{u + 1} (crystallineStructureSheaf S)).obj
        M) where
  hom := (Sheaf.isLimitConeΓ _).lift (bigSectionsCone S M)
  inv := AddCommGrpCat.ofHom
    { toFun := fun z => M.val.sectionsMk (fun U =>
          (Sheaf.ΓRes ((SheafOfModules.toSheaf.{u + 1} (crystallineStructureSheaf S)).obj M)
            U).hom z)
        (fun _ _ f => ConcreteCategory.congr_hom (Sheaf.ΓRes_map
          ((SheafOfModules.toSheaf.{u + 1} (crystallineStructureSheaf S)).obj M) f) z)
      map_zero' := PresheafOfModules.sections_ext _ _ fun U => map_zero (Sheaf.ΓRes
        ((SheafOfModules.toSheaf.{u + 1} (crystallineStructureSheaf S)).obj M) U).hom
      map_add' := fun z z' => PresheafOfModules.sections_ext _ _ fun U => map_add (Sheaf.ΓRes
        ((SheafOfModules.toSheaf.{u + 1} (crystallineStructureSheaf S)).obj M) U).hom z z' }
  hom_inv_id := by
    ext s
    exact PresheafOfModules.sections_ext _ _ fun U =>
      ConcreteCategory.congr_hom ((Sheaf.isLimitConeΓ _).fac (bigSectionsCone S M) U) s
  inv_hom_id := by
    refine (Sheaf.isLimitConeΓ _).hom_ext fun U => ?_
    ext z
    exact ConcreteCategory.congr_hom ((Sheaf.isLimitConeΓ _).fac (bigSectionsCone S M) U) _

/-- `bigSectionsIsoΓ` against the restriction maps: a global section is sent to its value. -/
@[reassoc]
theorem bigSectionsIsoΓ_hom_comp_ΓRes (M : BigModuleSheaf S) (U : (Thickening S)ᵒᵖ) :
    (bigSectionsIsoΓ S M).hom ≫
        Sheaf.ΓRes ((SheafOfModules.toSheaf.{u + 1} (crystallineStructureSheaf S)).obj M) U =
      bigSectionsEval S M U :=
  (Sheaf.isLimitConeΓ _).fac (bigSectionsCone S M) U

/-- `bigSectionsIsoΓ` as an isomorphism of functors. -/
def bigSectionsIsoBigGlobalSections :
    bigBaseModuleGlobalSections S ⋙ forgetBaseAction S ≅
      SheafOfModules.toSheaf.{u + 1} (crystallineStructureSheaf S) ⋙ bigGlobalSections S :=
  NatIso.ofComponents (bigSectionsIsoΓ S) fun {M M'} g => by
    refine (Sheaf.isLimitConeΓ _).hom_ext fun U => ?_
    change (_ ≫ (bigSectionsIsoΓ S M').hom) ≫ Sheaf.ΓRes _ U =
      ((bigSectionsIsoΓ S M).hom ≫ (bigGlobalSections S).map _) ≫ Sheaf.ΓRes _ U
    rw [Category.assoc, Category.assoc, Sheaf.ΓRes_naturality, bigSectionsIsoΓ_hom_comp_ΓRes,
      bigSectionsIsoΓ_hom_comp_ΓRes_assoc]
    rfl

/-- `Γ(CRIS(X/S), N) ≅ Γ(Cris(X/S), i^{-1}N)`, the `A`-action forgotten. -/
def bigSectionsIsoAbelian :
    bigBaseModuleGlobalSections S ⋙ forgetBaseAction S ≅
      bigRestrictToAbelian S ⋙ globalSections S :=
  bigSectionsIsoBigGlobalSections S ≪≫
    Functor.isoWhiskerLeft (SheafOfModules.toSheaf.{u + 1} (crystallineStructureSheaf S))
      (smallRestrictionGlobalSectionsIso (S := S)).symm

variable {S} {S' : GlobalCrystallineSituation.{u}} (fS : S.S ⟶ S'.S) (fX : S.X ⟶ S'.X)
  (hf : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap fS = fX ≫ S'.toClosedFiber)

/-- Forgetting the action after restricting scalars is forgetting the action. -/
def restrictScalarsForgetIso :
    ModuleCat.restrictScalars.{u + 1} (baseChangeRingHom fS) ⋙ forgetBaseAction S' ≅
      forgetBaseAction S :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

/-- Bookkeeping for the naturality statements below: a naturality square followed by a
functor applied to a second one, in arbitrary categories. -/
private lemma natTwo {𝒦 𝒦' : Type*} [Category* 𝒦] [Category* 𝒦'] (C : 𝒦 ⥤ 𝒦')
    {X₁ X₂ : 𝒦'} {Y₁ Y₂ Z₁ Z₂ : 𝒦} (y : X₁ ⟶ X₂) (a₁ : X₁ ⟶ C.obj Y₁) (a₂ : X₂ ⟶ C.obj Y₂)
    (p : Y₁ ⟶ Y₂) (b₁ : Y₁ ⟶ Z₁) (b₂ : Y₂ ⟶ Z₂) (q : Z₁ ⟶ Z₂) (h₁ : y ≫ a₂ = a₁ ≫ C.map p)
    (h₂ : p ≫ b₂ = b₁ ≫ q) : y ≫ a₂ ≫ C.map b₂ = (a₁ ≫ C.map b₁) ≫ C.map q := by
  rw [reassoc_of% h₁, ← C.map_comp, h₂, C.map_comp, Category.assoc]

/-- **The unit of restriction along change of base is natural.** -/
theorem changeBaseRestrictionUnit_naturality {N₁ N₂ : Sheaf (topology S') AddCommGrpCat.{u + 1}}
    (y : N₁ ⟶ N₂) :
    y ≫ changeBaseRestrictionUnit S S' fS fX hf N₂ =
      changeBaseRestrictionUnit S S' fS fX hf N₁ ≫
        (changeBaseDirectImage S S' fS fX hf).map ((bigDirectImage S).map ((smallRestriction S).map
          (((changeBase S S' fS fX hf).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
            (topology S) (topology S')).map y))) :=
  natTwo (changeBaseDirectImage S S' fS fX hf) y _ _ _ _ _ _
    (((changeBase S S' fS fX hf).sheafAdjunctionCocontinuous AddCommGrpCat.{u + 1}
      (topology S) (topology S')).unit.naturality y)
    ((bigDirectImageAdjunction S).unit.naturality
      (((changeBase S S' fS fX hf).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (topology S) (topology S')).map y))

/-- **The module unit `ℱ ⟶ f_{cris, *}f_cris^*ℱ` is natural in the sheaf of modules.** -/
theorem crisModuleUnit_naturality {F₁ F₂ : ModuleSheaf S'} (h : F₁ ⟶ F₂) :
    (toAbelianSheaf S').map h ≫ crisModuleUnit S S' fS fX hf F₂ =
      crisModuleUnit S S' fS fX hf F₁ ≫ (crisDirectImage S S' fS fX hf).map
        ((toAbelianSheaf S).map ((crisModuleInverseImage fS fX hf).map h)) :=
  natTwo (smallRestriction S') ((toAbelianSheaf S').map h) _ _
    ((SheafOfModules.toSheaf.{u + 1} (crystallineStructureSheaf S')).map
      ((moduleLowerShriek S').map h)) _ _ _
    (((toAbelianSheaf S').map_comp _ _).symm.trans ((congrArg (toAbelianSheaf S').map
      ((moduleLowerShriekAdjunction S').unit.naturality h)).trans
        ((toAbelianSheaf S').map_comp _ _)))
    (changeBaseRestrictionUnit_naturality fS fX hf
      ((SheafOfModules.toSheaf.{u + 1} (crystallineStructureSheaf S')).map
        ((moduleLowerShriek S').map h)))

/-- **The comparison `f_cris^{-1}ℱ ⟶ f_cris^*ℱ` is natural in the sheaf of modules.** -/
theorem crisModuleComparison_naturality {F₁ F₂ : ModuleSheaf S'} (h : F₁ ⟶ F₂) :
    (crisInverseImage S S' fS fX hf).map ((toAbelianSheaf S').map h) ≫
        crisModuleComparison S S' fS fX hf F₂ =
      crisModuleComparison S S' fS fX hf F₁ ≫
        (toAbelianSheaf S).map ((crisModuleInverseImage fS fX hf).map h) := by
  simp only [crisModuleComparison]
  rw [← Adjunction.homEquiv_naturality_left_symm, ← Adjunction.homEquiv_naturality_right_symm,
    crisModuleUnit_naturality]

/-- Bookkeeping for `lowerShriekCounitPullback_naturality`, in arbitrary categories. -/
private lemma natL {𝒜 ℬ : Type*} [Category* 𝒜] [Category* ℬ] (L : 𝒜 ⥤ ℬ)
    {A₁ A₂ B₁ B₂ : 𝒜} {N₁ N₂ : ℬ} (m : A₁ ⟶ A₂) (ι₁ : A₁ ⟶ B₁) (ι₂ : A₂ ⟶ B₂) (r : B₁ ⟶ B₂)
    (h₁ : m ≫ ι₂ = ι₁ ≫ r) (e₁ : L.obj B₁ ⟶ N₁) (e₂ : L.obj B₂ ⟶ N₂) (gg : N₁ ⟶ N₂)
    (h₂ : L.map r ≫ e₂ = e₁ ≫ gg) :
    L.map m ≫ L.map ι₂ ≫ e₂ = (L.map ι₁ ≫ e₁) ≫ gg := by
  rw [← L.map_comp_assoc, h₁, L.map_comp_assoc, h₂, Category.assoc]

/-- **`lowerShriekCounitPullback` is natural.** -/
theorem lowerShriekCounitPullback_naturality {N₁ N₂ : BigModuleSheaf S'} (g : N₁ ⟶ N₂) :
    (crisModuleInverseImage fS fX hf).map ((moduleRestrictι S').map g) ≫
        lowerShriekCounitPullback fS fX hf N₂ =
      lowerShriekCounitPullback fS fX hf N₁ ≫
        (moduleRestrictι S).map ((changeBaseBigModulePullback S S' fS fX hf).map g) := by
  have E := natL (moduleLowerShriek S') _ _ _ _
    ((crisRestrictModulesIsoModuleRestrictι S').inv.naturality g) _ _ _
    ((moduleLowerShriekAdjunction S').counit.naturality g)
  ext X x
  exact ConcreteCategory.congr_hom (congrArg (fun φ => φ.val.app
    (op ((changeBase S S' fS fX hf).obj ((CrystallineThickening.ι S).obj X.unop)))) E) x

/-- Bookkeeping for the naturality of `crisComparisonTrans`, in arbitrary categories: a
naturality square followed by a functor applied to a second one. -/
theorem comp_map_comp_of_naturality {𝒦 𝒦' : Type*} [Category* 𝒦] [Category* 𝒦'] (T : 𝒦 ⥤ 𝒦')
    {X₁ X₂ : 𝒦'} {Y₁ Y₂ Z₁ Z₂ : 𝒦} (a : X₁ ⟶ X₂) (b₁ : X₁ ⟶ T.obj Y₁) (b₂ : X₂ ⟶ T.obj Y₂)
    (m : Y₁ ⟶ Y₂) (k₁ : Y₁ ⟶ Z₁) (k₂ : Y₂ ⟶ Z₂) (q : Z₁ ⟶ Z₂) (h₁ : a ≫ b₂ = b₁ ≫ T.map m)
    (h₂ : m ≫ k₂ = k₁ ≫ q) : a ≫ b₂ ≫ T.map k₂ = (b₁ ≫ T.map k₁) ≫ T.map q :=
  natTwo T a b₁ b₂ m k₁ k₂ q h₁ h₂

/-- **`f_cris^{-1}(i^{-1}N) ⟶ i^{-1}f_CRIS^*N`** on abelian sheaves: the comparison of the
abelian inverse image with the module pullback, followed by `lowerShriekCounitPullback`. -/
def crisComparisonTrans :
    bigRestrictToAbelian S' ⋙ crisInverseImage S S' fS fX hf ⟶
      changeBaseBigModulePullback S S' fS fX hf ⋙ bigRestrictToAbelian S where
  app N := crisModuleComparison S S' fS fX hf ((moduleRestrictι S').obj N) ≫
    (toAbelianSheaf S).map (lowerShriekCounitPullback fS fX hf N)
  naturality _ _ g := comp_map_comp_of_naturality (toAbelianSheaf S) _ _ _ _ _ _ _
    (crisModuleComparison_naturality fS fX hf ((moduleRestrictι S').map g))
    (lowerShriekCounitPullback_naturality fS fX hf g)

/-- Bookkeeping for `changeBaseBigBaseGlobalSectionsTrans_comp_bigSectionsIsoAbelian`, in an
arbitrary category. -/
private lemma pasteUnderived {𝒦 : Type*} [Category* 𝒦]
    {X₀ X₁ X₂ X₃ X₄ X₅ Y₁ Y₂ Y₃ Y₄ Y₅ Y₆ Z₁ Z₂ : 𝒦}
    (b : X₀ ⟶ X₁) (si : X₁ ⟶ X₂) (u : X₂ ⟶ X₃) (cG : X₃ ⟶ X₄) (Δc : X₄ ⟶ X₅) (ρ : X₅ ⟶ Z₂)
    (m₁ : X₂ ⟶ Y₁) (mv : Y₁ ⟶ Y₂) (cGH : Y₂ ⟶ X₅) (H1 : u ≫ cG ≫ Δc = m₁ ≫ mv ≫ cGH)
    (sg : Y₂ ⟶ Y₃) (rG : Y₃ ⟶ Y₄) (k : Y₄ ⟶ Z₂) (H2 : cGH ≫ ρ = sg ≫ rG ≫ k)
    (sL : Y₁ ⟶ Y₅) (Γv : Y₅ ⟶ Y₃) (H3 : mv ≫ sg = sL ≫ Γv)
    (rL : Y₅ ⟶ Y₆) (vV : Y₆ ⟶ Y₄) (H4 : Γv ≫ rG = rL ≫ vV)
    (wV : Y₆ ⟶ Z₁) (j : Z₁ ⟶ Z₂) (H5 : vV ≫ k = wV ≫ j)
    (Γw : Y₅ ⟶ X₁) (rN : X₁ ⟶ Z₁) (H6 : rL ≫ wV = Γw ≫ rN)
    (mw : Y₁ ⟶ X₂) (sN : X₂ ⟶ X₁) (H7 : sL ≫ Γw = mw ≫ sN) (H8 : m₁ ≫ mw = 𝟙 _)
    (H9 : si ≫ sN = 𝟙 _) (ev : X₀ ⟶ Z₁) (H10 : b ≫ rN = ev) :
    ((b ≫ si) ≫ u ≫ cG ≫ Δc) ≫ ρ = ev ≫ j := by
  simp only [Category.assoc]
  rw [reassoc_of% H1, H2, reassoc_of% H3, reassoc_of% H4, H5, reassoc_of% H6, reassoc_of% H7,
    reassoc_of% H8, reassoc_of% H9, reassoc_of% H10]

/-- The counit `i_!i^{-1}N ⟶ N` pulled back along `f_cris`, read on underlying abelian sheaves at
an object of `Cris(X/S)`, is the counit at the image of the object under change of base. -/
theorem toAbelianSheaf_map_lowerShriekCounitPullback_app (N : BigModuleSheaf S')
    (A : (CrystallineThickening S)ᵒᵖ) :
    ((toAbelianSheaf S).map (lowerShriekCounitPullback fS fX hf N)).hom.app A =
      ((SheafOfModules.toSheaf.{u + 1} (crystallineStructureSheaf S')).map
        ((moduleLowerShriek S').map ((crisRestrictModulesIsoModuleRestrictι S').inv.app N) ≫
          (moduleLowerShriekAdjunction S').counit.app N)).hom.app
        (op ((changeBase S S' fS fX hf).obj ((CrystallineThickening.ι S).obj A.unop))) :=
  rfl

/-- **The unit of restriction along change of base, a restriction, and the two Kan extension
counits** compose to the restriction of the sheaf. -/
theorem changeBaseRestrictionUnit_app_comp_map_ranCounit
    (N : Sheaf (topology S') AddCommGrpCat.{u + 1}) {d : (Thickening S')ᵒᵖ}
    {c' : (CrystallineThickening S)ᵒᵖ}
    (τ : d ⟶ (changeBase S S' fS fX hf).op.obj ((CrystallineThickening.ι S).op.obj c')) :
    (changeBaseRestrictionUnit S S' fS fX hf N).hom.app d ≫
      ((changeBaseDirectImage S S' fS fX hf).obj ((bigDirectImage S).obj ((smallRestriction S).obj
        (((changeBase S S' fS fX hf).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (topology S) (topology S')).obj N)))).obj.map τ ≫
      ((changeBase S S' fS fX hf).op.ranCounit.app ((bigDirectImage S).obj ((smallRestriction S).obj
        (((changeBase S S' fS fX hf).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (topology S) (topology S')).obj N))).obj).app ((CrystallineThickening.ι S).op.obj c') ≫
      ((CrystallineThickening.ι S).op.ranCounit.app ((smallRestriction S).obj
        (((changeBase S S' fS fX hf).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (topology S) (topology S')).obj N)).obj).app c' = N.obj.map τ := by
  set N' := ((changeBase S S' fS fX hf).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (topology S) (topology S')).obj N
  have hβ := Functor.sheafAdjunctionCocontinuous_unit_app_hom (G := CrystallineThickening.ι S)
    (A := AddCommGrpCat.{u + 1}) (J := smallTopology S) (K := topology S) N'
  have hu := Functor.sheafAdjunctionCocontinuous_unit_app_hom (G := changeBase S S' fS fX hf)
    (A := AddCommGrpCat.{u + 1}) (J := topology S) (K := topology S') N
  refine ran_unit_comp_counit_eq_map (changeBase S S' fS fX hf).op (CrystallineThickening.ι S).op
    N.obj _ _ (fun c => ?_) (fun c' => ?_) τ
  · rw [hu]
    exact Functor.ranCounit_app_app_ranAdjunction_unit_app_app _ _ _
  · exact (congrArg (· ≫ _) (congr_app hβ ((CrystallineThickening.ι S).op.obj c'))).trans
      (Functor.ranCounit_app_app_ranAdjunction_unit_app_app _ _ _)

/-- **The unit of restriction along change of base, followed by the two Kan extension counits**
at the image of an object of `Cris(X/S)`, is the identity. -/
theorem changeBaseRestrictionUnit_app_comp_ranCounit (N : Sheaf (topology S') AddCommGrpCat.{u + 1})
    (A : CrystallineThickening S) :
    (changeBaseRestrictionUnit S S' fS fX hf N).hom.app
        (op ((changeBase S S' fS fX hf).obj ((CrystallineThickening.ι S).obj A))) ≫
      ((changeBase S S' fS fX hf).op.ranCounit.app ((bigDirectImage S).obj ((smallRestriction S).obj
        (((changeBase S S' fS fX hf).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (topology S) (topology S')).obj N))).obj).app (op ((CrystallineThickening.ι S).obj A)) ≫
      ((CrystallineThickening.ι S).op.ranCounit.app ((smallRestriction S).obj
        (((changeBase S S' fS fX hf).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (topology S) (topology S')).obj N)).obj).app (op A) = 𝟙 _ := by
  have h := changeBaseRestrictionUnit_app_comp_map_ranCounit fS fX hf N (c' := op A)
    (𝟙 (op ((changeBase S S' fS fX hf).obj ((CrystallineThickening.ι S).obj A))))
  rwa [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp] at h

/-- Bookkeeping for the left hand side of
`changeBaseBigBaseGlobalSectionsTrans_comp_bigSectionsIsoAbelian`. -/
private lemma pasteUnderivedLeft {𝒦 : Type*} [Category* 𝒦] {X₀ X₁ X₂ X₃ X₄ Z₁ : 𝒦}
    (a : X₀ ⟶ X₁) (r : X₁ ⟶ X₂) (b : X₂ ⟶ X₃) (si : X₃ ⟶ X₄) (ρ : X₄ ⟶ Z₁) (ρ' : X₃ ⟶ Z₁)
    (ev' : X₂ ⟶ Z₁) (E : X₀ ⟶ Z₁) (h₁ : si ≫ ρ = ρ') (h₂ : b ≫ ρ' = ev') (h₃ : a ≫ r ≫ ev' = E) :
    (a ≫ r ≫ b ≫ si) ≫ ρ = E := by
  rw [Category.assoc, Category.assoc, Category.assoc, h₁, h₂, h₃]

/-- An identity `e.hom ≫ a = b` read through `e.inv`, in an arbitrary category. -/
private lemma inv_comp_eq_of {𝒦 : Type*} [Category* 𝒦] {X Y Z : 𝒦} (e : X ≅ Y) (a : Y ⟶ Z)
    (b : X ⟶ Z) (h : e.hom ≫ a = b) : e.inv ≫ b = a := by
  rw [← h, Iso.inv_hom_id_assoc]

/-- A functor carries an identity `a ≫ b = 𝟙` to one. -/
private lemma map_comp_eq_id {𝒦 𝒦' : Type*} [Category* 𝒦] [Category* 𝒦'] (F : 𝒦 ⥤ 𝒦')
    {X Y : 𝒦} (a : X ⟶ Y) (b : Y ⟶ X) (h : a ≫ b = 𝟙 _) : F.map a ≫ F.map b = 𝟙 _ := by
  rw [← F.map_comp, h, F.map_id]

/-- Bookkeeping for `H1` of `changeBaseBigBaseGlobalSectionsTrans_comp_bigSectionsIsoAbelian`. -/
private lemma pasteH1 {𝒦 𝒦' : Type*} [Category* 𝒦] [Category* 𝒦'] (Fm : 𝒦 ⥤ 𝒦')
    {X Y Y' Y'' Y₁ : 𝒦} {W W' W'' : 𝒦'} (u : X ⟶ Y) (gc : Y ⟶ Y') (gk : Y' ⟶ Y'')
    (cG : Fm.obj Y ⟶ W) (cG' : Fm.obj Y' ⟶ W') (cGH : Fm.obj Y'' ⟶ W'') (dc : W ⟶ W')
    (dk : W' ⟶ W'') (n1 : Fm.map gc ≫ cG' = cG ≫ dc) (n2 : Fm.map gk ≫ cGH = cG' ≫ dk)
    (m₁ : X ⟶ Y₁) (m₂ : Y₁ ⟶ Y'') (hm : u ≫ gc ≫ gk = m₁ ≫ m₂) (Δc : W ⟶ W'')
    (hΔc : Δc = dc ≫ dk) : Fm.map u ≫ cG ≫ Δc = Fm.map m₁ ≫ Fm.map m₂ ≫ cGH := by
  rw [hΔc, ← reassoc_of% n1, ← n2, ← Fm.map_comp_assoc, ← Fm.map_comp_assoc, ← Fm.map_comp_assoc,
    Category.assoc, hm, Fm.map_comp_assoc]

/-- Bookkeeping for the composite in `H1` of
`changeBaseBigBaseGlobalSectionsTrans_comp_bigSectionsIsoAbelian`. -/
private lemma pasteHm {𝒦 : Type*} [Category* 𝒦] {X Y Y' Y'' Y₁ : 𝒦} (u : X ⟶ Y)
    (gc : Y ⟶ Y') (gk : Y' ⟶ Y'') (cmu : X ⟶ Y') (m₁ : X ⟶ Y₁) (a : Y₁ ⟶ Y')
    (h₀ : u ≫ gc = cmu) (h₁ : cmu = m₁ ≫ a) {m₂ : Y₁ ⟶ Y''} (h₂ : m₂ = a ≫ gk) :
    u ≫ gc ≫ gk = m₁ ≫ m₂ := by
  rw [reassoc_of% h₀, h₁, h₂, Category.assoc]

/-- Bookkeeping for `H2` of `changeBaseBigBaseGlobalSectionsTrans_comp_bigSectionsIsoAbelian`. -/
private lemma pasteH2 {𝒦 : Type*} [Category* 𝒦] {X Y Z W V U T : 𝒦} (sg : X ⟶ Y)
    (c₁ : Y ⟶ Z) (c₂ : Z ⟶ W) (ρ : W ⟶ T) (r' : Z ⟶ V) (k₂ : V ⟶ T) (rG : Y ⟶ U) (k₁ : U ⟶ V)
    (hc₂ : c₂ ≫ ρ = r' ≫ k₂) (hc₁ : c₁ ≫ r' = rG ≫ k₁) (cGH : X ⟶ W) (h : cGH = sg ≫ c₁ ≫ c₂) :
    cGH ≫ ρ = sg ≫ rG ≫ k₁ ≫ k₂ := by
  rw [h, Category.assoc, Category.assoc, hc₂, reassoc_of% hc₁]

/-- Bookkeeping for `H5` of `changeBaseBigBaseGlobalSectionsTrans_comp_bigSectionsIsoAbelian`. -/
private lemma pasteH5 {𝒦 : Type*} [Category* 𝒦] {X Y Z W Y' Z' : 𝒦} (cb : X ⟶ Y') (yV : Y' ⟶ Y)
    (k₁ : Y ⟶ Z) (k₂ : Z ⟶ W) (k₁' : Y' ⟶ Z') (yA : Z' ⟶ Z) (k₂' : Z' ⟶ X) (xA : X ⟶ W)
    (h₁ : yV ≫ k₁ = k₁' ≫ yA) (h₂ : yA ≫ k₂ = k₂' ≫ xA) (h₃ : cb ≫ k₁' ≫ k₂' = 𝟙 _)
    (vV : X ⟶ Y) (hv : vV = cb ≫ yV) (wV : X ⟶ W) (hw : xA = wV) :
    vV ≫ k₁ ≫ k₂ = wV ≫ 𝟙 _ := by
  rw [hv, Category.assoc, reassoc_of% h₁, h₂, reassoc_of% h₃, hw, Category.comp_id]

/-- **The underived comparison of arrow 2 is the underived pullback of [Stacks, Tag 07QA].** -/
theorem changeBaseBigBaseGlobalSectionsTrans_comp_bigSectionsIsoAbelian (N : BigModuleSheaf S') :
    (forgetBaseAction S').map ((changeBaseBigBaseGlobalSectionsTrans fS fX hf).app N) ≫
        (restrictScalarsForgetIso fS).hom.app _ ≫
        (bigSectionsIsoAbelian S).hom.app ((changeBaseBigModulePullback S S' fS fX hf).obj N) =
      (bigSectionsIsoAbelian S').hom.app N ≫
        (globalSections S').map (crisUnit S S' fS fX hf ((bigRestrictToAbelian S').obj N)) ≫
        (crisGlobalSectionsIso S S' fS fX hf).hom.app
          (crisPullback S S' fS fX hf ((bigRestrictToAbelian S').obj N)) ≫
        (globalSections S).map ((crisComparisonTrans fS fX hf).app N) := by
  refine (Sheaf.isLimitConeΓ _).hom_ext fun A => ?_
  show _ ≫ Sheaf.ΓRes _ A = _ ≫ Sheaf.ΓRes _ A
  -- notation
  let T := SheafOfModules.toSheaf.{u + 1} (crystallineStructureSheaf S')
  let σ := smallRestrictionGlobalSectionsIso (S := S')
  let cg := crisGlobalSectionsIso S S' fS fX hf
  let F' := (moduleRestrictι S').obj N
  let L := (moduleLowerShriek S').obj F'
  let LA := T.obj L
  let PN := (changeBaseBigModulePullback S S' fS fX hf).obj N
  let H := (bigRestrictToAbelian S).obj PN
  let G := (changeBaseDirectImage S S' fS fX hf).obj ((bigDirectImage S).obj H)
  let V := op ((changeBase S S' fS fX hf).obj ((CrystallineThickening.ι S).obj A.unop))
  let w := (moduleLowerShriek S').map ((crisRestrictModulesIsoModuleRestrictι S').inv.app N) ≫
    (moduleLowerShriekAdjunction S').counit.app N
  let v : LA ⟶ G := changeBaseRestrictionUnit S S' fS fX hf LA ≫
    (changeBaseDirectImage S S' fS fX hf).map
      ((bigDirectImage S).map ((toAbelianSheaf S).map (lowerShriekCounitPullback fS fX hf N)))
  have hL := pasteUnderivedLeft ((forgetBaseAction S').map
      ((changeBaseBigBaseGlobalSectionsTrans fS fX hf).app N))
    ((restrictScalarsForgetIso fS).hom.app _) (bigSectionsIsoΓ S PN).hom
    ((smallRestrictionGlobalSectionsIso (S := S)).inv.app
      ((SheafOfModules.toSheaf.{u + 1} (crystallineStructureSheaf S)).obj PN))
    (Sheaf.ΓRes H A) _ _ (bigSectionsEval S' N V)
    (inv_comp_eq_of ((smallRestrictionGlobalSectionsIso (S := S)).app _) _ _
      (smallRestrictionGlobalSectionsIso_hom_app_comp_ΓRes_ι S _ A.unop))
    (bigSectionsIsoΓ_hom_comp_ΓRes S PN _) (by ext; rfl)
  -- the triangle identity of `i_! ⊣ i^{-1}`
  have htri : (moduleLowerShriekAdjunction S').unit.app F' ≫
      (crisRestrictModules.{u + 1} S').map w =
        (crisRestrictModulesIsoModuleRestrictι S').inv.app N := by
    have hn := (moduleLowerShriekAdjunction S').unit.naturality
      ((crisRestrictModulesIsoModuleRestrictι S').inv.app N)
    have ht := (moduleLowerShriekAdjunction S').right_triangle_components N
    simp only [Functor.id_map, Functor.comp_map] at hn
    rw [CategoryTheory.Functor.map_comp, ← reassoc_of% hn, ht, Category.comp_id]
  have hab : (toAbelianSheaf S').map ((moduleLowerShriekAdjunction S').unit.app F') ≫
      (smallRestriction S').map
        (T.map w) = 𝟙 _ := by
    have h := (toAbelianSheaf S').map_comp ((moduleLowerShriekAdjunction S').unit.app F')
      ((crisRestrictModules.{u + 1} S').map w)
    rw [htri] at h
    exact h.symm.trans rfl
  have H8 := map_comp_eq_id (globalSections S') _ _ hab
  let x := (toAbelianSheaf S).map (lowerShriekCounitPullback fS fX hf N)
  let cMC := crisModuleComparison S S' fS fX hf F'
  have H1 := pasteH1 (globalSections S') (crisUnit S S' fS fX hf ((bigRestrictToAbelian S').obj N))
    ((crisDirectImage S S' fS fX hf).map cMC) ((crisDirectImage S S' fS fX hf).map x)
    (cg.hom.app
      (crisPullback S S' fS fX hf ((bigRestrictToAbelian S').obj N)))
    (cg.hom.app
      ((toAbelianSheaf S).obj ((crisModuleInverseImage fS fX hf).obj F')))
    (cg.hom.app H) ((globalSections S).map cMC)
    ((globalSections S).map x) (cg.hom.naturality cMC)
    (cg.hom.naturality x)
    ((toAbelianSheaf S').map ((moduleLowerShriekAdjunction S').unit.app F'))
    ((smallRestriction S').map v)
    (pasteHm _ _ _ _ _ _ (crisUnit_comp_crisModuleComparison S S' fS fX hf F') rfl
      ((smallRestriction S').map_comp _ _))
    ((globalSections S).map ((crisComparisonTrans fS fX hf).app N))
    ((globalSections S).map_comp _ _)
  have H2 := pasteH2 (σ.hom.app G)
    ((changeBaseDirectImageGlobalSectionsIso S S' fS fX hf).hom.app ((bigDirectImage S).obj H))
    ((bigDirectImageGlobalSectionsIso S).hom.app H) (Sheaf.ΓRes H A) _ _ (Sheaf.ΓRes G V) _
    (bigDirectImageGlobalSectionsIso_hom_app_comp_ΓRes S H A.unop)
    (changeBaseDirectImageGlobalSectionsIso_hom_app_comp_ΓRes S S' fX fS hf
      ((bigDirectImage S).obj H) ((CrystallineThickening.ι S).obj A.unop))
    (cg.hom.app H)
    (crisGlobalSectionsIso_hom_app_eq S S' fS fX hf H)
  have h₁ := congr_app ((changeBase S S' fS fX hf).op.ranCounit.naturality
    ((bigDirectImage S).map x).hom) (op ((CrystallineThickening.ι S).obj A.unop))
  have h₂ := congr_app ((CrystallineThickening.ι S).op.ranCounit.naturality x.hom) A
  simp only [Functor.comp_obj, Functor.whiskeringLeft_obj_obj, Functor.comp_map,
    Functor.whiskeringLeft_obj_map, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.id_map] at h₁ h₂
  have H5 := pasteH5 ((changeBaseRestrictionUnit S S' fS fX hf LA).hom.app V)
    (((changeBaseDirectImage S S' fS fX hf).map ((bigDirectImage S).map x)).hom.app V) _ _ _ _ _ _
    h₁ h₂ (changeBaseRestrictionUnit_app_comp_ranCounit fS fX hf LA A.unop) (v.hom.app V) rfl
    ((T.map w).hom.app V) rfl
  have hR := pasteUnderived (bigSectionsIsoΓ S' N).hom
    (σ.inv.app
      (T.obj N))
    ((globalSections S').map (crisUnit S S' fS fX hf ((bigRestrictToAbelian S').obj N)))
    (cg.hom.app
      (crisPullback S S' fS fX hf ((bigRestrictToAbelian S').obj N)))
    ((globalSections S).map ((crisComparisonTrans fS fX hf).app N)) (Sheaf.ΓRes H A)
    ((globalSections S').map ((toAbelianSheaf S').map
      ((moduleLowerShriekAdjunction S').unit.app F')))
    ((globalSections S').map ((smallRestriction S').map v))
    (cg.hom.app H) H1
    (σ.hom.app G) (Sheaf.ΓRes G V) _ H2
    (σ.hom.app LA) ((bigGlobalSections S').map v)
    (σ.hom.naturality v)
    (Sheaf.ΓRes LA V) (v.hom.app V) (Sheaf.ΓRes_naturality v V)
    ((T.map w).hom.app V) (𝟙 _)
    H5
    ((bigGlobalSections S').map
      (T.map w))
    (Sheaf.ΓRes (T.obj N) V)
    (Sheaf.ΓRes_naturality (T.map w)
      V).symm
    _ _ (σ.hom.naturality
      (T.map w)).symm H8
    (σ.inv_hom_id_app _)
    _ (bigSectionsIsoΓ_hom_comp_ΓRes S' N V)
  exact hL.trans (hR.trans (Category.comp_id _)).symm

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
