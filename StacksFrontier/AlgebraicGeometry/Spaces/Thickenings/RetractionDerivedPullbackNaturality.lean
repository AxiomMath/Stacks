module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.RetractionDerivedPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartBaseChangeCompIso

/-!
# Naturality in `V` of the identification of `𝒪_X[𝒪_X ⊗_k V]`-modules with `𝒪_{X_V}`-modules

Let `X ⟶ X_V ⟶ X` and `X ⟶ X_W ⟶ X` be the base changes of `Spec k ⟶ Spec k[V] ⟶ Spec k` and
`Spec k ⟶ Spec k[W] ⟶ Spec k` along one `p : X ⟶ Spec k`, and `H : X_W ⟶ X_V` a morphism
compatible with the sections and the retractions, together with a ring map
`g : 𝒪_X[𝒪_X ⊗_k V] ⟶ 𝒪_X[𝒪_X ⊗_k W]` that `H` induces under the identifications of the
structure sheaves. Then, through `AlgebraicGeometry.Space.squareZeroModuleEquivalence`, the direct
image of modules along `H` is restriction of scalars along `g`
(`AlgebraicGeometry.Space.squareZeroPushforwardNaturalityIso`), so the pullback of modules along
`H` is extension of scalars along `g` (`AlgebraicGeometry.Space.squareZeroPullbackNaturalityIso`),
and on derived categories the derived pullback along `H` is the derived base change along `g`
(`AlgebraicGeometry.Space.squareZeroDerivedPullbackNaturality`). These are the comparisons `G2`
and `G3` of the proof of `toLift_pullback` in Stacks 0DLL.

The compatibility of `g` with `H` is taken here on the site of `X_V`, as an equation of maps
`𝒪_{X_V} ⟶ i_V^* (𝒪_X[𝒪_X ⊗_k W])` (`AlgebraicGeometry.Space.thickeningPushforwardRingMap`).

`χ` (`AlgebraicGeometry.Space.squareZeroDerivedPullbackNaturality`) is the comparison of two left
derived functors of degreewise extension of scalars along `g` followed by the equivalence for `W`:
the derived base change along `g` followed by the derived equivalence for `W`
(`AlgebraicGeometry.Space.squareZeroDerivedExtensionOfScalarsComparison`), and the derived
equivalence for `V` followed by the derived pullback along `H`
(`AlgebraicGeometry.Space.squareZeroDerivedPullbackNaturalityComparison`).

Nothing here is registered.

## References

* [Stacks Project, Tag 0DLL](https://stacks.math.columbia.edu/tag/0DLL)
-/

@[expose] public noncomputable section

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

open CategoryTheory CategoryTheory.Limits Opposite Deformation.Artin Deformation.ComplexLift
  Stacks.TensorByBaseModule

universe d d' u

namespace AlgebraicGeometry.Space

section Generic

variable {C : Type*} [Category* C] {D : Type*} [Category* D] {E : Type*} [Category* E]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {L : GrothendieckTopology E}
  {F : C ⥤ D} {G : D ⥤ E} [F.IsContinuous J K] [G.IsContinuous K L] [(F ⋙ G).IsContinuous J L]
  {T : Sheaf J RingCat.{u}} {R' : Sheaf K RingCat.{u}} {R : Sheaf L RingCat.{u}}

/-- Restriction of sections along `G`, then of scalars along `α`, then the pushforward along `F`
and `φ`, is the pushforward along `F ⋙ G` and the composite ring map. -/
def pushforwardRestrictScalarsPushforwardIso
    (α : R' ⟶ (G.sheafPushforwardContinuous RingCat.{u} K L).obj R)
    (φ : T ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R') :
    (SheafOfModules.pushforward.{u} (F := G)
          (𝟙 ((G.sheafPushforwardContinuous RingCat.{u} K L).obj R)) ⋙
        SheafOfModules.restrictScalars.{u} α) ⋙ SheafOfModules.pushforward.{u} φ ≅
      SheafOfModules.pushforward.{u} (F := F ⋙ G)
        (φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map α) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

/-- Restriction of scalars along `β`, then of sections along `F`, then of scalars along `α`, is
the pushforward along `F` and the composite ring map. -/
def restrictScalarsPushforwardRestrictScalarsIso {R₀ : Sheaf K RingCat.{u}} (β : R₀ ⟶ R')
    (α : T ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R₀) :
    SheafOfModules.restrictScalars.{u} β ⋙
        (SheafOfModules.pushforward.{u} (F := F)
            (𝟙 ((F.sheafPushforwardContinuous RingCat.{u} J K).obj R₀)) ⋙
          SheafOfModules.restrictScalars.{u} α) ≅
      SheafOfModules.pushforward.{u} (F := F)
        (α ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map β) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

/-- **Two composites of restrictions of sections and of scalars agree** as soon as their ring maps
do, up to an isomorphism `e : G' ≅ F ⋙ G` of the functors of sites. -/
def pushforwardRestrictScalarsCongrIso {G' : C ⥤ E} [G'.IsContinuous J L] {R₀ : Sheaf L RingCat.{u}}
    (e : G' ≅ F ⋙ G) (α : R' ⟶ (G.sheafPushforwardContinuous RingCat.{u} K L).obj R)
    (φ : T ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R') (β : R₀ ⟶ R)
    (γ : T ⟶ (G'.sheafPushforwardContinuous RingCat.{u} J L).obj R₀)
    (h : (φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map α) ≫
        (Functor.sheafPushforwardContinuousNatTrans e.hom RingCat.{u} J L).app R =
      γ ≫ (G'.sheafPushforwardContinuous RingCat.{u} J L).map β) :
    (SheafOfModules.pushforward.{u} (F := G)
          (𝟙 ((G.sheafPushforwardContinuous RingCat.{u} K L).obj R)) ⋙
        SheafOfModules.restrictScalars.{u} α) ⋙ SheafOfModules.pushforward.{u} φ ≅
      SheafOfModules.restrictScalars.{u} β ⋙
        (SheafOfModules.pushforward.{u} (F := G')
            (𝟙 ((G'.sheafPushforwardContinuous RingCat.{u} J L).obj R₀)) ⋙
          SheafOfModules.restrictScalars.{u} γ) :=
  pushforwardRestrictScalarsPushforwardIso α φ ≪≫ SheafOfModules.pushforwardCongr₂ _ e h ≪≫
    (restrictScalarsPushforwardRestrictScalarsIso β γ).symm

end Generic

section GenericDerived

variable {C₁ : Type*} [Category* C₁] [Abelian C₁] [HasDerivedCategory C₁]
  {C₂ : Type*} [Category* C₂] [Abelian C₂] [HasDerivedCategory C₂]
  (E : C₁ ≌ C₂) [E.functor.Additive] {T : Type*} [Category* T]

/-- The comparison of `LF` precomposed with the derived equivalence of `E`, for a comparison
`α : Q ⋙ LF ⟶ F'` of `LF` and an identification `F ≅ E ⋙ F'` on complexes. -/
def precompDerivedEquivalenceComparison (LF : DerivedCategory C₂ ⥤ T)
    {F' : CochainComplex C₂ ℤ ⥤ T} (α : DerivedCategory.Q ⋙ LF ⟶ F')
    {F : CochainComplex C₁ ℤ ⥤ T}
    (e : F ≅ E.functor.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ F') :
    DerivedCategory.Q ⋙ ((Stacks.DerivedQCoh.Equivalence.mapDerivedCategory E).functor ⋙ LF) ⟶ F :=
  Functor.whiskerLeft DerivedCategory.Q
      (Iso.refl ((Stacks.DerivedQCoh.Equivalence.mapDerivedCategory E).functor ⋙ LF)).inv ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight E.functor.mapDerivedCategoryFactors.symm.inv LF ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (E.functor.mapHomologicalComplex (ComplexShape.up ℤ)) α ≫ e.inv

/-- The component of `AlgebraicGeometry.Space.precompDerivedEquivalenceComparison` at a complex
`K`. -/
theorem precompDerivedEquivalenceComparison_app (LF : DerivedCategory C₂ ⥤ T)
    {F' : CochainComplex C₂ ℤ ⥤ T} (α : DerivedCategory.Q ⋙ LF ⟶ F')
    {F : CochainComplex C₁ ℤ ⥤ T} (e : F ≅ E.functor.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ F')
    (K : CochainComplex C₁ ℤ) :
    (precompDerivedEquivalenceComparison E LF α e).app K =
      LF.map (E.functor.mapDerivedCategoryFactors.hom.app K) ≫
        α.app ((E.functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫ e.inv.app K := by
  simp [precompDerivedEquivalenceComparison]

/-- **Precomposing a left derived functor with the derived equivalence of `E` gives a left derived
functor**, with `AlgebraicGeometry.Space.precompDerivedEquivalenceComparison`. -/
theorem isLeftDerivedFunctor_precompDerivedEquivalenceComparison (LF : DerivedCategory C₂ ⥤ T)
    {F' : CochainComplex C₂ ℤ ⥤ T} (α : DerivedCategory.Q ⋙ LF ⟶ F')
    {F : CochainComplex C₁ ℤ ⥤ T} (e : F ≅ E.functor.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ F')
    [LF.IsLeftDerivedFunctor α (HomologicalComplex.quasiIso C₂ (ComplexShape.up ℤ))] :
    ((Stacks.DerivedQCoh.Equivalence.mapDerivedCategory E).functor ⋙ LF).IsLeftDerivedFunctor
      (precompDerivedEquivalenceComparison E LF α e)
      (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ)) := by
  have := Functor.IsLeftDerivedFunctor.isRightKanExtension LF α
    (HomologicalComplex.quasiIso C₂ (ComplexShape.up ℤ))
  have : (E.functor.mapHomologicalComplex (ComplexShape.up ℤ)).IsEquivalence :=
    (E.mapHomologicalComplex (ComplexShape.up ℤ)).isEquivalence_functor
  have : (Stacks.DerivedQCoh.Equivalence.mapDerivedCategory E).functor.IsEquivalence :=
    (Stacks.DerivedQCoh.Equivalence.mapDerivedCategory E).isEquivalence_functor
  exact ⟨(Functor.isRightKanExtension_iff_precomp_equivalence
    (G := E.functor.mapHomologicalComplex (ComplexShape.up ℤ))
    (G' := (Stacks.DerivedQCoh.Equivalence.mapDerivedCategory E).functor)
    (precompDerivedEquivalenceComparison E LF α e) α
    E.functor.mapDerivedCategoryFactors.symm e (Iso.refl _) rfl).1 inferInstance⟩

/-- The comparison of `LF` followed by the derived equivalence of `E`, for a comparison
`α : L ⋙ LF ⟶ F₀ ⋙ Q` of `LF`. -/
def postcompDerivedEquivalenceComparison {C₀ D₀ : Type*} [Category* C₀] [Category* D₀]
    {L : C₀ ⥤ D₀} (LF : D₀ ⥤ DerivedCategory C₁) {F₀ : C₀ ⥤ CochainComplex C₁ ℤ}
    (α : L ⋙ LF ⟶ F₀ ⋙ DerivedCategory.Q) :
    L ⋙ (LF ⋙ (Stacks.DerivedQCoh.Equivalence.mapDerivedCategory E).functor) ⟶
      (F₀ ⋙ E.functor.mapHomologicalComplex (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q :=
  (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight α (Stacks.DerivedQCoh.Equivalence.mapDerivedCategory E).functor ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft F₀ E.functor.mapDerivedCategoryFactors.hom ≫
    (Functor.associator _ _ _).inv

/-- The component of `AlgebraicGeometry.Space.postcompDerivedEquivalenceComparison` at an object
`K`. -/
theorem postcompDerivedEquivalenceComparison_app {C₀ D₀ : Type*} [Category* C₀] [Category* D₀]
    {L : C₀ ⥤ D₀} (LF : D₀ ⥤ DerivedCategory C₁) {F₀ : C₀ ⥤ CochainComplex C₁ ℤ}
    (α : L ⋙ LF ⟶ F₀ ⋙ DerivedCategory.Q) (K : C₀) :
    (postcompDerivedEquivalenceComparison E LF α).app K =
      (Stacks.DerivedQCoh.Equivalence.mapDerivedCategory E).functor.map (α.app K) ≫
        E.functor.mapDerivedCategoryFactors.hom.app (F₀.obj K) := by
  simp [postcompDerivedEquivalenceComparison]

/-- **Following a left derived functor by the derived equivalence of `E` gives a left derived
functor**, with `AlgebraicGeometry.Space.postcompDerivedEquivalenceComparison`: the derived
equivalence is a right adjoint. -/
theorem isLeftDerivedFunctor_postcompDerivedEquivalenceComparison {C₀ D₀ : Type*} [Category* C₀]
    [Category* D₀] {L : C₀ ⥤ D₀} (W : MorphismProperty C₀) [L.IsLocalization W]
    (LF : D₀ ⥤ DerivedCategory C₁) {F₀ : C₀ ⥤ CochainComplex C₁ ℤ}
    (α : L ⋙ LF ⟶ F₀ ⋙ DerivedCategory.Q) [LF.IsLeftDerivedFunctor α W] :
    (LF ⋙ (Stacks.DerivedQCoh.Equivalence.mapDerivedCategory E).functor).IsLeftDerivedFunctor
      (postcompDerivedEquivalenceComparison E LF α) W := by
  have := (Stacks.DerivedQCoh.Equivalence.mapDerivedCategory E).isRightAdjoint_functor
  have h := (Functor.isLeftDerivedFunctor_iff_isRightKanExtension _
    ((Functor.associator _ _ _).inv ≫
      Functor.whiskerRight α (Stacks.DerivedQCoh.Equivalence.mapDerivedCategory E).functor) W).1
    inferInstance
  rw [Functor.isLeftDerivedFunctor_iff_isRightKanExtension]
  exact (Functor.isRightKanExtension_iff_of_iso₂ _ _
    (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft F₀ E.functor.mapDerivedCategoryFactors ≪≫
      (Functor.associator _ _ _).symm) (Iso.refl _) (by
        simp [postcompDerivedEquivalenceComparison])).1 h

end GenericDerived

section GenericChi

variable {A : Type*} [Category* A] [Abelian A] [hA : HasDerivedCategory A]
  {A' : Type*} [Category* A'] [Abelian A'] [hA' : HasDerivedCategory A']
  {C₂ : Type*} [Category* C₂] [Abelian C₂] [HasDerivedCategory C₂]
  {C₂' : Type*} [Category* C₂'] [Abelian C₂'] [HasDerivedCategory C₂']
  (EV : A ≌ C₂) [hEV : EV.functor.Additive] (EW : A' ≌ C₂') [hEW : EW.functor.Additive]
  (LF : DerivedCategory C₂ ⥤ DerivedCategory C₂') (P : CochainComplex C₂ ℤ ⥤ CochainComplex C₂' ℤ)
  (αP : DerivedCategory.Q ⋙ LF ⟶ P ⋙ DerivedCategory.Q)
  [LF.IsLeftDerivedFunctor αP (HomologicalComplex.quasiIso C₂ (ComplexShape.up ℤ))]
  (Lg : DerivedCategory A ⥤ DerivedCategory A') (F₀ : CochainComplex A ℤ ⥤ CochainComplex A' ℤ)
  (αg : DerivedCategory.Q ⋙ Lg ⟶ F₀ ⋙ DerivedCategory.Q)
  [Lg.IsLeftDerivedFunctor αg (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))]
  (γ : EV.functor.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ P ≅
    F₀ ⋙ EW.functor.mapHomologicalComplex (ComplexShape.up ℤ))

/-- The factorization of the derived equivalence of `EW` through the localizations, read after
`F₀`. -/
def derivedEquivalenceFactorsIso :
    (F₀ ⋙ DerivedCategory.Q) ⋙ (Stacks.DerivedQCoh.Equivalence.mapDerivedCategory EW).functor ≅
      (F₀ ⋙ EW.functor.mapHomologicalComplex (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft F₀ EW.functor.mapDerivedCategoryFactors ≪≫
    (Functor.associator _ _ _).symm

/-- **The comparison `χ` of two left derived functors**: `Lg` followed by the derived equivalence
of `EW`, and the derived equivalence of `EV` followed by `LF`, are left derived functors of
`F₀ ⋙ EW` and `EV ⋙ P` respectively, which `γ` identifies. -/
def derivedEquivalenceLeftDerivedIso :
    Lg ⋙ (Stacks.DerivedQCoh.Equivalence.mapDerivedCategory EW).functor ≅
      (Stacks.DerivedQCoh.Equivalence.mapDerivedCategory EV).functor ⋙ LF :=
  haveI : (Stacks.DerivedQCoh.Equivalence.mapDerivedCategory EW).functor.IsRightAdjoint :=
    (Stacks.DerivedQCoh.Equivalence.mapDerivedCategory EW).isRightAdjoint_functor
  haveI := isLeftDerivedFunctor_precompDerivedEquivalenceComparison EV LF αP
    ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight γ DerivedCategory.Q).symm
  Functor.leftDerivedNatIso _ _
    ((Functor.associator _ _ _).inv ≫
      Functor.whiskerRight αg (Stacks.DerivedQCoh.Equivalence.mapDerivedCategory EW).functor)
    (precompDerivedEquivalenceComparison EV LF αP
      ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight γ DerivedCategory.Q).symm)
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))
    (derivedEquivalenceFactorsIso EW F₀)

/-- **`χ` is compatible with the comparisons with complexes.** -/
theorem derivedEquivalenceLeftDerivedIso_fac (K : CochainComplex A ℤ) :
    (derivedEquivalenceLeftDerivedIso EV EW LF P αP Lg F₀ αg γ).hom.app (DerivedCategory.Q.obj K) ≫
        LF.map (EV.functor.mapDerivedCategoryFactors.hom.app K) ≫
        αP.app ((EV.functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Q.map (γ.hom.app K) =
      (Stacks.DerivedQCoh.Equivalence.mapDerivedCategory EW).functor.map (αg.app K) ≫
        (derivedEquivalenceFactorsIso EW F₀).hom.app K := by
  have := (Stacks.DerivedQCoh.Equivalence.mapDerivedCategory EW).isRightAdjoint_functor
  have := isLeftDerivedFunctor_precompDerivedEquivalenceComparison EV LF αP
    ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight γ DerivedCategory.Q).symm
  have h := Functor.leftDerivedNatTrans_app _ _
    ((Functor.associator _ _ _).inv ≫
      Functor.whiskerRight αg (Stacks.DerivedQCoh.Equivalence.mapDerivedCategory EW).functor)
    (precompDerivedEquivalenceComparison EV LF αP
      ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight γ DerivedCategory.Q).symm)
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))
    (derivedEquivalenceFactorsIso EW F₀).hom K
  rw [precompDerivedEquivalenceComparison_app] at h
  simp only [Iso.symm_inv, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.associator_inv_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Category.id_comp] at h
  exact h

end GenericChi

section Naturality

variable {k : Type u} [CommRing k] {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {toS : Spec (.of k) ⟶ S} {hk : B.Contains (Spec (.of k))} {V W : SiteModule k B}
  {X X'V X'W : AlgebraicSpaces B S hS} {p : X.1 ⟶ yoneda.obj (algebraOver k B S hS toS hk)}
  {iV : X ⟶ X'V} (hiV : IsThickeningHom B S hS iV)
  {qV : X'V ⟶ X} (hV : iV ≫ qV = 𝟙 X) {hqV : yoneda.relativelyRepresentable qV.hom}
  {p'V : X'V.1 ⟶ yoneda.obj (squareZeroOver k B S hS toS V)}
  {τV : squareZeroOver k B S hS toS V ⟶ algebraOver k B S hS toS hk}
  (hipV : iV.hom ≫ p'V = p ≫ yoneda.map (squareZeroArrow k B S hS toS hk V))
  (hpbV : IsPullback qV.hom p'V p (yoneda.map τV))
  (hβτV : squareZeroArrow k B S hS toS hk V ≫ τV = 𝟙 _)
  {iW : X ⟶ X'W} (hiW : IsThickeningHom B S hS iW)
  {qW : X'W ⟶ X} (hW : iW ≫ qW = 𝟙 X) {hqW : yoneda.relativelyRepresentable qW.hom}
  {p'W : X'W.1 ⟶ yoneda.obj (squareZeroOver k B S hS toS W)}
  {τW : squareZeroOver k B S hS toS W ⟶ algebraOver k B S hS toS hk}
  (hipW : iW.hom ≫ p'W = p ≫ yoneda.map (squareZeroArrow k B S hS toS hk W))
  (hpbW : IsPullback qW.hom p'W p (yoneda.map τW))
  (hβτW : squareZeroArrow k B S hS toS hk W ≫ τW = 𝟙 _)
  {H : X'W ⟶ X'V} (hH : yoneda.relativelyRepresentable H.hom) (hiH : iW ≫ H = iV)

include hiV hiH in
/-- The composite `i_W ≫ H` is relatively representable. -/
theorem squareZeroChart_rep_comp : yoneda.relativelyRepresentable (iW ≫ H).hom := by
  rw [hiH]
  exact hiV.isClosedImmersion.rep

/-- Chart base change along `i_V` equals chart base change along `i_W ≫ H`, for
`i_W ≫ H = i_V`. -/
theorem smallBaseChange_eq_of_comp_eq :
    smallBaseChange B S hS iV hiV.isClosedImmersion.rep =
      smallBaseChange B S hS (iW ≫ H) (squareZeroChart_rep_comp hiV hiH) := by
  subst hiH
  rfl

/-- **Chart base change along `i_V` is chart base change along `H` and then along `i_W`**, for
`i_W ≫ H = i_V`: `AlgebraicGeometry.Space.smallBaseChangeChartCompIso`. -/
def squareZeroChartCompIso :
    smallBaseChange B S hS iV hiV.isClosedImmersion.rep ≅
      smallBaseChange B S hS H hH ⋙ smallBaseChange B S hS iW hiW.isClosedImmersion.rep :=
  eqToIso (smallBaseChange_eq_of_comp_eq hiV hiH) ≪≫
    smallBaseChangeChartCompIso B S hS iW H hiW.isClosedImmersion.rep hH
      (squareZeroChart_rep_comp hiV hiH)

variable {g : sqZeroExtSheafAnySite (structureSheaf B S hS X.1 X.2)
      ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
        (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
        (squareZeroCoefficientMap k B S hS toS hk p)).obj V.obj) ⟶
    sqZeroExtSheafAnySite (structureSheaf B S hS X.1 X.2)
      ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
        (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
        (squareZeroCoefficientMap k B S hS toS hk p)).obj W.obj)}

attribute [local instance] isContinuous_smallBaseChange

/-- **The ring map of `H` on the site of `X_V`** relative to a ring map
`ψ : 𝒪_{X_W} ⟶ i_W^* R` on the site of `X_W`:
`𝒪_{X_V} ⟶ H_* 𝒪_{X_W} ⟶ H_* i_W^* R ≅ i_V^* R`. -/
def thickeningPushforwardRingMap {R : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u}}
    (ψ : structureSheaf B S hS X'W.1 X'W.2 ⟶
      (thickeningRetractionEquivalence B S hS hiW hW hqW CommRingCat.{u}).functor.obj R) :
    structureSheaf B S hS X'V.1 X'V.2 ⟶
      (thickeningRetractionEquivalence B S hS hiV hV hqV CommRingCat.{u}).functor.obj R :=
  smallBaseChangeSharpCommRingCat B S hS H hH ≫
    ((smallBaseChange B S hS H hH).sheafPushforwardContinuous CommRingCat.{u}
      (SmallEtale.topology B S hS X'V.1) (SmallEtale.topology B S hS X'W.1)).map ψ ≫
    (Functor.sheafPushforwardContinuousNatTrans (squareZeroChartCompIso hiV hiW hH hiH).hom
      CommRingCat.{u} (SmallEtale.topology B S hS X'V.1) (SmallEtale.topology B S hS X.1)).app R

/-- `AlgebraicGeometry.Space.thickeningPushforwardRingMap`, read on sheaves of rings. -/
theorem thickeningPushforwardRingMap_ringCat
    {R : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u}}
    (ψ : structureSheaf B S hS X'W.1 X'W.2 ⟶
      (thickeningRetractionEquivalence B S hS hiW hW hqW CommRingCat.{u}).functor.obj R) :
    (sheafCompose (SmallEtale.topology B S hS X'V.1) (forget₂ CommRingCat.{u} RingCat.{u})).map
        (thickeningPushforwardRingMap (hqV := hqV) hiV hV hiW hW hH hiH ψ) =
      ((smallBaseChangeSharp B S hS H hH ≫
        ((smallBaseChange B S hS H hH).sheafPushforwardContinuous RingCat.{u}
          (SmallEtale.topology B S hS X'V.1) (SmallEtale.topology B S hS X'W.1)).map
          ((sheafCompose (SmallEtale.topology B S hS X'W.1)
            (forget₂ CommRingCat.{u} RingCat.{u})).map ψ)) ≫
      (Functor.sheafPushforwardContinuousNatTrans (squareZeroChartCompIso hiV hiW hH hiH).hom
        RingCat.{u} (SmallEtale.topology B S hS X'V.1) (SmallEtale.topology B S hS X.1)).app
        (Stacks.SheafOfModules.Tensor.ringSheaf R) :
        smallEtaleRingSheaf B S hS X'V.1 X'V.2 ⟶
          ((smallBaseChange B S hS iV hiV.isClosedImmersion.rep).sheafPushforwardContinuous
            RingCat.{u}
            (SmallEtale.topology B S hS X'V.1) (SmallEtale.topology B S hS X.1)).obj
            (Stacks.SheafOfModules.Tensor.ringSheaf R)) :=
  rfl

/-- The Comparison Lemma equivalence of a thickening on a morphism of sheaves of commutative rings,
read on sheaves of rings: restriction along chart base change along `i`. -/
theorem thickeningRetractionEquivalence_functor_map_ringCat
    {R₁ R₂ : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u}} (g : R₁ ⟶ R₂) :
    (sheafCompose (SmallEtale.topology B S hS X'V.1) (forget₂ CommRingCat.{u} RingCat.{u})).map
        ((thickeningRetractionEquivalence B S hS hiV hV hqV CommRingCat.{u}).functor.map g) =
      ((smallBaseChange B S hS iV hiV.isClosedImmersion.rep).sheafPushforwardContinuous RingCat.{u}
          (SmallEtale.topology B S hS X'V.1) (SmallEtale.topology B S hS X.1)).map
        ((sheafCompose (SmallEtale.topology B S hS X.1)
          (forget₂ CommRingCat.{u} RingCat.{u})).map g) :=
  rfl

/-- The compatibility of `g` with `H`, read on sheaves of rings, in the form
`SheafOfModules.pushforwardCongr₂` consumes. -/
theorem squareZeroPushforwardNaturality_ringMap_eq
    (hg : (squareZeroStructureSheafIso (hq := hqV) hiV hV hipV hpbV hβτV).hom ≫
        (thickeningRetractionEquivalence B S hS hiV hV hqV CommRingCat.{u}).functor.map g =
      thickeningPushforwardRingMap (hqV := hqV) hiV hV hiW hW hH hiH
        (squareZeroStructureSheafIso (hq := hqW) hiW hW hipW hpbW hβτW).hom) :
    (smallBaseChangeSharp B S hS H hH ≫
        ((smallBaseChange B S hS H hH).sheafPushforwardContinuous RingCat.{u}
          (SmallEtale.topology B S hS X'V.1) (SmallEtale.topology B S hS X'W.1)).map
          ((sheafCompose (SmallEtale.topology B S hS X'W.1)
            (forget₂ CommRingCat.{u} RingCat.{u})).map
            (squareZeroStructureSheafIso (hq := hqW) hiW hW hipW hpbW hβτW).hom)) ≫
      (Functor.sheafPushforwardContinuousNatTrans (squareZeroChartCompIso hiV hiW hH hiH).hom
        RingCat.{u} (SmallEtale.topology B S hS X'V.1) (SmallEtale.topology B S hS X.1)).app
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (sqZeroExtSheafAnySite (structureSheaf B S hS X.1 X.2)
            ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
              (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
              (squareZeroCoefficientMap k B S hS toS hk p)).obj W.obj))) =
    (sheafCompose (SmallEtale.topology B S hS X'V.1) (forget₂ CommRingCat.{u} RingCat.{u})).map
        (squareZeroStructureSheafIso (hq := hqV) hiV hV hipV hpbV hβτV).hom ≫
      ((smallBaseChange B S hS iV hiV.isClosedImmersion.rep).sheafPushforwardContinuous RingCat.{u}
        (SmallEtale.topology B S hS X'V.1) (SmallEtale.topology B S hS X.1)).map
        ((sheafCompose (SmallEtale.topology B S hS X.1)
          (forget₂ CommRingCat.{u} RingCat.{u})).map g) := by
  refine (thickeningPushforwardRingMap_ringCat (hqV := hqV) hiV hV hiW hW hH hiH _).symm.trans ?_
  refine (congrArg (sheafCompose (SmallEtale.topology B S hS X'V.1)
    (forget₂ CommRingCat.{u} RingCat.{u})).map hg).symm.trans ?_
  rw [Functor.map_comp, thickeningRetractionEquivalence_functor_map_ringCat]
  rfl

/-- **The pushforward of modules along `H` is restriction of scalars along `g`**, read through
`AlgebraicGeometry.Space.squareZeroModuleEquivalence` for `V` and `W`, as soon as `g` is the ring
map of `H` on the site of `X_V`: both are restriction of sections along chart base change along
`i_V`, up to `AlgebraicGeometry.Space.squareZeroChartCompIso`. -/
def squareZeroPushforwardNaturalityIso
    (hg : (squareZeroStructureSheafIso (hq := hqV) hiV hV hipV hpbV hβτV).hom ≫
        (thickeningRetractionEquivalence B S hS hiV hV hqV CommRingCat.{u}).functor.map g =
      thickeningPushforwardRingMap (hqV := hqV) hiV hV hiW hW hH hiH
        (squareZeroStructureSheafIso (hq := hqW) hiW hW hipW hpbW hβτW).hom) :
    (squareZeroModuleEquivalence (hq := hqW) hiW hW hipW hpbW hβτW).functor ⋙
        smallBaseChangeModulePushforward.{u, u} B S hS H hH ≅
      SheafOfModules.restrictScalars
          ((sheafCompose (SmallEtale.topology B S hS X.1)
            (forget₂ CommRingCat.{u} RingCat.{u})).map g) ⋙
        (squareZeroModuleEquivalence (hq := hqV) hiV hV hipV hpbV hβτV).functor :=
  pushforwardRestrictScalarsCongrIso (squareZeroChartCompIso hiV hiW hH hiH)
    (T := smallEtaleRingSheaf B S hS X'V.1 X'V.2)
    (R₀ := Stacks.SheafOfModules.Tensor.ringSheaf
      (sqZeroExtSheafAnySite (structureSheaf B S hS X.1 X.2)
        ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
          (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
          (squareZeroCoefficientMap k B S hS toS hk p)).obj V.obj)))
    (R := Stacks.SheafOfModules.Tensor.ringSheaf
      (sqZeroExtSheafAnySite (structureSheaf B S hS X.1 X.2)
        ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
          (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
          (squareZeroCoefficientMap k B S hS toS hk p)).obj W.obj)))
    ((sheafCompose (SmallEtale.topology B S hS X'W.1) (forget₂ CommRingCat.{u} RingCat.{u})).map
      (squareZeroStructureSheafIso (hq := hqW) hiW hW hipW hpbW hβτW).hom)
    (smallBaseChangeSharp B S hS H hH)
    ((sheafCompose (SmallEtale.topology B S hS X.1) (forget₂ CommRingCat.{u} RingCat.{u})).map g)
    ((sheafCompose (SmallEtale.topology B S hS X'V.1) (forget₂ CommRingCat.{u} RingCat.{u})).map
      (squareZeroStructureSheafIso (hq := hqV) hiV hV hipV hpbV hβτV).hom)
    (squareZeroPushforwardNaturality_ringMap_eq hiV hV hipV hpbV hβτV hiW hW hipW hpbW hβτW
      hH hiH hg)

/-- **The right adjoints of the two sides of `G2`**: the direct image of modules along `H`, read
through the equivalences for `V` and `W`, is restriction of scalars along `g`
(`AlgebraicGeometry.Space.squareZeroPushforwardNaturalityIso`, transported along the
equivalences). -/
def squareZeroPushforwardNaturalityRightAdjointIso
    (hg : (squareZeroStructureSheafIso (hq := hqV) hiV hV hipV hpbV hβτV).hom ≫
        (thickeningRetractionEquivalence B S hS hiV hV hqV CommRingCat.{u}).functor.map g =
      thickeningPushforwardRingMap (hqV := hqV) hiV hV hiW hW hH hiH
        (squareZeroStructureSheafIso (hq := hqW) hiW hW hipW hpbW hβτW).hom) :
    (smallEtaleRingedToposHom B S hS H).pushforwardModules ⋙
        (squareZeroModuleEquivalence (hq := hqV) hiV hV hipV hpbV hβτV).inverse ≅
      (squareZeroModuleEquivalence (hq := hqW) hiW hW hipW hpbW hβτW).inverse ⋙
        SheafOfModules.restrictScalars
          ((sheafCompose (SmallEtale.topology B S hS X.1)
            (forget₂ CommRingCat.{u} RingCat.{u})).map g) :=
  Functor.isoWhiskerRight (pushforwardModulesIsoModulePushforward B S hS H ≪≫
      modulePushforwardChartIso B S hS H hH) _ ≪≫
    Functor.isoWhiskerRight ((Functor.leftUnitor _).symm ≪≫
      Functor.isoWhiskerRight
          (squareZeroModuleEquivalence (hq := hqW) hiW hW hipW hpbW hβτW).counitIso.symm _ ≪≫
        Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (squareZeroPushforwardNaturalityIso hiV hV hipV hpbV hβτV
        hiW hW hipW hpbW hβτW hH hiH hg)) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
          (squareZeroModuleEquivalence (hq := hqV) hiV hV hipV hpbV hβτV).unitIso.symm ≪≫
        Functor.rightUnitor _)

/-- The adjunction `E_V ⋙ H^* ⊣ E_W⁻¹ ⋙ g_*`: the composite of the equivalence for `V` with
`H^* ⊣ H_*`, with right adjoint transported along
`AlgebraicGeometry.Space.squareZeroPushforwardNaturalityRightAdjointIso`. -/
def squareZeroPullbackNaturalityAdjunction
    (hg : (squareZeroStructureSheafIso (hq := hqV) hiV hV hipV hpbV hβτV).hom ≫
        (thickeningRetractionEquivalence B S hS hiV hV hqV CommRingCat.{u}).functor.map g =
      thickeningPushforwardRingMap (hqV := hqV) hiV hV hiW hW hH hiH
        (squareZeroStructureSheafIso (hq := hqW) hiW hW hipW hpbW hβτW).hom) :
    (squareZeroModuleEquivalence (hq := hqV) hiV hV hipV hpbV hβτV).functor ⋙
        (smallEtaleRingedToposHom B S hS H).toModulesHom.pullbackModules ⊣
      (squareZeroModuleEquivalence (hq := hqW) hiW hW hipW hpbW hβτW).inverse ⋙
        SheafOfModules.restrictScalars
          ((sheafCompose (SmallEtale.topology B S hS X.1)
            (forget₂ CommRingCat.{u} RingCat.{u})).map g) :=
  ((squareZeroModuleEquivalence (hq := hqV) hiV hV hipV hpbV hβτV).toAdjunction.comp
      (RingedToposHom.pullbackAdjPushforwardModules
        (smallEtaleRingedToposHom B S hS H))).ofNatIsoRight
    (squareZeroPushforwardNaturalityRightAdjointIso hiV hV hipV hpbV hβτV hiW hW hipW hpbW hβτW
      hH hiH hg)

variable (g) in
/-- The adjunction `g^* ⋙ E_W ⊣ E_W⁻¹ ⋙ g_*`: extension of scalars along `g`, Stacks 03CZ,
followed by the equivalence for `W`. -/
def squareZeroExtensionOfScalarsAdjunction :
    extensionOfScalars g ⋙ (squareZeroModuleEquivalence (hq := hqW) hiW hW hipW hpbW hβτW).functor ⊣
      (squareZeroModuleEquivalence (hq := hqW) hiW hW hipW hpbW hβτW).inverse ⋙
        SheafOfModules.restrictScalars
          ((sheafCompose (SmallEtale.topology B S hS X.1)
            (forget₂ CommRingCat.{u} RingCat.{u})).map g) :=
  (Stacks.Sheaves.RingedToposModules.extendRestrictScalarsAdjunction _ _ _ _).comp
    (squareZeroModuleEquivalence (hq := hqW) hiW hW hipW hpbW hβτW).toAdjunction

/-- **Stacks 0DLL, `G2`: the pullback of modules along `H` is extension of scalars along `g`**,
read through `AlgebraicGeometry.Space.squareZeroModuleEquivalence` for `V` and `W`: the left
adjoints of the two sides of `AlgebraicGeometry.Space.squareZeroPushforwardNaturalityIso`
(`CategoryTheory.Adjunction.leftAdjointUniq` of
`AlgebraicGeometry.Space.squareZeroPullbackNaturalityAdjunction` and
`AlgebraicGeometry.Space.squareZeroExtensionOfScalarsAdjunction`). -/
def squareZeroPullbackNaturalityIso
    (hg : (squareZeroStructureSheafIso (hq := hqV) hiV hV hipV hpbV hβτV).hom ≫
        (thickeningRetractionEquivalence B S hS hiV hV hqV CommRingCat.{u}).functor.map g =
      thickeningPushforwardRingMap (hqV := hqV) hiV hV hiW hW hH hiH
        (squareZeroStructureSheafIso (hq := hqW) hiW hW hipW hpbW hβτW).hom) :
    (squareZeroModuleEquivalence (hq := hqV) hiV hV hipV hpbV hβτV).functor ⋙
        (modulePullbackDataTopos B S hS).pull H ≅
      extensionOfScalars g ⋙
        (squareZeroModuleEquivalence (hq := hqW) hiW hW hipW hpbW hβτW).functor :=
  (squareZeroPullbackNaturalityAdjunction hiV hV hipV hpbV hβτV hiW hW hipW hpbW hβτW hH hiH
    hg).leftAdjointUniq (squareZeroExtensionOfScalarsAdjunction hiW hW hipW hpbW hβτW g)

/-- **`G2` on cochain complexes**: degreewise pullback along `H` after the equivalence for `V`
is degreewise extension of scalars along `g` followed by the equivalence for `W`. -/
def squareZeroComplexPullbackNaturalityIso
    (hg : (squareZeroStructureSheafIso (hq := hqV) hiV hV hipV hpbV hβτV).hom ≫
        (thickeningRetractionEquivalence B S hS hiV hV hqV CommRingCat.{u}).functor.map g =
      thickeningPushforwardRingMap (hqV := hqV) hiV hV hiW hW hH hiH
        (squareZeroStructureSheafIso (hq := hqW) hiW hW hipW hpbW hβτW).hom) :
    (squareZeroModuleEquivalence (hq := hqV) hiV hV hipV hpbV hβτV).functor.mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙
        ((modulePullbackDataTopos B S hS).pull H).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      extensionOfScalarsCochainComplex (SmallEtale.topology B S hS X.1) g ⋙
        (squareZeroModuleEquivalence (hq := hqW) hiW hW hipW hpbW
            hβτW).functor.mapHomologicalComplex (ComplexShape.up ℤ) :=
  @Functor.mapHomologicalComplexCompIso ℤ _ _ _ _ _ _ _ _ _ _ _ _
      (squareZeroPullbackNaturalityIso hiV hV hipV hpbV hβτV hiW hW hipW hpbW hβτW hH hiH hg)
      (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _
        (squareZeroModuleEquivalence_functor_additive (hq := hqV) hiV hV hipV hpbV hβτV))
      (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _
        (modulePullbackDataTopos_additive B S hS H))
      (@Functor.preservesZeroMorphisms_comp _ _ _ _ _ _ _ _ _ _ _
        (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _
          (additive_extensionOfScalars g))
        (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _
          (squareZeroModuleEquivalence_functor_additive (hq := hqW) hiW hW hipW hpbW hβτW)))
      (ComplexShape.up ℤ) ≪≫
    (@Functor.mapHomologicalComplexCompIso ℤ _ _ _ _ _ _ _ _ _ _ _ _
      (Iso.refl (extensionOfScalars g ⋙
        (squareZeroModuleEquivalence (hq := hqW) hiW hW hipW hpbW hβτW).functor))
      (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _
        (additive_extensionOfScalars g))
      (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _
        (squareZeroModuleEquivalence_functor_additive (hq := hqW) hiW hW hipW hpbW hβτW))
      (@Functor.preservesZeroMorphisms_comp _ _ _ _ _ _ _ _ _ _ _
        (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _
          (additive_extensionOfScalars g))
        (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _
          (squareZeroModuleEquivalence_functor_additive (hq := hqW) hiW hW hipW hpbW hβτW)))
      (ComplexShape.up ℤ)).symm

section Derived

attribute [local instance 10000] HasDerivedCategory.standard

variable [hDV : HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (sqZeroExtSheafAnySite (structureSheaf B S hS X.1 X.2)
      ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
        (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
        (squareZeroCoefficientMap k B S hS toS hk p)).obj V.obj))))]
  [hDW : HasDerivedCategory.{d'} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (sqZeroExtSheafAnySite (structureSheaf B S hS X.1 X.2)
      ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
        (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
        (squareZeroCoefficientMap k B S hS toS hk p)).obj W.obj))))]

/-- The derived equivalence of `AlgebraicGeometry.Space.squareZeroDerivedEquivalence` is the
functor induced by the module equivalence on derived categories. -/
theorem squareZeroDerivedEquivalence_functor :
    (squareZeroDerivedEquivalence (hq := hqV) hiV hV hipV hpbV hβτV).functor =
      @Functor.mapDerivedCategory _ _ _ hDV _ _ _ _
        (squareZeroModuleEquivalence (hq := hqV) hiV hV hipV hpbV hβτV).functor
        (squareZeroModuleEquivalence_functor_additive (hq := hqV) hiV hV hipV hpbV hβτV) _ _ :=
  rfl

/-- The factorization `Q ⋙ eD ≅ E ⋙ Q` of the derived equivalence of
`AlgebraicGeometry.Space.squareZeroDerivedEquivalence` through the localizations:
`CategoryTheory.Functor.mapDerivedCategoryFactors` of the module equivalence. -/
def squareZeroDerivedEquivalenceFactors :
    DerivedCategory.Q ⋙ (squareZeroDerivedEquivalence (hq := hqV) hiV hV hipV hpbV hβτV).functor ≅
      (squareZeroModuleEquivalence (hq := hqV) hiV hV hipV hpbV hβτV).functor.mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  @Functor.mapDerivedCategoryFactors _ _ _ hDV _ _ _ _
    (squareZeroModuleEquivalence (hq := hqV) hiV hV hipV hpbV hβτV).functor
    (squareZeroModuleEquivalence_functor_additive (hq := hqV) hiV hV hipV hpbV hβτV) _ _

/-- **The comparison of the derived pullback along `H`, after the derived equivalence for `V`, with
degreewise extension of scalars along `g` followed by the equivalence for `W`**: the factorization
of the derived equivalence, the comparison of the derived pullback with degreewise pullback
(`AlgebraicGeometry.Space.derivedPullComparison`), and
`AlgebraicGeometry.Space.squareZeroComplexPullbackNaturalityIso`. -/
def squareZeroDerivedPullbackNaturalityComparison
    (hg : (squareZeroStructureSheafIso (hq := hqV) hiV hV hipV hpbV hβτV).hom ≫
        (thickeningRetractionEquivalence B S hS hiV hV hqV CommRingCat.{u}).functor.map g =
      thickeningPushforwardRingMap (hqV := hqV) hiV hV hiW hW hH hiH
        (squareZeroStructureSheafIso (hq := hqW) hiW hW hipW hpbW hβτW).hom) :
    DerivedCategory.Q ⋙ ((squareZeroDerivedEquivalence (hq := hqV) hiV hV hipV hpbV hβτV).functor ⋙
        derivedPull B S hS (hasDerivedModulePullbacks B S hS) H) ⟶
      (extensionOfScalarsCochainComplex (SmallEtale.topology B S hS X.1) g ⋙
        (squareZeroModuleEquivalence (hq := hqW) hiW hW hipW hpbW
            hβτW).functor.mapHomologicalComplex (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q :=
  @precompDerivedEquivalenceComparison _ _ _ hDV _ _ _ _
    (squareZeroModuleEquivalence (hq := hqV) hiV hV hipV hpbV hβτV)
    (squareZeroModuleEquivalence_functor_additive (hq := hqV) hiV hV hipV hpbV hβτV) _ _
    (derivedPull B S hS (hasDerivedModulePullbacks B S hS) H) _ (derivedPullComparison B S hS H) _
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (squareZeroComplexPullbackNaturalityIso hiV hV hipV hpbV hβτV
        hiW hW hipW hpbW hβτW hH hiH hg) DerivedCategory.Q).symm

omit hDW in
/-- **The derived pullback along `H`, read through the derived equivalence for `V`, is a left
derived functor** of degreewise extension of scalars along `g` followed by the equivalence for `W`,
with the comparison `AlgebraicGeometry.Space.squareZeroDerivedPullbackNaturalityComparison`: the
derived pullback is the left derived functor of degreewise pullback
(`AlgebraicGeometry.Space.isLeftDerivedFunctor_derivedPullComparison`), and precomposing with the
derived equivalence preserves left derived functors. -/
theorem isLeftDerivedFunctor_squareZeroDerivedPullbackNaturalityComparison
    (hg : (squareZeroStructureSheafIso (hq := hqV) hiV hV hipV hpbV hβτV).hom ≫
        (thickeningRetractionEquivalence B S hS hiV hV hqV CommRingCat.{u}).functor.map g =
      thickeningPushforwardRingMap (hqV := hqV) hiV hV hiW hW hH hiH
        (squareZeroStructureSheafIso (hq := hqW) hiW hW hipW hpbW hβτW).hom) :
    ((squareZeroDerivedEquivalence (hq := hqV) hiV hV hipV hpbV hβτV).functor ⋙
        derivedPull B S hS (hasDerivedModulePullbacks B S hS) H).IsLeftDerivedFunctor
      (squareZeroDerivedPullbackNaturalityComparison hiV hV hipV hpbV hβτV hiW hW hipW hpbW hβτW
        hH hiH hg)
      (HomologicalComplex.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (sqZeroExtSheafAnySite (structureSheaf B S hS X.1 X.2)
          ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
            (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
            (squareZeroCoefficientMap k B S hS toS hk p)).obj V.obj)))) (ComplexShape.up ℤ)) :=
  by
  unfold squareZeroDerivedPullbackNaturalityComparison
  exact @isLeftDerivedFunctor_precompDerivedEquivalenceComparison _ _ _ hDV _ _ _ _
    (squareZeroModuleEquivalence (hq := hqV) hiV hV hipV hpbV hβτV)
    (squareZeroModuleEquivalence_functor_additive (hq := hqV) hiV hV hipV hpbV hβτV) _ _
    (derivedPull B S hS (hasDerivedModulePullbacks B S hS) H) _ (derivedPullComparison B S hS H) _ _
    (isLeftDerivedFunctor_derivedPullComparison B S hS H)

variable (g) in
/-- Degreewise extension of scalars along `g`, localized and followed by the derived equivalence
for `W`, is degreewise extension of scalars followed by the equivalence for `W`, localized. -/
def squareZeroExtensionOfScalarsFactorsIso :
    (extensionOfScalarsCochainComplex (SmallEtale.topology B S hS X.1) g ⋙ DerivedCategory.Q) ⋙
        (squareZeroDerivedEquivalence (hq := hqW) hiW hW hipW hpbW hβτW).functor ≅
      (extensionOfScalarsCochainComplex (SmallEtale.topology B S hS X.1) g ⋙
        (squareZeroModuleEquivalence (hq := hqW) hiW hW hipW hpbW
            hβτW).functor.mapHomologicalComplex
          (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (extensionOfScalarsCochainComplex (SmallEtale.topology B S hS X.1) g)
      (squareZeroDerivedEquivalenceFactors (hqV := hqW) (hDV := hDW) hiW hW hipW hpbW hβτW) ≪≫
    (Functor.associator _ _ _).symm

variable (g) in
/-- The comparison of the derived base change along `g` followed by the derived equivalence for
`W`: `Deformation.ComplexLift.derivedExtensionOfScalarsCounit` followed by the equivalence. -/
def squareZeroDerivedExtensionOfScalarsComparison :
    DerivedCategory.Q ⋙ (derivedExtensionOfScalars.{d, d'} g ⋙
        (squareZeroDerivedEquivalence (hq := hqW) hiW hW hipW hpbW hβτW).functor) ⟶
      (extensionOfScalarsCochainComplex (SmallEtale.topology B S hS X.1) g ⋙ DerivedCategory.Q) ⋙
        (squareZeroDerivedEquivalence (hq := hqW) hiW hW hipW hpbW hβτW).functor :=
  (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (derivedExtensionOfScalarsCounit.{d, d'} g)
      (squareZeroDerivedEquivalence (hq := hqW) hiW hW hipW hpbW hβτW).functor

variable (g) in
/-- The derived base change along `g` followed by the derived equivalence for `W` is a left derived
functor, the derived equivalence being a right adjoint. -/
theorem isLeftDerivedFunctor_derivedExtensionOfScalars_comp_squareZeroDerivedEquivalence :
    (derivedExtensionOfScalars.{d, d'} g ⋙
        (squareZeroDerivedEquivalence (hq := hqW) hiW hW hipW hpbW
          hβτW).functor).IsLeftDerivedFunctor
      (squareZeroDerivedExtensionOfScalarsComparison (hqW := hqW) hiW hW hipW hpbW hβτW g)
      (HomologicalComplex.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (sqZeroExtSheafAnySite (structureSheaf B S hS X.1 X.2)
          ((tensorByBaseModuleOfHom k (SmallEtale.topology B S hS X.1)
            (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
            (squareZeroCoefficientMap k B S hS toS hk p)).obj V.obj)))) (ComplexShape.up ℤ)) := by
  have := (squareZeroDerivedEquivalence (hq := hqW) hiW hW hipW hpbW hβτW).isRightAdjoint_functor
  unfold squareZeroDerivedExtensionOfScalarsComparison
  infer_instance

/-- **Stacks 0DLL, `G3` (`χ`): the derived base change along `g`, followed by the derived
equivalence for `W`, is the derived equivalence for `V` followed by the derived pullback along
`H`**: both are left derived functors of degreewise extension of scalars along `g` followed by
the equivalence for `W`, the first because the derived equivalence is a right adjoint, the second
by `AlgebraicGeometry.Space.isLeftDerivedFunctor_squareZeroDerivedPullbackNaturalityComparison`.
It is `AlgebraicGeometry.Space.derivedEquivalenceLeftDerivedIso` at these data, so
`AlgebraicGeometry.Space.derivedEquivalenceLeftDerivedIso_fac` is its compatibility with the
comparisons with complexes. -/
def squareZeroDerivedPullbackNaturality
    (hg : (squareZeroStructureSheafIso (hq := hqV) hiV hV hipV hpbV hβτV).hom ≫
        (thickeningRetractionEquivalence B S hS hiV hV hqV CommRingCat.{u}).functor.map g =
      thickeningPushforwardRingMap (hqV := hqV) hiV hV hiW hW hH hiH
        (squareZeroStructureSheafIso (hq := hqW) hiW hW hipW hpbW hβτW).hom) :
    derivedExtensionOfScalars.{d, d'} g ⋙
        (squareZeroDerivedEquivalence (hq := hqW) hiW hW hipW hpbW hβτW).functor ≅
      (squareZeroDerivedEquivalence (hq := hqV) hiV hV hipV hpbV hβτV).functor ⋙
        derivedPull B S hS (hasDerivedModulePullbacks B S hS) H :=
  @derivedEquivalenceLeftDerivedIso _ _ _ hDV _ _ _ hDW _ _ _ _ _ _ _ _
    (squareZeroModuleEquivalence (hq := hqV) hiV hV hipV hpbV hβτV)
    (squareZeroModuleEquivalence_functor_additive (hq := hqV) hiV hV hipV hpbV hβτV)
    (squareZeroModuleEquivalence (hq := hqW) hiW hW hipW hpbW hβτW)
    (squareZeroModuleEquivalence_functor_additive (hq := hqW) hiW hW hipW hpbW hβτW)
    (derivedPull B S hS (hasDerivedModulePullbacks B S hS) H)
    (((modulePullbackDataTopos B S hS).pull H).mapHomologicalComplex (ComplexShape.up ℤ))
    (derivedPullComparison B S hS H) (isLeftDerivedFunctor_derivedPullComparison B S hS H)
    (derivedExtensionOfScalars.{d, d'} g)
    (extensionOfScalarsCochainComplex (SmallEtale.topology B S hS X.1) g)
    (derivedExtensionOfScalarsCounit.{d, d'} g)
    (isLeftDerivedFunctor_derivedExtensionOfScalarsCounit.{d, d'} g)
    (squareZeroComplexPullbackNaturalityIso hiV hV hipV hpbV hβτV hiW hW hipW hpbW hβτW hH hiH hg)

/-- `AlgebraicGeometry.Space.squareZeroDerivedEquivalenceFactors` is
`CategoryTheory.Functor.mapDerivedCategoryFactors` of the module equivalence. -/
theorem squareZeroDerivedEquivalenceFactors_eq :
    squareZeroDerivedEquivalenceFactors (hqV := hqV) hiV hV hipV hpbV hβτV =
      @Functor.mapDerivedCategoryFactors _ _ _ hDV _ _ _ _
        (squareZeroModuleEquivalence (hq := hqV) hiV hV hipV hpbV hβτV).functor
        (squareZeroModuleEquivalence_functor_additive (hq := hqV) hiV hV hipV hpbV hβτV) _ _ :=
  rfl

end Derived

end Naturality

end AlgebraicGeometry.Space

end
