module

public import StacksFrontier.AlgebraicGeometry.Duality.FiniteTwistedTraceComp
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingModuleDataOfFiniteMap
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.CompIsoIndependence
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekRelativeDualizingModule

/-!
# The chart data of `H⁰(f^!𝒪_Y)` along a map of finite factorizations

Let `f = i₁ ≫ π₁` be a factorization of a locally quasi-finite morphism of `FTS S` into an open
immersion and a finite morphism, and `h : T ⟶ T₁` finite with `i ≫ h = i₁` cartesian. Then
`f = i ≫ (h ≫ π₁)` is a second such factorization, and the trace of `h ≫ π₁` is the trace of
`π₁` after the trace `τ : h_*H⁰(a_{h ≫ π₁}𝒪_Y) ⟶ H⁰(a_{π₁}𝒪_Y)` of `h`
(`Stacks.Duality.FiniteTrace.trace_comp`). The chart identifications of `H⁰(f^!𝒪_Y)` with the
algebraic relative dualizing modules attached to the two factorizations agree as soon as the
identifications `H⁰(f^!𝒪_Y) ≅ H⁰(a 𝒪_Y)|_X` are compatible with `τ` on `X`.

This is a step of the independence of the factorization in [Stacks, Tag 0BUL].
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

section RestrictPushforward

variable {X T T₁ : Scheme.{u}} {i : X ⟶ T} {i₁ : X ⟶ T₁} [IsOpenImmersion i] [IsOpenImmersion i₁]
  {h : T ⟶ T₁} (sq : IsPullback i (𝟙 X) h i₁)

/-- The inverse of `Γ(T, i(W)) ≅ Γ(X, W)` through the open immersion `i ≫ h`. -/
theorem appIso_inv_comp_app_comp_map {X T T₁ : Scheme.{u}} (i : X ⟶ T) (h : T ⟶ T₁)
    [IsOpenImmersion i] [IsOpenImmersion (i ≫ h)] (W : X.Opens)
    (e : i ''ᵁ W = h ⁻¹ᵁ ((i ≫ h) ''ᵁ W)) :
    ((i ≫ h).appIso W).inv ≫ h.app ((i ≫ h) ''ᵁ W) ≫ T.presheaf.map (eqToHom e).op =
      (i.appIso W).inv := by
  rw [← cancel_mono (i.appIso W).hom, Iso.inv_hom_id, Scheme.Hom.appIso_hom]
  simp only [Category.assoc]
  rw [Scheme.Hom.naturality_assoc]
  calc _ = (((i ≫ h).appIso W).inv ≫ (i ≫ h).app ((i ≫ h) ''ᵁ W)) ≫
        X.presheaf.map ((TopologicalSpace.Opens.map i.base).map (eqToHom e).op.unop).op ≫
          X.presheaf.map (eqToHom (i.preimage_image_eq W).symm).op := by
        rw [Scheme.Hom.comp_app i h ((i ≫ h) ''ᵁ W)]
        exact ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Category.assoc _ _ _))).symm
    _ = 𝟙 _ := by
        rw [Scheme.Hom.appIso_inv_app (i ≫ h) W]
        exact ((congrArg (_ ≫ ·) (X.presheaf.map_comp _ _).symm).trans
          (X.presheaf.map_comp _ _).symm).trans
            ((congrArg X.presheaf.map (Subsingleton.elim _ _)).trans (X.presheaf.map_id _))

/-- **Restriction of a direct image along a cartesian square**: for `i ≫ h = i₁` cartesian over
`𝟙 X`, with `i`, `i₁` open immersions, `(h_*M)|_X ≅ M|_X`. -/
def restrictPushforwardIsoOfIsPullback :
    Scheme.Modules.pushforward h ⋙ Scheme.Modules.restrictFunctor i₁ ≅
      Scheme.Modules.restrictFunctor i :=
  SheafOfModules.pushforwardComp _ _ ≪≫
    SheafOfModules.pushforwardNatIso _ (NatIso.ofComponents
      (fun W ↦ eqToIso (IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback sq.flip W))
      fun _ ↦ Subsingleton.elim _ _) ≪≫
    SheafOfModules.pushforwardCongr (by
      ext W x
      obtain rfl : i ≫ h = i₁ := sq.w.trans (Category.id_comp _)
      exact congrArg (fun φ => ((forget₂ CommRingCat RingCat).map φ).hom x)
        (appIso_inv_comp_app_comp_map i h W.unop
          (IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback sq.flip W.unop)))

end RestrictPushforward

variable {S : Scheme.{u}} [IsNoetherian S] {X Y : FTS S} {f : X ⟶ Y} [LocallyQuasiFinite f.left]

/-- The factorization `f = i ≫ (h ≫ π₁)` through a scheme `T` finite over `T₁`. -/
abbrev OpenFiniteFactorization.ofMap (F₁ : OpenFiniteFactorization f) {T : Scheme.{u}}
    (i : X.left ⟶ T) [IsOpenImmersion i] (h : T ⟶ F₁.space) [IsFinite h]
    (hih : i ≫ h = F₁.immersion) : OpenFiniteFactorization f where
  space := T
  immersion := i
  toBase := h ≫ F₁.toBase
  fac := by rw [← Category.assoc, hih, F₁.fac]

omit [LocallyQuasiFinite f.left] in
/-- `a_h(a_{π₁}(𝒪_Y))` has no cohomology in negative degrees, being `a_{h ≫ π₁}(𝒪_Y)`. -/
theorem isGE_twisted_twisted (F₁ : OpenFiniteFactorization f) {T : Scheme.{u}} {i : X.left ⟶ T}
    [IsOpenImmersion i] (h : T ⟶ F₁.space) [IsFinite h] (hih : i ≫ h = F₁.immersion)
    [CompactSpace T] [QuasiSeparatedSpace T] :
    ((FiniteTrace.twisted h).obj ((FiniteTrace.twisted F₁.toBase).obj
      (derivedStructureSheaf Y.left))).obj.IsGE 0 :=
  have : ((FiniteTrace.twisted (h ≫ F₁.toBase)).obj (derivedStructureSheaf Y.left)).obj.IsGE 0 :=
    isGE_twisted_finiteToBase (F₁.ofMap i h hih)
  FiniteTrace.isGE_of_iso' ((ObjectProperty.ι _).mapIso
    ((FiniteTrace.twistedCompIso h F₁.toBase).app (derivedStructureSheaf Y.left))) 0 this

/-- The trace of `h : T ⟶ T₁` on `H⁰(a_{h ≫ π₁}(𝒪_Y)) ⟶ H⁰(a_{π₁}(𝒪_Y))`. -/
def OpenFiniteFactorization.mapTrace (F₁ : OpenFiniteFactorization f) {T : Scheme.{u}}
    {i : X.left ⟶ T} [IsOpenImmersion i] (h : T ⟶ F₁.space) [IsFinite h]
    (hih : i ≫ h = F₁.immersion) [CompactSpace T] [QuasiSeparatedSpace T] :
    (Scheme.Modules.pushforward h).obj (finiteZeroTwisted (F₁.ofMap i h hih)) ⟶
      finiteZeroTwisted F₁ :=
  haveI : ((FiniteTrace.twisted (h ≫ F₁.toBase)).obj (derivedStructureSheaf Y.left)).obj.IsGE 0 :=
    isGE_twisted_finiteToBase (F₁.ofMap i h hih)
  haveI := isGE_twisted_twisted F₁ h hih
  FiniteTrace.compTrace h F₁.toBase (derivedStructureSheaf Y.left)

omit [LocallyQuasiFinite f.left] in
/-- On sections, the trace of `h ≫ π₁` is the trace of `π₁` after the trace of `h`. -/
theorem OpenFiniteFactorization.traceApp_finiteTrace_ofMap (F₁ : OpenFiniteFactorization f)
    {T : Scheme.{u}} {i : X.left ⟶ T} [IsOpenImmersion i] (h : T ⟶ F₁.space) [IsFinite h]
    (hih : i ≫ h = F₁.immersion) [CompactSpace T] [QuasiSeparatedSpace T] (U : Y.left.Opens)
    (s : Γ(finiteZeroTwisted (F₁.ofMap i h hih), h ⁻¹ᵁ (F₁.toBase ⁻¹ᵁ U))) :
    traceApp (h ≫ F₁.toBase) (finiteTrace (F₁.ofMap i h hih)) U s =
      traceApp F₁.toBase (finiteTrace F₁) U ((F₁.mapTrace h hih).app (F₁.toBase ⁻¹ᵁ U) s) := by
  have : ((FiniteTrace.twisted (h ≫ F₁.toBase)).obj (derivedStructureSheaf Y.left)).obj.IsGE 0 :=
    isGE_twisted_finiteToBase (F₁.ofMap i h hih)
  have := isGE_twisted_twisted F₁ h hih
  have := congrArg (fun φ => Scheme.Modules.Hom.app (φ ≫
    ((singleFunctorCompHomologyFunctorIso Y.left.Modules 0).app
      (SheafOfModules.unit Y.left.ringCatSheaf)).hom) U s)
    (FiniteTrace.trace_comp h F₁.toBase (derivedStructureSheaf Y.left))
  exact this

/-- `𝒪_Y` as an object of `D⁺_QCoh(𝒪_Y)`. -/
abbrev structurePlus (Y : FTS S) : quasiCoherentDerivedCategoryPlusOfModel Y.left :=
  ⟨derivedStructureSheaf Y.left, KoszulRegular.isBoundedBelow_singleFunctor_obj _⟩

/-- `H⁰(f^!_j 𝒪_Y) ≅ H⁰(f^!_c 𝒪_Y)`, from the isomorphism of [Stacks, Tag 0AA0]. -/
def upperShriekStructureSheafZerothCompactificationIso (j c : CompactificationOf (Over.mk f.left)) :
    upperShriekStructureSheafZeroth f j ≅ upperShriekStructureSheafZeroth f c :=
  (homologyFunctor X.left.Modules 0).mapIso ((ObjectProperty.ι _).mapIso
    ((ObjectProperty.ι _).mapIso
      ((DominatingCompactification.upperShriekPlusIso f j c).app (structurePlus Y))))

omit [LocallyQuasiFinite f.left] in
/-- The identification `H⁰(f^!𝒪_Y) ≅ H⁰(a 𝒪_Y)|_X` at `j` is the one at `c` after the
isomorphism of [Stacks, Tag 0AA0] from `j` to `c`. -/
theorem upperShriekStructureSheafZerothIso_eq_trans (F : OpenFiniteFactorization f)
    (j c : CompactificationOf (Over.mk f.left)) :
    upperShriekStructureSheafZerothIso F j =
      upperShriekStructureSheafZerothCompactificationIso j c ≪≫
        upperShriekStructureSheafZerothIso F c := by
  ext1
  show (homologyFunctor X.left.Modules 0).map ((ObjectProperty.ι _).map
      ((ObjectProperty.ι _).map ((DominatingCompactification.upperShriekPlusIso f j
        F.compactification).hom.app (structurePlus Y)) ≫
        ((restrictedDerivedRestrictAdjointIso F.immersion).app _).inv)) ≫ _ =
    (homologyFunctor X.left.Modules 0).map ((ObjectProperty.ι _).map ((ObjectProperty.ι _).map
      ((DominatingCompactification.upperShriekPlusIso f j c).hom.app (structurePlus Y)))) ≫
    (homologyFunctor X.left.Modules 0).map ((ObjectProperty.ι _).map
      ((ObjectProperty.ι _).map ((DominatingCompactification.upperShriekPlusIso f c
        F.compactification).hom.app (structurePlus Y)) ≫
        ((restrictedDerivedRestrictAdjointIso F.immersion).app _).inv)) ≫ _
  rw [← upperShriekPlusIso_trans f j c F.compactification, Iso.trans_hom, NatTrans.comp_app]
  simp only [Functor.map_comp]
  exact (congrArg (· ≫ _) ((congrArg (homologyFunctor X.left.Modules 0).map
    ((congrArg _ (Category.assoc _ _ _)).trans (Functor.map_comp _ _ _))).trans
      (Functor.map_comp _ _ _))).trans (Category.assoc _ _ _)

omit [LocallyQuasiFinite f.left] in
/-- The restriction of sections through the identification at `j` is the one at `c`, followed by
the isomorphism of [Stacks, Tag 0AA0] from `c` back to `j`. -/
theorem chartRestrict_upperShriekStructureSheafZerothIso (F : OpenFiniteFactorization f)
    (j c : CompactificationOf (Over.mk f.left)) {W : F.space.Opens} {V : X.left.Opens}
    (hV : V ≤ F.immersion ⁻¹ᵁ W) (m : Γ(finiteZeroTwisted F, W)) :
    chartRestrict (finiteZeroTwisted F) (upperShriekStructureSheafZerothIso F j) hV m =
      (upperShriekStructureSheafZerothCompactificationIso j c).inv.app V
        (chartRestrict (finiteZeroTwisted F) (upperShriekStructureSheafZerothIso F c) hV m) := by
  rw [chartRestrict_apply, chartRestrict_apply, upperShriekStructureSheafZerothIso_eq_trans F j c]
  rfl

/-- **The chart identifications for `i₁ ≫ π₁` and `i ≫ (h ≫ π₁)` agree** when the two
identifications `H⁰(f^!𝒪_Y) ≅ H⁰(a 𝒪_Y)|_X` are compatible on `X` with the trace of `h`. -/
theorem OpenFiniteFactorization.localEquiv_relativeDualizingModuleData_ofMap_of_chartRestrict
    (F₁ : OpenFiniteFactorization f) {T : Scheme.{u}} [CompactSpace T] [QuasiSeparatedSpace T]
    (i : X.left ⟶ T) [IsOpenImmersion i] (h : T ⟶ F₁.space) [IsFinite h]
    (sq : IsPullback i (𝟙 X.left) h F₁.immersion) (j : CompactificationOf (Over.mk f.left))
    (hres : ∀ (W : F₁.space.Opens) (V : X.left.Opens) (hV : V ≤ F₁.immersion ⁻¹ᵁ W)
      (s : Γ(finiteZeroTwisted (F₁.ofMap i h (sq.w.trans (Category.id_comp _))), h ⁻¹ᵁ W)),
      chartRestrict (finiteZeroTwisted F₁) (upperShriekStructureSheafZerothIso F₁ j) hV
          ((F₁.mapTrace h (sq.w.trans (Category.id_comp _))).app W s) =
        chartRestrict (finiteZeroTwisted (F₁.ofMap i h (sq.w.trans (Category.id_comp _))))
          (upperShriekStructureSheafZerothIso (F₁.ofMap i h (sq.w.trans (Category.id_comp _))) j)
          (le_preimage_of_map h (sq.w.trans (Category.id_comp _)) hV) s)
    (U : Y.left.affineOpens) (V : X.left.affineOpens) (hVU : V.1 ≤ f.left ⁻¹ᵁ U.1) :
    letI : Algebra Γ(Y.left, U.1) Γ(X.left, V.1) := (f.left.appLE U V hVU).hom.toAlgebra
    ∀ G : FiniteOpenFactorization.{u, u, u} Γ(Y.left, U.1) Γ(X.left, V.1),
      ((F₁.ofMap i h (sq.w.trans (Category.id_comp _))).relativeDualizingModuleData j).localEquiv
          U V hVU G = (F₁.relativeDualizingModuleData j).localEquiv U V hVU G := by
  intro G
  generalize sq.w.trans (Category.id_comp _) = hih at hres ⊢
  have : (finiteZeroTwisted (F₁.ofMap i h hih)).IsQuasicoherent :=
    ((FiniteTrace.twisted (h ≫ F₁.toBase)).obj (derivedStructureSheaf Y.left)).2 0
  exact ofFiniteTraceLocalEquiv_eq_of_isPullback h F₁.fac (finiteZeroTwisted F₁)
    (finiteZeroTwisted (F₁.ofMap i h hih)) (finiteTrace F₁) (finiteTrace (F₁.ofMap i h hih))
    (bijective_traceDual_finiteTrace F₁) (bijective_traceDual_finiteTrace (F₁.ofMap i h hih))
    (upperShriekStructureSheafZerothIso F₁ j)
    (upperShriekStructureSheafZerothIso (F₁.ofMap i h hih) j) (F₁.mapTrace h hih) sq
    (F₁.traceApp_finiteTrace_ofMap h hih) hres U V hVU G

end Stacks.Duality
