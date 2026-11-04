module

public import StacksFrontier.AlgebraicGeometry.SectionRingProjQuasicoherent.Glue
public import StacksFrontier.AlgebraicGeometry.SectionRingProjQuasicoherent.Bijective
public import StacksFrontier.AlgebraicGeometry.ProjQuasiCoherentRecovery.Basic
public import StacksFrontier.AlgebraicGeometry.ExternalTensorPullback.ComparisonSections
public import StacksFrontier.AlgebraicGeometry.ProjStalkGlobalSections.GlobalSections

/-!
# Stacks Tag 01QJ: `f^* M̃ ≅ ℱ` for the section ring of an ample invertible sheaf

In Situation 01QH — `X` a scheme, `L` an ample invertible `𝒪_X`-module, `S = Γ_*(X, L)`,
`Y = Proj S` and `f : X ⟶ Y` the canonical morphism of Stacks Tag 01PZ — let `ℱ` be a
quasi-coherent `𝒪_X`-module and `M = Γ_*(X, L, ℱ)`. Stacks Tag 01QJ asserts that there are
isomorphisms `f^* M̃ ⟶ ℱ`, functorial in `ℱ`, such that `M_0 ⟶ Γ(Y, M̃) ⟶ Γ(X, ℱ)` is the
identity.

## The proof

`f` is an open immersion (Stacks Tag 01Q1), so `f^*` is restriction along `f`
(`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`). The morphism
`M̃|_X ⟶ ℱ` is `Stacks.SectionRingProjQuasicoherent.gluedComparison`: on the chart
`X_a = f⁻¹ D₊(a)` it is the division `M_{(a)} ⟶ Γ(X_a, ℱ)` of Stacks Tag 01PW, and these agree on
overlaps. For `ℱ` quasi-coherent that division is bijective (Tag 01PW,
`Stacks.SectionRingProjQuasicoherent.localDivision_injective` and
`Stacks.SectionRingProjQuasicoherent.localDivision_surjective`), so the comparison is bijective on
a basis of `X` and hence an isomorphism. In degree zero the division by `a⁰` is the identity, and
the global section of `M̃` attached to `m ∈ M_0` is `m / 1` on every chart (Tag 01M7), which gives
the normalization.

## Main definitions

* `Stacks.SectionRingProjQuasicoherent.gluedComparisonNatTrans`: `M̃|_X ⟶ ℱ`, natural in `ℱ`.
* `Stacks.SectionRingProjQuasicoherent.pullbackTildeComparison`: `f^* M̃ ⟶ ℱ`, natural in `ℱ`.

## Main results

* `Stacks.SectionRingProjQuasicoherent.isIso_pullbackTildeComparison_app`: it is an isomorphism
  for `ℱ` quasi-coherent.
* `Stacks.SectionRingProjQuasicoherent.pullbackTildeComparison_degreeZero`: the normalization on
  `M_0`.
* `Stacks.SectionRingProjQuasicoherent.pullbackTildeComparison_spec`: **Stacks Tag 01QJ**.

## References

* [Stacks Project, Tag 01QJ](https://stacks.math.columbia.edu/tag/01QJ)
* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
* [Stacks Project, Tag 01M7](https://stacks.math.columbia.edu/tag/01M7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite TopologicalSpace
open Stacks.TensorPowers (natTensorPow)
open Stacks.GradedSections (powSections mul mulMap sectionRing)
open Stacks.TwistedSections (twistPow twistSections twistModule)
open Stacks.SectionProduct (globalSection)
open Stacks.AmpleFiniteAvoidance (nvOpen grading)
open Stacks.SectionRingProjMorphism (projHomOfIsAmple)
open scoped Stacks.GradedLocalization

universe u

namespace Stacks.SectionRingProjQuasicoherent

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

attribute [local instance] ProjectiveSpectrum.isPrime

variable {X : Scheme.{u}} (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
  (hL : Stacks.Ample.IsAmple X L)

section Restrict

variable [IsOpenImmersion (projHomOfIsAmple L hL)]

/-! ### Bijectivity on the charts -/

/-- **The local map on a chart is bijective for `ℱ` quasi-coherent** (Stacks Tag 01PW). -/
theorem bijective_localFun (F : X.Modules) [F.IsQuasicoherent] (c : GoodChart L hL) :
    Function.Bijective (localFun L hL F c) :=
  Function.Bijective.comp
    (⟨localDivision_injective L F hL c.1.deg_pos c.1.val,
      localDivision_surjective L F hL c.1.deg_pos c.1.val⟩ :
      Function.Bijective (localDivision L F c.1.val le_rfl))
    (Function.Bijective.comp
      (ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv (grading L)
        (Stacks.TwistedSections.moduleGrading F L)
        (Stacks.ExternalGrading.of_mem_summand c.1.deg c.1.val) c.1.deg_pos).bijective
      (ConcreteCategory.bijective_of_isIso
        (ProjectiveSpectrum.Proj.imageSectionsIso (projHomOfIsAmple L hL)
          (tildeModule L F) (nvOpen L c.1.val) _ (image_nvOpen L hL c)).hom))

/-- **`M̃|_X ⟶ ℱ` is an isomorphism for `ℱ` quasi-coherent**: it is bijective on the basis of
good charts. -/
theorem isIso_gluedComparison (F : X.Modules) [F.IsQuasicoherent] :
    IsIso (gluedComparison L hL F) :=
  Stacks.AlgebraicGeometry.ProjQuasiCoherentRecovery.isIso_of_bijective_app_onBasis _ F
    (fun c : GoodChart L hL => nvOpen L c.1.val) (isBasis_goodChart L hL) _ fun c => by
      rw [gluedComparison_app]
      exact bijective_localFun L hL F c

/-- **The comparison `M̃|_X ⟶ ℱ` as a natural transformation in `ℱ`.** -/
def gluedComparisonNatTrans :
    tildeFunctor L ⋙ Scheme.Modules.restrictFunctor (projHomOfIsAmple L hL) ⟶ 𝟭 X.Modules where
  app F := gluedComparison L hL F
  naturality _ _ φ := gluedComparison_naturality L hL _ φ

/-! ### The normalization in degree zero -/

/-- The element of `M_0` named by a twisted section of degree zero. -/
def degreeZeroElem (F : X.Modules) (t : twistSections F L 0) :
    Stacks.TwistedSections.moduleGrading F L 0 :=
  ⟨DirectSum.of (twistSections F L) 0 t, ⟨t, rfl⟩⟩

/-- **On a chart, the global section `m / 1` of `M̃` attached to `m ∈ M_0` is sent to `m`.** -/
theorem localFun_degreeZero (F : X.Modules) (t : twistSections F L 0) (c : GoodChart L hL)
    (z : Γ((tildeModule L F).restrict (projHomOfIsAmple L hL), nvOpen L c.1.val))
    (hz : (ProjectiveSpectrum.Proj.imageSectionsIso (projHomOfIsAmple L hL) (tildeModule L F)
        (nvOpen L c.1.val) _ (image_nvOpen L hL c)).hom z =
      (tildeModule L F).presheaf.map (homOfLE le_top).op
        (Stacks.AlgebraicGeometry.ProjStalkGlobalSections.degreeZeroToGlobalSections (grading L)
          (Stacks.TwistedSections.moduleGrading F L) (degreeZeroElem L F t))) :
    localFun L hL F c z = unitSec t (nvOpen L c.1.val) := by
  have h1 := Stacks.AlgebraicGeometry.ProjStalkGlobalSections.degreeZeroToGlobalSections_basicOpen
    (grading L) (Stacks.TwistedSections.moduleGrading F L)
    (Stacks.ExternalGrading.of_mem_summand c.1.deg c.1.val) c.1.deg_pos (degreeZeroElem L F t)
  let t0 : twistSections F L (0 * c.1.deg) :=
    Stacks.TwistedSections.twistCongr (Nat.zero_mul c.1.deg).symm t
  have h2 := localDivision_fraction L F c.1.val (le_refl (nvOpen L c.1.val))
    (ProjectiveSpectrum.Proj.degreeZeroFraction (grading L)
      (Stacks.TwistedSections.moduleGrading F L)
      (Stacks.ExternalGrading.of_mem_summand c.1.deg c.1.val) 0
      (degreeZeroElem L F t).1 (by simpa only [zero_smul] using (degreeZeroElem L F t).2))
    0 t0 (congrArg (fun w => LocalizedModule.mk w _) (of_twistCongr _ t).symm)
  refine (congrArg (fun w => localDivision L F c.1.val le_rfl
    (ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv (grading L)
      (Stacks.TwistedSections.moduleGrading F L)
      (Stacks.ExternalGrading.of_mem_summand c.1.deg c.1.val) c.1.deg_pos w)) hz).trans ?_
  refine (congrArg (localDivision L F c.1.val le_rfl) h1).trans (h2.trans ?_)
  refine (LinearEquiv.symm_apply_eq _).mpr ?_
  have he : (eqToHom (congrArg (twistPow F L) (Nat.zero_mul c.1.deg).symm) ≫
      eqToHom (congrArg (twistPow F L) (Nat.mul_comm 0 c.1.deg)) :
        twistPow F L 0 ⟶ twistPow F L (c.1.deg * 0)) = 𝟙 _ := by
    rw [eqToHom_trans]
    rfl
  exact congrArg (fun φ => Scheme.Modules.Hom.app φ (nvOpen L c.1.val)
    (unitSec t (nvOpen L c.1.val))) he

/-- A restriction map of a module on a scheme depends only on its source and target. -/
private theorem presheaf_map_apply_congr {Y : Scheme.{u}} (M : Y.Modules) {A B : Y.Opens}
    (i j : op A ⟶ op B) (x : Γ(M, A)) : M.presheaf.map i x = M.presheaf.map j x :=
  congrArg (fun i => ConcreteCategory.hom (M.presheaf.map i) x) (Subsingleton.elim _ _)

/-- Three restrictions of a module on a scheme compose to one. -/
theorem presheaf_map_map_map {Y : Scheme.{u}} (M : Y.Modules) {A B C D : Y.Opens}
    (a : op A ⟶ op B) (b : op B ⟶ op C) (c : op C ⟶ op D) (e : op A ⟶ op D) (x : Γ(M, A)) :
    M.presheaf.map c (M.presheaf.map b (M.presheaf.map a x)) = M.presheaf.map e x := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
    ← Functor.map_comp]
  exact presheaf_map_apply_congr M _ _ x

/-- Two restrictions of a module on a scheme compose to one. -/
theorem presheaf_map_map {Y : Scheme.{u}} (M : Y.Modules) {A B C : Y.Opens}
    (a : op A ⟶ op B) (b : op B ⟶ op C) (e : op A ⟶ op C) (x : Γ(M, A)) :
    M.presheaf.map b (M.presheaf.map a x) = M.presheaf.map e x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  exact presheaf_map_apply_congr M _ _ x

/-- `ProjectiveSpectrum.Proj.imageSectionsIso` is the restriction along the equality of opens. -/
theorem imageSectionsIso_hom_apply {Y : Scheme.{u}} (g : X ⟶ Y) [IsOpenImmersion g]
    (N : Y.Modules) (V : X.Opens) (W : Y.Opens) (h : g ''ᵁ V = W) (y : Γ(N.restrict g, V)) :
    (ProjectiveSpectrum.Proj.imageSectionsIso g N V W h).hom y =
      N.presheaf.map (eqToHom h.symm).op ((N.restrictAppIso g V).hom y) := rfl

/-- **The comparison `M̃|_X ⟶ ℱ` on a section that is `m / 1` on every chart** is `m`. -/
theorem gluedComparison_app_eq_of_degreeZero (F : X.Modules) (t : twistSections F L 0)
    {V : X.Opens} (y : Γ((tildeModule L F).restrict (projHomOfIsAmple L hL), V))
    (hy : ∀ (c : GoodChart L hL) (hle : nvOpen L c.1.val ≤ V),
      (ProjectiveSpectrum.Proj.imageSectionsIso (projHomOfIsAmple L hL) (tildeModule L F)
        (nvOpen L c.1.val) _ (image_nvOpen L hL c)).hom
          (((tildeModule L F).restrict (projHomOfIsAmple L hL)).presheaf.map (homOfLE hle).op y) =
      (tildeModule L F).presheaf.map (homOfLE le_top).op
        (Stacks.AlgebraicGeometry.ProjStalkGlobalSections.degreeZeroToGlobalSections (grading L)
          (Stacks.TwistedSections.moduleGrading F L) (degreeZeroElem L F t))) :
    (gluedComparison L hL F).app V y =
      F.presheaf.map (homOfLE le_top).op (globalSection X F t) := by
  have hcover : V ≤ iSup (fun p : {c : GoodChart L hL // nvOpen L c.1.val ≤ V} =>
      nvOpen L p.1.1.val) := by
    intro x hx
    rw [Opens.mem_iSup]
    obtain ⟨W, hW, hxW, hWV⟩ := Opens.isBasis_iff_nbhd.mp (isBasis_goodChart L hL)
      (show x ∈ V from hx)
    obtain ⟨c, rfl⟩ := hW
    exact ⟨⟨c, hWV⟩, hxW⟩
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨_, F.isSheaf⟩
    (fun p : {c : GoodChart L hL // nvOpen L c.1.val ≤ V} => nvOpen L p.1.1.val) V
    (fun p => homOfLE p.2) hcover _ _ fun p => ?_
  obtain ⟨c, hle⟩ := p
  have hn := ConcreteCategory.congr_hom
    ((gluedComparison L hL F).mapPresheaf.naturality (homOfLE hle).op) y
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, Scheme.Modules.mapPresheaf_app,
    Scheme.Modules.mapPresheaf_app] at hn
  refine hn.symm.trans ?_
  rw [Scheme.Modules.Hom.app, gluedComparison_app]
  refine (localFun_degreeZero L hL F t c _ (hy c hle)).trans ?_
  rw [unitSec_eq_map_globalSection]
  exact (presheaf_map_map F _ _ _ _).symm

/-- **The normalization of `M̃|_X ⟶ ℱ` in degree zero**: the restriction to `X` of the global
section `m / 1` of `M̃` attached to `m ∈ M_0` (Tag 01M7) is sent to `m`, read as a global section
of `ℱ` through `M_0 = Hom(𝒪_X, ℱ ⊗ L^{⊗ 0}) = Γ(X, ℱ)`. -/
theorem gluedComparison_degreeZero (F : X.Modules) (t : twistSections F L 0) :
    (gluedComparison L hL F).app (projHomOfIsAmple L hL ⁻¹ᵁ ⊤)
        (((Scheme.Modules.restrictAdjunction (projHomOfIsAmple L hL)).unit.app
          (tildeModule L F)).app ⊤
          (Stacks.AlgebraicGeometry.ProjStalkGlobalSections.degreeZeroToGlobalSections (grading L)
            (Stacks.TwistedSections.moduleGrading F L) (degreeZeroElem L F t))) =
      F.presheaf.map (homOfLE le_top).op (globalSection X F t) := by
  refine gluedComparison_app_eq_of_degreeZero L hL F t _ fun c hle => ?_
  exact (imageSectionsIso_hom_apply (projHomOfIsAmple L hL) (tildeModule L F) _ _
    (image_nvOpen L hL c) _).trans
    (presheaf_map_map_map (tildeModule L F)
      (homOfLE ((projHomOfIsAmple L hL).image_preimage_le ⊤)).op
      (homOfLE (Scheme.Hom.image_mono (projHomOfIsAmple L hL) hle)).op
      (eqToHom (image_nvOpen L hL c).symm).op (homOfLE le_top).op _)

end Restrict

/-! ### Stacks Tag 01QJ -/

/-- **The comparison `f^* M̃ ⟶ ℱ` of Stacks Tag 01QJ**, natural in `ℱ`, for `M = Γ_*(X, L, ℱ)`
and `f : X ⟶ Proj Γ_*(X, L)` the canonical morphism. Since `f` is an open immersion (Stacks Tag
01Q1), `f^*` is restriction along `f`
(`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`),
and the comparison is `gluedComparisonNatTrans`. -/
def pullbackTildeComparison : pullbackTildeFunctor L hL ⟶ 𝟭 X.Modules :=
  haveI := Stacks.SectionRingProjImmersion.isOpenImmersion_projHomOfIsAmple L hL
  (Functor.isoWhiskerLeft (tildeFunctor L)
      (Scheme.Modules.restrictFunctorIsoPullback (projHomOfIsAmple L hL))).inv ≫
    gluedComparisonNatTrans L hL

/-- For `f` an open immersion, the component of `pullbackTildeComparison` at `ℱ` is the inverse of
the identification of `f^* M̃` with the restriction of `M̃` along `f`, followed by
`gluedComparison`. -/
theorem pullbackTildeComparison_app [IsOpenImmersion (projHomOfIsAmple L hL)] (F : X.Modules) :
    (pullbackTildeComparison L hL).app F =
      (Scheme.Modules.restrictFunctorIsoPullback (projHomOfIsAmple L hL)).inv.app
        ((tildeFunctor L).obj F) ≫ gluedComparison L hL F := rfl

/-- **`f^* M̃ ⟶ ℱ` is an isomorphism for `ℱ` quasi-coherent.** -/
theorem isIso_pullbackTildeComparison_app (F : X.Modules) [F.IsQuasicoherent] :
    IsIso ((pullbackTildeComparison L hL).app F) := by
  have := Stacks.SectionRingProjImmersion.isOpenImmersion_projHomOfIsAmple L hL
  rw [pullbackTildeComparison_app]
  exact IsIso.comp_isIso'
    (Iso.isIso_inv ((Scheme.Modules.restrictFunctorIsoPullback (projHomOfIsAmple L hL)).app
      ((tildeFunctor L).obj F)))
    (isIso_gluedComparison L hL F)

/-- **The isomorphism `f^* M̃ ≅ ℱ` of Stacks Tag 01QJ** for `ℱ` quasi-coherent. -/
def pullbackTildeIso (F : X.Modules) [F.IsQuasicoherent] :
    (pullbackTildeFunctor L hL).obj F ≅ F :=
  haveI := isIso_pullbackTildeComparison_app L hL F
  asIso ((pullbackTildeComparison L hL).app F)

/-- The forward map of `pullbackTildeIso` is the component of `pullbackTildeComparison`. -/
theorem pullbackTildeIso_hom (F : X.Modules) [F.IsQuasicoherent] :
    (pullbackTildeIso L hL F).hom = (pullbackTildeComparison L hL).app F := rfl

/-- **The normalization of Stacks Tag 01QJ**: `M_0 ⟶ Γ(Proj S, M̃) ⟶ Γ(X, f^* M̃) ⟶ Γ(X, ℱ)` is the
identity. An element `m` of `M_0 = Γ(X, ℱ ⊗ L^{⊗ 0})` is a twisted section `t` of degree zero
(`degreeZeroElem`, and every element of `M_0` is of this form by
`Stacks.TwistedSections.mem_moduleGrading_natCast_iff`); Tag 01M7 attaches to it the global section
`m / 1` of `M̃`, which is pulled back to `X` along the unit of `f^* ⊣ f_*`; the comparison sends
it to the global section of `ℱ` named by `t`, restricted to `f⁻¹(Proj S) = X`. -/
theorem pullbackTildeComparison_degreeZero (F : X.Modules) (t : twistSections F L 0) :
    ((pullbackTildeComparison L hL).app F).app (projHomOfIsAmple L hL ⁻¹ᵁ ⊤)
        (Stacks.Tag01VSPullbackTensor.modulesPullbackUnit (projHomOfIsAmple L hL)
          ((tildeFunctor L).obj F) ⊤
          (Stacks.AlgebraicGeometry.ProjStalkGlobalSections.degreeZeroToGlobalSections (grading L)
            (Stacks.TwistedSections.moduleGrading F L) (degreeZeroElem L F t))) =
      F.presheaf.map (homOfLE le_top).op (globalSection X F t) := by
  have := Stacks.SectionRingProjImmersion.isOpenImmersion_projHomOfIsAmple L hL
  have h1 : (Scheme.Modules.restrictAdjunction (projHomOfIsAmple L hL)).unit.app
        ((tildeFunctor L).obj F) ≫
      (Scheme.Modules.pushforward (projHomOfIsAmple L hL)).map
        ((Scheme.Modules.restrictFunctorIsoPullback (projHomOfIsAmple L hL)).hom.app
          ((tildeFunctor L).obj F)) =
      (Scheme.Modules.pullbackPushforwardAdjunction (projHomOfIsAmple L hL)).unit.app
        ((tildeFunctor L).obj F) :=
    Adjunction.unit_leftAdjointUniq_hom_app _ _ _
  have hunit : (Scheme.Modules.pullbackPushforwardAdjunction (projHomOfIsAmple L hL)).unit.app
        ((tildeFunctor L).obj F) ≫
      (Scheme.Modules.pushforward (projHomOfIsAmple L hL)).map
        ((Scheme.Modules.restrictFunctorIsoPullback (projHomOfIsAmple L hL)).inv.app
          ((tildeFunctor L).obj F)) =
      (Scheme.Modules.restrictAdjunction (projHomOfIsAmple L hL)).unit.app
        ((tildeFunctor L).obj F) := by
    rw [← h1, Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app,
      CategoryTheory.Functor.map_id]
    exact Category.comp_id _
  have h2 := ConcreteCategory.congr_hom (congrArg (fun φ => Scheme.Modules.Hom.app φ ⊤) hunit)
    (Stacks.AlgebraicGeometry.ProjStalkGlobalSections.degreeZeroToGlobalSections (grading L)
      (Stacks.TwistedSections.moduleGrading F L) (degreeZeroElem L F t))
  exact (congrArg ((gluedComparison L hL F).app _) h2).trans (gluedComparison_degreeZero L hL F t)

/-- **Stacks Tag 01QJ.** In Situation 01QH — `X` a scheme, `L` an ample invertible `𝒪_X`-module,
`S = Γ_*(X, L)` and `f : X ⟶ Proj S` the canonical morphism of Tag 01PZ — the comparison
`pullbackTildeComparison : f^* M̃ ⟶ ℱ`, `M = Γ_*(X, L, ℱ)`, is a natural transformation in `ℱ`
(functoriality), it is an isomorphism for every quasi-coherent `ℱ`, and
`M_0 ⟶ Γ(Proj S, M̃) ⟶ Γ(X, ℱ)` is the identity. -/
@[stacks 01QJ "the natural transformation `f^*M̃ ⟶ ℱ` is an isomorphism for `ℱ` quasi-coherent and
is the identity on `M_0`"]
theorem pullbackTildeComparison_spec :
    (∀ (F : X.Modules) [F.IsQuasicoherent], IsIso ((pullbackTildeComparison L hL).app F)) ∧
      ∀ (F : X.Modules) (t : twistSections F L 0),
        ((pullbackTildeComparison L hL).app F).app (projHomOfIsAmple L hL ⁻¹ᵁ ⊤)
            (Stacks.Tag01VSPullbackTensor.modulesPullbackUnit (projHomOfIsAmple L hL)
              ((tildeFunctor L).obj F) ⊤
              (Stacks.AlgebraicGeometry.ProjStalkGlobalSections.degreeZeroToGlobalSections
                (grading L) (Stacks.TwistedSections.moduleGrading F L) (degreeZeroElem L F t))) =
          F.presheaf.map (homOfLE le_top).op (globalSection X F t) :=
  ⟨fun F _ => isIso_pullbackTildeComparison_app L hL F, pullbackTildeComparison_degreeZero L hL⟩

end Stacks.SectionRingProjQuasicoherent

end
