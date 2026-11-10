module

public import StacksFrontier.AlgebraicGeometry.SectionRingProjQuasicoherent.Division
public import StacksFrontier.AlgebraicGeometry.SectionRingProjQuasicoherent.Basic
public import StacksFrontier.AlgebraicGeometry.SectionRingChartOpen.Basic
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwistSectionComparison
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjConeChart
public import StacksFrontier.AlgebraicGeometry.TensorSectionNonvanishing.ProjTwistLocalComparison
public import StacksFrontier.AlgebraicGeometry.ProjGradedModuleQcoh.ChartSections
public import StacksFrontier.Topology.Sheaves.Basis.ModuleHomOnBasis

/-!
# The comparison `M̃|_X ⟶ ℱ` for the section ring of an ample invertible sheaf

Let `X` be a scheme, `L` an ample invertible `𝒪_X`-module, `S = Γ_*(X, L)`, `f : X ⟶ Proj S` the
canonical morphism of Stacks Tag 01PZ, assumed an open immersion (Stacks Tag 01Q1), and `ℱ` an
`𝒪_X`-module with `M = Γ_*(X, L, ℱ)`. This file glues the divisions of
`Stacks.SectionRingProjQuasicoherent.localDivision` into a morphism `M̃|_X ⟶ ℱ` on `X`, natural in
`ℱ`, where `M̃|_X` is the restriction of `M̃` along `f`.

The good charts are the `X_a = f⁻¹ D₊(a)` with `D₊(a)` inside the image of `f`; they form a basis
of `X`. The sections of `M̃|_X` over `X_a` are those of `M̃` over `D₊(a)`, that is `M_{(a)}`
(Tag 01M6), and the local map is the division by the powers of `a`. It is linear over
`Γ(X_a, 𝒪_X)` because the ring map `f` induces on the sections over `D₊(a)` is, on `S_{(a)}`, the
chart ring map of Tag 01PZ (`app_awayToSection`), and the division is semilinear over that
(`Stacks.SectionRingProjQuasicoherent.localDivision_smul`). The local maps at two charts
`X_b ⊆ X_a` agree, by `Stacks.SectionRingProjQuasicoherent.localDivision_change`.

## Main definitions

* `Stacks.SectionRingProjQuasicoherent.tildeModule`: `M̃` on `Proj S`.
* `Stacks.SectionRingProjQuasicoherent.gluedComparison`: the morphism `M̃|_X ⟶ ℱ`.

## Main results

* `Stacks.SectionRingProjQuasicoherent.app_awayToSection`: the ring map induced by `f` on the
  sections over `D₊(a)` is the chart ring map.
* `Stacks.SectionRingProjQuasicoherent.isBasis_goodChart`: the good charts form a basis of `X`.
* `Stacks.SectionRingProjQuasicoherent.gluedComparison_app`: the comparison on a good chart is the
  division.
* `Stacks.SectionRingProjQuasicoherent.gluedComparison_naturality`: it is natural in `ℱ`.

## References

* [Stacks Project, Tag 0B5I](https://stacks.math.columbia.edu/tag/0B5I)
* [Stacks Project, Tag 01PZ](https://stacks.math.columbia.edu/tag/01PZ)
* [Stacks Project, Tag 01QJ](https://stacks.math.columbia.edu/tag/01QJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite TopologicalSpace
open Stacks.TensorPowers (natTensorPow)
open Stacks.GradedSections (powSections mul mulMap sectionRing)
open Stacks.TwistedSections (twistPow twistSections twistModule)
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

/-! ### The chart ring map is the ring map of the canonical morphism -/

/-- Mathlib's open immersion `Spec (A_{(s)}) ⟶ Proj A` on the sections over `D₊(s)`, after
`A_{(s)} ⟶ Γ(D₊(s), 𝒪)`, is the identification of `A_{(s)}` with the global sections of its
spectrum. -/
theorem awayToSection_comp_awayι_appLE {A σ : Type u} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] {s : A} {d : ℕ}
    (hs : s ∈ 𝒜 d) (hd : 0 < d)
    (h : ⊤ ≤ Proj.awayι 𝒜 s hs hd ⁻¹ᵁ Proj.basicOpen 𝒜 s) :
    Proj.awayToSection 𝒜 s ≫ (Proj.awayι 𝒜 s hs hd).appLE _ ⊤ h =
      (Scheme.ΓSpecIso (.of (HomogeneousLocalization.Away 𝒜 s))).inv := by
  let U := Proj.basicOpen 𝒜 s
  let e := Proj.basicOpenIsoSpec 𝒜 s hs hd
  have hh : e.hom.appTop = (Scheme.ΓSpecIso _).hom ≫
      Proj.awayToSection 𝒜 s ≫ U.topIso.inv := Proj.basicOpenToSpec_app_top 𝒜 s
  have hi : U.ι.appLE U ⊤ (by simp) = U.topIso.inv := by
    simp only [Scheme.Opens.ι_appLE, Scheme.Opens.topIso]
    congr 1
  rw [show (Proj.awayι 𝒜 s hs hd).appLE U ⊤ h =
      U.ι.appLE U ⊤ (by simp) ≫ e.inv.appTop by
        rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
        exact (Scheme.Hom.appLE_comp_appLE e.inv U.ι U ⊤ ⊤ _ _).symm, hi, ← Category.assoc]
  have hh' : Proj.awayToSection 𝒜 s ≫ U.topIso.inv =
      (Scheme.ΓSpecIso _).inv ≫ e.hom.appTop := by rw [hh]; simp
  rw [hh', Category.assoc, ← Scheme.Hom.comp_appTop, e.inv_hom_id]
  exact Category.comp_id _

/-- Restricting along `W ≤ V` and back along `V ≤ W` is the identity. -/
theorem presheaf_map_map_of_le {X : Scheme.{u}} {V W : X.Opens} (h₁ : W ≤ V) (h₂ : V ≤ W)
    (s : Γ(X, W)) :
    X.presheaf.map (homOfLE h₁).op (X.presheaf.map (homOfLE h₂).op s) = s := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp,
    show homOfLE h₁ ≫ homOfLE h₂ = 𝟙 W from Subsingleton.elim _ _, op_id,
    CategoryTheory.Functor.map_id]
  rfl

variable {X : Scheme.{u}} (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
  (hL : Stacks.Ample.IsAmple X L)

/-- **The ring map induced by the canonical morphism on the sections over `D₊(a)` is the chart
ring map of Stacks Tag 01PZ**: for `y ∈ S_{(a)}`, the pullback along `f` of the function `y` on
`D₊(a)` is `chartRingMap L a y` on `f⁻¹ D₊(a) = X_a`. -/
theorem app_awayToSection {d : ℕ} (a : powSections L d) (hd : 0 < d)
    (hU : projHomOfIsAmple L hL ⁻¹ᵁ Proj.basicOpen (grading L) (DirectSum.of (powSections L) d a)
      ≤ nvOpen L a)
    (y : HomogeneousLocalization.Away (grading L) (DirectSum.of (powSections L) d a)) :
    (projHomOfIsAmple L hL).app (Proj.basicOpen (grading L) (DirectSum.of (powSections L) d a))
        (Proj.awayToSection (grading L) (DirectSum.of (powSections L) d a) y) =
      Stacks.SectionRingChartMap.chartRingMap L a hU y := by
  set U0 := nvOpen L a with hU0
  set φ : CommRingCat.of (HomogeneousLocalization.Away (grading L)
      (DirectSum.of (powSections L) d a)) ⟶ Γ(X, U0) :=
    CommRingCat.ofHom (Stacks.SectionRingChartMap.chartRingMap L a (le_refl U0)) with hφ
  have hg : U0.ι ≫ projHomOfIsAmple L hL = U0.toSpecΓ ≫ Spec.map φ ≫
      Proj.awayι (grading L) (DirectSum.of (powSections L) d a)
        (Stacks.ExternalGrading.of_mem_summand d a) hd := by
    rw [Stacks.SectionRingProjImmersion.ι_comp_projHomOfIsAmple L hL a hd,
      ← Stacks.SectionRingChartOpen.chartHomOn_self L a hd,
      Stacks.SectionRingChartOpen.chartHomOn_val]
  have hpre : projHomOfIsAmple L hL ⁻¹ᵁ
      Proj.basicOpen (grading L) (DirectSum.of (powSections L) d a) = U0 :=
    Stacks.SectionRingProjMorphism.projHomOfIsAmple_preimage_projBasicOpen L hL a hd
  have e₀ : (⊤ : U0.toScheme.Opens) ≤ U0.ι ⁻¹ᵁ (projHomOfIsAmple L hL ⁻¹ᵁ
      Proj.basicOpen (grading L) (DirectSum.of (powSections L) d a)) := by
    rw [hpre, U0.ι_preimage_self]
  have e₁ : (⊤ : U0.toScheme.Opens) ≤ (U0.ι ≫ projHomOfIsAmple L hL) ⁻¹ᵁ
      Proj.basicOpen (grading L) (DirectSum.of (powSections L) d a) := by
    rwa [Scheme.Hom.comp_preimage]
  have e₂ : (⊤ : U0.toScheme.Opens) ≤ ((U0.toSpecΓ ≫ Spec.map φ) ≫
      Proj.awayι (grading L) (DirectSum.of (powSections L) d a)
        (Stacks.ExternalGrading.of_mem_summand d a) hd) ⁻¹ᵁ
      Proj.basicOpen (grading L) (DirectSum.of (powSections L) d a) := by
    rwa [Category.assoc, ← hg]
  have e₃ : (⊤ : (Spec (CommRingCat.of (HomogeneousLocalization.Away (grading L)
      (DirectSum.of (powSections L) d a)))).Opens) ≤
      Proj.awayι (grading L) (DirectSum.of (powSections L) d a)
        (Stacks.ExternalGrading.of_mem_summand d a) hd ⁻¹ᵁ
      Proj.basicOpen (grading L) (DirectSum.of (powSections L) d a) := by
    rw [← Proj.opensRange_awayι (grading L) (DirectSum.of (powSections L) d a)
      (Stacks.ExternalGrading.of_mem_summand d a) hd, Scheme.Hom.preimage_opensRange]
  have e₄ : (⊤ : U0.toScheme.Opens) ≤ (U0.toSpecΓ ≫ Spec.map φ) ⁻¹ᵁ ⊤ := by simp
  have key : Proj.awayToSection (grading L) (DirectSum.of (powSections L) d a) ≫
      (projHomOfIsAmple L hL).app (Proj.basicOpen (grading L) (DirectSum.of (powSections L) d a)) ≫
        U0.ι.appLE _ ⊤ e₀ = φ ≫ U0.topIso.inv := by
    rw [← Scheme.Hom.comp_appLE U0.ι (projHomOfIsAmple L hL) _ ⊤ e₁,
      Stacks.AlgebraicGeometry.ProjChartSections.appLE_congr_hom
        (hg.trans (Category.assoc _ _ _).symm) _ ⊤ e₁ e₂,
      ← Scheme.Hom.appLE_comp_appLE _ _ _ ⊤ ⊤ e₃ e₄, ← Category.assoc,
      awayToSection_comp_awayι_appLE,
        Stacks.AlgebraicGeometry.ProjChartSections.appLE_top_top, Scheme.Hom.comp_appTop,
      ← Scheme.ΓSpecIso_inv_naturality_assoc, Scheme.Opens.toSpecΓ_appTop, Iso.inv_hom_id_assoc]
  have hι : U0.ι.appLE _ ⊤ e₀ ≫ U0.topIso.hom = X.presheaf.map (homOfLE hpre.ge).op := by
    rw [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_hom]
    exact (X.presheaf.map_comp _ _).symm.trans (congrArg X.presheaf.map (Subsingleton.elim _ _))
  have hcomp : U0.ι.appLE _ ⊤ e₀ ≫ U0.topIso.hom ≫ X.presheaf.map (homOfLE hU).op = 𝟙 _ := by
    rw [← Category.assoc, hι]
    exact (X.presheaf.map_comp _ _).symm.trans
      ((congrArg X.presheaf.map (Subsingleton.elim _ _)).trans (X.presheaf.map_id _))
  have key' : Proj.awayToSection (grading L) (DirectSum.of (powSections L) d a) ≫
      (projHomOfIsAmple L hL).app (Proj.basicOpen (grading L) (DirectSum.of (powSections L) d a)) =
        φ ≫ X.presheaf.map (homOfLE hU).op := by
    simpa only [Category.assoc, hcomp, Category.comp_id, Iso.inv_hom_id_assoc] using
      key =≫ (U0.topIso.hom ≫ X.presheaf.map (homOfLE hU).op)
  have hy := ConcreteCategory.congr_hom key' y
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hy
  rw [hy, hφ]
  exact Stacks.SectionRingChartOpen.map_chartRingMap L a (le_refl U0) hU hU y

/-- **The chart ring map on any open inside `f⁻¹ D₊(a)`** is the ring map induced by `f`. -/
theorem appLE_awayToSection {d : ℕ} (a : powSections L d) (hd : 0 < d) {V : X.Opens}
    (hV : V ≤ projHomOfIsAmple L hL ⁻¹ᵁ
      Proj.basicOpen (grading L) (DirectSum.of (powSections L) d a))
    (hVa : V ≤ nvOpen L a)
    (y : HomogeneousLocalization.Away (grading L) (DirectSum.of (powSections L) d a)) :
    (projHomOfIsAmple L hL).appLE _ V hV
        (Proj.awayToSection (grading L) (DirectSum.of (powSections L) d a) y) =
      Stacks.SectionRingChartMap.chartRingMap L a hVa y := by
  have hpre := Stacks.SectionRingProjMorphism.projHomOfIsAmple_preimage_projBasicOpen L hL a hd
  rw [Scheme.Hom.appLE, CommRingCat.comp_apply, app_awayToSection L hL a hd hpre.le]
  exact Stacks.SectionRingChartOpen.map_chartRingMap L a hpre.le hVa hV y

/-! ### The local map on a chart -/

variable (F : X.Modules) [IsOpenImmersion (projHomOfIsAmple L hL)]

/-- A homogeneous element of positive degree whose standard open lies in the image of the
canonical morphism. The nonvanishing opens of these form a basis of `X`. -/
def GoodChart : Type u :=
  {c : Stacks.SectionRingProjMorphism.PosSection L //
    Proj.basicOpen (grading L) (DirectSum.of (powSections L) c.deg c.val) ≤
      (projHomOfIsAmple L hL).opensRange}

/-- The image of `X_a` is `D₊(a)` for a good chart. -/
theorem image_nvOpen (c : GoodChart L hL) :
    projHomOfIsAmple L hL ''ᵁ nvOpen L c.1.val =
      Proj.basicOpen (grading L) (DirectSum.of (powSections L) c.1.deg c.1.val) := by
  rw [← Stacks.SectionRingProjMorphism.projHomOfIsAmple_preimage_projBasicOpen L hL c.1.val
      c.1.deg_pos, Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.mpr c.2]

/-- **`M̃` as a module on the scheme `Proj Γ_*(X, L)`**: the sheaf associated to the graded
module `M = Γ_*(X, L, ℱ)`. This is `(tildeFunctor L).obj ℱ` (`tildeModule_eq`). -/
def tildeModule : (AlgebraicGeometry.Proj (grading L)).Modules :=
  ProjectiveSpectrum.Proj.associatedModuleSheaf (grading L)
    (Stacks.TwistedSections.moduleGrading F L)

/-- `tildeModule L F` is the image of `F` under `tildeFunctor L`. -/
theorem tildeModule_eq : tildeModule L F = (tildeFunctor L).obj F := rfl

/-- **The local map of Stacks Tag 01QJ on the chart `X_a`**: a section of the restriction of `M̃`
to `X` over `X_a` is a section of `M̃` over `D₊(a)`, hence an element of `M_{(a)}`, which the
division by the powers of `a` sends to `Γ(X_a, ℱ)`. -/
def localFun (c : GoodChart L hL)
    (x : Γ((tildeModule L F).restrict (projHomOfIsAmple L hL), nvOpen L c.1.val)) :
    Γ(F, nvOpen L c.1.val) :=
  localDivision L F c.1.val le_rfl
    (ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv (grading L)
      (Stacks.TwistedSections.moduleGrading F L)
      (Stacks.ExternalGrading.of_mem_summand c.1.deg c.1.val) c.1.deg_pos
      ((ProjectiveSpectrum.Proj.imageSectionsIso (projHomOfIsAmple L hL)
        (tildeModule L F) (nvOpen L c.1.val) _ (image_nvOpen L hL c)).hom x))

/-- The local map on the chart `X_a` is additive. -/
theorem localFun_add (c : GoodChart L hL)
    (x y : Γ((tildeModule L F).restrict (projHomOfIsAmple L hL), nvOpen L c.1.val)) :
    localFun L hL F c (x + y) = localFun L hL F c x + localFun L hL F c y :=
  (congrArg (localDivision L F c.1.val le_rfl)
      ((congrArg (ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv (grading L)
          (Stacks.TwistedSections.moduleGrading F L)
          (Stacks.ExternalGrading.of_mem_summand c.1.deg c.1.val) c.1.deg_pos)
        (map_add (ConcreteCategory.hom (ProjectiveSpectrum.Proj.imageSectionsIso
          (projHomOfIsAmple L hL) (tildeModule L F) (nvOpen L c.1.val) _
          (image_nvOpen L hL c)).hom) x y)).trans (map_add _ _ _))).trans (map_add _ _ _)

/-- The chart ring map recovers a function on `X_a` from the function on `D₊(a)` it comes from. -/
theorem chartRingMap_eq_of_awayToSection (c : GoodChart L hL) (s : Γ(X, nvOpen L c.1.val))
    (y : HomogeneousLocalization.Away (grading L) (DirectSum.of (powSections L) c.1.deg c.1.val))
    (hy : Proj.awayToSection (grading L) (DirectSum.of (powSections L) c.1.deg c.1.val) y =
      (AlgebraicGeometry.Proj (grading L)).presheaf.map (eqToHom (image_nvOpen L hL c).symm).op
        (((projHomOfIsAmple L hL).appIso (nvOpen L c.1.val)).inv s)) :
    Stacks.SectionRingChartMap.chartRingMap L c.1.val le_rfl y = s := by
  have hpre := Stacks.SectionRingProjMorphism.projHomOfIsAmple_preimage_projBasicOpen L hL
    c.1.val c.1.deg_pos
  rw [← appLE_awayToSection L hL c.1.val c.1.deg_pos hpre.ge le_rfl y, hy,
    ← CommRingCat.comp_apply, Scheme.Hom.map_appLE, ← Scheme.Hom.appIso_hom',
    Iso.inv_hom_id_apply]

/-- The local map `localFun` only depends on the image of the section in `M̃(D₊(a))`. -/
private theorem localFun_congr (c : GoodChart L hL)
    {x : Γ((tildeModule L F).restrict (projHomOfIsAmple L hL), nvOpen L c.1.val)}
    {w : (tildeModule L F).presheaf.obj (op (Proj.basicOpen (grading L)
      (DirectSum.of (powSections L) c.1.deg c.1.val)))}
    (h : (ConcreteCategory.hom (ProjectiveSpectrum.Proj.imageSectionsIso (projHomOfIsAmple L hL)
        (tildeModule L F) (nvOpen L c.1.val) _ (image_nvOpen L hL c)).hom) x = w) :
    localFun L hL F c x = localDivision L F c.1.val le_rfl
      (ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv (grading L)
        (Stacks.TwistedSections.moduleGrading F L)
        (Stacks.ExternalGrading.of_mem_summand c.1.deg c.1.val) c.1.deg_pos w) := by
  subst h
  rfl

/-- **The local map is linear over `Γ(X_a, 𝒪_X)`.** A function `s` on `X_a` acts on the restriction
of `M̃` through the function on `D₊(a)` it comes from, which is a fraction `y` of `S_{(a)}`; the
division is semilinear over the chart ring map, and the chart ring map sends `y` back to `s`. -/
theorem localFun_smul (c : GoodChart L hL) (s : Γ(X, nvOpen L c.1.val))
    (x : Γ((tildeModule L F).restrict (projHomOfIsAmple L hL), nvOpen L c.1.val)) :
    localFun L hL F c (s • x) = s • localFun L hL F c x := by
  obtain ⟨y, hy⟩ := ProjectiveSpectrum.Proj.surjective_awayToSection (grading L)
    (Stacks.ExternalGrading.of_mem_summand c.1.deg c.1.val) c.1.deg_pos
    ((AlgebraicGeometry.Proj (grading L)).presheaf.map (eqToHom (image_nvOpen L hL c).symm).op
      (((projHomOfIsAmple L hL).appIso (nvOpen L c.1.val)).inv s))
  have h1 := ProjectiveSpectrum.Proj.imageSectionsIso_smul (projHomOfIsAmple L hL)
    (tildeModule L F) (nvOpen L c.1.val) _ (image_nvOpen L hL c) s x
  rw [← hy] at h1
  have h2 := (ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv (grading L)
      (Stacks.TwistedSections.moduleGrading F L)
      (Stacks.ExternalGrading.of_mem_summand c.1.deg c.1.val) c.1.deg_pos).map_smul y
    ((ProjectiveSpectrum.Proj.imageSectionsIso (projHomOfIsAmple L hL)
        (tildeModule L F) (nvOpen L c.1.val) _ (image_nvOpen L hL c)).hom x)
  have h3 := localDivision_smul L F c.1.val (le_refl (nvOpen L c.1.val)) y
    (ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv (grading L)
      (Stacks.TwistedSections.moduleGrading F L)
      (Stacks.ExternalGrading.of_mem_summand c.1.deg c.1.val) c.1.deg_pos
      ((ProjectiveSpectrum.Proj.imageSectionsIso (projHomOfIsAmple L hL)
        (tildeModule L F) (nvOpen L c.1.val) _ (image_nvOpen L hL c)).hom x))
  exact (localFun_congr L hL F c h1).trans ((congrArg (localDivision L F c.1.val le_rfl) h2).trans
    (h3.trans (congrArg (· • _) (chartRingMap_eq_of_awayToSection L hL c s y hy))))

/-- **The local map on the chart `X_a`, as a morphism of `Γ(X_a, 𝒪_X)`-modules.** -/
def localMap (c : GoodChart L hL) :
    ((tildeModule L F).restrict (projHomOfIsAmple L hL)).val.obj (op (nvOpen L c.1.val)) ⟶
      F.val.obj (op (nvOpen L c.1.val)) :=
  ConcreteCategory.ofHom
    { toFun := localFun L hL F c
      map_add' := localFun_add L hL F c
      map_smul' := localFun_smul L hL F c }

/-- The local map `localMap` applied to a section is `localFun` of that section. -/
theorem localMap_apply (c : GoodChart L hL)
    (x : Γ((tildeModule L F).restrict (projHomOfIsAmple L hL), nvOpen L c.1.val)) :
    localMap L hL F c x = localFun L hL F c x := rfl

/-- **The local maps agree on overlaps.** For `X_b ⊆ X_a`, restricting a section and then dividing
by the powers of `b` is dividing by the powers of `a` and then restricting: a fraction `t / aⁿ` is
rewritten as `c t / b^N` with `aⁿ c = b^N` (`ProjTwistLocalComparison.exists_rewrite_data`), and
the two divisions agree by `localDivision_change`. -/
theorem localFun_restrict (c c' : GoodChart L hL) (h : nvOpen L c'.1.val ≤ nvOpen L c.1.val)
    (x : Γ((tildeModule L F).restrict (projHomOfIsAmple L hL), nvOpen L c.1.val)) :
    localFun L hL F c' (((tildeModule L F).restrict (projHomOfIsAmple L hL)).presheaf.map
        (homOfLE h).op x) =
      F.presheaf.map (homOfLE h).op (localFun L hL F c x) := by
  obtain ⟨⟨d, hd, a⟩, ha⟩ := c
  obtain ⟨⟨e, he, q⟩, hq⟩ := c'
  have hW : Proj.basicOpen (grading L) (DirectSum.of (powSections L) e q) ≤
      Proj.basicOpen (grading L) (DirectSum.of (powSections L) d a) := by
    rw [← image_nvOpen L hL ⟨⟨d, hd, a⟩, ha⟩, ← image_nvOpen L hL ⟨⟨e, he, q⟩, hq⟩]
    exact Scheme.Hom.image_mono _ h
  have hnat := ProjectiveSpectrum.Proj.imageSectionsIso_naturality (projHomOfIsAmple L hL)
    (tildeModule L F) _ _ _ _ (image_nvOpen L hL ⟨⟨d, hd, a⟩, ha⟩)
    (image_nvOpen L hL ⟨⟨e, he, q⟩, hq⟩) h hW
  have hx := ConcreteCategory.congr_hom hnat x
  let z := (ProjectiveSpectrum.Proj.imageSectionsIso (projHomOfIsAmple L hL) (tildeModule L F)
    (nvOpen L a) _ (image_nvOpen L hL ⟨⟨d, hd, a⟩, ha⟩)).hom x
  obtain ⟨n, xx, hxx, hz⟩ :=
    Stacks.SheafOfModules.degreeZeroLocalization_exists_fraction_of_degree (grading L)
      (Stacks.TwistedSections.moduleGrading F L) (Stacks.ExternalGrading.of_mem_summand d a)
      (ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv (grading L)
        (Stacks.TwistedSections.moduleGrading F L) (Stacks.ExternalGrading.of_mem_summand d a)
        hd z)
  obtain ⟨t, rfl⟩ := Stacks.TwistedSections.mem_moduleGrading_natCast_iff.mp hxx
  obtain ⟨b, cc, ⟨γ, hγ⟩, hgm, hj, -⟩ :=
    Stacks.AlgebraicGeometry.ProjTwistLocalComparison.exists_rewrite_data (grading L)
      (Stacks.ExternalGrading.of_mem_summand d a) hd
      (Stacks.ExternalGrading.of_mem_summand e q) he hW n
  have hdeg : n * d + n * (b * e - d) = n * b * e := by omega
  have hmem : DirectSum.of (powSections L) (n * (b * e - d)) γ •
      DirectSum.of (twistSections F L) (n * d) t ∈
        Stacks.TwistedSections.moduleGrading F L (((n * b) * e : ℕ) : ℤ) := by
    rw [of_smul_of_eq_twistMul]
    exact ⟨Stacks.TwistedSections.twistCongr hdeg (t ≫ twistMul γ (n * d)),
      of_twistCongr hdeg _⟩
  let A' : GradedModuleDegreeZeroLocalization (grading L) (Stacks.TwistedSections.moduleGrading F L)
      (DirectSum.of (powSections L) e q) :=
    ⟨_, Stacks.SheafOfModules.mk_mem_degreeZeroLocalization_of_degree (grading L)
      (Stacks.TwistedSections.moduleGrading F L) (Stacks.ExternalGrading.of_mem_summand e q)
      (n * b) _ hmem⟩
  have hgm' : DirectSum.of (powSections L) e q ^ (n * b) =
      DirectSum.of (powSections L) d a ^ n *
        DirectSum.of (powSections L) (n * (b * e - d)) γ := by rw [hgm, hγ]
  have hE' := Stacks.AlgebraicGeometry.ProjTwistLocalComparison.standardOpenEquiv_restrict_mk
    (grading L) (Stacks.TwistedSections.moduleGrading F L)
    (Stacks.ExternalGrading.of_mem_summand d a) hd (Stacks.ExternalGrading.of_mem_summand e q) he
    hW hgm' z A' hz rfl
  have hchange := localDivision_change L F a q γ (le_refl (nvOpen L a))
    (le_refl (nvOpen L q)) (homOfLE h) n (n * b) (by rw [Nat.mul_comm d n, hdeg]; ring)
    hgm'.symm _ A' t hz rfl
  have hstep : (ConcreteCategory.hom (ProjectiveSpectrum.Proj.imageSectionsIso
      (projHomOfIsAmple L hL) (tildeModule L F) (nvOpen L q) _
      (image_nvOpen L hL ⟨⟨e, he, q⟩, hq⟩)).hom)
        (((tildeModule L F).restrict (projHomOfIsAmple L hL)).presheaf.map (homOfLE h).op x) =
      (tildeModule L F).presheaf.map (homOfLE hW).op z := hx
  exact (localFun_congr L hL F ⟨⟨e, he, q⟩, hq⟩ hstep).trans
    ((congrArg (localDivision L F q (le_refl (nvOpen L q))) hE').trans hchange)


/-- **The nonvanishing opens of the good charts form a basis of `X`.** For `x ∈ U`, the image of
`U` is an open of `Proj Γ_*(X, L)` containing `f x`, so it contains a standard open `D₊(a)` around
`f x`; that standard open lies in the image of `f`, and its preimage `X_a` lies in `U`. -/
theorem isBasis_goodChart :
    Opens.IsBasis (Set.range (fun c : GoodChart L hL => nvOpen L c.1.val)) := by
  rw [Opens.isBasis_iff_nbhd]
  intro U x hx
  have hfx : projHomOfIsAmple L hL x ∈ projHomOfIsAmple L hL ''ᵁ U :=
    (Scheme.Hom.apply_mem_image_iff _).mpr hx
  obtain ⟨_, ⟨p, rfl⟩, hpx, hpU⟩ :=
    (Opens.isBasis_iff_nbhd.mp
      (Stacks.AlgebraicGeometry.ProjTwistComparison.isBasis_positiveBasicOpen (grading L))) hfx
  obtain ⟨d, hd, a, ha⟩ := p.2
  have hbo : Stacks.AlgebraicGeometry.ProjTwistComparison.positiveBasicOpen (grading L) p =
      Proj.basicOpen (grading L) (DirectSum.of (powSections L) d a) := by
    rw [Stacks.AlgebraicGeometry.ProjTwistComparison.positiveBasicOpen, ← ha]
    rfl
  have hgood : Proj.basicOpen (grading L) (DirectSum.of (powSections L) d a) ≤
      (projHomOfIsAmple L hL).opensRange :=
    hbo ▸ hpU.trans (Scheme.Hom.image_le_opensRange _ U)
  have hpre := Stacks.SectionRingProjMorphism.projHomOfIsAmple_preimage_projBasicOpen L hL a hd
  refine ⟨nvOpen L a, ⟨⟨⟨d, hd, a⟩, hgood⟩, rfl⟩, ?_, ?_⟩
  · rw [← hpre]
    exact hbo ▸ hpx
  · rw [← hpre, ← Scheme.Hom.preimage_image_eq (projHomOfIsAmple L hL) U]
    exact Scheme.Hom.preimage_mono _ (hbo ▸ hpU)

/-- **The comparison `M̃|_X ⟶ ℱ`**, glued from the divisions on the good charts. -/
def gluedComparison :
    (tildeModule L F).restrict (projHomOfIsAmple L hL) ⟶ F :=
  Stacks.BasisRestriction.moduleSheafHomOfSectionHomOnBasis
    ((tildeModule L F).restrict (projHomOfIsAmple L hL)) F
    (fun c : GoodChart L hL => nvOpen L c.1.val) (localMap L hL F) (isBasis_goodChart L hL)
    (fun c c' h x => localFun_restrict L hL F c c' h x)

/-- On the nonvanishing open `X_a` of a good chart, the comparison `M̃|_X ⟶ ℱ` is the local map
`localMap`. -/
theorem gluedComparison_app (c : GoodChart L hL) :
    (gluedComparison L hL F).val.app (op (nvOpen L c.1.val)) = localMap L hL F c :=
  Stacks.BasisRestriction.moduleSheafHomOfSectionHomOnBasis_app _ F _ (localMap L hL F)
    (isBasis_goodChart L hL) _ c

/-- **The local map is natural in `ℱ`.** -/
theorem localFun_naturality {G : X.Modules} (φ : F ⟶ G) (c : GoodChart L hL)
    (x : Γ((tildeModule L F).restrict (projHomOfIsAmple L hL), nvOpen L c.1.val)) :
    localFun L hL G c (((Scheme.Modules.restrictFunctor (projHomOfIsAmple L hL)).map
        ((tildeFunctor L).map φ)).app (nvOpen L c.1.val) x) =
      φ.app (nvOpen L c.1.val) (localFun L hL F c x) := by
  have hI := ConcreteCategory.congr_hom
    ((Scheme.Modules.Hom.mapPresheaf ((tildeFunctor L).map φ)).naturality
      (eqToHom (image_nvOpen L hL c).symm).op) x
  have hloc := Stacks.AlgebraicGeometry.ProjSheafFunctoriality.associatedModuleSheafMap_standardOpen
    (grading L) (Stacks.TwistedSections.moduleGrading F L)
    (Stacks.TwistedSections.moduleGrading G L)
    (Stacks.TwistedSections.twistModuleLinearMap φ)
    (Stacks.TwistedSections.twistModuleHom_mem_moduleGrading φ)
    (Stacks.ExternalGrading.of_mem_summand c.1.deg c.1.val) c.1.deg_pos
    ((ProjectiveSpectrum.Proj.imageSectionsIso (projHomOfIsAmple L hL) (tildeModule L F)
      (nvOpen L c.1.val) _ (image_nvOpen L hL c)).hom x)
  exact (localFun_congr L hL G c hI.symm).trans
    (localDivision_naturality L F φ c.1.val le_rfl _ _ hloc)

/-- **The comparison `M̃|_X ⟶ ℱ` is natural in `ℱ`.** -/
theorem gluedComparison_naturality {G : X.Modules} (φ : F ⟶ G) :
    (Scheme.Modules.restrictFunctor (projHomOfIsAmple L hL)).map ((tildeFunctor L).map φ) ≫
        gluedComparison L hL G =
      gluedComparison L hL F ≫ φ := by
  refine Stacks.BasisRestriction.moduleSheafHom_ext_onBasis _ _
    (fun c : GoodChart L hL => nvOpen L c.1.val) (isBasis_goodChart L hL) _ _ fun c => ?_
  change ((Scheme.Modules.restrictFunctor (projHomOfIsAmple L hL)).map
      ((tildeFunctor L).map φ)).val.app _ ≫ (gluedComparison L hL G).val.app _ =
    (gluedComparison L hL F).val.app _ ≫ φ.val.app _
  rw [gluedComparison_app, gluedComparison_app]
  ext x
  exact localFun_naturality L hL F φ c x

end Stacks.SectionRingProjQuasicoherent


end
