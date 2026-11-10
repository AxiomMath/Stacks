module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartGradedThetaChart
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.AffineHomQcohSource
public import StacksFrontier.AlgebraicGeometry.SectionsColimit.Basic
public import StacksFrontier.AlgebraicGeometry.TwistChartLocality.ChartQcoh
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwistAwayPieceScalars
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartGradedIntegerSemilinear

/-!
# The chart datum of `θ` for Stacks Tag 01NK, as a morphism of sheaves on the chart

Let `A = ⨁_{n ≥ 0} 𝒜 n` be a graded ring, `T` a scheme, `L` an invertible `𝒪_T`-module,
`ψ : A → Γ_*(T, L)` a graded map and `r_{L, ψ} : U(ψ) ⟶ Proj 𝒜` the morphism of
[Stacks, Tag 01NK]. The comparison

  `θ : r_{L, ψ}^*(⨁_{d ∈ ℤ} 𝒪_X(d)) ⟶ ⨁_{d ∈ ℤ} L^{⊗ d}|_{U(ψ)}`

of that tag is the adjoint transpose of a family of morphisms
`𝒪_X(n) ⟶ (r_{L, ψ})_* (L^{⊗ n}|_{U(ψ)})` of sheaves of `𝒪_{Proj 𝒜}`-modules, and that family is
glued from data on the standard opens `D₊(f)` of homogeneous `f` of positive degree. **This file
builds the datum on one chart, in one degree, and promotes it from a map of sections to a morphism
of sheaves of modules on that chart.**

Two steps. First the chart comparison of
`Stacks.AlgebraicGeometry.ProjChartGradedDivision.intChartSection` — additive by
`intChartSectionHom`, and `A_{(f)}`-semilinear along the dehomogenisation ring map by
`…ProjChartGradedIntegerSemilinear.intChartSection_smul` — is read as a morphism of
`A_{(f)}`-modules `Γ(D₊(f), 𝒪_X(n)) ⟶ Γ(D₊(f), (r_{L, ψ})_* L^{⊗ n})`, using
`…ProjTwistAwayPiece.sectionsTwistEquivGradedPiece` on the source and clause (1) of the tag on the
target. Second, that map of sections is promoted to a morphism of the restrictions to the chart by
`Stacks.AlgebraicGeometry.ModuleLimits.restrictHomOfΓMap`.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjChartGradedTheta.chartΓAddHom`,
  `…chartΓLinearMap` and `…chartΓMap` — **the chart datum of `θ` in degree `n`**, as an additive
  map, as an `A_{(f)}`-linear map, and as a morphism of `ModuleCat A_{(f)}`.
* `…chartRestrictHom` — **the chart datum as a morphism of sheaves of modules**
  `𝒪_X(n)|_{D₊(f)} ⟶ ((r_{L, ψ})_* L^{⊗ n})|_{D₊(f)}`, with `…chartRestrictHom_app_top` saying
  that it acts on the sections over `D₊(f)` by the chart datum.

## Main results

* `…imageSectionsIso_moduleSpecΓ_smul` and `…imageSectionsIso_moduleSpecΓ_smul_inv` — **the
  `A_{(f)}`-action on the global sections of a restriction to the chart of `f` is the
  `AlgebraicGeometry.Proj.awayToSection`-action on the sections over `D₊(f)`**, in both
  directions. This is the source-side scalar comparison, general in the sheaf of modules.
* `…chartTargetIso_smul` and `…chartTargetIso_smul_inv` — **the target-side scalar comparison**:
  the identification of the sections of `(r_{L, ψ})_* L^{⊗ n}` over `D₊(f)` with the sections of
  `L^{⊗ n}` over the chart open is semilinear along the dehomogenisation ring map. The sections of
  a direct image are the sections over the preimage by `rfl`, so this is
  `…GradedSections.awayToSection_glued_app` of the sibling file together with the semilinearity of
  the identification of restricted sections with sections over an image.

## Implementation notes

The promotion in the second step is `restrictHomOfΓMap`, which requires the **source** to be
quasi-coherent and assumes **nothing** about the target. That is what this situation needs: the
target is a direct image along `r_{L, ψ}`, a morphism which is neither quasi-compact nor
quasi-separated, so the repository's `…ModuleLimits.exists_hom_app_top_eq` and
`…ModuleLimits.moduleSpec_exists_hom`, which ask both sides to be quasi-coherent, do not apply.
The quasi-coherence used is that of the twisting sheaf on `Proj 𝒜` itself
(`…TwistChartLocality.isQuasicoherent_twistingSheaf`), after which the restriction's own
quasi-coherence is `inferInstance`; no transport along `AlgebraicGeometry.Proj.awayι` is involved,
because `𝒪_X(n)|_{D₊(f)}` *is* a sheaf of modules on `Spec A_{(f)}` and its sections over `⊤` *are*
`Γ(D₊(f), 𝒪_X(n))`, each by `rfl`.

Three spelling frictions, each handled the same way. The two readings of a chart module — as
`Γ(M.restrict (awayι …), ⊤)` and as `moduleSpecΓFunctor.obj (M.restrict (awayι …))` — are the same
type but only the second carries the `A_{(f)}`-action, so `chartΓAddHom` is stated at the second
and `chartΓAddHom_apply` is `rfl`. The implicit ring of `AlgebraicGeometry.moduleSpecΓFunctor` is
supplied explicitly everywhere, without which instance search unfolds the object and loses the
module structure. And the additivity of the chart datum is taken from the `AddMonoidHom`
composite rather than proved by `simp`, because `intChartSectionHom_apply` is a `simp` lemma and
fires first, replacing the additive map by its underlying function.

`awayι_image_top` restates `Stacks.AlgebraicGeometry.TwistChartLocality.awayι_image_top`, which is
not imported here because its module pulls in the whole relative-Proj chain; this is the same
reason `Stacks.AlgebraicGeometry.ModuleHomGlue.image_preimage_eq_self` restates
`…TwistUnique.image_preimage_eq_self`.

## What this file does not do

`θ` is not built here and no `stacks` attribute is attached. The three steps that remain with this
file in hand — the gluing of the charts into a single morphism
`𝒪_X(n) ⟶ (r_{L, ψ})_* (L^{⊗ n}|_{U(ψ)})` on `Proj 𝒜` by
`Stacks.AlgebraicGeometry.ModuleHomGlue.existsUnique_hom_of_restrict_cover`, the multiplicativity
of the resulting family over an *arbitrary* open of `Proj 𝒜`, and the adjoint transpose — are all
taken in `StacksFrontier.AlgebraicGeometry.Constructions.ProjChartGradedThetaBuild`, which builds
`θ` and carries the tag. The transpose used there is the non-unital companion of
`Stacks.RingedSpace.transposeUnitalHom`; that namespace is `Stacks.RingedSpace`, with no
`SymmetricPullback` component.

## References

* [Stacks Project, Tag 01NK](https://stacks.math.columbia.edu/tag/01NK)
* [Stacks Project, Tag 01MN](https://stacks.math.columbia.edu/tag/01MN)
* [Stacks Project, Tag 01M6](https://stacks.math.columbia.edu/tag/01M6)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry HomogeneousLocalization
open AlgebraicGeometry.ProjectiveSpectrum.Proj (imageSectionsIso imageSectionsIso_smul
  awayι_appIso_top_inv twistingSheaf integerGrading)
open Stacks.GradedLocalization (gradedPiece smul_mem_gradedPiece)
open Stacks.AlgebraicGeometry.ProjChartFullGraded (GradedSections)
open Stacks.AlgebraicGeometry.ProjTwistAwayPiece (sectionsTwistEquivGradedPiece
  coe_sectionsTwistEquivGradedPiece_smul)
open Stacks.AlgebraicGeometry.ProjChartGradedDivision (intChartSection intChartSectionHom
  intChartSection_smul)
open Stacks.NonvanishingOpen (nonvanishingOpen)
open Stacks.TensorPowers (natTensorPow)
open Stacks.AmpleProjectiveImmersion (tensorPowerModule)

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

universe u w

namespace Stacks.AlgebraicGeometry.ProjChartGradedTheta

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {d : ℕ} {f : A}

/-- The image of the whole chart spectrum of `f` is the standard open `D₊(f)`. -/
theorem awayι_image_top (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    AlgebraicGeometry.Proj.awayι 𝒜 f hf hd ''ᵁ ⊤ = AlgebraicGeometry.Proj.basicOpen 𝒜 f := by
  rw [Scheme.Hom.image_top_eq_opensRange, AlgebraicGeometry.Proj.opensRange_awayι]

/-- The `A_{(f)}`-action on the global sections of a restriction to the chart of `f` is the
`awayToSection`-action on the sections over `D₊(f)`. -/
theorem imageSectionsIso_moduleSpecΓ_smul (M : (AlgebraicGeometry.Proj 𝒜).Modules)
    (hf : f ∈ 𝒜 d) (hd : 0 < d) (ρ : Away 𝒜 f)
    (x : moduleSpecΓFunctor.obj (M.restrict (AlgebraicGeometry.Proj.awayι 𝒜 f hf hd))) :
    (imageSectionsIso (AlgebraicGeometry.Proj.awayι 𝒜 f hf hd) M ⊤
          (AlgebraicGeometry.Proj.basicOpen 𝒜 f) (awayι_image_top 𝒜 hf hd)).hom (ρ • x)
      = (AlgebraicGeometry.Proj.awayToSection 𝒜 f).hom ρ •
          (imageSectionsIso (AlgebraicGeometry.Proj.awayι 𝒜 f hf hd) M ⊤
            (AlgebraicGeometry.Proj.basicOpen 𝒜 f) (awayι_image_top 𝒜 hf hd)).hom x := by
  rw [← Stacks.AlgebraicGeometry.SectionsColimit.moduleSpecΓ_smul
    (M.restrict (AlgebraicGeometry.Proj.awayι 𝒜 f hf hd)) ρ x]
  have hscalar := ConcreteCategory.congr_hom (awayι_appIso_top_inv 𝒜 hf hd) ρ
  simp only [ConcreteCategory.comp_apply] at hscalar
  rw [imageSectionsIso_smul (AlgebraicGeometry.Proj.awayι 𝒜 f hf hd) M ⊤
    (AlgebraicGeometry.Proj.basicOpen 𝒜 f) (awayι_image_top 𝒜 hf hd) _ x, hscalar]

section Target

variable {T : Scheme.{u}} {L : T.Modules} [Stacks.Ample.IsInvertibleModule T L]
  (ψ : GradedSections 𝒜 L) {e : ℕ}

/-- Elementwise form of `awayToSection_glued_app`. -/
theorem appIso_inv_glued_app_awayToSection (hf : f ∈ 𝒜 e) (he : 0 < e) (ρ : Away 𝒜 f) :
    (ψ.coveringOpen.ι.appIso
        (ψ.glued ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 f)).inv
        ((ψ.glued.app (AlgebraicGeometry.Proj.basicOpen 𝒜 f))
          ((AlgebraicGeometry.Proj.awayToSection 𝒜 f).hom ρ))
      = (ψ.homogeneousRatios hf (ψ.chartOpen_eq hf he).le).lift he ρ := by
  have h := ConcreteCategory.congr_hom (ψ.awayToSection_glued_app hf he) ρ
  simp only [ConcreteCategory.comp_apply, CommRingCat.hom_ofHom] at h
  exact h

/-- **The comparison of the direct image's sections over `D₊(f)` with the sections of `L^{⊗ n}`
over the chart open is semilinear** along the dehomogenisation ring map. -/
theorem chartTargetIso_smul (hf : f ∈ 𝒜 e) (he : 0 < e) (n : ℤ) (ρ : Away 𝒜 f)
    (v : Γ(ψ.pushLaurent n, AlgebraicGeometry.Proj.basicOpen 𝒜 f)) :
    (ψ.chartTargetIso n f).hom ((AlgebraicGeometry.Proj.awayToSection 𝒜 f).hom ρ • v)
      = (ψ.homogeneousRatios hf (ψ.chartOpen_eq hf he).le).lift he ρ •
          (ψ.chartTargetIso n f).hom v := by
  have key := imageSectionsIso_smul ψ.coveringOpen.ι (tensorPowerModule T L n)
      (ψ.glued ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 f) (ψ.chartOpen f) rfl
      ((ψ.glued.app (AlgebraicGeometry.Proj.basicOpen 𝒜 f))
        ((AlgebraicGeometry.Proj.awayToSection 𝒜 f).hom ρ)) v
  simp only [eqToHom_refl, CategoryTheory.op_id, CategoryTheory.Functor.map_id,
    ConcreteCategory.id_apply] at key
  rw [appIso_inv_glued_app_awayToSection 𝒜 ψ hf he ρ] at key
  exact key

/-- If a bijection intertwines two scalar actions, so does its inverse. -/
private theorem inv_smul_of_hom_smul {X Y α β : Type*} [SMul α X] [SMul β Y] {h : X → Y}
    {g : Y → X} {a : α} {b : β} (hs : ∀ x, h (a • x) = b • h x) (hinj : Function.Injective h)
    (hg : ∀ y, h (g y) = y) (y : Y) : g (b • y) = a • g y :=
  hinj (by rw [hs, hg, hg])

/-- Inverse form of `imageSectionsIso_moduleSpecΓ_smul`. -/
theorem imageSectionsIso_moduleSpecΓ_smul_inv (M : (AlgebraicGeometry.Proj 𝒜).Modules)
    (hf : f ∈ 𝒜 d) (hd : 0 < d) (ρ : Away 𝒜 f)
    (y : Γ(M, AlgebraicGeometry.Proj.basicOpen 𝒜 f)) :
    (imageSectionsIso (AlgebraicGeometry.Proj.awayι 𝒜 f hf hd) M ⊤
          (AlgebraicGeometry.Proj.basicOpen 𝒜 f) (awayι_image_top 𝒜 hf hd)).inv
        ((AlgebraicGeometry.Proj.awayToSection 𝒜 f).hom ρ • y)
      = ρ • (show moduleSpecΓFunctor.obj
            (M.restrict (AlgebraicGeometry.Proj.awayι 𝒜 f hf hd)) from
          (imageSectionsIso (AlgebraicGeometry.Proj.awayι 𝒜 f hf hd) M ⊤
            (AlgebraicGeometry.Proj.basicOpen 𝒜 f) (awayι_image_top 𝒜 hf hd)).inv y) := by
  exact inv_smul_of_hom_smul (imageSectionsIso_moduleSpecΓ_smul 𝒜 M hf hd ρ)
    (ConcreteCategory.bijective_of_isIso _).1 (Iso.inv_hom_id_apply _) y

/-- Inverse form of `chartTargetIso_smul`. -/
theorem chartTargetIso_smul_inv (hf : f ∈ 𝒜 e) (he : 0 < e) (n : ℤ) (ρ : Away 𝒜 f)
    (w : Γ(tensorPowerModule T L n, ψ.chartOpen f)) :
    (ψ.chartTargetIso n f).inv
        ((ψ.homogeneousRatios hf (ψ.chartOpen_eq hf he).le).lift he ρ • w)
      = (AlgebraicGeometry.Proj.awayToSection 𝒜 f).hom ρ • (ψ.chartTargetIso n f).inv w := by
  exact inv_smul_of_hom_smul (chartTargetIso_smul 𝒜 ψ hf he n ρ)
    (ConcreteCategory.bijective_of_isIso _).1 (Iso.inv_hom_id_apply _) w

/-- The twisting sheaf at the `AlgebraicGeometry.Scheme.Modules` spelling. -/
abbrev twistM (n : ℤ) : (AlgebraicGeometry.Proj 𝒜).Modules :=
  show (AlgebraicGeometry.Proj 𝒜).Modules from twistingSheaf 𝒜 n

/-- Abbreviation for the chart identification of the restricted sections of a module. -/
abbrev chartSectionsIso (M : (AlgebraicGeometry.Proj 𝒜).Modules) (hf : f ∈ 𝒜 e) (he : 0 < e) :
    Γ(M.restrict (AlgebraicGeometry.Proj.awayι 𝒜 f hf he), ⊤)
      ≅ Γ(M, AlgebraicGeometry.Proj.basicOpen 𝒜 f) :=
  imageSectionsIso (AlgebraicGeometry.Proj.awayι 𝒜 f hf he) M ⊤
    (AlgebraicGeometry.Proj.basicOpen 𝒜 f) (awayι_image_top 𝒜 hf he)

/-- **The chart datum of `θ` in degree `n`, as an additive map**: the identification of the
restricted sections with the sections over `D₊(f)`, then `Γ(D₊(f), 𝒪_X(n)) ≅ (A_f)_n`, then the
chart comparison of the tag, then back along the two identifications on the target side. -/
def chartΓAddHom (hf : f ∈ 𝒜 e) (he : 0 < e) (n : ℤ) :
    (moduleSpecΓFunctor (R := CommRingCat.of (Away 𝒜 f))).obj
        ((twistM 𝒜 n).restrict (AlgebraicGeometry.Proj.awayι 𝒜 f hf he)) →+
      (moduleSpecΓFunctor (R := CommRingCat.of (Away 𝒜 f))).obj
        ((ψ.pushLaurent n).restrict (AlgebraicGeometry.Proj.awayι 𝒜 f hf he)) :=
  (ConcreteCategory.hom (chartSectionsIso 𝒜 (ψ.pushLaurent n) hf he).inv).comp
    ((ConcreteCategory.hom (ψ.chartTargetIso n f).inv).comp
      ((intChartSectionHom ψ hf (ψ.chartOpen_eq hf he).le he n).comp
        ((sectionsTwistEquivGradedPiece 𝒜 hf he n).toAddMonoidHom.comp
          (ConcreteCategory.hom (chartSectionsIso 𝒜 (twistM 𝒜 n) hf he).hom))))

/-- The chart datum, applied to a section. -/
@[simp] theorem chartΓAddHom_apply (hf : f ∈ 𝒜 e) (he : 0 < e) (n : ℤ)
    (x : (moduleSpecΓFunctor (R := CommRingCat.of (Away 𝒜 f))).obj
      ((twistM 𝒜 n).restrict (AlgebraicGeometry.Proj.awayι 𝒜 f hf he))) :
    chartΓAddHom 𝒜 ψ hf he n x
      = (chartSectionsIso 𝒜 (ψ.pushLaurent n) hf he).inv
          ((ψ.chartTargetIso n f).inv
            (intChartSectionHom ψ hf (ψ.chartOpen_eq hf he).le he n
              (sectionsTwistEquivGradedPiece 𝒜 hf he n
                ((chartSectionsIso 𝒜 (twistM 𝒜 n) hf he).hom x)))) := rfl

/-- **The chart datum of `θ` in degree `n`, as an `A_{(f)}`-linear map.** -/
def chartΓLinearMap (hf : f ∈ 𝒜 e) (he : 0 < e) (n : ℤ) :
    (moduleSpecΓFunctor (R := CommRingCat.of (Away 𝒜 f))).obj
        ((twistM 𝒜 n).restrict (AlgebraicGeometry.Proj.awayι 𝒜 f hf he)) →ₗ[Away 𝒜 f]
      (moduleSpecΓFunctor (R := CommRingCat.of (Away 𝒜 f))).obj
        ((ψ.pushLaurent n).restrict (AlgebraicGeometry.Proj.awayι 𝒜 f hf he)) where
  toFun x := chartΓAddHom 𝒜 ψ hf he n x
  map_add' x y := (chartΓAddHom 𝒜 ψ hf he n).map_add x y
  map_smul' ρ x := by
    have h1 : (chartSectionsIso 𝒜 (twistM 𝒜 n) hf he).hom (ρ • x)
        = (AlgebraicGeometry.Proj.awayToSection 𝒜 f).hom ρ •
            (chartSectionsIso 𝒜 (twistM 𝒜 n) hf he).hom x :=
      imageSectionsIso_moduleSpecΓ_smul 𝒜 (twistM 𝒜 n) hf he ρ x
    have h2 : sectionsTwistEquivGradedPiece 𝒜 hf he n
          ((AlgebraicGeometry.Proj.awayToSection 𝒜 f).hom ρ •
            (chartSectionsIso 𝒜 (twistM 𝒜 n) hf he).hom x)
        = ⟨HomogeneousLocalization.val ρ •
             ((sectionsTwistEquivGradedPiece 𝒜 hf he n
               ((chartSectionsIso 𝒜 (twistM 𝒜 n) hf he).hom x) :
                 LocalizedModule.Away f A)),
           smul_mem_gradedPiece 𝒜 _ hf n ρ
             (sectionsTwistEquivGradedPiece 𝒜 hf he n
               ((chartSectionsIso 𝒜 (twistM 𝒜 n) hf he).hom x)).2⟩ :=
      Subtype.ext (coe_sectionsTwistEquivGradedPiece_smul 𝒜 hf he n ρ _)
    have h3 := intChartSection_smul ψ hf (ψ.chartOpen_eq hf he).le he n ρ
      (sectionsTwistEquivGradedPiece 𝒜 hf he n
        ((chartSectionsIso 𝒜 (twistM 𝒜 n) hf he).hom x))
    rw [chartΓAddHom_apply, chartΓAddHom_apply]
    simp only [RingHom.id_apply, h1,
      Stacks.AlgebraicGeometry.ProjChartGradedDivision.intChartSectionHom_apply, h2, h3,
      chartTargetIso_smul_inv 𝒜 ψ hf he n ρ,
      imageSectionsIso_moduleSpecΓ_smul_inv 𝒜 (ψ.pushLaurent n) hf he ρ]

/-- **The chart datum of `θ` in degree `n`, as a morphism of `A_{(f)}`-modules.** -/
def chartΓMap (hf : f ∈ 𝒜 e) (he : 0 < e) (n : ℤ) :
    (moduleSpecΓFunctor (R := CommRingCat.of (Away 𝒜 f))).obj
        ((twistM 𝒜 n).restrict (AlgebraicGeometry.Proj.awayι 𝒜 f hf he))
      ⟶ (moduleSpecΓFunctor (R := CommRingCat.of (Away 𝒜 f))).obj
          ((ψ.pushLaurent n).restrict (AlgebraicGeometry.Proj.awayι 𝒜 f hf he)) :=
  ModuleCat.ofHom
    (X := (moduleSpecΓFunctor (R := CommRingCat.of (Away 𝒜 f))).obj
      ((twistM 𝒜 n).restrict (AlgebraicGeometry.Proj.awayι 𝒜 f hf he)))
    (Y := (moduleSpecΓFunctor (R := CommRingCat.of (Away 𝒜 f))).obj
      ((ψ.pushLaurent n).restrict (AlgebraicGeometry.Proj.awayι 𝒜 f hf he)))
    (chartΓLinearMap 𝒜 ψ hf he n)

/-- **The chart datum of `θ` in degree `n`, as a morphism of sheaves of modules on the chart.**
The twisting sheaf is quasi-coherent, so a morphism out of its restriction to the chart is exactly
a map of the sections over `D₊(f)`, with no hypothesis at all on the target — which is what this
needs, the target being a direct image along a morphism that is neither quasi-compact nor
quasi-separated. -/
def chartRestrictHom (hf : f ∈ 𝒜 e) (he : 0 < e) (n : ℤ) :
    (twistM 𝒜 n).restrict (AlgebraicGeometry.Proj.awayι 𝒜 f hf he)
      ⟶ (ψ.pushLaurent n).restrict (AlgebraicGeometry.Proj.awayι 𝒜 f hf he) :=
  haveI : SheafOfModules.IsQuasicoherent (twistM 𝒜 n) :=
    Stacks.AlgebraicGeometry.TwistChartLocality.isQuasicoherent_twistingSheaf 𝒜 n
  Stacks.AlgebraicGeometry.ModuleLimits.restrictHomOfΓMap
    (AlgebraicGeometry.Proj.awayι 𝒜 f hf he) (chartΓMap 𝒜 ψ hf he n)

/-- **The chart morphism acts on the sections over `D₊(f)` by the chart datum.** -/
theorem chartRestrictHom_app_top (hf : f ∈ 𝒜 e) (he : 0 < e) (n : ℤ)
    (a : Γ(twistM 𝒜 n, AlgebraicGeometry.Proj.awayι 𝒜 f hf he ''ᵁ ⊤)) :
    (chartRestrictHom 𝒜 ψ hf he n).app ⊤ a = chartΓLinearMap 𝒜 ψ hf he n a :=
  have : SheafOfModules.IsQuasicoherent (twistM 𝒜 n) :=
    Stacks.AlgebraicGeometry.TwistChartLocality.isQuasicoherent_twistingSheaf 𝒜 n
  Stacks.AlgebraicGeometry.ModuleLimits.restrictHomOfΓMap_app_top
    (AlgebraicGeometry.Proj.awayι 𝒜 f hf he) (chartΓMap 𝒜 ψ hf he n) a

end Target

end Stacks.AlgebraicGeometry.ProjChartGradedTheta

end
