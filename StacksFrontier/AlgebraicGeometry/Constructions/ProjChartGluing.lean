module

public import StacksFrontier.AlgebraicGeometry.Constructions.MorphismToProjRatios
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjSectionsUniqueness
public import StacksFrontier.AlgebraicGeometry.SectionExtension.Basic

/-!
# The preimages of the standard opens under the glued morphism into `Proj`

Let `A = ⨁_{n ≥ 0} 𝒜 n` be a graded ring, `X = Proj(A)`, `d > 0`, and let
`U_d = ⋃_{f ∈ 𝒜 d} D₊(f) ⊆ X`. Let `Y` be a scheme, `L` an invertible `𝒪_Y`-module and
`ψ : A^{(d)} → Γ_*(Y, L)` a graded map, given as
`Stacks.AlgebraicGeometry.ProjChartFromRatios.VeroneseSections`. For `f ∈ 𝒜 d` with `s = ψ(f)`
there is a chart `Y_s ⟶ D₊(f) ⊆ U_d`. This file proves that a morphism `φ : Y ⟶ U_d` that
restricts to these charts on a family of opens covering `Y` satisfies

  `φ ⁻¹ᵁ D₊(e) = Y_{ψ(e)}` for every `e ∈ 𝒜 d`,

and computes the effect on sections of a morphism that restricts to a chart.

## Main results

* `Stacks.AlgebraicGeometry.ProjChartGluing.chartToProj_preimage_basicOpen`: the preimage of
  `D₊(g)` under a chart is the basic open of the value of the chart's ring map on the fraction
  `g^d/f^d`, Mathlib's `HomogeneousLocalization.Away.isLocalizationElem`.
* `Stacks.AlgebraicGeometry.ProjChartGluing.lift_isLocalizationElem`: that value, read off the
  degreewise data as `c_d(g^d)`.
* `Stacks.AlgebraicGeometry.ProjChartGluing.appLE_eq_lift` and
  `Stacks.AlgebraicGeometry.ProjChartGluing.appLE_awayToSection`: a morphism that restricts to the
  chart induces, on `Γ(Proj A, D₊(f))`, the chart's ring map `A_{(f)} →+* Γ(X, U)`, read through
  `AlgebraicGeometry.Proj.basicOpenIsoAway`; evaluated on the section of a fraction `a/f^n` it is
  the value of that ring map there.
* `Stacks.AlgebraicGeometry.ProjChartGluing.nonvanishingOpen_pow_eq`: `Y_{s^n} = Y_s` for `n > 0`.
* `Stacks.AlgebraicGeometry.ProjChartGluing.chartToProj_preimage_basicOpen_eq_inf`: the preimage
  of `D₊(g)` under the chart of `f` over `W` is `Y_{ψ(g)} ⊓ W`.
* `Stacks.AlgebraicGeometry.ProjChartGluing.preimage_basicOpen_eq_nonvanishingOpen`:
  `φ ⁻¹ᵁ D₊(e) = Y_{ψ(e)}`.

## References

* [Stacks Project, Tag 01N8](https://stacks.math.columbia.edu/tag/01N8)
* [Stacks Project, Section 01N4](https://stacks.math.columbia.edu/tag/01N4)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry
open AlgebraicGeometry.Proj (degreeOpen)
open HomogeneousLocalization
open Stacks.TensorPowers (natTensorPow)
open Stacks.TensorPowerTrivialize (resTop)
open Stacks.NonvanishingOpen (nonvanishingOpen)

namespace Stacks.AlgebraicGeometry.ProjChartGluing

universe u w

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso Stacks.SheafInternalHom.isLocalization_sheafify
  Stacks.SheafInternalHom.monoidalCategory Stacks.SheafInternalHom.sheafifyMonoidal
  Stacks.SheafInternalHom.braidedCategory Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

/-! ### The preimage of a standard open under one chart -/

section OneChart

open Stacks.MorphismToProj

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜] {d : ℕ} {f : A} {hf : f ∈ 𝒜 d}
  {X : Scheme.{u}} {U : X.Opens}

/-- For `f` and `g` homogeneous of the same positive degree `d`, the preimage of the standard open
`D₊(g)` under the chart `U ⟶ Proj A` attached to a family of homogeneous ratios for `f` is the
basic open of the value of the induced ring map on the fraction `g^d/f^d`. -/
theorem chartToProj_preimage_basicOpen (R : HomogeneousRatios 𝒜 hf ↥Γ(X, U)) (hd : 0 < d)
    {g : A} (hg : g ∈ 𝒜 d) :
    R.chartToProj hd ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 g =
      U.ι ⁻¹ᵁ X.basicOpen (R.lift hd (Away.isLocalizationElem hf hg)) := by
  rw [HomogeneousRatios.chartToProj, Scheme.Hom.comp_preimage,
    AlgebraicGeometry.Proj.awayι_preimage_basicOpen (f_deg := hf) (hm := hd) (g_deg := hg)
      (hm' := hd),
    HomogeneousRatios.toSpecAway]
  exact (Scheme.Hom.comp_preimage _ _ _).trans
    (Scheme.Opens.toSpecΓ_preimage_basicOpen U (R.lift hd (Away.isLocalizationElem hf hg)))

/-- The value of the induced ring map on the fraction `g^d/f^d` is the degreewise datum `c_d`
evaluated on `g^d`. -/
theorem lift_isLocalizationElem (R : HomogeneousRatios 𝒜 hf ↥Γ(X, U)) (hd : 0 < d)
    {g : A} (hg : g ∈ 𝒜 d) :
    R.lift hd (Away.isLocalizationElem hf hg) =
      R.toFun d ⟨g ^ d, HomogeneousRatios.pow_mem hg d⟩ :=
  R.lift_mk hd d (g ^ d) _ _ rfl

/-- If a morphism `Φ : X ⟶ Proj A` restricts on `U` to the chart attached to a family of
homogeneous ratios, then the ring map `Γ(Proj A, D₊(f)) ⟶ Γ(X, U)` it induces is the chart's ring
map `A_{(f)} →+* Γ(X, U)`, read through the identification
`AlgebraicGeometry.Proj.basicOpenIsoAway` of `A_{(f)}` with `Γ(Proj A, D₊(f))`. -/
theorem appLE_eq_lift (R : HomogeneousRatios 𝒜 hf ↥Γ(X, U)) (hd : 0 < d) {Φ : X ⟶ Proj 𝒜}
    (hΦ : U.ι ≫ Φ = R.chartToProj hd) (hle : U ≤ Φ ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 f) :
    Φ.appLE (AlgebraicGeometry.Proj.basicOpen 𝒜 f) U hle =
      (AlgebraicGeometry.Proj.basicOpenIsoAway 𝒜 f hf hd).inv ≫
        CommRingCat.ofHom (R.lift hd) := by
  have hres : Φ.resLE (AlgebraicGeometry.Proj.basicOpen 𝒜 f) U hle = R.chart hd := by
    rw [← cancel_mono (AlgebraicGeometry.Proj.basicOpen 𝒜 f).ι, Scheme.Hom.resLE_comp_ι, hΦ]
    exact (R.chart_ι hd).symm
  have h2 : (R.chart hd).appTop =
      (AlgebraicGeometry.Proj.basicOpen 𝒜 f).topIso.hom ≫
        Φ.appLE (AlgebraicGeometry.Proj.basicOpen 𝒜 f) U hle ≫ U.topIso.inv := by
    rw [← hres]
    exact Scheme.Hom.resLE_app_top ..
  have hts : R.toSpecAway hd =
      R.chart hd ≫ (AlgebraicGeometry.Proj.basicOpenIsoSpec 𝒜 f hf hd).hom := by
    rw [HomogeneousRatios.chart, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have h3 : AlgebraicGeometry.Proj.awayToSection 𝒜 f ≫
        ((AlgebraicGeometry.Proj.basicOpen 𝒜 f).topIso.inv ≫ (R.chart hd).appTop) =
      CommRingCat.ofHom (R.lift hd) ≫ U.topIso.inv := by
    rw [← R.toSpecAway_appTop hd, hts, Scheme.Hom.comp_appTop,
      AlgebraicGeometry.Proj.basicOpenIsoSpec_hom,
      show (AlgebraicGeometry.Proj.basicOpenToSpec 𝒜 f).appTop =
          (Scheme.ΓSpecIso _).hom ≫ AlgebraicGeometry.Proj.awayToSection 𝒜 f ≫
            (AlgebraicGeometry.Proj.basicOpen 𝒜 f).topIso.inv from
        AlgebraicGeometry.Proj.basicOpenToSpec_app_top 𝒜 f]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  have h4 : (AlgebraicGeometry.Proj.basicOpen 𝒜 f).topIso.inv ≫ (R.chart hd).appTop =
      (AlgebraicGeometry.Proj.basicOpenIsoAway 𝒜 f hf hd).inv ≫
        CommRingCat.ofHom (R.lift hd) ≫ U.topIso.inv :=
    (Iso.eq_inv_comp _).mpr (by rwa [AlgebraicGeometry.Proj.basicOpenIsoAway_hom])
  have h5 : Φ.appLE (AlgebraicGeometry.Proj.basicOpen 𝒜 f) U hle =
      (AlgebraicGeometry.Proj.basicOpen 𝒜 f).topIso.inv ≫ (R.chart hd).appTop ≫
        U.topIso.hom := by
    rw [h2]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  rw [h5, ← Category.assoc, h4]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- If a morphism `Φ : X ⟶ Proj A` restricts on `U` to the chart attached to a family of
homogeneous ratios, then the value of the induced ring map `Γ(Proj A, D₊(f)) ⟶ Γ(X, U)` on the
section `AlgebraicGeometry.Proj.awayToSection` of a fraction `a/f^n` is the value of the chart's
ring map on that fraction. -/
theorem appLE_awayToSection (R : HomogeneousRatios 𝒜 hf ↥Γ(X, U)) (hd : 0 < d) {Φ : X ⟶ Proj 𝒜}
    (hΦ : U.ι ≫ Φ = R.chartToProj hd) (hle : U ≤ Φ ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 f)
    (u : Away 𝒜 f) :
    Φ.appLE (AlgebraicGeometry.Proj.basicOpen 𝒜 f) U hle
        (AlgebraicGeometry.Proj.awayToSection 𝒜 f u) = R.lift hd u := by
  rw [appLE_eq_lift R hd hΦ hle, CategoryTheory.comp_apply]
  refine congrArg (R.lift hd) ?_
  rw [← AlgebraicGeometry.Proj.basicOpenIsoAway_hom 𝒜 f hf hd, ← CategoryTheory.comp_apply]
  exact ConcreteCategory.congr_hom
    (AlgebraicGeometry.Proj.basicOpenIsoAway 𝒜 f hf hd).hom_inv_id u

end OneChart

/-! ### The chart of `f`, and the standard open of another element -/

section Psi

open Stacks.AlgebraicGeometry.ProjChartFromRatios
open Stacks.AlgebraicGeometry.ProjChartFromRatios.VeroneseSections

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜] {d : ℕ} {Y : Scheme.{u}} {L : Y.Modules}
  [Stacks.Ample.IsInvertibleModule Y L] (ψ : VeroneseSections 𝒜 d L) {f : A}

/-- The nonvanishing open of a positive power `ψ(f^n)` of the section `ψ(f)` is that of `ψ(f)`
itself. -/
theorem nonvanishingOpen_pow_eq (hf : f ∈ 𝒜 d) {n : ℕ} (hn : 0 < n) :
    nonvanishingOpen Y (natTensorPow L n) (ψ.pow hf n) =
      nonvanishingOpen Y (natTensorPow L 1) (ψ.pow hf 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  refine le_antisymm ?_ (ψ.le_nonvanishingOpen_pow hf _)
  have h := nonvanishingOpen_mulSections L (ψ.pow hf m) (ψ.pow hf 1)
  rw [ψ.mulSections_pow hf m 1] at h
  exact h.le.trans inf_le_right

variable (hd : 0 < d) (hf : f ∈ 𝒜 d) {W : Y.Opens}
  (hW : W ≤ nonvanishingOpen Y (natTensorPow L 1) (ψ.pow hf 1))

/-- The value of the chart's ring map on the fraction `g^d/f^d` is the ratio `ψ(g^d)/ψ(f^d)`. -/
theorem lift_isLocalizationElem_eq_ratio {g : A} (hg : g ∈ 𝒜 d) :
    (ψ.homogeneousRatios hf hW).lift hd (Away.isLocalizationElem hf hg) =
      ψ.ratio hf hW d (ψ.pow hg d) := by
  rw [lift_isLocalizationElem _ hd hg]
  exact congrArg (ψ.ratio hf hW d) (ψ.toFun_eq_pow hg d _ rfl)

/-- The preimage of the standard open `D₊(g)` under the chart of `f` over `W` is
`Y_{ψ(g)} ⊓ W`. -/
theorem chartToProj_preimage_basicOpen_eq_inf {g : A} (hg : g ∈ 𝒜 d) :
    (ψ.homogeneousRatios hf hW).chartToProj hd ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 g =
      W.ι ⁻¹ᵁ (nonvanishingOpen Y (natTensorPow L 1) (ψ.pow hg 1) ⊓ W) := by
  rw [chartToProj_preimage_basicOpen _ hd hg, lift_isLocalizationElem_eq_ratio ψ hd hf hW hg,
    ← Stacks.SectionExtension.nonvanishingOpen_inf_eq_basicOpen (ψ.pow hf d) (ψ.pow hg d)
      (ψ.le_nonvanishingOpen hf hW d) _ (ψ.resTop_eq_ratio_smul hf hW d (ψ.pow hg d)),
    nonvanishingOpen_pow_eq ψ hg hd]

end Psi

/-! ### The preimages under the glued morphism -/

section Glued

open Stacks.AlgebraicGeometry.MorphismsIntoProj
open Stacks.AlgebraicGeometry.ProjChartFromRatios
open Stacks.AlgebraicGeometry.ProjChartFromRatios.VeroneseSections

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {d : ℕ} {Y : Scheme.{u}} {L : Y.Modules}
  [Stacks.Ample.IsInvertibleModule Y L]

/-- Let `φ : Y ⟶ U_d` restrict, on each member `W g` of a family of opens covering `Y` with
`W g ⊆ Y_{ψ(g)}`, to the chart of `g` there. Then `φ ⁻¹ᵁ D₊(e) = Y_{ψ(e)}` for every
`e ∈ 𝒜 d`. -/
theorem preimage_basicOpen_eq_nonvanishingOpen (hd : 0 < d) (ψ : VeroneseSections 𝒜 d L)
    {φ : Y ⟶ (degreeOpen 𝒜 d).toScheme} {W : 𝒜 d → Y.Opens}
    (hWle : ∀ g : 𝒜 d, W g ≤ nonvanishingOpen Y (natTensorPow L 1) (ψ.pow g.2 1))
    (hcover : ⨆ g : 𝒜 d, W g = ⊤)
    (hglue : ∀ g : 𝒜 d, (W g).ι ≫ φ = ψ.toDegreeOpen g.2 (hWle g) hd) (e : 𝒜 d) :
    toProj 𝒜 φ ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 (e : A) =
      nonvanishingOpen Y (natTensorPow L 1) (ψ.pow e.2 1) := by
  have key : ∀ (g : 𝒜 d) (y : Y), y ∈ W g →
      ((y ∈ toProj 𝒜 φ ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 (e : A)) ↔
        y ∈ nonvanishingOpen Y (natTensorPow L 1) (ψ.pow e.2 1)) := by
    intro g y hyg
    have hc : (W g).ι ≫ toProj 𝒜 φ =
        (ψ.homogeneousRatios g.2 (hWle g)).chartToProj hd := by
      rw [show (W g).ι ≫ toProj 𝒜 φ = ((W g).ι ≫ φ) ≫ (degreeOpen 𝒜 d).ι from
        (Category.assoc _ _ _).symm, hglue g]
      exact (ψ.homogeneousRatios g.2 (hWle g)).toProj_toDegreeOpen hd
    have hopen : (W g).ι ⁻¹ᵁ (toProj 𝒜 φ ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 (e : A)) =
        (W g).ι ⁻¹ᵁ (nonvanishingOpen Y (natTensorPow L 1) (ψ.pow e.2 1) ⊓ W g) := by
      rw [← Scheme.Hom.comp_preimage, hc,
        chartToProj_preimage_basicOpen_eq_inf ψ hd g.2 (hWle g) e.2]
    have h1 : (⟨y, hyg⟩ : (W g).toScheme) ∈
          (W g).ι ⁻¹ᵁ (toProj 𝒜 φ ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 (e : A)) ↔
        (⟨y, hyg⟩ : (W g).toScheme) ∈
          (W g).ι ⁻¹ᵁ (nonvanishingOpen Y (natTensorPow L 1) (ψ.pow e.2 1) ⊓ W g) :=
      hopen ▸ Iff.rfl
    exact ⟨fun hy ↦ (h1.mp hy).1, fun hy ↦ h1.mpr ⟨hy, hyg⟩⟩
  refine Opens.ext (Set.ext fun y ↦ ?_)
  obtain ⟨g, hyg⟩ := Opens.mem_iSup.mp (hcover ▸ (Opens.mem_top y : y ∈ (⊤ : Y.Opens)))
  exact key g y hyg

end Glued

end Stacks.AlgebraicGeometry.ProjChartGluing

end
