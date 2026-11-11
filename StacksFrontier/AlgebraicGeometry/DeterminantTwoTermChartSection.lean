module

public import StacksFrontier.AlgebraicGeometry.DeterminantTwoTermChartDeltaSection
public import StacksFrontier.AlgebraicGeometry.DeterminantTwoTermChartDetIso
import all StacksFrontier.AlgebraicGeometry.DeterminantTwoTermChartDeltaSection

/-!
# Elements of the determinant module, read as sections on an affine chart

Let `X` be a scheme and `L` a perfect object of `D(𝒪_X)` of Tor-amplitude in `[-1, 0]`. On every
affine open `V` of `X` the determinant `AlgebraicGeometry.DeterminantTwoTerm.chartDet` of `L` is
the sheaf associated with the determinant module `det(M_V)` of More on Algebra, Section 0FJI of
the chart complex `M_V`, transported to `V`. This file reads an arbitrary element `x` of `det(M_V)`
as a section on the chart of `V`, in the shape the glueing datum of
`StacksFrontier/AlgebraicGeometry/AffineOpensDirectedGlue.lean` consumes, and proves that **the
comparison isomorphisms of that glueing datum act on these sections as the comparison of
determinant modules** `AlgebraicGeometry.DeterminantTwoTerm.chartDetModuleIso`: for affine opens
`V ≤ W` the comparison carries the section of `ρ(x) = chartDetModuleIso (1 ⊗ x)` on `V` to the
restriction to `V` of the section of `x` on `W`.

This is the general form of
`AlgebraicGeometry.DeterminantTwoTerm.localAppFun_chartDetComp_chartDeltaSection`, which is the
case of the canonical element; the proof follows the same steps, with an arbitrary element in
place of the canonical one.

## Main definitions

* `AlgebraicGeometry.DeterminantTwoTerm.chartRestrictDet`: the comparison of determinant modules
  `det(M_W) → det(M_V)`, `x ↦ chartDetModuleIso (1 ⊗ x)`.
* `AlgebraicGeometry.DeterminantTwoTerm.chartSpecSec`: an element of `det(M_V)` as a global section
  of the determinant on `Spec Γ(X, V)`.
* `AlgebraicGeometry.DeterminantTwoTerm.chartTop`: the same, as a global section of the
  determinant on the open subscheme `V`.
* `AlgebraicGeometry.DeterminantTwoTerm.chartSection`: the same, as a section on the chart of `V`.

## Main results

* `AlgebraicGeometry.DeterminantTwoTerm.localAppFun_chartDetComp_chartSection`: the comparison of
  the glueing datum on these sections.
* `AlgebraicGeometry.DeterminantTwoTerm.chartSection_delta`: the section of the canonical element
  is `AlgebraicGeometry.DeterminantTwoTerm.chartDeltaSection`.

## References

* [Stacks Project, Lemma 36.39.1 (Tag 0FJX)](https://stacks.math.columbia.edu/tag/0FJX)
* [Stacks Project, Section 15.124 (Tag 0FJI)](https://stacks.math.columbia.edu/tag/0FJI)
* [Stacks Project, Lemma 26.7.3 (Tag 01I9)](https://stacks.math.columbia.edu/tag/01I9)
-/

@[expose] public noncomputable section

open CategoryTheory TwoTermDeterminant Opposite
open Stacks.SheafOfModules
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.DeterminantTwoTerm

variable {X : Scheme.{u}}

/-! ### The comparison of determinant modules as a map -/

/-- **The comparison of determinant modules along an inclusion of affine opens**, as a map
`det(M_W) → det(M_V)`: `x ↦ chartDetModuleIso (1 ⊗ x)`, semilinear over the restriction of
functions `Γ(X, W) ⟶ Γ(X, V)`. -/
def chartRestrictDet (L : PerfectTwoTermAmplitude X) {V W : X.affineOpens} (h : V ≤ W)
    (x : chartDetModule L W) : chartDetModule L V :=
  letI : Algebra Γ(X, (W.1 : X.Opens)) Γ(X, (V.1 : X.Opens)) :=
    (affineRestriction X h).hom.toAlgebra
  chartDetModuleIso L h (1 ⊗ₜ[Γ(X, (W.1 : X.Opens))] x)

/-! ### Elements as sections -/

/-- An element of the determinant module `det(M_V)`, as a global section of the determinant of `L`
on `Spec Γ(X, V)`, which is the sheaf associated with `det(M_V)`. -/
def chartSpecSec (L : PerfectTwoTermAmplitude X) (V : X.affineOpens) (x : chartDetModule L V) :
    Γ(chartDetSpec L V, ⊤) :=
  (tilde.toOpen (chartDetModule L V) ⊤).hom x

/-- An element of the determinant module `det(M_V)`, as a global section of the determinant of `L`
on the open subscheme `V`, read through
`AlgebraicGeometry.DeterminantTwoTerm.chartDetSpecRestrictIso`. -/
def chartTop (L : PerfectTwoTermAmplitude X) (V : X.affineOpens) (x : chartDetModule L V) :
    Γ(chartDet L V, ⊤) :=
  Scheme.Modules.Hom.app (chartDetSpecRestrictIso L V).hom ⊤
    ((chartDetSpec L V).val.map (homOfLE le_top).op (chartSpecSec L V x))

/-- **An element of the determinant module `det(M_V)`, read as a section on the chart of `V`.** -/
def chartSection (L : PerfectTwoTermAmplitude X) (V : X.affineOpens) (x : chartDetModule L V) :
    ToType (openSections (AffineOpensGlue.chart X V) (chartDet L V) (V.1 : X.Opens)) :=
  (chartDet L V).val.map (homOfLE le_top).op (chartTop L V x)

/-- The canonical element, read as a section on the chart, is
`AlgebraicGeometry.DeterminantTwoTerm.chartDeltaSection`. -/
theorem chartSection_delta {L : PerfectTwoTermAmplitude X} (hL : IsRankZeroOn L)
    (V : X.affineOpens) :
    chartSection L V (delta (chartComplex L V) (hL V)) = chartDeltaSection hL V :=
  rfl

/-! ### The comparison on the spectra -/

/-- **The chart comparison on the spectra carries the section of `x` to the section of its
comparison.** For affine opens `V ≤ W` of `X`, the identification
`AlgebraicGeometry.DeterminantTwoTerm.chartDetSpecRestrict` carries the global section of
`x ∈ det(M_W)` on the spectrum of `W`, restricted along the unit of the restriction adjunction, to
the global section of `chartRestrictDet L h x` on the spectrum of `V`. -/
private theorem chartDetSpecRestrict_hom_app_unit_sec (L : PerfectTwoTermAmplitude X)
    {V W : X.affineOpens} (h : V ≤ W) (x : chartDetModule L W) :
    Scheme.Modules.Hom.app (chartDetSpecRestrict L h).hom ⊤
        (Scheme.Modules.Hom.app ((Scheme.Modules.restrictAdjunction
          (Spec.map (affineRestriction X h))).unit.app (chartDetSpec L W)) ⊤
          (chartSpecSec L W x)) =
      chartSpecSec L V (chartRestrictDet L h x) := by
  have hkey := pullbackTildeIso_hom_app_unit_toOpen Γ(X, (W.1 : X.Opens))
    Γ(X, (V.1 : X.Opens)) (affineRestriction X h) (chartDetModule L W) x
  have e1 := twoIsoHom_app ((Scheme.Modules.restrictFunctorIsoPullback
      (Spec.map (affineRestriction X h))).app (chartDetSpec L W))
    (chartDetSpecPullbackIso L h) (⊤ : (Spec Γ(X, (V.1 : X.Opens))).Opens)
    (Scheme.Modules.Hom.app ((Scheme.Modules.restrictAdjunction
      (Spec.map (affineRestriction X h))).unit.app (chartDetSpec L W)) ⊤ (chartSpecSec L W x))
  have e2 := congrArg (fun z => Scheme.Modules.Hom.app (chartDetSpecPullbackIso L h).hom
      (⊤ : (Spec Γ(X, (V.1 : X.Opens))).Opens) z)
    (restrictFunctorIsoPullback_app_unit (Spec.map (affineRestriction X h))
      (chartDetSpec L W) (chartSpecSec L W x))
  have e3 := twoIsoHom_app ((pullbackTildeIso Γ(X, (W.1 : X.Opens)) Γ(X, (V.1 : X.Opens))
      (affineRestriction X h)).app (chartDetModule L W))
    ((tilde.functor Γ(X, (V.1 : X.Opens))).mapIso (chartDetModuleIso L h).toModuleIso)
    (⊤ : (Spec Γ(X, (V.1 : X.Opens))).Opens)
    (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackPushforwardAdjunction
      (Spec.map (affineRestriction X h))).unit.app (chartDetSpec L W)) ⊤ (chartSpecSec L W x))
  have e4 := congrArg (fun z => Scheme.Modules.Hom.app
      ((tilde.functor Γ(X, (V.1 : X.Opens))).mapIso (chartDetModuleIso L h).toModuleIso).hom
      (⊤ : (Spec Γ(X, (V.1 : X.Opens))).Opens) z) hkey
  exact e1.trans (e2.trans (e3.trans (e4.trans
    (app_tilde_toOpen Γ(X, (V.1 : X.Opens)) (chartDetModuleIso L h).toModuleIso.hom _))))

/-! ### The comparison of the glueing datum on the sections -/

/-- **Peeling the pushforward off the determinant on `V`** carries the section of `x` to the
section of `x`. -/
private theorem step_peelV_sec (L : PerfectTwoTermAmplitude X) (V : X.affineOpens)
    (x : chartDetModule L V) (U : ((V.1 : X.Opens) : Scheme.{u}).Opens) :
    Scheme.Modules.Hom.app (AffineOpensGlue.restrictPushforwardIso (chartDet L V)).hom U
        (globalRes (chartDet L V)
          ((V.1 : X.Opens).ι ⁻¹ᵁ ((V.1 : X.Opens).ι ''ᵁ U)) (chartTop L V x)) =
      globalRes (chartDet L V) U (chartTop L V x) :=
  (restrictPushforwardIso_hom_apply (chartDet L V) U _).trans
    (resSec_globalRes (chartDet L V)
      (le_of_eq ((V.1 : X.Opens).ι.preimage_image_eq U).symm) (chartTop L V x))

/-- **The chart comparison on the open subschemes carries the section of the comparison of `x` to
the section of `x`.** -/
private theorem step_restrict_sec (L : PerfectTwoTermAmplitude X) {V W : X.affineOpens}
    (h : V ≤ W) (x : chartDetModule L W) (U : ((V.1 : X.Opens) : Scheme.{u}).Opens) :
    Scheme.Modules.Hom.app (chartDetRestrictIso L h).hom U
        (globalRes (chartDet L V) U (chartTop L V (chartRestrictDet L h x))) =
      globalRes (chartDet L W) (X.homOfLE (AffineOpensGlue.coe_le_coe h) ''ᵁ U)
        (chartTop L W x) := by
  have hIs : Spec.map (affineRestriction X h) ''ᵁ (V.2.isoSpec.hom ''ᵁ U) ≤
      Spec.map (affineRestriction X h) ''ᵁ ⊤ :=
    (Spec.map (affineRestriction X h)).image_mono le_top
  have h3 : (V.2.isoSpec.hom ≫ Spec.map (affineRestriction X h)) ''ᵁ U ≤
      Spec.map (affineRestriction X h) ''ᵁ (V.2.isoSpec.hom ''ᵁ U) := le_of_eq (by simp)
  have h4 : (X.homOfLE (AffineOpensGlue.coe_le_coe h) ≫ W.2.isoSpec.hom) ''ᵁ U ≤
      (V.2.isoSpec.hom ≫ Spec.map (affineRestriction X h)) ''ᵁ U :=
    le_of_eq (by simp [isoSpec_hom_specMap_chartRestriction h])
  have h5 : W.2.isoSpec.hom ''ᵁ (X.homOfLE (AffineOpensGlue.coe_le_coe h) ''ᵁ U) ≤
      (X.homOfLE (AffineOpensGlue.coe_le_coe h) ≫ W.2.isoSpec.hom) ''ᵁ U := le_of_eq (by simp)
  have hB1 := app_restrict_globalRes V.2.isoSpec.hom (chartDetSpec L V)
    (chartDetSpecRestrictIso L V).hom U (chartSpecSec L V (chartRestrictDet L h x))
  have hinv := (inv_app_apply_eq (chartDetSpecRestrict L h) ⊤
    (Scheme.Modules.Hom.app ((Scheme.Modules.restrictAdjunction
      (Spec.map (affineRestriction X h))).unit.app (chartDetSpec L W)) ⊤ (chartSpecSec L W x))
    (chartSpecSec L V (chartRestrictDet L h x))
    (chartDetSpecRestrict_hom_app_unit_sec L h x)).trans
    (restrictAdjunction_unit_app_top (Spec.map (affineRestriction X h)) (chartDetSpec L W)
      (chartSpecSec L W x))
  have hf1 := (restrictFunctor_map_apply V.2.isoSpec.hom (chartDetSpecRestrict L h).inv U
      (globalRes (chartDetSpec L V) (V.2.isoSpec.hom ''ᵁ U)
        (chartSpecSec L V (chartRestrictDet L h x)))).trans
    ((app_resSec (chartDetSpecRestrict L h).inv
        (le_top : V.2.isoSpec.hom ''ᵁ U ≤ ⊤) (chartSpecSec L V (chartRestrictDet L h x))).trans
      ((congrArg (fun z => resSec (Scheme.Modules.restrict (chartDetSpec L W)
            (Spec.map (affineRestriction X h)))
            (le_top : V.2.isoSpec.hom ''ᵁ U ≤ ⊤) z) hinv).trans
        (restrict_resSec_globalRes (Spec.map (affineRestriction X h)) (chartDetSpec L W)
          (le_top : V.2.isoSpec.hom ''ᵁ U ≤ ⊤) hIs (chartSpecSec L W x))))
  have hf2 := (restrictFunctorComp_inv_apply V.2.isoSpec.hom
      (Spec.map (affineRestriction X h)) (chartDetSpec L W) U h3 _).trans
    (resSec_globalRes (chartDetSpec L W) h3 (chartSpecSec L W x))
  have hf3 := (restrictFunctorCongr_hom_apply (isoSpec_hom_specMap_chartRestriction h)
      (chartDetSpec L W) U h4 _).trans
    (resSec_globalRes (chartDetSpec L W) h4 (chartSpecSec L W x))
  have hf4 := (restrictFunctorComp_hom_apply (X.homOfLE (AffineOpensGlue.coe_le_coe h))
      W.2.isoSpec.hom
      (chartDetSpec L W) U h5 _).trans
    (resSec_globalRes (chartDetSpec L W) h5 (chartSpecSec L W x))
  have hf5 := (restrictFunctor_map_apply (X.homOfLE (AffineOpensGlue.coe_le_coe h))
      ((Scheme.Modules.restrictFunctorIsoPullback W.2.isoSpec.hom).hom.app
        (chartDetSpec L W)) U _).trans
    (app_restrict_globalRes W.2.isoSpec.hom (chartDetSpec L W)
      ((Scheme.Modules.restrictFunctorIsoPullback W.2.isoSpec.hom).hom.app (chartDetSpec L W))
      (X.homOfLE (AffineOpensGlue.coe_le_coe h) ''ᵁ U) (chartSpecSec L W x))
  refine Eq.trans (congrArg (fun z => Scheme.Modules.Hom.app (chartDetRestrictIso L h).hom U z)
    hB1.symm) ?_
  refine Eq.trans (comp_app_apply (chartDetSpecRestrictIso L V).hom
    (chartDetRestrictIso L h).hom U _).symm ?_
  refine Eq.trans (ConcreteCategory.congr_hom
    (congrArg (fun φ => Scheme.Modules.Hom.app φ U) (chartDetChase L h)) _) ?_
  refine Eq.trans (fiveCompApp _ _ _ _ _ U _) ?_
  rw [hf1, hf2, hf3, hf4]
  exact hf5

/-- **Peeling the pushforward off the determinant on `W`** carries the section of `x` to the
section of `x`. -/
private theorem step_peelLe_sec (L : PerfectTwoTermAmplitude X) {V W : X.affineOpens}
    (h : V ≤ W) (x : chartDetModule L W) (U : ((V.1 : X.Opens) : Scheme.{u}).Opens) :
    Scheme.Modules.Hom.app
        (AffineOpensGlue.restrictPushforwardLeIso (AffineOpensGlue.coe_le_coe h)
          (chartDet L W)).hom U
        (globalRes (chartDet L W)
          ((W.1 : X.Opens).ι ⁻¹ᵁ ((V.1 : X.Opens).ι ''ᵁ U)) (chartTop L W x)) =
      globalRes (chartDet L W) (X.homOfLE (AffineOpensGlue.coe_le_coe h) ''ᵁ U)
        (chartTop L W x) := by
  have hA : (X.homOfLE (AffineOpensGlue.coe_le_coe h) ≫ (W.1 : X.Opens).ι) ''ᵁ U ≤
      (V.1 : X.Opens).ι ''ᵁ U := le_of_eq (by simp only [Scheme.homOfLE_ι])
  have hB : (W.1 : X.Opens).ι ''ᵁ (X.homOfLE (AffineOpensGlue.coe_le_coe h) ''ᵁ U) ≤
      (X.homOfLE (AffineOpensGlue.coe_le_coe h) ≫ (W.1 : X.Opens).ι) ''ᵁ U :=
    le_of_eq (by rw [← Scheme.Hom.comp_image])
  have hg1 := (restrictFunctorCongr_inv_apply (X.homOfLE_ι (AffineOpensGlue.coe_le_coe h))
      ((Scheme.Modules.pushforward (W.1 : X.Opens).ι).obj (chartDet L W)) U hA _).trans
    (pushforward_resSec_globalRes (W.1 : X.Opens).ι (chartDet L W) hA (chartTop L W x))
  have hg2 := (restrictFunctorComp_hom_apply (X.homOfLE (AffineOpensGlue.coe_le_coe h))
      (W.1 : X.Opens).ι ((Scheme.Modules.pushforward (W.1 : X.Opens).ι).obj (chartDet L W))
      U hB _).trans
    (pushforward_resSec_globalRes (W.1 : X.Opens).ι (chartDet L W) hB (chartTop L W x))
  have hg3 := (restrictFunctor_mapIso_apply (X.homOfLE (AffineOpensGlue.coe_le_coe h))
      (AffineOpensGlue.restrictPushforwardIso (chartDet L W)) U _).trans
    ((restrictPushforwardIso_hom_apply (chartDet L W)
        (X.homOfLE (AffineOpensGlue.coe_le_coe h) ''ᵁ U) _).trans
      (resSec_globalRes (chartDet L W)
        (le_of_eq ((W.1 : X.Opens).ι.preimage_image_eq
          (X.homOfLE (AffineOpensGlue.coe_le_coe h) ''ᵁ U)).symm) (chartTop L W x)))
  refine Eq.trans (threeIsoHom_app
    ((Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι (AffineOpensGlue.coe_le_coe h))).symm.app
      ((Scheme.Modules.pushforward (W.1 : X.Opens).ι).obj (chartDet L W)))
    ((Scheme.Modules.restrictFunctorComp (X.homOfLE (AffineOpensGlue.coe_le_coe h))
      (W.1 : X.Opens).ι).app
      ((Scheme.Modules.pushforward (W.1 : X.Opens).ι).obj (chartDet L W)))
    ((Scheme.Modules.restrictFunctor (X.homOfLE (AffineOpensGlue.coe_le_coe h))).mapIso
      (AffineOpensGlue.restrictPushforwardIso (chartDet L W))) U _) ?_
  refine Eq.trans (congrArg (fun z => Scheme.Modules.Hom.app
      ((Scheme.Modules.restrictFunctor (X.homOfLE (AffineOpensGlue.coe_le_coe h))).mapIso
        (AffineOpensGlue.restrictPushforwardIso (chartDet L W))).hom U
      (Scheme.Modules.Hom.app ((Scheme.Modules.restrictFunctorComp
        (X.homOfLE (AffineOpensGlue.coe_le_coe h)) (W.1 : X.Opens).ι).hom.app
          ((Scheme.Modules.pushforward (W.1 : X.Opens).ι).obj (chartDet L W))) U z)) hg1) ?_
  refine Eq.trans (congrArg (fun z => Scheme.Modules.Hom.app
      ((Scheme.Modules.restrictFunctor (X.homOfLE (AffineOpensGlue.coe_le_coe h))).mapIso
        (AffineOpensGlue.restrictPushforwardIso (chartDet L W))).hom U z) hg2) ?_
  exact hg3

/-- **The comparison of the glueing datum carries the section of the comparison of `x` to the
section of `x`**, over an arbitrary open of the smaller chart. -/
private theorem chartDetComp_hom_app_sec (L : PerfectTwoTermAmplitude X) {V W : X.affineOpens}
    (h : V ≤ W) (x : chartDetModule L W) (U : ((V.1 : X.Opens) : Scheme.{u}).Opens) :
    Scheme.Modules.Hom.app (chartDetComp L h).hom U
        (globalRes (chartDet L V)
          ((V.1 : X.Opens).ι ⁻¹ᵁ ((V.1 : X.Opens).ι ''ᵁ U))
          (chartTop L V (chartRestrictDet L h x))) =
      globalRes (chartDet L W)
        ((W.1 : X.Opens).ι ⁻¹ᵁ ((V.1 : X.Opens).ι ''ᵁ U)) (chartTop L W x) := by
  have hmid := (congrArg (fun z => Scheme.Modules.Hom.app (chartDetRestrictIso L h).hom U z)
    (step_peelV_sec L V (chartRestrictDet L h x) U)).trans (step_restrict_sec L h x U)
  have hlast := symm_hom_app_apply_eq
    (AffineOpensGlue.restrictPushforwardLeIso (AffineOpensGlue.coe_le_coe h) (chartDet L W)) U
    (globalRes (chartDet L W)
      ((W.1 : X.Opens).ι ⁻¹ᵁ ((V.1 : X.Opens).ι ''ᵁ U)) (chartTop L W x))
    (globalRes (chartDet L W) (X.homOfLE (AffineOpensGlue.coe_le_coe h) ''ᵁ U) (chartTop L W x))
    (step_peelLe_sec L h x U)
  rw [chartDetComp_eq]
  refine Eq.trans (threeIsoHom_app (AffineOpensGlue.restrictPushforwardIso (chartDet L V))
    (chartDetRestrictIso L h)
    (AffineOpensGlue.restrictPushforwardLeIso (AffineOpensGlue.coe_le_coe h) (chartDet L W)).symm U
    (globalRes (chartDet L V)
      ((V.1 : X.Opens).ι ⁻¹ᵁ ((V.1 : X.Opens).ι ''ᵁ U))
      (chartTop L V (chartRestrictDet L h x)))) ?_
  exact (congrArg (fun z => Scheme.Modules.Hom.app
    (AffineOpensGlue.restrictPushforwardLeIso (AffineOpensGlue.coe_le_coe h)
      (chartDet L W)).symm.hom U z) hmid).trans hlast

/-- The restriction from `W` to `V` of the section of `x` on the chart of `W` is the restriction
to the preimage of `V` in `W` of the global section of `x` there. -/
private theorem chartSection_restrict (L : PerfectTwoTermAmplitude X) {V W : X.affineOpens}
    (h : V ≤ W) (x : chartDetModule L W) :
    ((Scheme.Modules.pushforward (AffineOpensGlue.chart X W)).obj (chartDet L W)).val.map
        (homOfLE (show (V.1 : X.Opens) ≤ (W.1 : X.Opens) from h)).op
        (chartSection L W x) =
      globalRes (chartDet L W) ((W.1 : X.Opens).ι ⁻¹ᵁ (V.1 : X.Opens)) (chartTop L W x) :=
  (resSec_eq ((Scheme.Modules.pushforward (W.1 : X.Opens).ι).obj (chartDet L W))
      (homOfLE (show (V.1 : X.Opens) ≤ (W.1 : X.Opens) from h)).op
      (show (V.1 : X.Opens) ≤ (W.1 : X.Opens) from h) (chartSection L W x)).trans
    (pushforward_resSec_globalRes (W.1 : X.Opens).ι (chartDet L W)
      (show (V.1 : X.Opens) ≤ (W.1 : X.Opens) from h) (chartTop L W x))

/-- The section of `y` on the chart of `V`, restricted along the image of the preimage of `V`, is
the global section of `y` restricted to that preimage. -/
private theorem resSec_chartSection (L : PerfectTwoTermAmplitude X) (V : X.affineOpens)
    (y : chartDetModule L V)
    (h₁ : (V.1 : X.Opens).ι ''ᵁ ((V.1 : X.Opens).ι ⁻¹ᵁ (V.1 : X.Opens)) ≤ (V.1 : X.Opens)) :
    resSec ((Scheme.Modules.pushforward (V.1 : X.Opens).ι).obj (chartDet L V)) h₁
        (chartSection L V y) =
      globalRes (chartDet L V)
        ((V.1 : X.Opens).ι ⁻¹ᵁ ((V.1 : X.Opens).ι ''ᵁ ((V.1 : X.Opens).ι ⁻¹ᵁ (V.1 : X.Opens))))
        (chartTop L V y) :=
  pushforward_resSec_globalRes (V.1 : X.Opens).ι (chartDet L V) h₁ (chartTop L V y)

/-- The global section of `x` on `W`, restricted to the preimage of the image of the preimage of
`V` and then back to the preimage of `V`, is its restriction to the preimage of `V`. -/
private theorem resSec_chartTop (L : PerfectTwoTermAmplitude X) {V W : X.affineOpens}
    (x : chartDetModule L W)
    (h₂ : (V.1 : X.Opens) ≤ (V.1 : X.Opens).ι ''ᵁ ((V.1 : X.Opens).ι ⁻¹ᵁ (V.1 : X.Opens))) :
    resSec ((Scheme.Modules.pushforward (W.1 : X.Opens).ι).obj (chartDet L W)) h₂
        (globalRes (chartDet L W)
          ((W.1 : X.Opens).ι ⁻¹ᵁ
            ((V.1 : X.Opens).ι ''ᵁ ((V.1 : X.Opens).ι ⁻¹ᵁ (V.1 : X.Opens))))
          (chartTop L W x)) =
      globalRes (chartDet L W) ((W.1 : X.Opens).ι ⁻¹ᵁ (V.1 : X.Opens)) (chartTop L W x) :=
  pushforward_resSec_globalRes (W.1 : X.Opens).ι (chartDet L W) h₂ (chartTop L W x)

/-- `AlgebraicGeometry.DeterminantTwoTerm.chartDetComp_hom_app_sec` at the open `W.ι ⁻¹ᵁ V`, with
the two restriction maps of `AlgebraicGeometry.localApp` collapsed. -/
private theorem localAppFun_chartSection_aux (L : PerfectTwoTermAmplitude X)
    {V W : X.affineOpens} (h : V ≤ W) (x : chartDetModule L W) :
    localAppFun (chartDetComp L h).hom (V.1 : X.Opens) le_rfl
        (chartSection L V (chartRestrictDet L h x)) =
      globalRes (chartDet L W) ((W.1 : X.Opens).ι ⁻¹ᵁ (V.1 : X.Opens)) (chartTop L W x) := by
  have h₁ : (V.1 : X.Opens).ι ''ᵁ ((V.1 : X.Opens).ι ⁻¹ᵁ (V.1 : X.Opens)) ≤ (V.1 : X.Opens) :=
    Scheme.Hom.image_preimage_le _ _
  have h₂ : (V.1 : X.Opens) ≤ (V.1 : X.Opens).ι ''ᵁ ((V.1 : X.Opens).ι ⁻¹ᵁ (V.1 : X.Opens)) :=
    le_of_eq (Stacks.AlgebraicGeometry.ModuleLimits.image_preimage_of_le
      (le_refl (V.1 : X.Opens))).symm
  refine Eq.trans (localAppFun_eq (chartDetComp L h).hom
    (chartSection L V (chartRestrictDet L h x)) h₁ h₂) ?_
  refine Eq.trans (congrArg (fun z => resSec
      ((Scheme.Modules.pushforward (W.1 : X.Opens).ι).obj (chartDet L W)) h₂
      (Scheme.Modules.Hom.app (chartDetComp L h).hom ((V.1 : X.Opens).ι ⁻¹ᵁ (V.1 : X.Opens)) z))
    (resSec_chartSection L V (chartRestrictDet L h x) h₁)) ?_
  refine Eq.trans (congrArg (fun z => resSec
      ((Scheme.Modules.pushforward (W.1 : X.Opens).ι).obj (chartDet L W)) h₂ z)
    (chartDetComp_hom_app_sec L h x ((V.1 : X.Opens).ι ⁻¹ᵁ (V.1 : X.Opens)))) ?_
  exact resSec_chartTop L x h₂

/-- **The comparisons of the glueing datum act on sections as the comparison of determinant
modules.** Let `X` be a scheme, `L` a perfect object of `D(𝒪_X)` of Tor-amplitude in `[-1, 0]`,
`V ≤ W` affine opens of `X` and `x` an element of the determinant module of the chart complex on
`W`. The comparison `AlgebraicGeometry.DeterminantTwoTerm.chartDetComp` carries the section on the
chart of `V` of `chartRestrictDet L h x` to the restriction to `V` of the section of `x` on the
chart of `W`. -/
theorem localAppFun_chartDetComp_chartSection (L : PerfectTwoTermAmplitude X)
    {V W : X.affineOpens} (h : V ≤ W) (x : chartDetModule L W) :
    localAppFun (chartDetComp L h).hom (V.1 : X.Opens) le_rfl
        (chartSection L V (chartRestrictDet L h x)) =
      ((Scheme.Modules.pushforward (AffineOpensGlue.chart X W)).obj (chartDet L W)).val.map
        (homOfLE (show (V.1 : X.Opens) ≤ (W.1 : X.Opens) from h)).op
        (chartSection L W x) :=
  (localAppFun_chartSection_aux L h x).trans (chartSection_restrict L h x).symm

end AlgebraicGeometry.DeterminantTwoTerm

end
