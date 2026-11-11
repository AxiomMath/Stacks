module

public import StacksFrontier.Examples.Spaces.CurveFamilyNotScheme.Blowup.ExceptionalOrder
public import StacksFrontier.Examples.Spaces.CurveFamilyNotScheme.Blowup.Regular
public import StacksFrontier.AlgebraicGeometry.Blowup.RegularSurfaceBlowupGlobal
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.Difference
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierComplement
public import StacksFrontier.AlgebraicGeometry.Divisors.LocallyPrincipalLowDimensionalPoint
public import StacksFrontier.AlgebraicGeometry.Divisors.PrincipalSlice
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.EquationsBaseChange
public import StacksFrontier.AlgebraicGeometry.Curves.InseparableGenusChangeFunctionField
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.IdealSheafStalk
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.ExceptionalFibreGlobal
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.NormalPosition.Family
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.NormalPosition.OffFibre
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.StrictTransformSupport
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.CurveStrictTransform
import all StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.CurveStrictTransform

/-!
# The strict transform of a regular curve through the centre of a point blowup

Let `Y` be a regular Noetherian scheme of dimension two, `y` a closed point with
two-dimensional local ring, `π : Z ⟶ Y` the blowup at `y` with exceptional divisor `E`, and let
`Y₀ ⊆ Y` be an integral regular effective Cartier divisor through `y`, cut out by a global
function `t` with `t ∈ 𝔪_y \ 𝔪_y²`. This file proves the facts about the strict transform `C` of
`Y₀` that the construction of [Stacks, Tag 0D5E] uses:

* `C` is an effective Cartier divisor whose support is the closure of `π⁻¹(Y₀ ∖ {y})`;
* the total transform is `E + C`: `π⁻¹(Y₀) = E · C` as ideal sheaves;
* `π` restricts to an isomorphism `C ≅ Y₀`.

## Main definitions

* `Stacks.Examples.CurveFamilyNotScheme.strictTransformIdeal`: the ideal sheaf of `C`.
* `Stacks.Examples.CurveFamilyNotScheme.strictTransformToFibre`: the morphism `C ⟶ Y₀`.

## Main results

* `Stacks.Examples.CurveFamilyNotScheme.coe_support_strictTransformIdeal`: the support of `C` is
  `Stacks.Examples.CurveFamilyNotScheme.strictTransformSet`.
* `Stacks.Examples.CurveFamilyNotScheme.isEffectiveCartierDivisor_strictTransformIdeal`.
* `Stacks.Examples.CurveFamilyNotScheme.exceptionalIdeal_mul_strictTransformIdeal`: `E · C` is
  the inverse image of `Y₀`.
* `Stacks.Examples.CurveFamilyNotScheme.isIso_strictTransformToFibre`.

## Implementation notes

The strict transform is the library's `AlgebraicGeometry.transformIdeal`. The inclusion
`π⁻¹Y₀ ≤ E · C` holds stalkwise (the stalkwise computation of
`AlgebraicGeometry.CurveStrictTransform`); writing `π⁻¹Y₀ = E · C · K`, the cofactor `K` is
locally principal and supported in `E`. If `K` were not the unit ideal it would have a point of
local dimension at most one, which on `E` is only the generic point of `E`; then `K ≤ E` and
`π⁻¹Y₀ ≤ E²`, contradicting
`Stacks.Examples.CurveFamilyNotScheme.not_comap_le_exceptionalIdeal_sq`.

## References

* [Stacks Project, Tag 0D5E](https://stacks.math.columbia.edu/tag/0D5E)
* [Stacks Project, Tag 0BI7](https://stacks.math.columbia.edu/tag/0BI7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing
open Stacks.Divisors (IsEffectiveCartierDivisor)

universe u

namespace Stacks.Examples.CurveFamilyNotScheme

variable {Y : Scheme.{u}} (y : Y) (hy : IsClosed ({y} : Set Y))

/-- The ideal sheaf of the strict transform of a closed subscheme `Y₀ ⊆ Y` on the blowup at
`y`. -/
abbrev strictTransformIdeal (Y₀ : Y.IdealSheafData) : (pointBlowup y hy).IdealSheafData :=
  transformIdeal Y₀ y hy

/-- **The support of the strict transform is the closure of the inverse image of `Y₀ ∖ {y}`.** -/
theorem coe_support_strictTransformIdeal [IsNoetherian Y] (Y₀ : Y.IdealSheafData) :
    ((strictTransformIdeal y hy Y₀).support : Set (pointBlowup y hy)) =
      strictTransformSet y hy (Y₀.support : Set Y) := by
  rw [strictTransformSet, Set.preimage_sdiff]
  exact Stacks.ResolutionOfSurfaces.coe_support_transformIdeal Y₀ y hy

/-- The comparison morphism of the strict transform with its scheme-theoretic image is an
isomorphism. -/
theorem isIso_toImage_transformToBlowUp (Y₀ : Y.IdealSheafData) :
    IsIso (transformToBlowUp Y₀ y hy).toImage := by
  have := isClosedImmersion_transformToBlowUp Y₀ y hy
  infer_instance

/-- The closed subscheme cut out by the strict transform ideal is the strict transform of
`AlgebraicGeometry.transform`. -/
@[no_expose]
def strictTransformSubschemeIso (Y₀ : Y.IdealSheafData) :
    (strictTransformIdeal y hy Y₀).subscheme ≅ transform Y₀ y hy := by
  have hiso : IsIso (transformToBlowUp Y₀ y hy).toImage := isIso_toImage_transformToBlowUp y hy Y₀
  exact (@asIso _ _ _ _ (transformToBlowUp Y₀ y hy).toImage hiso).symm

/-- `strictTransformSubschemeIso` lies over the blowup. -/
@[reassoc]
theorem strictTransformSubschemeIso_hom_comp (Y₀ : Y.IdealSheafData) :
    (strictTransformSubschemeIso y hy Y₀).hom ≫ transformToBlowUp Y₀ y hy =
      (strictTransformIdeal y hy Y₀).subschemeι := by
  have hiso := isIso_toImage_transformToBlowUp y hy Y₀
  change inv (transformToBlowUp Y₀ y hy).toImage ≫ transformToBlowUp Y₀ y hy =
    (transformToBlowUp Y₀ y hy).imageι
  rw [IsIso.inv_comp_eq, Scheme.Hom.toImage_imageι]

/-- The morphism from the strict transform of `Y₀` to `Y₀` induced by the blowup. -/
def strictTransformToFibre (Y₀ : Y.IdealSheafData) :
    (strictTransformIdeal y hy Y₀).subscheme ⟶ Y₀.subscheme :=
  (strictTransformSubschemeIso y hy Y₀).hom ≫ transformToCurve Y₀ y hy

/-- The morphism `C ⟶ Y₀` lies over the blowup morphism. -/
@[reassoc]
theorem strictTransformToFibre_comp_subschemeι (Y₀ : Y.IdealSheafData) :
    strictTransformToFibre y hy Y₀ ≫ Y₀.subschemeι =
      (strictTransformIdeal y hy Y₀).subschemeι ≫ pointBlowupToBase y hy := by
  rw [strictTransformToFibre, Category.assoc, ← transformToBlowUp_comp_toBase,
    strictTransformSubschemeIso_hom_comp_assoc]
  rfl

/-- An integral regular effective Cartier divisor is a configuration curve. -/
private theorem isConfigCurve_fibre {Y₀ : Y.IdealSheafData} [IsIntegral Y₀.subscheme]
    (hY₀C : IsEffectiveCartierDivisor Y₀) (hY₀reg : IsRegular Y₀.subscheme) :
    Stacks.ResolutionOfSurfaces.IsConfigCurve Y₀ :=
  ⟨inferInstance, hY₀C, Or.inl hY₀reg⟩

section Surface

variable [IsNoetherian Y] (hreg : IsRegular Y) (hdim : topologicalKrullDim Y = 2)
  (hydim : ringKrullDim (Y.presheaf.stalk y) = 2) {Y₀ : Y.IdealSheafData}
  [IsIntegral Y₀.subscheme] (hY₀C : IsEffectiveCartierDivisor Y₀)
  (hY₀reg : IsRegular Y₀.subscheme) (hyY₀ : y ∈ (Y₀.support : Set Y))

include hreg hdim hydim hY₀C hY₀reg hyY₀

omit hreg in
/-- `Y₀` is one-dimensional. -/
theorem topologicalKrullDim_fibre : topologicalKrullDim Y₀.subscheme = 1 :=
  (isConfigCurve_fibre hY₀C hY₀reg).topologicalKrullDim_eq_one_of_ringKrullDim_eq_two hdim hydim
    hyY₀

/-- The strict transform of `Y₀` is a configuration curve: integral, effective Cartier and
regular. -/
private theorem isConfigCurve_strictTransformIdeal :
    Stacks.ResolutionOfSurfaces.IsConfigCurve (strictTransformIdeal y hy Y₀) :=
  Stacks.ResolutionOfSurfaces.isConfigCurve_transformIdeal hreg hdim
    (isConfigCurve_fibre hY₀C hY₀reg) y hy
    (Stacks.ResolutionOfSurfaces.genericPoint_ne_of_ringKrullDim_eq_two
      (isConfigCurve_fibre hY₀C hY₀reg) hydim)
    fun _ => topologicalKrullDim_fibre y hdim hydim hY₀C hY₀reg hyY₀

/-- **The strict transform of `Y₀` is an effective Cartier divisor.** -/
theorem isEffectiveCartierDivisor_strictTransformIdeal :
    IsEffectiveCartierDivisor (strictTransformIdeal y hy Y₀) :=
  (isConfigCurve_strictTransformIdeal y hy hreg hdim hydim hY₀C hY₀reg
    hyY₀).isEffectiveCartierDivisor

/-- The strict transform of `Y₀` is integral. -/
theorem isIntegral_strictTransformIdeal :
    IsIntegral (strictTransformIdeal y hy Y₀).subscheme :=
  (isConfigCurve_strictTransformIdeal y hy hreg hdim hydim hY₀C hY₀reg hyY₀).isIntegral

omit hreg in
/-- **The strict transform of a regular curve through the centre maps isomorphically onto it**
([Stacks, Tag 0BI7] part (1)). -/
theorem isIso_strictTransformToFibre : IsIso (strictTransformToFibre y hy Y₀) := by
  have := isClosedImmersion_transformToBlowUp Y₀ y hy
  obtain ⟨y₀, hy₀⟩ : y ∈ Set.range Y₀.subschemeι := by rwa [Y₀.range_subschemeι]
  have := strictTransformToCurve_isIso Y₀ (topologicalKrullDim_fibre y hdim hydim hY₀C
    hY₀reg hyY₀) y hy y₀ hy₀ (hY₀reg.isRegularLocalRing_stalk y₀)
  rw [strictTransformToFibre]
  infer_instance

/-- **The total transform of `Y₀` is `E + C`.** If `Y₀` is cut out by a global function `t`
with `t ∈ 𝔪_y \ 𝔪_y²`, the inverse image of `Y₀` on the blowup at `y` is the product of the
exceptional ideal and the ideal of the strict transform. -/
theorem exceptionalIdeal_mul_strictTransformIdeal (t : Γ(Y, ⊤))
    (hY₀t : Y₀ = Scheme.IdealSheafData.ofIdealTop (Ideal.span {t}))
    (ht : Y.presheaf.Γgerm y t ∉ maximalIdeal (Y.presheaf.stalk y) ^ 2) :
    exceptionalIdeal (pointIdeal y hy) * strictTransformIdeal y hy Y₀ =
      Y₀.comap (pointBlowupToBase y hy) := by
  classical
  set π := pointBlowupToBase y hy with hπ
  set E := exceptionalIdeal (pointIdeal y hy) with hEdef
  set C := strictTransformIdeal y hy Y₀ with hCdef
  set T := Y₀.comap π with hTdef
  have : IsNoetherian (pointBlowup y hy) := Stacks.ResolutionOfSurfaces.isNoetherian_blowUp _
  have hZdim : topologicalKrullDim (pointBlowup y hy) = 2 :=
    (isRegular_and_topologicalKrullDim_blowUp_vanishingIdeal_singleton Y hreg hdim y hy).2
  have hE : IsEffectiveCartierDivisor E :=
    Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal _
  have hEcfg : Stacks.ResolutionOfSurfaces.IsConfigCurve E :=
    Stacks.ResolutionOfSurfaces.isConfigCurve_exceptionalIdeal hreg hdim y hy hydim
  have hC : IsEffectiveCartierDivisor C :=
    isEffectiveCartierDivisor_strictTransformIdeal y hy hreg hdim hydim hY₀C hY₀reg hyY₀
  have hEC : IsEffectiveCartierDivisor (E * C) := isEffectiveCartierDivisor_mul E C hE hC
  have hY₀le : Y₀ ≤ pointIdeal y hy := by
    rw [← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal]
    intro w hw
    rw [Set.mem_singleton_iff.mp hw]
    exact hyY₀
  have hmemE : ∀ z : pointBlowup y hy, z ∈ (E.support : Set (pointBlowup y hy)) ↔ π z = y :=
    fun z => mem_exceptionalIdeal_support_iff y hy z
  have hEtop : ∀ z : pointBlowup y hy, π z ≠ y → IdealSheafData.stalk E z = ⊤ := fun z hz =>
    (Stacks.Divisors.stalk_eq_top_iff_notMem_support E z).mpr fun h => hz ((hmemE z).mp h)
  have hoff : ∀ z : pointBlowup y hy, π z ≠ y →
      IdealSheafData.stalk T z = IdealSheafData.stalk C z := fun z hz =>
    (IdealSheafData.stalk_comap Y₀ π z).trans
      (Stacks.ResolutionOfSurfaces.stalk_transformIdeal_of_ne Y₀ y hy z hz).symm
  -- The total transform lies in `E · C`, stalkwise.
  have hle : T ≤ E * C := by
    refine IdealSheafData.le_of_stalk_le T (E * C) fun z => ?_
    rw [IdealSheafData.stalk_mul]
    by_cases hz : π z = y
    · by_cases hzC : z ∈ (C.support : Set (pointBlowup y hy))
      · have := isClosedImmersion_transformToBlowUp Y₀ y hy
        obtain ⟨w, rfl⟩ := mem_range_of_mem_support_ker (transformToBlowUp Y₀ y hy) hzC
        exact totalTransform_stalk_le_exceptional_mul_strictTransform Y₀ y hy hY₀le w
          ((hmemE _).mpr hz)
      · rw [(Stacks.Divisors.stalk_eq_top_iff_notMem_support C z).mpr hzC, Ideal.mul_top]
        exact iSup₂_mono fun U _ => Ideal.map_mono
          (Scheme.IdealSheafData.comap_mono π hY₀le U)
    · rw [hEtop z hz, Ideal.top_mul, hoff z hz]
  -- Write the total transform as `E · C · K`.
  obtain ⟨K, hK⟩ := exists_mul_eq_of_le_of_isEffectiveCartierDivisor (E * C) T hEC hle
  suffices hK1 : K = ⊤ by
    rw [hK, hK1, ← Scheme.IdealSheafData.one_eq_top, mul_one]
  -- `K` is the unit ideal off `E`.
  have hKoff : ∀ z : pointBlowup y hy, π z ≠ y → z ∉ (K.support : Set (pointBlowup y hy)) := by
    intro z hz hzK
    have h1 : IdealSheafData.stalk T z =
        IdealSheafData.stalk C z * IdealSheafData.stalk K z := by
      rw [hK, IdealSheafData.stalk_mul, IdealSheafData.stalk_mul, hEtop z hz, Ideal.top_mul]
    rw [hoff z hz] at h1
    have hKne : IdealSheafData.stalk K z ≠ ⊤ := fun h =>
      (Stacks.Divisors.stalk_eq_top_iff_notMem_support K z).mp h hzK
    by_cases hzC : z ∈ (C.support : Set (pointBlowup y hy))
    · obtain ⟨c, -, hc, hcC⟩ := exists_regular_generator_at_support C z hC hzC
      rw [hcC] at h1
      have hcmem : c ∈ Ideal.span {c} * IdealSheafData.stalk K z :=
        h1 ▸ Ideal.mem_span_singleton_self c
      obtain ⟨k, hk, hck⟩ := Ideal.mem_span_singleton_mul.mp hcmem
      have hk1 : k = 1 := hc.1 (hck.trans (mul_one c).symm)
      exact hKne ((Ideal.eq_top_iff_one _).mpr (hk1 ▸ hk))
    · rw [(Stacks.Divisors.stalk_eq_top_iff_notMem_support C z).mpr hzC, Ideal.top_mul] at h1
      exact hKne h1.symm
  -- `K` is locally principal.
  have hTeq : T = Scheme.IdealSheafData.ofIdealTop (Ideal.span {π.appTop.hom t}) := by
    rw [hTdef, hY₀t, Stacks.IdealSheaf.comap_ofIdealTop, Ideal.map_span, Set.image_singleton]
  have hKlp : Stacks.Divisors.IsLocallyPrincipal K := by
    intro x
    obtain ⟨U, hU, hxU, g, hg, hgen⟩ :=
      Stacks.Divisors.exists_affineOpen_ideal_eq_span_of_isEffectiveCartierDivisor (E * C) hEC x
    refine ⟨⟨U, hU⟩, hxU, ?_⟩
    set fU := ((pointBlowup y hy).presheaf.map (homOfLE le_top).op).hom (π.appTop.hom t)
    have hTU : T.ideal ⟨U, hU⟩ = Ideal.span {fU} := by
      rw [hTeq]
      exact Stacks.Divisors.ideal_ofIdealTop_span_singleton _ _
    have hmul : T.ideal ⟨U, hU⟩ = Ideal.span {g} * K.ideal ⟨U, hU⟩ := by
      rw [hK, ← hgen]
      rfl
    obtain ⟨h, hh, hgh⟩ := Ideal.mem_span_singleton_mul.mp
      (hmul ▸ hTU ▸ Ideal.mem_span_singleton_self fU)
    refine ⟨h, le_antisymm (fun k hk => ?_) (Ideal.span_le.mpr (by simpa using hh))⟩
    have hgk : g * k ∈ Ideal.span {fU} :=
      hTU ▸ hmul ▸ Ideal.mul_mem_mul (Ideal.mem_span_singleton_self g) hk
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hgk
    rw [← hgh] at hr
    have hkr : k = h * r := hg.1 (show g * k = g * (h * r) by rw [← hr]; ring)
    exact Ideal.mem_span_singleton'.mpr ⟨r, by rw [hkr, mul_comm]⟩
  -- Otherwise `K` would vanish at the generic point of `E`.
  by_contra hKne
  obtain ⟨z, hzK, hzdim⟩ := Stacks.Divisors.exists_mem_support_ringKrullDim_stalk_le_one K hKlp hKne
  have hzE : π z = y := by
    by_contra h
    exact hKoff z h hzK
  have hzEsupp : z ∈ (E.support : Set (pointBlowup y hy)) := (hmemE z).mpr hzE
  have := hEcfg.isIntegral
  have hgen : E.subschemeι (genericPoint E.subscheme) = z := by
    by_contra hne
    have h2 := hEcfg.ringKrullDim_stalk_eq_two hZdim hzEsupp hne
    rw [h2] at hzdim
    exact absurd hzdim (by norm_num)
  have hEK : E.support ≤ K.support := by
    intro w hw
    have hw' : w ∈ Set.range E.subschemeι := by rwa [E.range_subschemeι]
    obtain ⟨w', rfl⟩ := hw'
    have hspec : genericPoint E.subscheme ⤳ w' :=
      (genericPoint_spec E.subscheme).specializes (Set.mem_univ _)
    have hmap := hspec.map E.subschemeι.continuous
    rw [hgen] at hmap
    exact hmap.mem_closed K.support.isClosed hzK
  have hEred : IsReduced E.subscheme := isReduced_of_isRegular
    (Stacks.ResolutionOfSurfaces.isRegular_exceptionalDivisor_vanishingIdeal_singleton hreg hdim
      y hy hydim)
  have hKE : K ≤ E := by
    rw [Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme E E.support rfl]
    exact Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mp hEK
  have hTE : T ≤ E ^ 2 := by
    rw [hK, pow_two]
    intro U
    change E.ideal U * C.ideal U * K.ideal U ≤ E.ideal U * E.ideal U
    exact Ideal.mul_mono Ideal.mul_le_left (hKE U)
  have hty : Y.presheaf.Γgerm y t ∈ maximalIdeal (Y.presheaf.stalk y) := by
    have h := hyY₀
    rw [hY₀t] at h
    exact (Stacks.Divisors.mem_support_ofIdealTop_span_singleton_iff t y).mp h
  have := hreg.isRegularLocalRing_stalk y
  exact not_comap_le_exceptionalIdeal_sq y hy hydim Y₀ t hY₀t.symm.le hty ht hTE

/-- **The total transform is cut out by `π^* t`.** The product of the exceptional ideal and the
ideal of the strict transform is the ideal sheaf generated by the global function `t ∘ π`. -/
theorem exceptionalIdeal_mul_strictTransformIdeal_eq_ofIdealTop (t : Γ(Y, ⊤))
    (hY₀t : Y₀ = Scheme.IdealSheafData.ofIdealTop (Ideal.span {t}))
    (ht : Y.presheaf.Γgerm y t ∉ maximalIdeal (Y.presheaf.stalk y) ^ 2) :
    exceptionalIdeal (pointIdeal y hy) * strictTransformIdeal y hy Y₀ =
      Scheme.IdealSheafData.ofIdealTop
        (Ideal.span {(pointBlowupToBase y hy).appTop.hom t}) := by
  rw [exceptionalIdeal_mul_strictTransformIdeal y hy hreg hdim hydim hY₀C hY₀reg hyY₀ t hY₀t ht,
    hY₀t, Stacks.IdealSheaf.comap_ofIdealTop, Ideal.map_span, Set.image_singleton]

/-- **Set-theoretically, the inverse image of `Y₀` is `E ∪ C`.** -/
theorem preimage_support_eq_exceptionalSet_union (t : Γ(Y, ⊤))
    (hY₀t : Y₀ = Scheme.IdealSheafData.ofIdealTop (Ideal.span {t}))
    (ht : Y.presheaf.Γgerm y t ∉ maximalIdeal (Y.presheaf.stalk y) ^ 2) :
    pointBlowupToBase y hy ⁻¹' (Y₀.support : Set Y) =
      exceptionalSet y hy ∪ strictTransformSet y hy (Y₀.support : Set Y) := by
  ext z
  have h : z ∈ ((exceptionalIdeal (pointIdeal y hy) * strictTransformIdeal y hy Y₀).support :
      Set (pointBlowup y hy)) ↔
      z ∈ ((Y₀.comap (pointBlowupToBase y hy)).support : Set (pointBlowup y hy)) := by
    rw [exceptionalIdeal_mul_strictTransformIdeal y hy hreg hdim hydim hY₀C hY₀reg hyY₀ t hY₀t ht]
  rw [Scheme.IdealSheafData.support_mul, Closeds.coe_sup, Set.mem_union] at h
  have h2 : z ∈ ((Y₀.comap (pointBlowupToBase y hy)).support : Set (pointBlowup y hy)) ↔
      pointBlowupToBase y hy z ∈ (Y₀.support : Set Y) := by
    rw [Scheme.IdealSheafData.support_comap]
    rfl
  have hE : z ∈ exceptionalSet y hy ↔
      z ∈ ((exceptionalIdeal (pointIdeal y hy)).support : Set (pointBlowup y hy)) :=
    (mem_exceptionalIdeal_support_iff y hy z).symm
  rw [Set.mem_preimage, Set.mem_union, hE, ← coe_support_strictTransformIdeal]
  exact h2.symm.trans h.symm

end Surface

end Stacks.Examples.CurveFamilyNotScheme

end
