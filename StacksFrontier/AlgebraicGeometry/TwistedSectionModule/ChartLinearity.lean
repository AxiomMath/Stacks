module

public import StacksFrontier.AlgebraicGeometry.TwistedSectionModule.SliceSectionBridge
public import StacksFrontier.AlgebraicGeometry.SectionRingChartOpen.Basic
public import StacksFrontier.AlgebraicGeometry.ChartDegreeEqualisation.Basic
public import StacksFrontier.AlgebraicGeometry.SectionRingGeometric.UnitScalarSupplement

/-!
# The 𝒪-linearity of Stacks Tag 0B5L's comparison map over the chart ring map

Stacks Tag 0B5I's local datum asks its comparison map on a standard open to be linear over the
sections of the structure sheaf there, and `Stacks.TwistedSections.localizationLiftOfDegree_smul`
reduces that to one identity about the family of divisions: for every `m`, `n`, every homogeneous
`a` of degree `m • d` and every twisted section `t` of degree `d n`, dividing `a · t` by
`s ^ (m + n)` must be the value of a fixed ring map on the fraction `a / sᵐ` times the division of
`t` by `sⁿ`. **This file proves that identity**, with the ring map
`Stacks.SectionRingChartMap.chartRingMap` of Stacks Tag 01PW.

`StacksFrontier/AlgebraicGeometry/TwistedSectionModule/DivisionMultiplicativity.lean` proves the
identity for a numerator *already presented* as `e · sᵐ` with `e` of degree zero, with the scalar
`Stacks.TwistedSections.sliceUnitScalar L V e`. An arbitrary `a` admits no such presentation on
`X`; it admits one **after restriction to `V`**, because
`Stacks.TwistedSections.isIso_mapPowSections_openRestriction` makes `s` invertible there and
hence makes `sᵐ` invertible (`Stacks.TwistedSections.isIso_sectionPow`). The degree-zero factor
it produces lives on the slice site over `V`, where
`Stacks.SectionRingGeometric.schemeUnitScalar` — a global function on `X` — does not apply, so
`Stacks.TwistedSections.sliceUnitScalar_eq` does not reach it. What identifies its scalar instead
is the slice-unit bridge together with the uniqueness of a ratio.

## Main results

* `Stacks.TwistedSections.exists_sliceFactor`: **an arbitrary numerator factors through `sᵐ`
  after restriction to `V`**, the factor being an endomorphism of the slice site's monoidal unit.
* `Stacks.TwistedSections.openDivision_gsmul_of_sliceFactor`: **the multiplicativity of the
  division for a numerator so factored.** This is
  `Stacks.TwistedSections.powerDivision_gsmul_unitComp` run inside the modules on the slice site
  over `V`, where the degree-zero factor is allowed to live, with
  `Stacks.SectionRingGeometric.globalSection_unitComp_onSite` reading the factor as a function on
  `V`.
* `Stacks.TwistedSections.unitScalar_sliceFactor_eq`: **the factor's scalar is the chart ratio.**
* `Stacks.TwistedSections.openDivision_gsmul_chartFamily` and
  `Stacks.TwistedSections.openDivision_gsmul_chartRingMap`: **the identity
  `Stacks.TwistedSections.localizationLiftOfDegree_smul` consumes**, in the two degree spellings.
  The second is literally that hypothesis for `Stacks.SectionRingChartMap.chartRingMap L s hV`.
* `Stacks.TwistedSections.localizationLiftSections_smul`: **piece (iii) of Stacks Tag 0B5I's
  local datum**, the semilinearity of Stacks Tag 0B5L's comparison map over the chart ring map of
  Stacks Tag 01PW.

## Implementation notes

**The object identity `twistPow (𝟙_ C) L k = natTensorPow L k` is not needed, and no division at
`F := 𝟙_` occurs.** One might expect from
`StacksFrontier/AlgebraicGeometry/TwistedSectionModule/OpenRestriction.lean` that the
degree-zero factor has to be produced by `Stacks.TwistedSections.powerDivision` at the slice site
with `F := 𝟙_`, whose source is `twistSections (𝟙_ C) (L|_V) k` while the numerator is a
`powSections (L|_V) k`, so that the two differ by that object identity. **In fact the
factor is produced with no division at all.** A power of an invertible section is invertible
(`Stacks.TwistedSections.isIso_sectionPow`), so the factor is `b|_V ≫ (sᵐ|_V)⁻¹`, a morphism
`𝟙_ ⟶ 𝟙_` on the nose. That object identity remains true and remains not definitional; nothing
consumes it, so it is still not stated anywhere.

**Why the factor's scalar is identified through a product with `s`.** The relation available on
the slice is `b|_V = e · (sᵐ)|_V` at degree `d m`, and `Stacks.SectionRingChartMap.ratio` asks
its generator to be nonvanishing on `V`. For `m = 0` the generator `sᵐ` is the unit of the
section ring, whose nonvanishing open is not known to be everything — the same obstruction that
makes `Stacks.SectionRingChartMap.chartFamily` shift its exponent by one — so the relation is
multiplied through by `s`, which is a morphism of `𝒪_X`-modules and therefore carries the scalar
along unchanged. The generator becomes `s · sᵐ`, whose image in the section ring is `s^{m+1}`,
and `Stacks.SectionRingChartMap.ratioR_congr` identifies dividing by it with dividing by
`Stacks.SectionExtension.powSec L s (m + 1)`, the generator `chartFamily` uses.

**The lax unit of the restriction contributes nothing.** The slice-unit bridge
`Stacks.TwistedSections.schemeOpenUnitHomAddEquiv_mapTwistSections` computes a restricted global
section exactly, the lax unit's function on `V` being `1`
(`Stacks.TwistedSections.sliceUnitRatio_eq_one`). This file previously cancelled that function
between the two sides of the relation the ratio is computed from; the cancellation is gone.

**The scalar of a slice endomorphism is not a new notion.**
`Stacks.TwistedSections.sliceEndoScalar`, the function on `V` of an arbitrary endomorphism of the
slice site's monoidal unit, is the general form of
`Stacks.TwistedSections.sliceUnitScalar`, which is now *defined* as it at an endomorphism carried
to the slice from `X`; no twin was added.

## References

* [Stacks Project, Tag 0B5I](https://stacks.math.columbia.edu/tag/0B5I)
* [Stacks Project, Tag 0B5L](https://stacks.math.columbia.edu/tag/0B5L)
* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory AlgebraicGeometry Opposite
open Stacks.GradedSections (powSections mul mulMap sectionRing powCongr)
open Stacks.TensorPowers (natTensorPow)
open Stacks.TensorPowerTrivialize (resTop trivEquiv resTop_globalSection_mul)
open Stacks.SectionProduct (globalSection)
open Stacks.SectionExtension (powSec)
open Stacks.AmpleFiniteAvoidance (nvOpen grading)
open Stacks.SectionRingChartMap (ratio chartFamily chartRingMap)

universe u

namespace Stacks.TwistedSections

open Stacks.SheafInternalHom.SliceRestriction (schemeOpenRestriction schemeOverFunctorMonoidal
  schemeOpenUnitHomAddEquiv)
open Stacks.SheafOfModules.SliceRestriction (sliceRingPresheaf isSheaf_sliceRingPresheaf)

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive
  Stacks.SectionRingGeometric.presheafMonoidalPreadditiveStructure
  Stacks.SectionRingGeometric.sheafifyAdditive
  Stacks.SectionRingGeometric.tensorLeftAdditive
  Stacks.SectionRingGeometric.tensorRightAdditive
  Stacks.SheafInternalHom.SliceRestriction.schemeOverFunctorMonoidal


variable {X : Scheme.{u}}

/-! ### The degree-zero factor on the slice -/

section Factor

variable (F L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]

/-- **Two equal exponents give the same division over `V`.** A `subst` on a variable, so this
applies at the compound exponents the degree-zero localization produces. -/
theorem openDivision_exp_congr {d : ℕ} (s : powSections L d) (V : X.Opens)
    (hV : V ≤ nvOpen L s) {p q : ℕ} (h : p = q) (z : twistSections F L (d * p)) :
    openDivision F L s V hV q (twistCongr (congrArg (d * ·) h) z)
      = openDivision F L s V hV p z := by
  subst h
  exact congrArg (openDivision F L s V hV p) (twistCongr_rfl z)

/-- A slice endomorphism of the unit, composed in front of `w`, scales the section of `w` over `V`
by its scalar. -/
private theorem schemeOpenUnitHomAddEquiv_endo_comp (L F : X.Modules) (V : X.Opens)
    (e : powSections ((schemeOpenRestriction X V).obj L) 0)
    (w : 𝟙_ _ ⟶ (schemeOpenRestriction X V).obj F) :
    schemeOpenUnitHomAddEquiv V F (e ≫ w)
      = sliceEndoScalar L V e • schemeOpenUnitHomAddEquiv V F w :=
  Stacks.SectionRingGeometric.globalSection_unitComp_onSite (sliceRingPresheaf X.presheaf V)
    (isSheaf_sliceRingPresheaf X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) V) Over.mkIdTerminal e w

/-- **The degree-zero factor of an arbitrary numerator, on the slice site over `V`.** The power
`sᵐ` becomes invertible after restriction to `V`, so the restriction of any section of
`L ^⊗ (d m)` factors through it; the factor is a morphism `𝟙_ ⟶ 𝟙_` of the modules on the slice
site, produced with no division and no object identity. -/
theorem exists_sliceFactor {d : ℕ} (s : powSections L d) (V : X.Opens)
    (hV : V ≤ nvOpen L s) (m : ℕ) (b : powSections L (d * m)) :
    ∃ e : powSections ((schemeOpenRestriction X V).obj L) 0,
      mapPowSections (schemeOpenRestriction X V) b
        = e ≫ sectionPowOfDegree (mapPowSections (schemeOpenRestriction X V) s) m := by
  have := isIso_mapPowSections_openRestriction L s hV
  have hP : IsIso (sectionPowOfDegree (mapPowSections (schemeOpenRestriction X V) s) m) :=
    inferInstance
  refine ⟨mapPowSections (schemeOpenRestriction X V) b ≫
    @inv _ _ _ _ (sectionPowOfDegree (mapPowSections (schemeOpenRestriction X V) s) m) hP, ?_⟩
  exact (Category.comp_id _).symm.trans ((whisker_eq _
    (@IsIso.inv_hom_id _ _ _ _ _ hP).symm).trans (Category.assoc _ _ _).symm)

/-- **The multiplicativity of the division for a numerator factored on the slice.** If the
restriction of `b` to `V` factors as `e · sᵐ|_V` with `e` an endomorphism of the slice site's
monoidal unit, then dividing `b · t` by `s ^ (n + m)` over `V` is the function attached to `e` by
`Stacks.SectionRingGeometric.unitScalarOnSite` times the division of `t` by `sⁿ`.

This is `Stacks.TwistedSections.powerDivision_gsmul_unitComp` run inside the modules on the slice
site — where the degree-zero factor is allowed to live — followed by
`Stacks.SectionRingGeometric.globalSection_unitComp_onSite` at the terminal object `V ⟶ V`. -/
theorem openDivision_gsmul_of_sliceFactor {d : ℕ} (s : powSections L d) (V : X.Opens)
    (hV : V ≤ nvOpen L s) (n m : ℕ) (b : powSections L (d * m))
    (e : powSections ((schemeOpenRestriction X V).obj L) 0)
    (he : mapPowSections (schemeOpenRestriction X V) b
      = e ≫ sectionPowOfDegree (mapPowSections (schemeOpenRestriction X V) s) m)
    (t : twistSections F L (d * n)) :
    openDivision F L s V hV (n + m)
        (twistCongr (mul_add_degree d n m) (gsmul b t))
      = sliceEndoScalar L V e • openDivision F L s V hV n t := by
  have := isIso_mapPowSections_openRestriction L s hV
  have hnum : mapTwistSections (schemeOpenRestriction X V)
        (twistCongr (mul_add_degree d n m) (gsmul b t))
      = twistCongr (mul_add_degree d n m)
          (gsmul (e ≫ sectionPowOfDegree (mapPowSections (schemeOpenRestriction X V) s) m)
            (mapTwistSections (schemeOpenRestriction X V) t)) := by
    rw [mapTwistSections_twistCongr, mapTwistSections_gsmul, he]
  have hdiv : powerDivision (mapPowSections (schemeOpenRestriction X V) s) (n + m)
        (mapTwistSections (schemeOpenRestriction X V)
          (twistCongr (mul_add_degree d n m) (gsmul b t)))
      = e ≫ powerDivision (mapPowSections (schemeOpenRestriction X V) s) n
          (mapTwistSections (schemeOpenRestriction X V) t) :=
    (congrArg
        (fun z => powerDivision (mapPowSections (schemeOpenRestriction X V) s) (n + m) z)
        hnum).trans
      (powerDivision_gsmul_unitComp (mapPowSections (schemeOpenRestriction X V) s) n m e
        (mapTwistSections (schemeOpenRestriction X V) t))
  exact (congrArg (schemeOpenUnitHomAddEquiv V F) hdiv).trans
    (schemeOpenUnitHomAddEquiv_endo_comp L F V e _)

end Factor

/-! ### The scalar of the factor is the chart ratio -/

section Scalar

variable (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]

/-- **`s · sᵐ` and `s^{m+1}` have the same image in the section ring.** The left side is a
product of two sections, of degrees `d` and `d m`; the right side is
`Stacks.SectionExtension.powSec` at the exponent `m + 1`, of degree `d (m + 1)`. The two degrees
are the same number written differently, so no equation between *sections* is available, and this
is the equation between ring elements that replaces it. -/
theorem of_mul_sectionPow {d : ℕ} (s : powSections L d) (m : ℕ) :
    DirectSum.of (powSections L) (d + d * m) (mul s (sectionPowOfDegree s m))
      = DirectSum.of (powSections L) (d * (m + 1)) (powSec L s (m + 1)) := by
  rw [Stacks.SectionRingChartMap.of_mul_eq, of_sectionPowOfDegree, homogeneousSectionOfDegree,
    Stacks.SectionRingChartMap.of_powSec_eq_pow, pow_succ']

/-- **`V` lies inside the nonvanishing open of `s · sᵐ`**, for every `m`: that product is
`s^{m+1}` in the section ring, and `X_{s^{m+1}} = X_s`. This is what makes the generator usable
at `m = 0` as well, where `sᵐ` is the unit of the section ring and carries no nonvanishing
statement of its own. -/
theorem le_nvOpen_mul_sectionPow {d : ℕ} (s : powSections L d) {V : X.Opens}
    (hV : V ≤ nvOpen L s) (m : ℕ) : V ≤ nvOpen L (mul s (sectionPowOfDegree s m)) :=
  hV.trans_eq
    ((Stacks.SectionRingProjOverlap.nvOpen_powSec_of_one_le L s (m + 1)
        (Nat.le_add_left 1 m)).symm.trans
      (Stacks.SectionRingChartOpen.nvOpen_congr L (by ring) (powSec L s (m + 1))
        (mul s (sectionPowOfDegree s m)) (of_mul_sectionPow L s m).symm))

/-- **The chart family is the ratio by `s · sᵐ`.** `Stacks.SectionRingChartMap.chartFamily` at
the exponent `m` divides `s · b` by `s^{m+1}`, and
`Stacks.SectionRingChartMap.ratioR_congr` replaces that generator by `s · sᵐ`, whose degree is
the literal sum `d + d m` and which therefore appears in an equation between sections. -/
theorem chartFamily_eq_ratio_mul_sectionPow {d : ℕ} (s : powSections L d) {V : X.Opens}
    (hV : V ≤ nvOpen L s) (m : ℕ) (b : powSections L (d * m)) :
    chartFamily L s hV m (DirectSum.of (powSections L) (d * m) b)
      = ratio L (mul s (sectionPowOfDegree s m)) (le_nvOpen_mul_sectionPow L s hV m) (mul s b) := by
  rw [Stacks.SectionRingChartMap.chartFamily_apply, Stacks.SectionRingChartMap.numMapR_def,
    Stacks.SectionRingChartMap.ratioR_congr L (by ring) (powSec L s (m + 1))
      (mul s (sectionPowOfDegree s m)) _ (le_nvOpen_mul_sectionPow L s hV m)
      (of_mul_sectionPow L s m).symm,
    ← Stacks.SectionRingChartMap.of_mul_eq, Stacks.SectionRingChartMap.ratioR_of]

/-- **The scalar of a slice factor is the chart ratio.** If the restriction of `b` to `V` factors
as `e · sᵐ|_V`, the function `Stacks.SectionRingGeometric.unitScalarOnSite` attaches to `e` on the
slice site is the value of `Stacks.SectionRingChartMap.chartFamily` on `b`.

The factorisation is read on `V` through the slice-unit bridge, which computes the restricted
global section with no factor. The resulting relation at degree `d m` is multiplied
through by `s` — multiplication by a global section being a morphism of `𝒪_X`-modules, which
carries the scalar along — so that the generator is `s · sᵐ`, nonvanishing on `V`, and the
uniqueness of a ratio then computes the scalar. -/
theorem unitScalar_sliceFactor_eq {d : ℕ} (s : powSections L d) (V : X.Opens)
    (hV : V ≤ nvOpen L s) (m : ℕ) (b : powSections L (d * m))
    (e : powSections ((schemeOpenRestriction X V).obj L) 0)
    (he : mapPowSections (schemeOpenRestriction X V) b
      = e ≫ sectionPowOfDegree (mapPowSections (schemeOpenRestriction X V) s) m) :
    sliceEndoScalar L V e
      = chartFamily L s hV m (DirectSum.of (powSections L) (d * m) b) := by
  have := isIso_mapPowSections_openRestriction L s hV
  -- the factorisation, read on the slice as an identity of twisted sections of degree zero
  have key : e ≫ mapTwistSections (schemeOpenRestriction X V)
        (F := natTensorPow L (d * m)) (L := L) (m := 0) (sectionPowOfDegree s m)
      = mapTwistSections (schemeOpenRestriction X V)
        (F := natTensorPow L (d * m)) (L := L) (m := 0) b := by
    refine (cancel_mono (mapNatTensorPow (schemeOpenRestriction X V) L (d * m))).mp ?_
    exact (Category.assoc _ _ _).trans ((whisker_eq e
      (mapPowSections_eq_mapTwistSections (schemeOpenRestriction X V)
        (sectionPowOfDegree s m)).symm).trans
      (((whisker_eq e (mapPowSections_sectionPow (schemeOpenRestriction X V) s m)).trans
        he.symm).trans (mapPowSections_eq_mapTwistSections (schemeOpenRestriction X V) b)))
  -- the slice-unit bridge, with the lax unit's ratio appearing on both sides
  have h2 : schemeOpenUnitHomAddEquiv V (natTensorPow L (d * m))
        (mapTwistSections (schemeOpenRestriction X V)
          (F := natTensorPow L (d * m)) (L := L) (m := 0) b)
      = sliceEndoScalar L V e
        • schemeOpenUnitHomAddEquiv V (natTensorPow L (d * m))
            (mapTwistSections (schemeOpenRestriction X V)
              (F := natTensorPow L (d * m)) (L := L) (m := 0) (sectionPowOfDegree s m)) :=
    (congrArg (schemeOpenUnitHomAddEquiv V (natTensorPow L (d * m))) key).symm.trans
      (schemeOpenUnitHomAddEquiv_endo_comp L _ V e _)
  rw [schemeOpenUnitHomAddEquiv_mapTwistSections V (natTensorPow L (d * m)) L b,
    schemeOpenUnitHomAddEquiv_mapTwistSections V (natTensorPow L (d * m)) L
      (sectionPowOfDegree s m)] at h2
  -- multiply the relation through by `s`
  have h3 := congrArg (Scheme.Modules.Hom.app (mulMap s (d * m)) V) h2
  rw [Scheme.Modules.Hom.app_smul,
    ← resTop_globalSection_mul L s b V,
    ← resTop_globalSection_mul L s (sectionPowOfDegree s m) V] at h3
  -- the generator `s · sᵐ` is free on `V`, so a scalar acting on it is determined
  have hinj : ∀ f g : Γ(X, V),
      f • resTop (natTensorPow L (d + d * m))
            (globalSection X _ (mul s (sectionPowOfDegree s m))) V
          = g • resTop (natTensorPow L (d + d * m))
            (globalSection X _ (mul s (sectionPowOfDegree s m))) V → f = g := by
    intro f g hfg
    exact (trivEquiv (natTensorPow L (d + d * m))
      (globalSection X _ (mul s (sectionPowOfDegree s m)))
      (le_nvOpen_mul_sectionPow L s hV m)).injective hfg
  rw [chartFamily_eq_ratio_mul_sectionPow]
  refine hinj _ _ ?_
  rw [← h3, ← Stacks.SectionRingChartMap.ratio_smul_resTop L (mul s (sectionPowOfDegree s m))
    (le_nvOpen_mul_sectionPow L s hV m) (mul s b)]

end Scalar

/-! ### The 𝒪-linearity -/

section Linearity

variable (F L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]

/-- **The multiplicativity of the division at an arbitrary numerator**, with the scalar the value
of `Stacks.SectionRingChartMap.chartFamily`. The numerator is factored on the slice by
`Stacks.TwistedSections.exists_sliceFactor` and its scalar identified by
`Stacks.TwistedSections.unitScalar_sliceFactor_eq`. -/
theorem openDivision_gsmul_chartFamily {d : ℕ} (s : powSections L d) (V : X.Opens)
    (hV : V ≤ nvOpen L s) (n m : ℕ) (b : powSections L (d * m))
    (t : twistSections F L (d * n)) :
    openDivision F L s V hV (n + m)
        (twistCongr (mul_add_degree d n m) (gsmul b t))
      = chartFamily L s hV m (DirectSum.of (powSections L) (d * m) b)
        • openDivision F L s V hV n t := by
  obtain ⟨e, he⟩ := exists_sliceFactor L s V hV m b
  rw [openDivision_gsmul_of_sliceFactor F L s V hV n m b e he,
    unitScalar_sliceFactor_eq L s V hV m b e he]

/-- **The identity `Stacks.TwistedSections.localizationLiftOfDegree_smul` consumes**, for the
family of divisions over `V` and the chart ring map of Stacks Tag 01PW: dividing `a · t` by
`s ^ (m + n)` over `V` is the value of `Stacks.SectionRingChartMap.chartRingMap` on the fraction
`a / sᵐ` times the division of `t` by `sⁿ`.

The numerator's degree is `m • d` here, the spelling the degree-zero localization counts with,
and `Stacks.GradedSections.powCongr` moves it to the `d * m` of
`Stacks.TwistedSections.openDivision_gsmul_chartFamily`. -/
theorem openDivision_gsmul_chartRingMap {d : ℕ} (s : powSections L d) (V : X.Opens)
    (hV : V ≤ nvOpen L s) (m n : ℕ) (a : powSections L (m • d))
    (t : twistSections F L (d * n)) :
    openDivision F L s V hV (m + n)
        (twistCongr (nsmul_add_degree d m n) (gsmul a t))
      = chartRingMap L s hV
          (HomogeneousLocalization.Away.mk (grading L)
            (Stacks.ExternalGrading.of_mem_summand d s) m
            (DirectSum.of (powSections L) (m • d) a) ⟨a, rfl⟩)
        • openDivision F L s V hV n t := by
  have hdeg : m • d = d * m := by rw [smul_eq_mul, Nat.mul_comm]
  have hnum : twistCongr (nsmul_add_degree d m n) (gsmul a t)
      = twistCongr (congrArg (d * ·) (Nat.add_comm n m))
          (twistCongr (mul_add_degree d n m) (gsmul (a ≫ powCongr L hdeg) t)) := by
    rw [gsmul_comp_powCongr, twistCongr_trans, twistCongr_trans]
  rw [Stacks.SectionRingChartMap.chartRingMap_mk L s hV m
      (DirectSum.of (powSections L) (m • d) a) ⟨a, rfl⟩,
    show chartFamily L s hV m (DirectSum.of (powSections L) (m • d) a)
        = chartFamily L s hV m
            (DirectSum.of (powSections L) (d * m) (a ≫ powCongr L hdeg)) from
      congrArg _ (Stacks.ChartDegreeEqualisation.of_comp_powCongr L hdeg a).symm,
    ← openDivision_gsmul_chartFamily F L s V hV n m (a ≫ powCongr L hdeg) t, hnum,
    openDivision_exp_congr F L s V hV (Nat.add_comm n m)]

/-- **Piece (iii) of Stacks Tag 0B5I's local datum: the 𝒪-linearity of Stacks Tag 0B5L's
comparison map.** The map `Γ_*(X, ℱ, L)_{(s)} → Γ(ℱ, V)` of
`Stacks.TwistedSections.localizationLiftSections` is semilinear over the chart ring map
`Stacks.SectionRingChartMap.chartRingMap L s hV` of Stacks Tag 01PW, out of which the morphism
`X ⟶ Proj Γ_*(X, L)` of Stacks Tag 01PZ is built. -/
theorem localizationLiftSections_smul {d : ℕ} (s : powSections L d) (V : X.Opens)
    (hV : V ≤ nvOpen L s) (z : ringAtNonvanishingOpenOfDegree s)
    (w : sectionAtNonvanishingOpenOfDegree F L s) :
    localizationLiftSections F L s V hV (z • w)
      = chartRingMap L s hV z • localizationLiftSections F L s V hV w := by
  have hz := DFunLike.congr_fun (localizationLiftSections_eq F L s V hV) (z • w)
  have hw := DFunLike.congr_fun (localizationLiftSections_eq F L s V hV) w
  refine hz.trans ((localizationLiftOfDegree_smul s (openDivision F L s V hV)
    (isPowerInvariant_openDivision F L s V hV) (chartRingMap L s hV)
    (fun m n a t => openDivision_gsmul_chartRingMap F L s V hV m n a t) z w).trans ?_)
  exact congrArg (chartRingMap L s hV z • ·) hw.symm

end Linearity

end Stacks.TwistedSections

end
