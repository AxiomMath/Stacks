module

public import StacksFrontier.AlgebraicGeometry.Blowup.ExceptionalTwist
public import StacksFrontier.AlgebraicGeometry.Blowup.TwistOneExceptionalIdeal

/-!
# `𝒪_{X'}(n)` is the `n`-th power of the exceptional ideal sheaf of a blowup

Let `X` be a scheme, `ℐ ⊆ 𝒪_X` a quasi-coherent sheaf of ideals and `b : X' ⟶ X` the blowup of
`X` in `ℐ`, with exceptional divisor `E` cut out by `ℐ𝒪_{X'}`. Part (3) of [Stacks, Tag 02OS]
says `𝒪_{X'}(1) = ℐ𝒪_{X'}`; this file proves the same in every degree `n ≥ 0`:

`𝒪_{X'}(n) ≅ (ℐ𝒪_{X'})ⁿ`,

compatibly with the canonical maps into `𝒪_{X'}`. The comparison is local on the standard affine
charts of [Stacks, Tag 0804]: over the chart at a section `a ∈ ℐ(U)` the twist `𝒪_{X'}(n)` is
trivialized by `(a⁽¹⁾)ⁿ` and `(ℐ𝒪_{X'})ⁿ` by the `n`-th power of the pullback of `a`, and the
comparison is "divide by `(a⁽¹⁾)ⁿ`, then multiply by `aⁿ`". This is the map that the graded
module map `S(n) ⟶ S`, `Iᵈ⁺ⁿ ⊆ Iᵈ`, of the Rees algebra `S = ⨁ Iᵈ` induces on the chart. The
proof is the one of `AlgebraicGeometry.twistOneIsoExceptionalIdealModule` with the degree carried
along: two charts over the same affine open of the base agree inside a single `Proj`, two charts
over nested affine opens agree after transport along the Tag 01NO chart transition, and the
general case is checked on the cover of the overlap by the parts lying over affine opens.

The twist is indexed as `n * 1`, the degree `n * d` in which the trivialization
`Stacks.AlgebraicGeometry.ProjTrivialization.trivializingEquiv` of an element of degree `d = 1`
lands; `AlgebraicGeometry.blowUpTwistIsoExceptionalIdealPow` removes the factor at the end.

## Main definitions

* `AlgebraicGeometry.exceptionalIdealPowModule`: the ideal sheaf `(ℐ𝒪_{X'})ⁿ`.
* `AlgebraicGeometry.chartPowEquiv`: the chartwise comparison of `𝒪_{X'}(n)` with it.
* `AlgebraicGeometry.blowUpTwistIsoExceptionalIdealPow`: **`𝒪_{X'}(n) ≅ (ℐ𝒪_{X'})ⁿ`**.
* `AlgebraicGeometry.blowUpTwistToUnit`: the canonical map `𝒪_{X'}(n) ⟶ 𝒪_{X'}`.
* `AlgebraicGeometry.blowUpTwistContraction`: the canonical map `𝓕(n) = 𝓕 ⊗ 𝒪_{X'}(n) ⟶ 𝓕`.

## Main results

* `AlgebraicGeometry.incl_app_chartPowEquiv`: on the chart at `a`, the canonical map is division
  by `(a⁽¹⁾)ⁿ` followed by multiplication by the `n`-th power of the pullback of `a`.
* `AlgebraicGeometry.incl_app_twistPowLocalEquiv_gluedIso_hom`: the same for the glued
  comparison, through which `AlgebraicGeometry.blowUpTwistToUnit` is defined.
* `AlgebraicGeometry.schemeTheoreticSupport_iff_blowUpTwistContraction_eq_zero`:
  **[Stacks, Tag 0GA9]** — a quasi-coherent module of finite type on the blowup is scheme
  theoretically supported on `Y_c = cE` if and only if the canonical map `𝓕(c) ⟶ 𝓕` vanishes.

## References

* [Stacks Project, Tag 0GA9](https://stacks.math.columbia.edu/tag/0GA9)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
* [Stacks Project, Tag 0804](https://stacks.math.columbia.edu/tag/0804)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory TopologicalSpace Opposite
open HomogeneousLocalization
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj (moduleSections twistGrading twistingSheaf)
open Stacks.AlgebraicGeometry.ProjTrivialization (trivializingFun trivializingEquiv
  eq_of_val_mul_eq)

universe u w

attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local instance] ProjectiveSpectrum.isPrime

/-! ### The trivializing coefficient in an arbitrary degree, along a graded homomorphism -/

namespace Stacks.ProjTwistComparison

open HomogeneousIdeal

section Fibre

variable {A B : Type u} {σ τ : Type u}
  [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
  (φ : 𝒜 →+*ᵍ ℬ) (hφ : ℬ₊ ≤ 𝒜₊.map φ)

/-- **The trivializing coefficient of `𝒪(n)` at a degree-one element commutes with the twist
comparison**, in every degree `n`. This is `Stacks.ProjTwistComparison.app_trivializingEquiv_symm`
with the degree `1` of the twist replaced by an arbitrary `n`; the pointwise argument is the same,
the fibre comparison carrying the trivializing value of `f` in degree `n` to that of `φ f`
(`Stacks.ProjTwistComparison.fibreMap_trivializingFun`). -/
theorem app_trivializingEquiv_symm_of_mem_one (n : ℤ) {f : A} (hf : f ∈ 𝒜 1) {g : B}
    (hg : g ∈ ℬ 1) (hfg : φ f = g) {W : (AlgebraicGeometry.Proj 𝒜).Opens}
    (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒜 f)
    (hW' : AlgebraicGeometry.Proj.map φ hφ ⁻¹ᵁ W ≤ ProjectiveSpectrum.basicOpen ℬ g)
    (t : moduleSections 𝒜 (twistGrading 𝒜 (n * ((1 : ℕ) : ℤ))) W) :
    ((AlgebraicGeometry.Proj.map φ hφ).app W).hom ((trivializingEquiv 𝒜 hf n hW).symm t) =
      (trivializingEquiv ℬ hg n hW').symm (sectionsMap φ hφ (n * ((1 : ℕ) : ℤ)) W t) := by
  refine Subtype.ext (funext fun y => eq_of_val_mul_eq ℬ n hW' y ?_)
  have hy : ProjectiveSpectrum.comapFun φ hφ y.1 ∈ W := y.2
  calc HomogeneousLocalization.val
          ((((AlgebraicGeometry.Proj.map φ hφ).app W).hom
            ((trivializingEquiv 𝒜 hf n hW).symm t)).1 y) * trivializingFun ℬ n hW' y
      = fibreMap φ hφ y.1 (HomogeneousLocalization.val
              (((trivializingEquiv 𝒜 hf n hW).symm t).1 ⟨_, hy⟩)) *
          trivializingFun ℬ n hW' y :=
        congrArg (· * trivializingFun ℬ n hW' y) (val_app_proj_map φ hφ W _ y)
    _ = fibreMap φ hφ y.1 (HomogeneousLocalization.val
              (((trivializingEquiv 𝒜 hf n hW).symm t).1 ⟨_, hy⟩)) *
          fibreMap φ hφ y.1 (trivializingFun 𝒜 n hW ⟨_, hy⟩) :=
        congrArg (fibreMap φ hφ y.1 (HomogeneousLocalization.val
              (((trivializingEquiv 𝒜 hf n hW).symm t).1 ⟨_, hy⟩)) * ·)
          (fibreMap_trivializingFun φ hφ n hfg hW hW' y hy).symm
    _ = fibreMap φ hφ y.1 (HomogeneousLocalization.val
              (((trivializingEquiv 𝒜 hf n hW).symm t).1 ⟨_, hy⟩) *
            trivializingFun 𝒜 n hW ⟨_, hy⟩) :=
        (fibreMap_mul φ hφ y.1 _ _).symm
    _ = fibreMap φ hφ y.1 (t.1 ⟨_, hy⟩) :=
        congrArg (fibreMap φ hφ y.1)
          (Stacks.AlgebraicGeometry.ProjTrivialization.val_trivializingEquiv_symm_mul
            𝒜 hf n hW t ⟨_, hy⟩)
    _ = (sectionsMap φ hφ (n * ((1 : ℕ) : ℤ)) W t).1 y :=
        (sectionsMap_apply φ hφ (n * ((1 : ℕ) : ℤ)) W t y).symm
    _ = HomogeneousLocalization.val
            (((trivializingEquiv ℬ hg n hW').symm
              (sectionsMap φ hφ (n * ((1 : ℕ) : ℤ)) W t)).1 y) * trivializingFun ℬ n hW' y :=
        (Stacks.AlgebraicGeometry.ProjTrivialization.val_trivializingEquiv_symm_mul
          ℬ hg n hW' _ y).symm

end Fibre

end Stacks.ProjTwistComparison

/-! ### The trivializing coefficient of `𝒪(n)` on a standard open of a `Proj` -/

namespace Stacks.AlgebraicGeometry.ProjTrivialization

variable {S : Type u} [CommRing S] {σ : Type w} [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- **The chartwise trivializing coefficient of `𝒪(n)`**: a section of `𝒪(n)` over an open
contained in `D₊(f)`, for `f` of degree one, divided by the trivializing section `fⁿ`. -/
def twistPowCoeff (n : ℤ) {f : S} (hf : f ∈ 𝒮 1) {W : Opens (ProjectiveSpectrum.top 𝒮)}
    (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 f)
    (t : moduleSections 𝒮 (twistGrading 𝒮 (n * ((1 : ℕ) : ℤ))) W) :
    Γ(AlgebraicGeometry.Proj 𝒮, W) :=
  (trivializingEquiv 𝒮 hf n hW).symm t

/-- **The trivializing coefficient inverts multiplication by the trivializing section.** -/
theorem twistPowCoeff_val_mul (n : ℤ) {f : S} (hf : f ∈ 𝒮 1)
    {W : Opens (ProjectiveSpectrum.top 𝒮)} (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 f)
    (t : moduleSections 𝒮 (twistGrading 𝒮 (n * ((1 : ℕ) : ℤ))) W) (x : W) :
    HomogeneousLocalization.val ((twistPowCoeff 𝒮 n hf hW t).1 x) * trivializingFun 𝒮 n hW x
      = t.1 x :=
  val_trivializingEquiv_symm_mul 𝒮 hf n hW t x

/-- The trivializing coefficient is additive. -/
theorem twistPowCoeff_add (n : ℤ) {f : S} (hf : f ∈ 𝒮 1)
    {W : Opens (ProjectiveSpectrum.top 𝒮)} (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 f)
    (t t' : moduleSections 𝒮 (twistGrading 𝒮 (n * ((1 : ℕ) : ℤ))) W) :
    twistPowCoeff 𝒮 n hf hW (t + t')
      = twistPowCoeff 𝒮 n hf hW t + twistPowCoeff 𝒮 n hf hW t' :=
  map_add (trivializingEquiv 𝒮 hf n hW).symm t t'

/-- **The trivializing coefficient is linear over the functions on `D₊(f)`.** -/
theorem twistPowCoeff_smul (n : ℤ) {f : S} (hf : f ∈ 𝒮 1)
    {W : Opens (ProjectiveSpectrum.top 𝒮)} (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 f)
    (r : ToType ((AlgebraicGeometry.ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj.obj (op W)))
    (t : moduleSections 𝒮 (twistGrading 𝒮 (n * ((1 : ℕ) : ℤ))) W) :
    twistPowCoeff 𝒮 n hf hW (r • t)
      = (show Γ(AlgebraicGeometry.Proj 𝒮, W) from r) * twistPowCoeff 𝒮 n hf hW t :=
  map_smul (trivializingEquiv 𝒮 hf n hW).symm r t

/-- **The trivializing coefficient commutes with restriction.** -/
theorem twistPowCoeff_map (n : ℤ) {f : S} (hf : f ∈ 𝒮 1)
    {V W : Opens (ProjectiveSpectrum.top 𝒮)}
    (hV : V ≤ ProjectiveSpectrum.basicOpen 𝒮 f) (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒮 f)
    (hWV : W ≤ V) (t : moduleSections 𝒮 (twistGrading 𝒮 (n * ((1 : ℕ) : ℤ))) V) :
    twistPowCoeff 𝒮 n hf hW
        ((AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf 𝒮
          (n * ((1 : ℕ) : ℤ))).val.restrictₛₗ (homOfLE hWV).op t)
      = (((AlgebraicGeometry.Proj 𝒮).presheaf.map (homOfLE hWV).op)).hom
          (twistPowCoeff 𝒮 n hf hV t) :=
  Subtype.ext (funext fun x => eq_of_val_mul_eq 𝒮 n hW x
    ((twistPowCoeff_val_mul 𝒮 n hf hW _ x).trans
      (twistPowCoeff_val_mul 𝒮 n hf hV t ⟨x.1, hWV x.2⟩).symm))

/-- **A cross identity between two degree-one elements becomes, in degree `n`, an identity of
constant fractions times trivializing values.** If `z · g = w · f` in `𝒮`, then at every point of
`D₊(f) ∩ D₊(g)` the constant fraction of `zⁿ` times the trivializing value `gⁿ` is the constant
fraction of `wⁿ` times the trivializing value `fⁿ`. -/
theorem algebraMap_pow_mul_trivializingFun_comm (n : ℕ) {f g : S} {z w : S}
    {W : Opens (ProjectiveSpectrum.top 𝒮)}
    (hWf : W ≤ ProjectiveSpectrum.basicOpen 𝒮 f) (hWg : W ≤ ProjectiveSpectrum.basicOpen 𝒮 g)
    (hzw : z * g = w * f) (x : W) :
    algebraMap S (Localization x.1.asHomogeneousIdeal.toIdeal.primeCompl) z ^ n *
        trivializingFun 𝒮 n hWg x
      = algebraMap S (Localization x.1.asHomogeneousIdeal.toIdeal.primeCompl) w ^ n *
        trivializingFun 𝒮 n hWf x := by
  have hneg : (-(n : ℤ)).toNat = 0 := by omega
  have hpow : (z * g) ^ n = (w * f) ^ n := by rw [hzw]
  rw [trivializingFun, trivializingFun, ← map_pow, ← map_pow,
    ← Localization.mk_one_eq_algebraMap, ← Localization.mk_one_eq_algebraMap,
    Localization.mk_mul, Localization.mk_mul]
  refine Localization.mk_eq_mk_iff.mpr (Localization.r_of_eq ?_)
  simp only [Int.toNat_natCast, hneg, pow_zero, mul_one, Submonoid.coe_mul,
    OneMemClass.coe_one]
  rw [mul_pow, mul_pow] at hpow
  rw [hpow]

/-- **Two charts of one `Proj` give the same comparison of `𝒪(n)` with an ideal.** Dividing a
section of `𝒪(n)` by the trivializing section `fⁿ` and multiplying by `u` gives the same thing
as dividing by `gⁿ` and multiplying by `v`, as soon as `u` and `v` satisfy the cross identity
against the two trivializing values. -/
theorem twistPowCoeff_mul_comm (n : ℤ) {f g : S} (hf : f ∈ 𝒮 1) (hg : g ∈ 𝒮 1)
    {W : Opens (ProjectiveSpectrum.top 𝒮)}
    (hWf : W ≤ ProjectiveSpectrum.basicOpen 𝒮 f) (hWg : W ≤ ProjectiveSpectrum.basicOpen 𝒮 g)
    (u v : Γ(AlgebraicGeometry.Proj 𝒮, W))
    (huv : ∀ x : W, HomogeneousLocalization.val (u.1 x) * trivializingFun 𝒮 n hWg x
      = HomogeneousLocalization.val (v.1 x) * trivializingFun 𝒮 n hWf x)
    (t : moduleSections 𝒮 (twistGrading 𝒮 (n * ((1 : ℕ) : ℤ))) W) :
    twistPowCoeff 𝒮 n hf hWf t * u = twistPowCoeff 𝒮 n hg hWg t * v := by
  refine Subtype.ext (funext fun x => HomogeneousLocalization.val_injective _ ?_)
  have hA := twistPowCoeff_val_mul 𝒮 n hf hWf t x
  have hB := twistPowCoeff_val_mul 𝒮 n hg hWg t x
  change HomogeneousLocalization.val ((twistPowCoeff 𝒮 n hf hWf t).1 x * u.1 x)
      = HomogeneousLocalization.val ((twistPowCoeff 𝒮 n hg hWg t).1 x * v.1 x)
  rw [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_mul]
  refine ((isUnit_trivializingFun 𝒮 n hWf x).mul
    (isUnit_trivializingFun 𝒮 n hWg x)).mul_right_cancel ?_
  linear_combination
    (HomogeneousLocalization.val (u.1 x) * trivializingFun 𝒮 n hWg x) * hA -
      (HomogeneousLocalization.val (v.1 x) * trivializingFun 𝒮 n hWf x) * hB + t.1 x * (huv x)

end Stacks.AlgebraicGeometry.ProjTrivialization

namespace AlgebraicGeometry

open Stacks.AlgebraicGeometry.ProjTrivialization
open Stacks.SheafOfModules Stacks.RelativeProj

variable {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℕ)

/-! ### Inside one chart of the blowup -/

/-- **The two chartwise comparisons of `𝒪(n)` with the `n`-th power of the exceptional ideal
inside one chart of the blowup agree.** Over an open of `Proj 𝒜(U)` contained in the standard
opens of the degree-one generators of two sections `a, a'` of the centre on `U`, dividing by
`(a⁽¹⁾)ⁿ` and multiplying by the `n`-th power of the pullback of `a` gives the same thing as
dividing by `(a'⁽¹⁾)ⁿ` and multiplying by the `n`-th power of the pullback of `a'`. -/
theorem twistPowCoeff_mul_chartBaseSectionRes_pow_comm (U : X.affineOpens) (a a' : I.ideal U)
    {W : Opens (ProjectiveSpectrum.top ((reesSituation I).sectionRingGrading U.1))}
    (hWa : W ≤ ProjectiveSpectrum.basicOpen ((reesSituation I).sectionRingGrading U.1)
      (reesDegreeOne I U a).1)
    (hWa' : W ≤ ProjectiveSpectrum.basicOpen ((reesSituation I).sectionRingGrading U.1)
      (reesDegreeOne I U a').1)
    (t : moduleSections ((reesSituation I).sectionRingGrading U.1)
      (twistGrading ((reesSituation I).sectionRingGrading U.1) ((n : ℤ) * ((1 : ℕ) : ℤ))) W) :
    twistPowCoeff ((reesSituation I).sectionRingGrading U.1) n (reesDegreeOne I U a).2 hWa t *
        (reesSituation I).chartBaseSectionRes U.1 U.2 ((a : Γ(X, U.1)) ^ n) W
      = twistPowCoeff ((reesSituation I).sectionRingGrading U.1) n (reesDegreeOne I U a').2
          hWa' t *
        (reesSituation I).chartBaseSectionRes U.1 U.2 ((a' : Γ(X, U.1)) ^ n) W := by
  refine twistPowCoeff_mul_comm _ n (reesDegreeOne I U a).2 (reesDegreeOne I U a').2 hWa hWa'
    _ _ (fun x => ?_) t
  have hval : ∀ (r : Γ(X, U.1)), HomogeneousLocalization.val
      (((reesSituation I).chartBaseSectionRes U.1 U.2 (r ^ n) W).1 x) =
        algebraMap ((reesSituation I).sectionRing U.1)
          (Localization x.1.asHomogeneousIdeal.toIdeal.primeCompl)
          ((reesSituation I).sectionRingBaseMap U.1 r) ^ n := fun r =>
    ((reesSituation I).chartBaseSectionRes_val_eq U.1 U.2 (r ^ n) x).trans
      ((congrArg (algebraMap ((reesSituation I).sectionRing U.1)
          (Localization x.1.asHomogeneousIdeal.toIdeal.primeCompl))
        (map_pow ((reesSituation I).sectionRingBaseMap U.1) r n)).trans (map_pow _ _ n))
  refine Eq.trans (congrArg (· * trivializingFun _ n hWa' x) (hval (a : Γ(X, U.1)))) ?_
  refine Eq.trans ?_ (congrArg (· * trivializingFun _ n hWa x) (hval (a' : Γ(X, U.1)))).symm
  exact algebraMap_pow_mul_trivializingFun_comm _ n hWa hWa'
    (sectionRingBaseMap_mul_reesDegreeOne_comm I U (a : Γ(X, U.1)) (a' : Γ(X, U.1)) a a' rfl rfl)
    x

variable (U : X.affineOpens) (a : I.ideal U)

/-! ### The chartwise trivialization of `𝒪(n)` -/

/-- **A section of `𝒪_{X'}(n)` over an open of the chart at `a`, read on the relative-`Proj`
chart over `U`** as a section of the absolute twisting sheaf of `Proj 𝒜(U)`. -/
def chartTwistPowSections {V : (blowUp I).Opens}
    (hV : V ≤ (Stacks.BlowUpChartCover.chartOpen I U a).1)
    (t : ToType ((blowUpTwist I ((n : ℤ) * ((1 : ℕ) : ℤ))).val.obj (op V))) :
    moduleSections ((reesSituation I).sectionRingGrading U.1)
      (twistGrading ((reesSituation I).sectionRingGrading U.1) ((n : ℤ) * ((1 : ℕ) : ℤ)))
      (Situation.relativeProjChart (reesSituation I) U ⁻¹ᵁ V) :=
  (Situation.twistSectionsIso ((reesSituation I).twistTransition ((n : ℤ) * ((1 : ℕ) : ℤ))) U
    (hV.trans (chartOpen_le_opensRange_relativeProjChart I U a))).hom t

/-- **Reading a section of `𝒪_{X'}(n)` on the chart turns the action of a function on the
blowup into the action of its restriction to the chart.** -/
theorem chartTwistPowSections_smul {V : (blowUp I).Opens}
    (hV : V ≤ (Stacks.BlowUpChartCover.chartOpen I U a).1)
    (r : ToType ((blowUp I).ringCatSheaf.obj.obj (op V)))
    (t : ToType ((blowUpTwist I ((n : ℤ) * ((1 : ℕ) : ℤ))).val.obj (op V))) :
    chartTwistPowSections I n U a hV (r • t)
      = (show ToType ((ProjectiveSpectrum.Proj.structureSheaf
            ((reesSituation I).sectionRingGrading U.1)).obj.obj
            (op (Situation.relativeProjChart (reesSituation I) U ⁻¹ᵁ V)))
          from ((Situation.relativeProjChart (reesSituation I) U).app V).hom r) •
        chartTwistPowSections I n U a hV t :=
  (Situation.twistSectionsIso ((reesSituation I).twistTransition ((n : ℤ) * ((1 : ℕ) : ℤ))) U
    (hV.trans (chartOpen_le_opensRange_relativeProjChart I U a))).hom.hom.map_smul r t

/-- **The trivializing coefficient of `𝒪_{X'}(n)` on the chart at `a`**: a section of
`𝒪_{X'}(n)` over an open of the chart, divided by the trivializing section `(a⁽¹⁾)ⁿ` and read
back as a section of the structure sheaf of the blowup. -/
def chartTwistPowCoeff {V : (blowUp I).Opens}
    (hV : V ≤ (Stacks.BlowUpChartCover.chartOpen I U a).1)
    (t : ToType ((blowUpTwist I ((n : ℤ) * ((1 : ℕ) : ℤ))).val.obj (op V))) :
    Γ(blowUp I, V) :=
  (Situation.chartSectionsIso (reesSituation I) U
      (hV.trans (chartOpen_le_opensRange_relativeProjChart I U a))).inv.hom
    (twistPowCoeff ((reesSituation I).sectionRingGrading U.1) n (reesDegreeOne I U a).2
      (preimage_relativeProjChart_le_basicOpen I U a hV) (chartTwistPowSections I n U a hV t))

/-- **The chart reads the trivializing coefficient as the quotient of the section of `𝒪(n)` by
the trivializing section `(a⁽¹⁾)ⁿ`.** -/
theorem app_relativeProjChart_chartTwistPowCoeff {V : (blowUp I).Opens}
    (hV : V ≤ (Stacks.BlowUpChartCover.chartOpen I U a).1)
    (t : ToType ((blowUpTwist I ((n : ℤ) * ((1 : ℕ) : ℤ))).val.obj (op V))) :
    ((Situation.relativeProjChart (reesSituation I) U).app V).hom
        (chartTwistPowCoeff I n U a hV t)
      = twistPowCoeff ((reesSituation I).sectionRingGrading U.1) n (reesDegreeOne I U a).2
          (preimage_relativeProjChart_le_basicOpen I U a hV)
          (chartTwistPowSections I n U a hV t) :=
  Situation.chartSectionsIso_hom_inv_apply (reesSituation I) U
    (hV.trans (chartOpen_le_opensRange_relativeProjChart I U a)) _

/-- The trivializing coefficient of `t` is any section whose image on the relative-`Proj` chart is
the quotient of the section of `𝒪(n)` read there. -/
private theorem chartTwistPowCoeff_eq_of_app_eq {V : (blowUp I).Opens}
    (hV : V ≤ (Stacks.BlowUpChartCover.chartOpen I U a).1)
    (t : ToType ((blowUpTwist I ((n : ℤ) * ((1 : ℕ) : ℤ))).val.obj (op V)))
    (z : Γ(blowUp I, V))
    (h : ((Situation.relativeProjChart (reesSituation I) U).app V).hom z
      = twistPowCoeff ((reesSituation I).sectionRingGrading U.1) n (reesDegreeOne I U a).2
          (preimage_relativeProjChart_le_basicOpen I U a hV)
          (chartTwistPowSections I n U a hV t)) :
    chartTwistPowCoeff I n U a hV t = z :=
  Situation.injective_app_relativeProjChart (reesSituation I) U
    (hV.trans (chartOpen_le_opensRange_relativeProjChart I U a))
    ((app_relativeProjChart_chartTwistPowCoeff I n U a hV t).trans h.symm)

/-- The trivializing coefficient is additive. -/
theorem chartTwistPowCoeff_add {V : (blowUp I).Opens}
    (hV : V ≤ (Stacks.BlowUpChartCover.chartOpen I U a).1)
    (t t' : ToType ((blowUpTwist I ((n : ℤ) * ((1 : ℕ) : ℤ))).val.obj (op V))) :
    chartTwistPowCoeff I n U a hV (t + t')
      = chartTwistPowCoeff I n U a hV t + chartTwistPowCoeff I n U a hV t' := by
  refine chartTwistPowCoeff_eq_of_app_eq I n U a hV _ _ ?_
  rw [map_add, app_relativeProjChart_chartTwistPowCoeff,
    app_relativeProjChart_chartTwistPowCoeff]
  exact ((congrArg _ (map_add _ t t')).trans (twistPowCoeff_add _ _ _ _ _ _)).symm

/-- **The trivializing coefficient is linear over the functions on the blowup.** -/
theorem chartTwistPowCoeff_smul {V : (blowUp I).Opens}
    (hV : V ≤ (Stacks.BlowUpChartCover.chartOpen I U a).1)
    (r : ToType ((blowUp I).ringCatSheaf.obj.obj (op V)))
    (t : ToType ((blowUpTwist I ((n : ℤ) * ((1 : ℕ) : ℤ))).val.obj (op V))) :
    chartTwistPowCoeff I n U a hV (r • t)
      = (show Γ(blowUp I, V) from r) * chartTwistPowCoeff I n U a hV t := by
  refine chartTwistPowCoeff_eq_of_app_eq I n U a hV _ _ ?_
  rw [chartTwistPowSections_smul]
  exact ((map_mul _ _ _).trans
    (congrArg _ (app_relativeProjChart_chartTwistPowCoeff I n U a hV t))).trans
    (twistPowCoeff_smul _ _ _ _ _ _).symm

/-- The trivializing coefficient is a bijection onto the sections of the structure sheaf. -/
theorem bijective_chartTwistPowCoeff {V : (blowUp I).Opens}
    (hV : V ≤ (Stacks.BlowUpChartCover.chartOpen I U a).1) :
    Function.Bijective (chartTwistPowCoeff I n U a hV) := by
  have h1 : Function.Bijective (chartTwistPowSections I n U a hV) :=
    (Situation.twistSectionsIso ((reesSituation I).twistTransition ((n : ℤ) * ((1 : ℕ) : ℤ))) U
      (hV.trans (chartOpen_le_opensRange_relativeProjChart I U a))).toLinearEquiv.bijective
  have h2 : Function.Bijective
      (twistPowCoeff ((reesSituation I).sectionRingGrading U.1) n (reesDegreeOne I U a).2
        (preimage_relativeProjChart_le_basicOpen I U a hV)) :=
    (trivializingEquiv ((reesSituation I).sectionRingGrading U.1) (reesDegreeOne I U a).2 n
      (preimage_relativeProjChart_le_basicOpen I U a hV)).symm.bijective
  have h3 : Function.Bijective ((Situation.chartSectionsIso (reesSituation I) U
      (hV.trans (chartOpen_le_opensRange_relativeProjChart I U a))).inv.hom) :=
    ConcreteCategory.bijective_of_isIso (Situation.chartSectionsIso (reesSituation I) U
      (hV.trans (chartOpen_le_opensRange_relativeProjChart I U a))).inv
  exact (h3.comp h2).comp h1

/-- **Reading a section of `𝒪_{X'}(n)` on the chart commutes with restriction.** -/
theorem chartTwistPowSections_map {V W : (blowUp I).Opens}
    (hV : V ≤ (Stacks.BlowUpChartCover.chartOpen I U a).1) (hWV : W ≤ V)
    (t : ToType ((blowUpTwist I ((n : ℤ) * ((1 : ℕ) : ℤ))).val.obj (op V))) :
    chartTwistPowSections I n U a (hWV.trans hV)
        ((blowUpTwist I ((n : ℤ) * ((1 : ℕ) : ℤ))).val.restrictₛₗ (homOfLE hWV).op t)
      = (twistingSheaf ((reesSituation I).sectionRingGrading U.1)
          ((n : ℤ) * ((1 : ℕ) : ℤ))).val.restrictₛₗ
          (homOfLE (Scheme.Hom.preimage_mono
            (Situation.relativeProjChart (reesSituation I) U) hWV)).op
          (chartTwistPowSections I n U a hV t) :=
  Situation.twistSectionsIso_restrict
    ((reesSituation I).twistTransition ((n : ℤ) * ((1 : ℕ) : ℤ))) U
    (hV.trans (chartOpen_le_opensRange_relativeProjChart I U a)) hWV t

/-- **The trivializing coefficient commutes with restriction.** -/
theorem chartTwistPowCoeff_map {V W : (blowUp I).Opens}
    (hV : V ≤ (Stacks.BlowUpChartCover.chartOpen I U a).1) (hWV : W ≤ V)
    (t : ToType ((blowUpTwist I ((n : ℤ) * ((1 : ℕ) : ℤ))).val.obj (op V))) :
    ((blowUp I).presheaf.map (homOfLE hWV).op).hom (chartTwistPowCoeff I n U a hV t)
      = chartTwistPowCoeff I n U a (hWV.trans hV)
          ((blowUpTwist I ((n : ℤ) * ((1 : ℕ) : ℤ))).val.restrictₛₗ (homOfLE hWV).op t) := by
  refine (chartTwistPowCoeff_eq_of_app_eq I n U a (hWV.trans hV) _ _ ?_).symm
  refine Eq.trans (Situation.map_chartSectionsIso_hom (reesSituation I) U hWV _) ?_
  refine Eq.trans (congrArg (((AlgebraicGeometry.Proj
      ((reesSituation I).sectionRingGrading U.1)).presheaf.map
      (homOfLE (Scheme.Hom.preimage_mono
        (Situation.relativeProjChart (reesSituation I) U) hWV)).op).hom)
    (app_relativeProjChart_chartTwistPowCoeff I n U a hV t)) ?_
  rw [chartTwistPowSections_map]
  exact (twistPowCoeff_map ((reesSituation I).sectionRingGrading U.1) n
    (reesDegreeOne I U a).2 (preimage_relativeProjChart_le_basicOpen I U a hV)
    (preimage_relativeProjChart_le_basicOpen I U a (hWV.trans hV))
    (Scheme.Hom.preimage_mono (Situation.relativeProjChart (reesSituation I) U) hWV)
    (chartTwistPowSections I n U a hV t)).symm

/-- The trivialization of `𝒪_{X'}(n)` over an open of the chart at `a`. -/
def chartTwistPowEquiv {V : (blowUp I).Opens}
    (hV : V ≤ (Stacks.BlowUpChartCover.chartOpen I U a).1) :
    ToType ((blowUpTwist I ((n : ℤ) * ((1 : ℕ) : ℤ))).val.obj (op V))
      ≃ₗ[ToType ((blowUp I).ringCatSheaf.obj.obj (op V))]
        ToType ((blowUp I).ringCatSheaf.obj.obj (op V)) :=
  LinearEquiv.ofBijective
    (({ toFun := chartTwistPowCoeff I n U a hV
        map_add' := chartTwistPowCoeff_add I n U a hV
        map_smul' := chartTwistPowCoeff_smul I n U a hV } :
      ToType ((blowUpTwist I ((n : ℤ) * ((1 : ℕ) : ℤ))).val.obj (op V))
        →ₗ[ToType ((blowUp I).ringCatSheaf.obj.obj (op V))]
          ToType ((blowUp I).ringCatSheaf.obj.obj (op V))))
    (bijective_chartTwistPowCoeff I n U a hV)

/-- The trivialization `chartTwistPowEquiv` sends a section to its trivializing coefficient. -/
@[simp] theorem chartTwistPowEquiv_apply {V : (blowUp I).Opens}
    (hV : V ≤ (Stacks.BlowUpChartCover.chartOpen I U a).1)
    (t : ToType ((blowUpTwist I ((n : ℤ) * ((1 : ℕ) : ℤ))).val.obj (op V))) :
    chartTwistPowEquiv I n U a hV t = chartTwistPowCoeff I n U a hV t := rfl

/-! ### The chartwise trivialization of `(ℐ𝒪_{X'})ⁿ` -/

/-- **The `n`-th power of the ideal sheaf of the exceptional divisor of a blowup**, as a sheaf of
modules: the ideal sheaf of the `n`-fold thickening of the exceptional divisor. -/
abbrev exceptionalIdealPowModule : (blowUp I).Modules :=
  Stacks.ClosedImmersion.idealSheaf (exceptionalIdeal I ^ n).subschemeι.toLRSHom.toShHom

/-- On the standard chart at `a`, the `n`-th power of the exceptional ideal is generated by the
`n`-th power of the pullback of `a`. -/
theorem ideal_exceptionalIdeal_pow_eq_span_chartGenerator_pow :
    (exceptionalIdeal I ^ n).ideal (Stacks.BlowUpChartCover.chartOpen I U a) =
      Ideal.span {Stacks.BlowUpChartCover.chartGenerator I U a ^ n} := by
  rw [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply,
    Stacks.BlowUpChartCover.ideal_exceptionalIdeal_eq_span_chartGenerator,
    Ideal.span_singleton_pow]

/-- The trivialization of the `n`-th power of the exceptional ideal sheaf over an open of the
chart at `a`, by the `n`-th power of the pullback of `a`. -/
def chartIdealPowEquiv {V : (blowUp I).Opens}
    (hV : V ≤ (Stacks.BlowUpChartCover.chartOpen I U a).1) :
    ToType ((exceptionalIdealPowModule I n).val.obj (op V))
      ≃ₗ[ToType ((blowUp I).ringCatSheaf.obj.obj (op V))]
        ToType ((blowUp I).ringCatSheaf.obj.obj (op V)) :=
  (Stacks.CartierAffineLocalConverse.trivialization (exceptionalIdeal I ^ n)
    (Stacks.BlowUpChartCover.chartOpen I U a) (Stacks.BlowUpChartCover.chartGenerator I U a ^ n)
    (pow_mem (Stacks.BlowUpChartCover.chartGenerator_mem_nonZeroDivisors I U a) n)
    (ideal_exceptionalIdeal_pow_eq_span_chartGenerator_pow I n U a)).θ V (homOfLE hV)

/-- **The chartwise comparison of `𝒪_{X'}(n)` with `(ℐ𝒪_{X'})ⁿ`** over an open of the standard
affine chart at `a`: divide by the trivializing section `(a⁽¹⁾)ⁿ`, then multiply by the `n`-th
power of the pullback of `a`. -/
def chartPowEquiv {V : (blowUp I).Opens}
    (hV : V ≤ (Stacks.BlowUpChartCover.chartOpen I U a).1) :
    ToType ((blowUpTwist I ((n : ℤ) * ((1 : ℕ) : ℤ))).val.obj (op V))
      ≃ₗ[ToType ((blowUp I).ringCatSheaf.obj.obj (op V))]
        ToType ((exceptionalIdealPowModule I n).val.obj (op V)) :=
  (chartTwistPowEquiv I n U a hV).trans (chartIdealPowEquiv I n U a hV).symm

/-- **The chartwise comparison is division by `(a⁽¹⁾)ⁿ` followed by multiplication by `aⁿ`.**
The image in the structure sheaf of the section of `(ℐ𝒪_{X'})ⁿ` attached to `t` is the
trivializing coefficient of `t` times the `n`-th power of the restricted generator. -/
theorem incl_app_chartPowEquiv {V : (blowUp I).Opens}
    (hV : V ≤ (Stacks.BlowUpChartCover.chartOpen I U a).1)
    (t : ToType ((blowUpTwist I ((n : ℤ) * ((1 : ℕ) : ℤ))).val.obj (op V))) :
    ((Stacks.CartierAffineLocal.incl (exceptionalIdeal I ^ n)).val.app (op V)).hom
        (chartPowEquiv I n U a hV t)
      = chartTwistPowCoeff I n U a hV t * chartGeneratorRes I U a hV ^ n := by
  refine (Stacks.CartierAffineLocalConverse.incl_app_eq_θ_mul (exceptionalIdeal I ^ n)
    (Stacks.BlowUpChartCover.chartOpen I U a)
    (Stacks.BlowUpChartCover.chartGenerator I U a ^ n)
    (pow_mem (Stacks.BlowUpChartCover.chartGenerator_mem_nonZeroDivisors I U a) n)
    (ideal_exceptionalIdeal_pow_eq_span_chartGenerator_pow I n U a)
    (homOfLE hV) (chartPowEquiv I n U a hV t) _
    ((chartIdealPowEquiv I n U a hV).apply_symm_apply _)).trans ?_
  exact congrArg (chartTwistPowCoeff I n U a hV t * ·) (map_pow _ _ n)

/-- **The chartwise comparison commutes with restriction.** -/
theorem chartPowEquiv_map {V W : (blowUp I).Opens}
    (hV : V ≤ (Stacks.BlowUpChartCover.chartOpen I U a).1) (hWV : W ≤ V)
    (t : ToType ((blowUpTwist I ((n : ℤ) * ((1 : ℕ) : ℤ))).val.obj (op V))) :
    chartPowEquiv I n U a (hWV.trans hV)
        ((blowUpTwist I ((n : ℤ) * ((1 : ℕ) : ℤ))).val.restrictₛₗ (homOfLE hWV).op t)
      = (exceptionalIdealPowModule I n).val.restrictₛₗ (homOfLE hWV).op
          (chartPowEquiv I n U a hV t) := by
  refine Stacks.CartierAffineLocal.injective_incl_app (exceptionalIdeal I ^ n) W ?_
  have hL := incl_app_chartPowEquiv I n U a (hWV.trans hV)
    ((blowUpTwist I ((n : ℤ) * ((1 : ℕ) : ℤ))).val.restrictₛₗ (homOfLE hWV).op t)
  have hnat := PresheafOfModules.naturality_apply
    (Stacks.CartierAffineLocal.incl (exceptionalIdeal I ^ n)).val (homOfLE hWV).op
    (chartPowEquiv I n U a hV t)
  have hR := incl_app_chartPowEquiv I n U a hV t
  have hc := chartTwistPowCoeff_map I n U a hV hWV t
  refine hL.trans (Eq.symm (hnat.trans ?_))
  refine (congrArg ((blowUp I).presheaf.map (homOfLE hWV).op).hom hR).trans ?_
  refine (map_mul ((blowUp I).presheaf.map (homOfLE hWV).op).hom _ _).trans ?_
  refine (congrArg (fun y => y * ((blowUp I).presheaf.map (homOfLE hWV).op).hom
    (chartGeneratorRes I U a hV ^ n)) hc).trans ?_
  refine congrArg (fun z => chartTwistPowCoeff I n U a (hWV.trans hV)
    ((blowUpTwist I ((n : ℤ) * ((1 : ℕ) : ℤ))).val.restrictₛₗ (homOfLE hWV).op t) * z) ?_
  exact (map_pow _ _ n).trans (congrArg (· ^ n) (map_chartGeneratorRes I U a hV hWV))

/-! ### Two charts of the blowup -/

/-- Two chartwise comparisons agree as soon as the coefficient-times-generator expressions they
are sent to in the structure sheaf do. -/
private theorem chartPowEquiv_eq_of_mul_eq {U U' : X.affineOpens} {a : I.ideal U}
    {a' : I.ideal U'} {V : (blowUp I).Opens}
    (hVa : V ≤ (Stacks.BlowUpChartCover.chartOpen I U a).1)
    (hVa' : V ≤ (Stacks.BlowUpChartCover.chartOpen I U' a').1)
    (t : ToType ((blowUpTwist I ((n : ℤ) * ((1 : ℕ) : ℤ))).val.obj (op V)))
    (h : chartTwistPowCoeff I n U a hVa t * chartGeneratorRes I U a hVa ^ n
      = chartTwistPowCoeff I n U' a' hVa' t * chartGeneratorRes I U' a' hVa' ^ n) :
    chartPowEquiv I n U a hVa t = chartPowEquiv I n U' a' hVa' t :=
  Stacks.CartierAffineLocal.injective_incl_app (exceptionalIdeal I ^ n) V
    ((incl_app_chartPowEquiv I n U a hVa t).trans
      (h.trans (incl_app_chartPowEquiv I n U' a' hVa' t).symm))

/-- **Two charts over the same affine open of the base give the same comparison of `𝒪_{X'}(n)`
with `(ℐ𝒪_{X'})ⁿ`.** The identity is checked inside the single `Proj 𝒜(U)`, where it is
`AlgebraicGeometry.twistPowCoeff_mul_chartBaseSectionRes_pow_comm`. -/
theorem chartPowEquiv_agree_of_eq_base (a' : I.ideal U) {V : (blowUp I).Opens}
    (hVa : V ≤ (Stacks.BlowUpChartCover.chartOpen I U a).1)
    (hVa' : V ≤ (Stacks.BlowUpChartCover.chartOpen I U a').1)
    (t : ToType ((blowUpTwist I ((n : ℤ) * ((1 : ℕ) : ℤ))).val.obj (op V))) :
    chartPowEquiv I n U a hVa t = chartPowEquiv I n U a' hVa' t := by
  refine chartPowEquiv_eq_of_mul_eq I n hVa hVa' t ?_
  refine Situation.injective_app_relativeProjChart (reesSituation I) U
    (hVa.trans (chartOpen_le_opensRange_relativeProjChart I U a)) ?_
  have hgen : ∀ (b : I.ideal U) (hb : V ≤ (Stacks.BlowUpChartCover.chartOpen I U b).1),
      ((Situation.relativeProjChart (reesSituation I) U).app V).hom
          (chartGeneratorRes I U b hb ^ n)
        = (reesSituation I).chartBaseSectionRes U.1 U.2 ((b : Γ(X, U.1)) ^ n)
            (Situation.relativeProjChart (reesSituation I) U ⁻¹ᵁ V) := fun b hb => by
    refine Eq.trans (congrArg ((Situation.relativeProjChart (reesSituation I) U).app V).hom
      ((congrArg (· ^ n) (chartGeneratorRes_eq_appLE I U b hb)).trans
        (map_pow _ _ n).symm)) ?_
    exact (reesSituation I).app_relativeProjChart_appLE U ((b : Γ(X, U.1)) ^ n)
      (hb.trans (Stacks.BlowUpChartCover.chartOpen_le I U b))
  refine Eq.trans (map_mul
    ((Situation.relativeProjChart (reesSituation I) U).app V).hom _ _) ?_
  refine Eq.symm (Eq.trans (map_mul
    ((Situation.relativeProjChart (reesSituation I) U).app V).hom _ _) ?_)
  refine Eq.symm (Eq.trans (congrArg₂ (· * ·)
    (app_relativeProjChart_chartTwistPowCoeff I n U a hVa t) (hgen a hVa)) ?_)
  refine Eq.trans ?_ (congrArg₂ (· * ·)
    (app_relativeProjChart_chartTwistPowCoeff I n U a' hVa' t) (hgen a' hVa')).symm
  exact twistPowCoeff_mul_chartBaseSectionRes_pow_comm I n U a a'
    (preimage_relativeProjChart_le_basicOpen I U a hVa)
    (preimage_relativeProjChart_le_basicOpen I U a' hVa')
    (chartTwistPowSections I n U a hVa t)

section TwoBases

variable {U U' : X.affineOpens} (h : U' ≤ U) (a : I.ideal U)

/-- **The trivializing coefficient of `𝒪_{X'}(n)` does not change under passing to the chart over
a smaller affine open of the base.** This is `AlgebraicGeometry.chartTwistCoeff_eq_of_le` in
degree `n`: the coefficient is transported along the Tag 01NO chart transition by
`Stacks.ProjTwistComparison.app_trivializingEquiv_symm_of_mem_one`. -/
theorem chartTwistPowCoeff_eq_of_le {V : (blowUp I).Opens}
    (hV : V ≤ (Stacks.BlowUpChartCover.chartOpen I U a).1)
    (hV' : V ≤ (Stacks.BlowUpChartCover.chartOpen I U' (restrictIdeal I h a)).1)
    (t : ToType ((blowUpTwist I ((n : ℤ) * ((1 : ℕ) : ℤ))).val.obj (op V))) :
    chartTwistPowCoeff I n U a hV t = chartTwistPowCoeff I n U' (restrictIdeal I h a) hV' t := by
  have hWW : Situation.projInclusionMap (reesSituation I) U'.1 U.1 h U'.2 U.2 ⁻¹ᵁ
        (Situation.relativeProjChart (reesSituation I) U ⁻¹ᵁ V)
      ≤ ProjectiveSpectrum.basicOpen ((reesSituation I).sectionRingGrading U'.1)
          (reesDegreeOne I U' (restrictIdeal I h a)).1 :=
    (Scheme.Hom.preimage_mono _ (preimage_relativeProjChart_le_basicOpen I U a hV)).trans
      (projInclusionMap_preimage_basicOpen_reesDegreeOne I h a).le
  have hstep : (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf
        ((reesSituation I).sectionRingGrading U'.1) ((n : ℤ) * ((1 : ℕ) : ℤ))).val.restrictₛₗ
        (homOfLE (Situation.preimage_relativeProjChart_eq (reesSituation I) h V).le).op
        (Stacks.ProjTwistComparison.sectionsMap
          (Situation.gradedSectionRestriction (reesSituation I) U'.1 U.1 h)
          (Situation.irrelevant_le_map_gradedSectionRestriction (reesSituation I) U'.1 U.1 h
            U'.2 U.2) ((n : ℤ) * ((1 : ℕ) : ℤ))
          (Situation.relativeProjChart (reesSituation I) U ⁻¹ᵁ V)
          (chartTwistPowSections I n U a hV t))
      = chartTwistPowSections I n U' (restrictIdeal I h a) hV' t := by
    refine Eq.trans ?_ (Situation.twistPushforwardMap_twistSectionsIso (reesSituation I)
      ((n : ℤ) * ((1 : ℕ) : ℤ)) h
      (hV'.trans (chartOpen_le_opensRange_relativeProjChart I U' (restrictIdeal I h a))) t)
    refine Eq.trans ?_ (Situation.twistPushforwardMap_apply (reesSituation I)
      ((n : ℤ) * ((1 : ℕ) : ℤ)) h (chartTwistPowSections I n U a hV t)).symm
    exact congrArg (fun i => ((Situation.twistChart (reesSituation I)
      ((n : ℤ) * ((1 : ℕ) : ℤ)) U').presheaf.map i).hom
      (Stacks.ProjTwistComparison.sectionsMap
        (Situation.gradedSectionRestriction (reesSituation I) U'.1 U.1 h)
        (Situation.irrelevant_le_map_gradedSectionRestriction (reesSituation I) U'.1 U.1 h
          U'.2 U.2) ((n : ℤ) * ((1 : ℕ) : ℤ))
        (Situation.relativeProjChart (reesSituation I) U ⁻¹ᵁ V)
        (chartTwistPowSections I n U a hV t))) (Subsingleton.elim _ _)
  refine Situation.injective_app_relativeProjChart (reesSituation I) U'
    (hV'.trans (chartOpen_le_opensRange_relativeProjChart I U' (restrictIdeal I h a))) ?_
  refine Eq.trans (Situation.app_relativeProjChart_of_le (reesSituation I) h _) ?_
  refine Eq.trans (congrArg
    (((Situation.projInclusionMap (reesSituation I) U'.1 U.1 h U'.2 U.2).appLE
        (Situation.relativeProjChart (reesSituation I) U ⁻¹ᵁ V)
        (Situation.relativeProjChart (reesSituation I) U' ⁻¹ᵁ V)
        (Situation.preimage_relativeProjChart_eq (reesSituation I) h V).le).hom)
    (app_relativeProjChart_chartTwistPowCoeff I n U a hV t)) ?_
  refine Eq.trans (congrArg
    (((AlgebraicGeometry.Proj ((reesSituation I).sectionRingGrading U'.1)).presheaf.map
      (homOfLE (Situation.preimage_relativeProjChart_eq (reesSituation I) h V).le).op).hom)
    (Stacks.ProjTwistComparison.app_trivializingEquiv_symm_of_mem_one
      (Situation.gradedSectionRestriction (reesSituation I) U'.1 U.1 h)
      (Situation.irrelevant_le_map_gradedSectionRestriction (reesSituation I) U'.1 U.1 h
        U'.2 U.2) n
      (reesDegreeOne I U a).2 (reesDegreeOne I U' (restrictIdeal I h a)).2
      (gradedSectionRestriction_reesDegreeOne I h a)
      (preimage_relativeProjChart_le_basicOpen I U a hV) hWW
      (chartTwistPowSections I n U a hV t))) ?_
  refine Eq.trans (twistPowCoeff_map ((reesSituation I).sectionRingGrading U'.1) n
    (reesDegreeOne I U' (restrictIdeal I h a)).2 hWW
    (preimage_relativeProjChart_le_basicOpen I U' (restrictIdeal I h a) hV')
    (Situation.preimage_relativeProjChart_eq (reesSituation I) h V).le _).symm ?_
  refine Eq.trans (congrArg (twistPowCoeff ((reesSituation I).sectionRingGrading U'.1) n
    (reesDegreeOne I U' (restrictIdeal I h a)).2
    (preimage_relativeProjChart_le_basicOpen I U' (restrictIdeal I h a) hV')) hstep) ?_
  exact (app_relativeProjChart_chartTwistPowCoeff I n U' (restrictIdeal I h a) hV' t).symm

/-- **The chartwise comparison does not change under passing to the chart over a smaller affine
open of the base.** -/
theorem chartPowEquiv_agree_of_le {V : (blowUp I).Opens}
    (hV : V ≤ (Stacks.BlowUpChartCover.chartOpen I U a).1)
    (hV' : V ≤ (Stacks.BlowUpChartCover.chartOpen I U' (restrictIdeal I h a)).1)
    (t : ToType ((blowUpTwist I ((n : ℤ) * ((1 : ℕ) : ℤ))).val.obj (op V))) :
    chartPowEquiv I n U a hV t = chartPowEquiv I n U' (restrictIdeal I h a) hV' t := by
  refine chartPowEquiv_eq_of_mul_eq I n hV hV' t ?_
  exact congrArg₂ (· * ·) (chartTwistPowCoeff_eq_of_le I n h a hV hV' t)
    (congrArg (· ^ n) (chartGeneratorRes_eq_of_le I h a hV hV'))

end TwoBases

/-- **Any two chartwise comparisons of `𝒪_{X'}(n)` with `(ℐ𝒪_{X'})ⁿ` agree** wherever both are
defined. As for `AlgebraicGeometry.chartEquiv_agree`, the identity is checked on the cover of the
overlap by the parts lying over the affine opens inside `U ⊓ U'` and propagated by the sheaf
condition. -/
theorem chartPowEquiv_agree (k l : (U : X.affineOpens) × I.ideal U) {V : (blowUp I).Opens}
    (hk : V ≤ (Stacks.BlowUpChartCover.chartOpen I k.1 k.2).1)
    (hl : V ≤ (Stacks.BlowUpChartCover.chartOpen I l.1 l.2).1)
    (t : ToType ((blowUpTwist I ((n : ℤ) * ((1 : ℕ) : ℤ))).val.obj (op V))) :
    chartPowEquiv I n k.1 k.2 hk t = chartPowEquiv I n l.1 l.2 hl t := by
  refine (OModuleLocalPresheaf.isSheaf_ofSheafOfModules (exceptionalIdealPowModule I n)
      (⊤ : (blowUp I).Opens)).eq_of_locally_eq (hV := le_top)
    (fun T : {T : X.affineOpens // T.1 ≤ k.1.1 ⊓ l.1.1} =>
      V ⊓ (Situation.relativeProjChart (reesSituation I) T.1).opensRange)
    (fun _ => inf_le_left) (le_iSup_inf_opensRange_relativeProjChart I k l hk hl) fun T => ?_
  have side : ∀ (m : (U : X.affineOpens) × I.ideal U) (hTm : T.1 ≤ m.1)
      (hm : V ≤ (Stacks.BlowUpChartCover.chartOpen I m.1 m.2).1)
      (hZ : V ⊓ (Situation.relativeProjChart (reesSituation I) T.1).opensRange
        ≤ (Stacks.BlowUpChartCover.chartOpen I T.1 (restrictIdeal I hTm m.2)).1),
      (exceptionalIdealPowModule I n).val.restrictₛₗ
          (homOfLE (inf_le_left : V ⊓ (Situation.relativeProjChart (reesSituation I)
            T.1).opensRange ≤ V)).op (chartPowEquiv I n m.1 m.2 hm t)
        = chartPowEquiv I n T.1 (restrictIdeal I hTm m.2) hZ
          ((blowUpTwist I ((n : ℤ) * ((1 : ℕ) : ℤ))).val.restrictₛₗ
            (homOfLE (inf_le_left : V ⊓ (Situation.relativeProjChart (reesSituation I)
              T.1).opensRange ≤ V)).op t) := fun m hTm hm hZ =>
    (chartPowEquiv_map I n m.1 m.2 hm inf_le_left t).symm.trans
      (chartPowEquiv_agree_of_le I n hTm m.2 (inf_le_left.trans hm) hZ _)
  have hZ : ∀ (m : (U : X.affineOpens) × I.ideal U) (hTm : T.1 ≤ m.1)
      (hm : V ≤ (Stacks.BlowUpChartCover.chartOpen I m.1 m.2).1),
      V ⊓ (Situation.relativeProjChart (reesSituation I) T.1).opensRange
        ≤ (Stacks.BlowUpChartCover.chartOpen I T.1 (restrictIdeal I hTm m.2)).1 :=
    fun m hTm hm => by
      rw [chartOpen_restrictIdeal_eq I hTm m.2]
      exact le_inf inf_le_right (inf_le_left.trans hm)
  have hTk : T.1 ≤ k.1 := T.2.trans inf_le_left
  have hTl : T.1 ≤ l.1 := T.2.trans inf_le_right
  exact (side k hTk hk (hZ k hTk hk)).trans
    ((chartPowEquiv_agree_of_eq_base I n T.1 (restrictIdeal I hTk k.2)
      (restrictIdeal I hTl l.2) _ _ _).trans (side l hTl hl (hZ l hTl hl)).symm)

/-- **The glueing datum of the comparison of `𝒪_{X'}(n)` with `(ℐ𝒪_{X'})ⁿ`**: the chartwise
comparisons over the standard affine charts of the blowup. -/
def twistPowLocalEquiv :
    OModuleLocalPresheaf.LocalEquiv
      (OModuleLocalPresheaf.ofSheafOfModules (blowUpTwist I ((n : ℤ) * ((1 : ℕ) : ℤ))) ⊤)
      (OModuleLocalPresheaf.ofSheafOfModules (exceptionalIdealPowModule I n) ⊤)
      ((U : X.affineOpens) × I.ideal U) where
  cover k := (Stacks.BlowUpChartCover.chartOpen I k.1 k.2).1
  cover_le _ := le_top
  le_iSup_cover := (iSup_chartOpen_eq_top I).ge
  equiv k _ hV := chartPowEquiv I n k.1 k.2 hV
  equiv_map k _ _ hV hWV t := chartPowEquiv_map I n k.1 k.2 hV hWV t
  equiv_agree k l _ hk hl t := chartPowEquiv_agree I n k l hk hl t

/-- On the chart at `a`, the glued comparison of `𝒪_{X'}(n)` with `(ℐ𝒪_{X'})ⁿ` is the chartwise
comparison at `a`. -/
theorem twistPowLocalEquiv_gluedIso_hom_app_of_le {V : (blowUp I).Opens}
    (hV : V ≤ (Stacks.BlowUpChartCover.chartOpen I U a).1)
    (t : ToType ((blowUpTwist I ((n : ℤ) * ((1 : ℕ) : ℤ))).val.obj (op V))) :
    (((twistPowLocalEquiv I n).gluedIso).hom.val.app (op V)).hom t = chartPowEquiv I n U a hV t :=
  (twistPowLocalEquiv I n).glueLinearEquiv_eq
    (OModuleLocalPresheaf.isSheaf_ofSheafOfModules (blowUpTwist I ((n : ℤ) * ((1 : ℕ) : ℤ))) ⊤)
    (OModuleLocalPresheaf.isSheaf_ofSheafOfModules (exceptionalIdealPowModule I n) ⊤) ⟨U, a⟩ hV t

/-- **The glued comparison on a chart is division by `(a⁽¹⁾)ⁿ` followed by multiplication by
`aⁿ`.** Over an open `V` of the standard chart at `a ∈ ℐ(U)`, the image in the structure sheaf of
the section of `(ℐ𝒪_{X'})ⁿ` that the glued comparison attaches to a section `t` of `𝒪_{X'}(n)` is
`t` divided by the trivializing section `(a⁽¹⁾)ⁿ`, times the `n`-th power of the pullback of `a`.
This is the description that makes the comparison canonical: it is the map induced by the
inclusions `Iᵈ⁺ⁿ ⊆ Iᵈ` of the Rees algebra, and it does not depend on `a`
(`AlgebraicGeometry.chartPowEquiv_agree`). -/
theorem incl_app_twistPowLocalEquiv_gluedIso_hom {V : (blowUp I).Opens}
    (hV : V ≤ (Stacks.BlowUpChartCover.chartOpen I U a).1)
    (t : ToType ((blowUpTwist I ((n : ℤ) * ((1 : ℕ) : ℤ))).val.obj (op V))) :
    ((Stacks.CartierAffineLocal.incl (exceptionalIdeal I ^ n)).val.app (op V)).hom
        ((((twistPowLocalEquiv I n).gluedIso).hom.val.app (op V)).hom t)
      = chartTwistPowCoeff I n U a hV t * chartGeneratorRes I U a hV ^ n := by
  rw [twistPowLocalEquiv_gluedIso_hom_app_of_le I n U a hV t]
  exact incl_app_chartPowEquiv I n U a hV t

/-- The twist `𝒪_{X'}(n)` is the twist in degree `n * 1`, the degree in which the trivialization
by a degree-one element lands. -/
theorem blowUpTwist_eq_mul_one : blowUpTwist I n = blowUpTwist I ((n : ℤ) * ((1 : ℕ) : ℤ)) :=
  congrArg (blowUpTwist I) (by push_cast; ring)

/-- The ideal sheaf `(ℐ𝒪_{X'})ⁿ` is, on the nose, the degree-`n` piece
`Stacks.Blowup.idealPowerKernel` of the Rees algebra of the exceptional ideal sheaf: both are the
kernel of `𝒪_{X'} ⟶ (ι)_* 𝒪_{nE}`, one spelled at ringed spaces and the other at schemes. -/
def exceptionalIdealPowModuleIso :
    exceptionalIdealPowModule I n ≅ Stacks.Blowup.idealPowerKernel (exceptionalIdeal I) n :=
  Iso.refl _

/-- The identification `exceptionalIdealPowModuleIso` is compatible with the inclusions into the
structure sheaf. -/
theorem exceptionalIdealPowModuleIso_hom_comp_exceptionalTwistInclusion :
    (exceptionalIdealPowModuleIso I n).hom ≫ exceptionalTwistInclusion I n =
      Stacks.CartierAffineLocal.incl (exceptionalIdeal I ^ n) :=
  Category.id_comp _

/-- **`𝒪_{X'}(n) ≅ (ℐ𝒪_{X'})ⁿ`** for the blowup `X'` of an arbitrary scheme `X` in an arbitrary
quasi-coherent sheaf of ideals `ℐ` and every `n ≥ 0`: the `n`-th twisting sheaf of the blowup is
the ideal sheaf of the `n`-fold thickening of the exceptional divisor, written as the degree-`n`
piece of the Rees algebra of the exceptional ideal sheaf. At `n = 1` this is part (3) of
[Stacks, Tag 02OS] (`AlgebraicGeometry.twistOneIsoExceptionalIdealModule`). -/
def blowUpTwistIsoExceptionalIdealPow :
    blowUpTwist I n ≅ Stacks.Blowup.idealPowerKernel (exceptionalIdeal I) n :=
  eqToIso (blowUpTwist_eq_mul_one I n) ≪≫ (twistPowLocalEquiv I n).gluedIso ≪≫
    exceptionalIdealPowModuleIso I n

/-! ### The canonical map `𝒪_{X'}(n) ⟶ 𝒪_{X'}` -/


/-- **The canonical map `𝒪_{X'}(n) ⟶ 𝒪_{X'}`** of the blowup: the identification of `𝒪_{X'}(n)`
with the ideal sheaf `(ℐ𝒪_{X'})ⁿ` followed by its inclusion into the structure sheaf. On the chart
at `a ∈ ℐ(U)` it is division by `(a⁽¹⁾)ⁿ` followed by multiplication by the `n`-th power of the
pullback of `a` (`AlgebraicGeometry.incl_app_twistPowLocalEquiv_gluedIso_hom`), the map that the
inclusions `Iᵈ⁺ⁿ ⊆ Iᵈ` of the Rees algebra induce. -/
def blowUpTwistToUnit : blowUpTwist I n ⟶ SheafOfModules.unit (blowUp I).ringCatSheaf :=
  (blowUpTwistIsoExceptionalIdealPow I n).hom ≫ exceptionalTwistInclusion I n

/-! ### Tag 0GA9 -/

attribute [local instance] modulesMonoidal

/-- **The canonical map `𝓕(n) ⟶ 𝓕`** on the blowup, for `𝓕(n) = 𝓕 ⊗ 𝒪_{X'}(n)`: the canonical map
`𝒪_{X'}(n) ⟶ 𝒪_{X'}` tensored with `𝓕`, followed by the right unitor. -/
def blowUpTwistContraction (F : (blowUp I).Modules) : F ⊗ blowUpTwist I n ⟶ F :=
  (F ◁ blowUpTwistToUnit I n) ≫ (ρ_ F).hom

/-- The canonical map `𝓕(n) ⟶ 𝓕` is the map `𝓕 ⊗ (ℐ𝒪_{X'})ⁿ ⟶ 𝓕` of
`AlgebraicGeometry.exceptionalTwistContraction`, precomposed with the identification
`𝒪_{X'}(n) ≅ (ℐ𝒪_{X'})ⁿ`. -/
theorem blowUpTwistContraction_eq (F : (blowUp I).Modules) :
    blowUpTwistContraction I n F =
      (F ◁ (blowUpTwistIsoExceptionalIdealPow I n).hom) ≫ exceptionalTwistContraction I n F := by
  change (F ◁ ((blowUpTwistIsoExceptionalIdealPow I n).hom ≫ exceptionalTwistInclusion I n)) ≫
    (ρ_ F).hom = _
  exact (congrArg (· ≫ (ρ_ F).hom) (MonoidalCategory.whiskerLeft_comp F _ _)).trans
    (Category.assoc _ _ _)

/-- **Stacks Project, Tag 0GA9.** Let `X'` be the blowup of a scheme `X` in a quasi-coherent sheaf
of ideals `ℐ`, with exceptional divisor `Y` cut out by `ℐ𝒪_{X'}`, and let `Y_c = cY` be its
`c`-fold thickening. A quasi-coherent `𝒪_{X'}`-module `𝓕` of finite type is scheme theoretically
supported on `Y_c` if and only if the canonical map `𝓕(c) ⟶ 𝓕` is zero, where
`𝓕(c) = 𝓕 ⊗ 𝒪_{X'}(c)` is the Serre twist and the canonical map is induced by
`𝒪_{X'}(c) ⟶ 𝒪_{X'}` (`AlgebraicGeometry.blowUpTwistToUnit`).

Stacks writes the canonical map as `𝓕 ⟶ 𝓕(c)`, induced by a map `𝒪_X ⟶ 𝒪_X(1)` vanishing exactly
along `Y`; but the section begins by recording `𝒪_X(1) = 𝒪_X(-Y)`, the ideal sheaf of `Y`, so the
map that exists and vanishes along `Y` is the inclusion `𝒪_X(1) ⟶ 𝒪_X`, and the statement is
read with it. -/
@[stacks 0GA9 "corrected: the canonical map runs 𝓕(c) ⟶ 𝓕, since 𝒪(1) is the ideal sheaf of Y"]
theorem schemeTheoreticSupport_iff_blowUpTwistContraction_eq_zero
    (F : (blowUp I).Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    exceptionalIdeal I ^ n ≤ Scheme.Modules.schemeTheoreticSupport F ↔
      blowUpTwistContraction I n F = 0 := by
  rw [schemeTheoreticSupport_iff_exceptionalTwistContraction_eq_zero, blowUpTwistContraction_eq]
  constructor
  · intro h
    rw [h, comp_zero]
  · intro h
    exact (cancel_epi (F ◁ (blowUpTwistIsoExceptionalIdealPow I n).hom)).1
      (h.trans comp_zero.symm)

end AlgebraicGeometry

end
