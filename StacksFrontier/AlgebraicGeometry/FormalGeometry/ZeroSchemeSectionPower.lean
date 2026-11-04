module

public import StacksFrontier.AlgebraicGeometry.SectionRingProjQuasicoherent.Division
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemePower
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.SectionPowerThickenings
public import StacksFrontier.AlgebraicGeometry.SectionRingVeroneseChart.DegreeOne
public import StacksFrontier.AlgebraicGeometry.TensorPowerDivision.Basic
public import StacksFrontier.AlgebraicGeometry.SectionRingProjOverlap.Basic
public import StacksFrontier.AlgebraicGeometry.TensorPowerTrivialize.Power

/-!
# The zero scheme of a power of a section, in the section ring

Let `X` be a scheme, `L` an ample invertible `𝒪_X`-module and `s ∈ Γ(X, L)`. Read `s` as a
homogeneous element of degree one of the section ring `Γ_*(X, L)`; its `D`-th power is a global
section `sᴰ` of `L ^⊗ D`. This file proves that the zero scheme of `sᴰ` is the `D`-th power of
the zero scheme of `s`:

`Z(sᴰ) = Z(s)ᴰ`.

The analogous statement for the sectionwise powers of the tensor-power construction is
`AlgebraicGeometry.zeroScheme_eval_sectionPow'`; the statement here is for the powers in the
section ring of Stacks Tag 01CV, over which the standard opens of `Proj Γ_*(X, L)` and the
division of Stacks Tag 01PW live.

## Implementation notes

Both sides are compared one affine open at a time through
`AlgebraicGeometry.zeroScheme_pow_eq_of_cover`, which asks, on each open of an affine cover, for a
generator `γ` of `L`, a generator `ω` of `L ^⊗ D` and a function `a` with `s = a γ` and
`sᴰ = aᴰ ω`. Ampleness gives sections `u` of `L ^⊗ m` and `u'` of `L ^⊗ (m+1)` not vanishing at
a given point, and on an affine open `V` inside both nonvanishing loci the generators are the
ratios `γ = u'/u` and `ω = u'ᴰ/uᴰ`: multiplication by `u` and by `uᴰ` is bijective on `V`. With
`a` the ratio of `u s` to `u'`, the relation `s = a γ` is `u s = a u'`, and `sᴰ = aᴰ ω` is
`(u s)ᴰ = aᴰ u'ᴰ`, which is `Stacks.SectionExtension.resTop_globalSection_powSec`.

## Main definitions

* `Stacks.Algebraization.degreeOneSection`: a global section of `L`, as a homogeneous element of
  degree one of the section ring.

## Main results

* `Stacks.Algebraization.zeroScheme_powSec_degreeOneSection`: `Z(sᴰ) = Z(s)ᴰ`.

## References

* [Stacks Project, Tag 02OQ](https://stacks.math.columbia.edu/tag/02OQ)
* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite TopologicalSpace
open Stacks.TensorPowers (natTensorPow)
open Stacks.GradedSections (powSections mul mulMap)
open Stacks.SectionProduct (globalSection)
open Stacks.AmpleFiniteAvoidance (nvOpen)
open Stacks.SectionExtension (powSec)
open Stacks.SectionRingProjQuasicoherent (unitSec)

universe u

namespace Stacks.Algebraization

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

variable {X : Scheme.{u}} (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]

/-- **A global section of `L`, as a homogeneous element of degree one of the section ring**,
through the left unitor `L ^⊗ 1 = 𝟙 ⊗ L ≅ L`. -/
def degreeOneSection (s : Γ(L, ⊤)) : powSections L 1 :=
  (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X (natTensorPow L 1)).symm
    ((λ_ L).inv.app ⊤ s)

omit [Ample.IsInvertibleModule X L] in
/-- The global section of `L ^⊗ 1` underlying `degreeOneSection L s` is the image of `s` under
the inverse of the left unitor. -/
theorem globalSection_degreeOneSection (s : Γ(L, ⊤)) :
    globalSection X _ (degreeOneSection L s) = (λ_ L).inv.app ⊤ s :=
  (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X (natTensorPow L 1)).apply_symm_apply _

/-- If `f` is a bijective map commuting with scalars, then `r ↦ r • f x` is bijective
iff `r ↦ r • x` is. -/
private theorem bijective_smul_map_iff {R M N : Type*} [SMul R M] [SMul R N] {f : M → N}
    (hf : Function.Bijective f) (hsm : ∀ (r : R) (x : M), f (r • x) = r • f x) (x : M) :
    Function.Bijective (fun r : R => r • f x) ↔ Function.Bijective fun r : R => r • x := by
  rw [← hf.of_comp_iff' (fun r : R => r • x)]
  exact iff_of_eq (congrArg _ (funext fun r => (hsm r x).symm))

/-- **Local generators from two consecutive degrees.** Let `u ∈ Γ(L ^⊗ m)` and
`u' ∈ Γ(L ^⊗ (m+1))`, and let `V` be an open inside both nonvanishing loci. Then there are a
generator `γ` of `L` over `V`, a generator `ω` of `L ^⊗ D` over `V` and a function `a` on `V` with
`s|_V = a γ` and `sᴰ|_V = aᴰ ω`. -/
theorem exists_generators_of_consecutive (s : Γ(L, ⊤)) {D : ℕ} (hD : 1 ≤ D) {m : ℕ}
    (u : powSections L m) (u' : powSections L (m + 1)) {V : X.Opens} (hu : V ≤ nvOpen L u)
    (hu' : V ≤ nvOpen L u') :
    ∃ (γ : Γ(L, V)) (ω : Γ(natTensorPow L (1 * D), V)) (a : Γ(X, V)),
      Function.Bijective (fun r : Γ(X, V) => r • γ) ∧
      Function.Bijective (fun r : Γ(X, V) => r • ω) ∧
      L.presheaf.map (homOfLE le_top).op s = a • γ ∧
      (natTensorPow L (1 * D)).presheaf.map (homOfLE le_top).op
          (globalSection X _ (powSec L (degreeOneSection L s) D)) = a ^ D • ω := by
  set sp := degreeOneSection L s with hsp
  -- the ratio `a` of `u s` to `u'`
  obtain ⟨a, ha⟩ := Stacks.SectionExtension.exists_resTop_eq_smul (natTensorPow L (m + 1))
    (globalSection X _ u') (globalSection X _ (mul u sp)) hu'
  -- degree one
  let μ₁ : L ⟶ natTensorPow L (m + 1) := (λ_ L).inv ≫ mulMap u 1
  have hμ₁ : Function.Bijective (μ₁.app V) :=
    (Stacks.TensorPowerDivision.bijective_app_mulMap L u (le_refl _) 1 V hu).comp
      (Stacks.TensorPowerDivision.bijective_app_of_isIso (λ_ L).inv V)
  have hgen₁ := Stacks.NonvanishingSpelling.bijective_smul X (natTensorPow L (m + 1))
    (globalSection X _ u') hu'
  obtain ⟨γ, hγ⟩ := hμ₁.2 ((natTensorPow L (m + 1)).presheaf.map (homOfLE le_top).op
    (globalSection X _ u'))
  have hsmul₁ : ∀ (r : Γ(X, V)) (z : Γ(L, V)), μ₁.app V (r • z) = r • μ₁.app V z := fun r z =>
    Scheme.Modules.Hom.app_smul μ₁ r z
  have hs : μ₁.app V (L.presheaf.map (homOfLE le_top).op s) =
      (natTensorPow L (m + 1)).presheaf.map (homOfLE le_top).op
        (globalSection X _ (mul u sp)) := by
    rw [← Stacks.TensorPowerTrivialize.resTop_app]
    congr 1
    rw [Stacks.SectionProduct.globalSection_mul, hsp, globalSection_degreeOneSection]
    rfl
  -- degree `D`
  let e : natTensorPow L ((m + 1) * D) ⟶ natTensorPow L (m * D + 1 * D) :=
    eqToHom (congrArg (natTensorPow L) (add_mul m 1 D))
  let μD : natTensorPow L (1 * D) ⟶ natTensorPow L (m * D + 1 * D) := mulMap (powSec L u D) (1 * D)
  have hnvu : V ≤ nvOpen L (powSec L u D) := by
    rwa [Stacks.SectionRingProjOverlap.nvOpen_powSec_of_one_le L u D hD]
  have hnvu' : V ≤ nvOpen L (powSec L u' D) := by
    rwa [Stacks.SectionRingProjOverlap.nvOpen_powSec_of_one_le L u' D hD]
  have hμD : Function.Bijective (μD.app V) :=
    Stacks.TensorPowerDivision.bijective_app_mulMap L (powSec L u D) (le_refl _) (1 * D) V hnvu
  have he : Function.Bijective (e.app V) := Stacks.TensorPowerDivision.bijective_app_of_isIso _ V
  have hgenD := Stacks.NonvanishingSpelling.bijective_smul X (natTensorPow L ((m + 1) * D))
    (globalSection X _ (powSec L u' D)) hnvu'
  obtain ⟨ω, hω⟩ := hμD.2 (e.app V ((natTensorPow L ((m + 1) * D)).presheaf.map
    (homOfLE le_top).op (globalSection X _ (powSec L u' D))))
  have hsmulD : ∀ (r : Γ(X, V)) (z : Γ(natTensorPow L (1 * D), V)),
      μD.app V (r • z) = r • μD.app V z := fun r z => Scheme.Modules.Hom.app_smul μD r z
  have hesmul : ∀ (r : Γ(X, V)) (z : Γ(natTensorPow L ((m + 1) * D), V)),
      e.app V (r • z) = r • e.app V z := fun r z => Scheme.Modules.Hom.app_smul e r z
  -- the product `uᴰ sᴰ` is `(u s)ᴰ`, transported along the degree identity
  have hof : DirectSum.of (powSections L) ((m + 1) * D) (powSec L (mul u sp) D) =
      DirectSum.of (powSections L) (m * D + 1 * D) (mul (powSec L u D) (powSec L sp D)) := by
    rw [Stacks.SectionRingChartMap.of_powSec_eq_pow, Stacks.SectionRingChartMap.of_mul_eq,
      Stacks.SectionRingChartMap.of_mul_eq, Stacks.SectionRingChartMap.of_powSec_eq_pow,
      Stacks.SectionRingChartMap.of_powSec_eq_pow, mul_pow]
  have htD : μD.app V ((natTensorPow L (1 * D)).presheaf.map (homOfLE le_top).op
      (globalSection X _ (powSec L sp D))) =
      e.app V ((natTensorPow L ((m + 1) * D)).presheaf.map (homOfLE le_top).op
        (globalSection X _ (powSec L (mul u sp) D))) := by
    rw [← Stacks.TensorPowerTrivialize.resTop_app, ← Stacks.SectionProduct.globalSection_mul]
    have key := Stacks.SectionRingProjQuasicoherent.eqToHom_app_unitSec_of_of_eq L (add_mul m 1 D)
      (powSec L (mul u sp) D) (mul (powSec L u D) (powSec L sp D)) hof V
    rw [Stacks.SectionRingProjQuasicoherent.unitSec_eq_map_globalSection,
      Stacks.SectionRingProjQuasicoherent.unitSec_eq_map_globalSection] at key
    exact key.symm
  have hpow := Stacks.SectionExtension.resTop_globalSection_powSec L u' (mul u sp) a ha D
  refine ⟨γ, ω, a, ?_, ?_, ?_, ?_⟩
  · exact (bijective_smul_map_iff hμ₁ hsmul₁ γ).1 (by rw [hγ]; exact hgen₁)
  · refine (bijective_smul_map_iff hμD hsmulD ω).1 ?_
    rw [hω]
    exact (bijective_smul_map_iff he hesmul _).2 hgenD
  · exact hμ₁.1 (by rwa [hs, hsmul₁, hγ])
  · apply hμD.1
    rw [htD, hsmulD, hω, ← hesmul]
    exact congrArg (e.app V) hpow

/-- **`Z(sᴰ) = Z(s)ᴰ`**, for `L` ample and the power `sᴰ` taken in the section ring. -/
theorem zeroScheme_powSec_degreeOneSection (hL : Stacks.Ample.IsAmple X L) (s : Γ(L, ⊤))
    {D : ℕ} (hD : 1 ≤ D) :
    zeroScheme X (natTensorPow L (1 * D)) (globalSection X _ (powSec L (degreeOneSection L s) D))
      = zeroScheme X L s ^ D := by
  classical
  obtain ⟨m, -, hcov, hcov'⟩ :=
    Stacks.SectionRingVeroneseChart.exists_consecutive_iSup_nvOpen_eq_top L hL
  have hpt : ∀ x : X, ∃ (V : X.affineOpens) (u : powSections L m) (u' : powSections L (m + 1)),
      x ∈ V.1 ∧ V.1 ≤ nvOpen L u ∧ V.1 ≤ nvOpen L u' := by
    intro x
    obtain ⟨u, hxu⟩ := Opens.mem_iSup.1 (hcov ▸ (Opens.mem_top x) : x ∈ ⨆ a, nvOpen L a)
    obtain ⟨u', hxu'⟩ := Opens.mem_iSup.1 (hcov' ▸ (Opens.mem_top x) : x ∈ ⨆ a, nvOpen L a)
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVsub⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
      (Opens.mem_inf.2 ⟨hxu, hxu'⟩) (nvOpen L u ⊓ nvOpen L u').2
    exact ⟨⟨V, hV⟩, u, u', hxV, fun y hy => (hVsub hy).1, fun y hy => (hVsub hy).2⟩
  choose V u u' hxV hVu hVu' using hpt
  exact zeroScheme_pow_eq_of_cover L (natTensorPow L (1 * D)) s _ D V
    (le_antisymm le_top fun y _ => Opens.mem_iSup.2 ⟨y, hxV y⟩) fun x =>
      exists_generators_of_consecutive L s hD (u x) (u' x) (hVu x) (hVu' x)

end Stacks.Algebraization

end
