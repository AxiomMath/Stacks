module

public import StacksFrontier.AlgebraicGeometry.SectionExtensionNoAmple.Basic
public import StacksFrontier.AlgebraicGeometry.TensorPowerTrivialize.Power

/-!
# The global annihilator half of [Stacks, Tag 01PW]

For `X` quasi-compact, `L` invertible, `G` quasi-coherent and `a` a homogeneous element of
positive degree, a global section of `G` vanishing on `X_a` is killed globally by a power of `a`:
there is a `p` and a power `σ` of `a` in degree `p` with `τ ⊗ σ = 0` in
`Γ(X, G ⊗ L ^⊗ p)`. This is the second application of Properties, Lemma 28.18.2 in the proof of
[Stacks, Tag 0BQR] — the step that turns a twisted global section into a *cocycle* of the twisted
complex.

## Implementation notes

The argument runs over the cover of
`Stacks.SectionExtensionNoAmple.exists_common_degree_affine_subcover`: one degree `N`, a finite
family `c i` of homogeneous elements of that degree, affine opens `V i ≤ X_{c i}` covering `X`,
and a power `a'` of `a` in the same degree `N` with `X_{a'} = X_a`. Over `V i` both `a'` and `c i`
are global sections of `L ^⊗ N` and `c i` does not vanish, so
`Stacks.TensorPowerTrivialize.resTop_eq_ratio_smul` names the ratio `f i` and
`Stacks.TensorPowerTrivialize.resTop_sectionPow` applies to its powers. Over the cover of
`Stacks.Tag01PWPartOne.exists_finite_affine_trivializing_cover`, whose members carry only a
*local* basis section `b i` of `L`, the passage from `f i ^ k · τ|_{W i} = 0` to `τ ⊗ a^k = 0`
would need `a^k|_{W i} = f i ^ k · b i ^{⊗ k}`, a power law for local sections that
`Stacks.TensorPowerTrivialize.resTop_sectionPow` does not give.

This cover needs `Stacks.SectionExtensionNoAmple.HasPointwiseNonvanishing` — every point lies in
the nonvanishing locus of some homogeneous element of positive degree — which [Stacks, Tag 01PW]
does not assume. Ampleness supplies it
(`Stacks.SectionExtensionNoAmple.hasPointwiseNonvanishing_of_isAmple`), so the result holds at the
hypotheses of [Stacks, Tag 0BQR]; it is not Tag 01PW, and no `@[stacks 01PW]` attribute is
attached.

## Main results

* `Stacks.SectionExtensionNoAmple.exists_tensorSection_eq_zero_of_hasPointwiseNonvanishing`:
  **the global annihilator half.** A global section of a quasi-coherent module vanishing on `X_a`
  is annihilated by a power of `a`, globally, with the power taken in a degree divisible by the
  degree of `a` and with the same nonvanishing locus as `a`.
* `Stacks.SectionExtensionNoAmple.exists_tensorSection_eq_zero_of_isAmple`: the same for an ample
  `L`, at the hypotheses of [Stacks, Tag 0BQR].

## References

* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
* [Stacks Project, Tag 0BQR](https://stacks.math.columbia.edu/tag/0BQR)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MonoidalCategory
open Stacks.Ample Stacks.NonvanishingOpen
open Stacks.AmpleFiniteAvoidance
open Stacks.TensorPowers (natTensorPow)
open Stacks.GradedSections (powSections)
open Stacks.SectionProduct (globalSection)
open Stacks.ModuleSectionExtension (res)
open Stacks.TensorPowerTrivialize (sectionPow powDeg powDeg_eq trivializationOfSection
  resTop_eq_ratio_smul nonvanishingLocus_inter_eq_basicOpen resTop_sectionPow
  nonvanishingLocus_sectionPow)
open Stacks.SectionExtension (exists_forall_le map_res_res_module)
open Stacks.SectionTensorFormula (tensorSection map_tensorSection tensorSection_smul_left
  tensorSection_smul_right tensorSection_zero_left)

universe u

namespace Stacks.SectionExtensionNoAmple

section GlobalAnnihilator

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

variable {X : Scheme.{u}} (L : X.Modules) [IsInvertibleModule X L]

/-- **The global annihilator half of [Stacks, Tag 01PW], over a cover whose basis sections are
global.** For `X` quasi-compact, `L` invertible with every point in the nonvanishing locus of a
homogeneous element of positive degree, `G` quasi-coherent, `a` homogeneous of positive degree
`n`, and `τ` a global section of `G` vanishing on `X_a`, there are a degree `p` divisible by `n`
and a homogeneous `σ` of degree `p` with `X_σ = X_a` and `τ ⊗ σ = 0` in `Γ(X, G ⊗ L ^⊗ p)`.

`σ` is a power of `a`: the cover supplies a power `a'` of `a` in a common degree `N`, and `σ` is
a power of `a'`. -/
theorem exists_tensorSection_eq_zero_of_hasPointwiseNonvanishing [CompactSpace X]
    (hpt : HasPointwiseNonvanishing L) (G : X.Modules) [G.IsQuasicoherent]
    {n : ℕ} (hn : 1 ≤ n) (a : powSections L n) (τ : Γ(G, ⊤))
    (hτ : res G (le_top : nvOpen L a ≤ ⊤) τ = 0) :
    ∃ (p : ℕ) (σ : powSections L p), n ∣ p ∧ nvLocus L σ = nvLocus L a ∧
      tensorSection G (natTensorPow L p) τ (globalSection X _ σ) = 0 := by
  classical
  obtain ⟨N, a', ι, hι, c, V, -, hdvd, ha, hVaff, hVle, hcover⟩ :=
    exists_common_degree_affine_subcover L ‹CompactSpace X› hpt hn a
  have : Finite ι := hι
  have hVle' : ∀ i, V i ≤ nonvanishingOpen X (natTensorPow L N) (globalSection X _ (c i)) :=
    hVle
  -- The ratio of `a'` against the nonvanishing global section `c i` over `V i`, together with
  -- the identification of `X_a ∩ V i` with its basic open.
  have hpack : ∀ i, ∃ g : Γ(X, V i),
      Stacks.TensorPowerTrivialize.resTop (natTensorPow L N) (globalSection X _ a') (V i)
          = g • Stacks.TensorPowerTrivialize.resTop (natTensorPow L N)
              (globalSection X _ (c i)) (V i) ∧
        nvLocus L a' ∩ (V i : Set X) = (X.basicOpen g : Set X) := fun i =>
    ⟨_, resTop_eq_ratio_smul (natTensorPow L N) (globalSection X _ (c i))
        (globalSection X _ a') (hVle' i),
      nonvanishingLocus_inter_eq_basicOpen (natTensorPow L N) (globalSection X _ (c i))
        (globalSection X _ a') (hVle' i)⟩
  choose f hfr hfb using hpack
  have hble : ∀ i, X.basicOpen (f i) ≤ nvOpen L a := by
    intro i x hx
    have hx' : x ∈ nvLocus L a' ∩ (V i : Set X) := by rw [hfb i]; exact hx
    change x ∈ (nvOpen L a : Set X)
    rw [coe_nvOpen, ← ha]
    exact hx'.1
  -- A uniform exponent killing `τ` over every member of the cover.
  have key : ∀ i, ∃ e : ℕ, f i ^ e • res G (le_top : V i ≤ ⊤) τ = 0 := by
    intro i
    refine Stacks.ModuleSectionExtension.exists_pow_smul_eq_zero G (hVaff i) (f i) _ ?_
    have hchain : res G (X.basicOpen_le (f i)) (res G (le_top : V i ≤ ⊤) τ)
        = res G (hble i) (res G (le_top : nvOpen L a ≤ ⊤) τ) := by
      simp only [res, map_res_res_module]
    rw [hchain, hτ]
    simp
  choose e he using key
  obtain ⟨k, hk⟩ := exists_forall_le e
  have hk0 : ∀ i, f i ^ k • res G (le_top : V i ≤ ⊤) τ = 0 := fun i => by
    rw [show k = k - e i + e i from (Nat.sub_add_cancel (hk i)).symm, pow_add, mul_smul, he i,
      smul_zero]
  refine ⟨powDeg N k, sectionPow L a' k, hdvd.trans ⟨k + 1, powDeg_eq N k⟩,
    (nonvanishingLocus_sectionPow L a' k).trans ha, ?_⟩
  -- Over each member of the cover the product vanishes, by the multiplicativity of the ratio.
  have hloc : ∀ i, tensorSection G (natTensorPow L (powDeg N k)) (res G (le_top : V i ≤ ⊤) τ)
      (Stacks.TensorPowerTrivialize.resTop (natTensorPow L (powDeg N k))
        (globalSection X _ (sectionPow L a' k)) (V i)) = 0 := fun i => by
    rw [resTop_sectionPow L (c i) a' (f i) (hfr i) k, tensorSection_smul_right,
      ← tensorSection_smul_left, pow_succ' (f i) k, mul_smul, hk0 i, smul_zero,
      tensorSection_zero_left]
  refine TopCat.Sheaf.eq_of_locally_eq'
    (⟨(G ⊗ natTensorPow L (powDeg N k)).presheaf,
      (G ⊗ natTensorPow L (powDeg N k)).isSheaf⟩ : TopCat.Sheaf Ab X)
    V ⊤ (fun i => homOfLE (le_top : V i ≤ ⊤)) hcover _ _ fun i => ?_
  have hz : (G ⊗ natTensorPow L (powDeg N k)).presheaf.map
      (homOfLE (le_top : V i ≤ ⊤)).op (0 : Γ(G ⊗ natTensorPow L (powDeg N k), ⊤)) = 0 := by
    simp
  change (G ⊗ natTensorPow L (powDeg N k)).presheaf.map (homOfLE (le_top : V i ≤ ⊤)).op
      (tensorSection G (natTensorPow L (powDeg N k)) τ (globalSection X _ (sectionPow L a' k)))
    = (G ⊗ natTensorPow L (powDeg N k)).presheaf.map (homOfLE (le_top : V i ≤ ⊤)).op 0
  rw [hz, map_tensorSection]
  exact hloc i

/-- **The global annihilator half at the hypotheses of [Stacks, Tag 0BQR].** For `L` ample, `G`
quasi-coherent and `τ` a global section of `G` vanishing on `X_a`, some power of `a` annihilates
`τ` globally.

Ampleness enters twice and only through the ample cluster: it makes `X` quasi-compact, and it
supplies `Stacks.SectionExtensionNoAmple.HasPointwiseNonvanishing` by
`Stacks.SectionExtensionNoAmple.hasPointwiseNonvanishing_of_isAmple`. -/
theorem exists_tensorSection_eq_zero_of_isAmple (hL : IsAmple X L) (G : X.Modules)
    [G.IsQuasicoherent] {n : ℕ} (hn : 1 ≤ n) (a : powSections L n) (τ : Γ(G, ⊤))
    (hτ : res G (le_top : nvOpen L a ≤ ⊤) τ = 0) :
    ∃ (p : ℕ) (σ : powSections L p), n ∣ p ∧ nvLocus L σ = nvLocus L a ∧
      tensorSection G (natTensorPow L p) τ (globalSection X _ σ) = 0 :=
  have : CompactSpace X := hL.1
  exists_tensorSection_eq_zero_of_hasPointwiseNonvanishing L
    (hasPointwiseNonvanishing_of_isAmple L hL) G hn a τ hτ

end GlobalAnnihilator

end Stacks.SectionExtensionNoAmple

end
