module

public import StacksFrontier.AlgebraicGeometry.SectionRingChartMap.Multiplicative
public import StacksFrontier.AlgebraicGeometry.ModuleSectionExtension.Localization
public import StacksFrontier.AlgebraicGeometry.AmpleGlobalGeneration.Twist

/-!
# The annihilator of a homogeneous section vanishing on a nonvanishing open

Let `X` be a scheme, `L` an invertible `𝒪_X`-module and `a` a homogeneous element of positive
degree `d` of the graded section ring `Γ_*(X, L) = ⨁_{n ≥ 0} Γ(X, L ^⊗ n)` of Stacks Tag 01CV.
This file proves the **injectivity input** to Stacks Tag 01PW at the arbitrary degree `d`, in the
case `𝓕 = 𝒪_X`: a homogeneous element `u` of `Γ_*(X, L)` whose section restricts to zero on the
nonvanishing open `X_a` is annihilated by a power of `a` in `Γ_*(X, L)`.

The conclusion is an equation **in the ring** `Γ_*(X, L)`, not between sections, so no degree
transport occurs anywhere: the degrees `p + N k` on the left and the exponents on the right sit as
indices of `DirectSum.of` and are crossed by `Stacks.SectionRingChartMap.of_mul_eq` and
`Stacks.SectionRingChartMap.of_powSec_eq_pow`.

## The argument

`Stacks.SectionExtension.exists_common_degree_affine_cover` provides, for `L` ample, a finite
family `c i` of homogeneous elements of one degree `N` whose nonvanishing opens are affine and
cover `X`. Over `X_{c i}` the generator `c i` is free, so a homogeneous `a'` of degree `N` is
`f i` times `c i` there, and `Stacks.SectionExtension.nonvanishingOpen_inf_eq_basicOpen` — which
needs no hypothesis — identifies `X_{a'} ⊓ X_{c i}` with `X.basicOpen (f i)`. On the affine
`X_{c i}` a section of a quasi-coherent module vanishing on that basic open is killed by a power
of `f i` (`Stacks.ModuleSectionExtension.exists_pow_smul_eq_zero`, which is Stacks Tag 01I9), and
the finitely many exponents are raised to a single `k`.

The passage from `f i ^ k · u|_{X_{c i}} = 0` to the vanishing of the *product* `u · a'^k` is the
multiplicativity of the ratio, `Stacks.SectionExtension.resTop_globalSection_powSec`: over
`X_{c i}` one has `a'^k = f i ^ k · (c i)^k`, so `u · a'^k` restricts to `f i ^ k` times
`u · (c i)^k`, and the scalar is carried onto `u` by commuting the product — multiplication by a
global section being a morphism of `𝒪_X`-modules, it acts on sections over every open and
commutes with the scalars there. The sheaf condition then assembles the vanishing.

## Main results

* `Stacks.SectionRingChartBijective.exists_pow_mul_of_eq_zero_of_cover`: **the annihilator against
  a finite affine cover**, with no ampleness: the cover is the hypothesis. Its members need only
  *sit inside* the nonvanishing opens `X_{c i}`, not be equal to them, so that the lemma also
  applies when the `X_{c i}` cover `X` without being affine.
* `Stacks.SectionRingChartBijective.exists_pow_mul_of_eq_zero`: **the deliverable**, for `L` ample
  and `a` of positive degree. The annihilating power is a power of `a` itself, which is what the
  degree-zero localization at `a` consumes; this is why the covering element is taken to be
  `Stacks.SectionExtension.powSec L a N₀`, a genuine power of `a`, rather than the element of
  degree `N` with the same nonvanishing locus that the cover lemma returns.

## References

* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MonoidalCategory
open Stacks.Ample Stacks.NonvanishingOpen
open Stacks.AmpleFiniteAvoidance
open Stacks.TensorPowers (natTensorPow)
open Stacks.GradedSections (powSections mul sectionRing mulMap powCongr mul_comm')
open Stacks.SectionProduct (globalSection globalSection_comp)
open Stacks.SectionExtension (powSec resTop resTop_app resTop_app_of_res_eq
  exists_resTop_eq_smul nonvanishingOpen_inf_eq_basicOpen exists_forall_le map_res_res_module
  nvOpen_eq exists_common_degree_affine_cover resTop_globalSection_powSec
  nvLocus_powSec_of_one_le)

universe u

namespace Stacks.SectionRingChartBijective

section Monoidal

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

omit [Stacks.Ample.IsInvertibleModule X L] in
/-- **A global section of a tensor power is determined by its restrictions to a cover.** The one
use of the sheaf condition in this file, with the carrier comparison
`Stacks.SectionProduct.globalSection` taken into account: a homogeneous section restricting to
zero on every member of a cover of `X` is zero. -/
theorem eq_zero_of_resTop_eq_zero {ι : Type*} {V : ι → X.Opens}
    (hcover : (⊤ : X.Opens) ≤ ⨆ i, V i) {p : ℕ} (w : powSections L p)
    (hw : ∀ i, resTop (V i) (globalSection X _ w) = 0) : w = 0 := by
  refine (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X
    (natTensorPow L p)).injective ?_
  refine Eq.trans ?_ (map_zero (Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X
    (natTensorPow L p))).symm
  show globalSection X (natTensorPow L p) w = 0
  refine TopCat.Sheaf.eq_of_locally_eq'
    (⟨(natTensorPow L p).presheaf, (natTensorPow L p).isSheaf⟩ : TopCat.Sheaf Ab X)
    V ⊤ (fun _ ↦ homOfLE le_top) hcover _ _ fun i ↦ ?_
  show resTop (V i) (globalSection X (natTensorPow L p) w)
    = (natTensorPow L p).presheaf.map (homOfLE (le_top : V i ≤ ⊤)).op 0
  rw [hw i, map_zero]

/-- **Multiplying a homogeneous section by a global one, with the scalar on the other factor.**
The restriction to `V` of `u · t` is a morphism of `𝒪_X`-modules applied to the restriction of
`u`, so a scalar multiplying `u|_V` can be pulled out of the product. The morphism is
multiplication by `t` followed by the degree transport of
`Stacks.GradedSections.mul_comm'`, which is what puts `u` in the position the morphism is applied
to. -/
theorem resTop_globalSection_mul_smul {p q : ℕ} (u : powSections L p) (t : powSections L q)
    {V : X.Opens} (g : Γ(X, V)) (hg : g • resTop (V) (globalSection X _ u) = 0) :
    g • resTop (V) (globalSection X (natTensorPow L (p + q)) (mul u t)) = 0 := by
  have hcomm : globalSection X (natTensorPow L (p + q)) (mul u t)
      = (mulMap t p ≫ powCongr L (Nat.add_comm q p)).app ⊤ (globalSection X _ u) := by
    rw [← mul_comm' t u, globalSection_comp, Scheme.Modules.Hom.comp_app]
    rfl
  rw [hcomm, resTop_app, ← Scheme.Modules.Hom.app_smul, hg, map_zero]

/-- **The annihilator against a finite affine cover, with no ampleness.** Let `a'` be a
homogeneous element of degree `N`, let `c i` be a finite family of homogeneous elements of the
same degree `N`, let `V i` be affine opens covering `X` with `V i ⊆ X_{c i}`, and let `u` be a
homogeneous element of degree `p` whose section vanishes on `X_{a'}`. Then `u · a'^k = 0` in
`Γ_*(X, L)` for some `k`.

This is the content of the injectivity half of Stacks Tag 01PW in the case `𝓕 = 𝒪_X` at an
arbitrary degree; ampleness enters only through the cover, which is the hypothesis here.

**The covering opens are not required to be the nonvanishing opens themselves**, only to sit
inside them: all that `c i` is used for is to be a free generator of `L ^⊗ N` over `V i`, which it
is on any open contained in `X_{c i}`. That is what makes the lemma usable when the `X_{c i}` are
*not* affine — under clause (a) of Stacks Tag 01PZ alone the `X_b` cover `X` but need not be
affine, and one shrinks each of them to an affine open around each of its points instead. For `L`
ample the `X_{c i}` themselves are affine, which is the case `V = fun i ↦ nvOpen L (c i)` taken by
`Stacks.SectionRingChartBijective.exists_pow_mul_of_eq_zero`. -/
theorem exists_pow_mul_of_eq_zero_of_cover {N : ℕ} (a' : powSections L N) {ι : Type u} [Finite ι]
    (c : ι → powSections L N) (U : X.Opens) (hU : nvOpen L a' = U)
    (V : ι → X.Opens) (hVmem : ∀ i, V i ≤ nvOpen L (c i))
    (hVaff : ∀ i, IsAffineOpen (V i))
    (hcover : (⊤ : X.Opens) ≤ ⨆ i, V i)
    {p : ℕ} (u : powSections L p) (hu : resTop U (globalSection X _ u) = 0) :
    ∃ k : ℕ, DirectSum.of (powSections L) p u
        * DirectSum.of (powSections L) N a' ^ k = 0 := by
  classical
  have hVle : ∀ i, V i ≤ nonvanishingOpen X (natTensorPow L N) (globalSection X _ (c i)) :=
    fun i ↦ (hVmem i).trans (le_of_eq (nvOpen_eq L (c i)))
  -- the ratio `f i = a' / c i` over the affine `V i ⊆ X_{c i}`
  choose f hf using fun i : ι ↦ exists_resTop_eq_smul (natTensorPow L N)
    (globalSection X _ (c i)) (globalSection X _ a') (hVle i)
  -- `U ⊓ V i` is the basic open of that ratio
  have hD : ∀ i, U ⊓ V i = X.basicOpen (f i) := fun i ↦ by
    rw [← hU]
    exact nonvanishingOpen_inf_eq_basicOpen (globalSection X _ (c i)) (globalSection X _ a')
      (hVle i) (f i) (hf i)
  have hDU : ∀ i, X.basicOpen (f i) ≤ U := fun i ↦ by rw [← hD i]; exact inf_le_left
  -- `u` restricts to zero on that basic open
  have hres : ∀ i, (natTensorPow L p).presheaf.map (homOfLE (X.basicOpen_le (f i))).op
      (resTop (V i) (globalSection X _ u)) = 0 := by
    intro i
    have h1 : (natTensorPow L p).presheaf.map (homOfLE (X.basicOpen_le (f i))).op
          (resTop (V i) (globalSection X _ u))
        = resTop (X.basicOpen (f i)) (globalSection X _ u) :=
      map_res_res_module _ _ _
    have h2 : resTop (X.basicOpen (f i)) (globalSection X _ u)
        = (natTensorPow L p).presheaf.map (homOfLE (hDU i)).op
          (resTop U (globalSection X _ u)) :=
      (map_res_res_module (hDU i) le_top _).symm
    rw [h1, h2, hu, map_zero]
  -- the affine annihilator, with the finitely many exponents raised to a single positive one
  have hqc : (natTensorPow L p).IsQuasicoherent :=
    Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule (natTensorPow L p)
  choose e he using fun i : ι ↦ Stacks.ModuleSectionExtension.exists_pow_smul_eq_zero
    (natTensorPow L p) (hVaff i) (f i) (resTop (V i) (globalSection X _ u)) (hres i)
  obtain ⟨k₀, hk₀⟩ := exists_forall_le e
  have hk : ∀ i, f i ^ (k₀ + 1) • resTop (V i) (globalSection X _ u) = 0 := by
    intro i
    have hsplit : k₀ + 1 = k₀ + 1 - e i + e i := by have := hk₀ i; omega
    rw [hsplit, pow_add, mul_smul, he i, smul_zero]
  -- the product vanishes on every member of the cover
  refine ⟨k₀ + 1, ?_⟩
  have hzero : mul u (powSec L a' (k₀ + 1)) = 0 := by
    refine eq_zero_of_resTop_eq_zero L hcover _ fun i ↦ ?_
    have hpow := resTop_globalSection_powSec L (c i) a' (f i) (hf i) (k₀ + 1)
    have hstep : resTop (V i)
          (globalSection X _ (mul u (powSec L a' (k₀ + 1))))
        = f i ^ (k₀ + 1) • resTop (V i)
          (globalSection X _ (mul u (powSec L (c i) (k₀ + 1)))) :=
      resTop_app_of_res_eq (mulMap u (N * (k₀ + 1))) _ _ _ hpow
    rw [hstep]
    exact resTop_globalSection_mul_smul L u (powSec L (c i) (k₀ + 1)) _ (hk i)
  have hofw : DirectSum.of (powSections L) (p + N * (k₀ + 1)) (mul u (powSec L a' (k₀ + 1)))
      = DirectSum.of (powSections L) p u
        * DirectSum.of (powSections L) (N * (k₀ + 1)) (powSec L a' (k₀ + 1)) :=
    Stacks.SectionRingChartMap.of_mul_eq L u (powSec L a' (k₀ + 1))
  rw [hzero, map_zero, Stacks.SectionRingChartMap.of_powSec_eq_pow L a' (k₀ + 1)] at hofw
  exact hofw.symm

/-- **The annihilator, for `L` ample.** A homogeneous element `u` of `Γ_*(X, L)` whose section
restricts to zero on the nonvanishing open `X_a` of a homogeneous element `a` of positive degree
is annihilated by a power of `a`.

This is the hypothesis `hker` of
`Stacks.SheafOfModules.homogeneousLocalizationLiftOfDegree_injective` for the chart ring map at
`a`, and it is the injectivity half of Stacks Tag 01PW at the degree of `a` in the case
`𝓕 = 𝒪_X`.

The covering element is taken to be the genuine power `Stacks.SectionExtension.powSec L a N₀`
rather than the element of degree `N` with the same nonvanishing locus that
`Stacks.SectionExtension.exists_common_degree_affine_cover` returns: the annihilator has to be a
power of `a` itself, and `Stacks.SectionRingChartMap.of_powSec_eq_pow` is what says so. -/
theorem exists_pow_mul_of_eq_zero (hL : IsAmple X L) {d : ℕ} (hd : 1 ≤ d) (a : powSections L d)
    {p : ℕ} (u : powSections L p)
    (hu : resTop (nvOpen L a) (globalSection X _ u) = 0) :
    ∃ k : ℕ, DirectSum.of (powSections L) p u
        * DirectSum.of (powSections L) d a ^ k = 0 := by
  obtain ⟨N, -, F, c, hN1, hdvd, -, hcaff, hcover⟩ :=
    exists_common_degree_affine_cover L hL hd a
  obtain ⟨N₀, rfl⟩ := hdvd
  have hN₀ : 1 ≤ N₀ := by
    rcases Nat.eq_zero_or_pos N₀ with h | h
    · rw [h, Nat.mul_zero] at hN1; omega
    · exact h
  have hnv : nvOpen L (powSec L a N₀) = nvOpen L a :=
    TopologicalSpace.Opens.ext (by
      rw [coe_nvOpen, coe_nvOpen, nvLocus_powSec_of_one_le L a N₀ hN₀])
  obtain ⟨k, hk⟩ := exists_pow_mul_of_eq_zero_of_cover L (powSec L a N₀) c (nvOpen L a) hnv
    (fun i ↦ nvOpen L (c i)) (fun _ ↦ le_rfl) hcaff hcover u hu
  refine ⟨N₀ * k, ?_⟩
  rwa [Stacks.SectionRingChartMap.of_powSec_eq_pow L a N₀, ← pow_mul] at hk

end Monoidal

end Stacks.SectionRingChartBijective

end
