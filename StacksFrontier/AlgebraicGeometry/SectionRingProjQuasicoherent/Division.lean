module

public import StacksFrontier.AlgebraicGeometry.SectionRingProjQuasicoherent.Multiplication
public import StacksFrontier.AlgebraicGeometry.TensorPowerDivision.Basic
public import StacksFrontier.AlgebraicGeometry.SectionRingChartMap.Multiplicative
public import StacksFrontier.AlgebraicGeometry.SectionRingChartMap.Chart
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DegreeZeroLocalizationArbitraryDegree

/-!
# Dividing a twisted section by a power of a section, on an open where it does not vanish

Let `X` be a scheme, `L` an invertible `𝒪_X`-module, `ℱ` an `𝒪_X`-module and `a` a global
section of `L ^⊗ d`. Write `ℱ ⊙ m = ℱ ⊗ L ^⊗ m` (`Stacks.TwistedSections.twistPow`). This file
studies multiplication by the powers of `a`,

`aᵏ : ℱ ⟶ ℱ ⊙ (d k)`,

as a morphism of `𝒪_X`-modules (`Stacks.SectionRingProjQuasicoherent.powMul`), and proves that it
is bijective on the sections over every open inside the nonvanishing open `X_a`. The quotient of a
section `t` of `ℱ ⊙ (d k)` by `aᵏ` over such an open is the preimage of `t`; this is the local
map of Stacks Tag 0B5L / Tag 01PW, and the comparison of Stacks Tag 01QJ is glued from it.

## Main definitions

* `Stacks.SectionRingProjQuasicoherent.unitSec`: the section over `U` of a morphism out of the
  monoidal unit, its value on the unit section.
* `Stacks.SectionRingProjQuasicoherent.powMul`: multiplication by `aᵏ`.

## Main results

* `Stacks.SectionRingProjQuasicoherent.bijective_twistMul_app`: multiplication by `a` is bijective
  on the sections over every open inside `X_a`.
* `Stacks.SectionRingProjQuasicoherent.powMul_comp_twistMul_powSec`: `a^{n + k}` is `aⁿ` followed
  by `aᵏ`.
* `Stacks.SectionRingProjQuasicoherent.bijective_powMul_app`: multiplication by `aᵏ` is bijective
  on the sections over every open inside `X_a`.
* `Stacks.SectionRingProjQuasicoherent.localDivision`: the division
  `Γ_*(X, L, ℱ)_{(a)} ⟶ Γ(U, ℱ)` for `U ⊆ X_a`, with its semilinearity (`localDivision_smul`),
  its compatibility with a change of section (`localDivision_change`) and its naturality in `ℱ`
  (`localDivision_naturality`).

## References

* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 01QJ](https://stacks.math.columbia.edu/tag/01QJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite TopologicalSpace
open Stacks.TensorPowers (natTensorPow)
open Stacks.GradedSections (powSections mul mulMap sectionRing)
open Stacks.TwistedSections (twistPow twistSections twistModule actMap twistPowMap)
open Stacks.SectionProduct (globalSection monoidalUnitSection forgetFun)
open Stacks.AmpleFiniteAvoidance (nvOpen grading)
open Stacks.SectionExtension (powSec)
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


variable {X : Scheme.{u}}

/-! ### Sections of morphisms out of the monoidal unit -/

/-- **The section over `U` carried by a morphism out of the monoidal unit**: its value on the
canonical unit section `Stacks.SectionProduct.monoidalUnitSection`. -/
def unitSec {M : X.Modules} (t : 𝟙_ X.Modules ⟶ M) (U : X.Opens) : Γ(M, U) :=
  t.app U (monoidalUnitSection X U)

/-- The section carried by `t ≫ g` is the image under `g` of the section carried by `t`. -/
theorem unitSec_comp {M N : X.Modules} (t : 𝟙_ X.Modules ⟶ M) (g : M ⟶ N) (U : X.Opens) :
    unitSec (t ≫ g) U = g.app U (unitSec t U) := rfl

/-- The section carried by a morphism out of the unit is compatible with restriction. -/
theorem map_unitSec {M : X.Modules} (t : 𝟙_ X.Modules ⟶ M) {U V : X.Opens} (i : V ⟶ U) :
    M.presheaf.map i.op (unitSec t U) = unitSec t V :=
  (PresheafOfModules.naturality_apply ((forgetFun X).map t) i.op
      (monoidalUnitSection X U)).symm.trans
    (congrArg (fun s => t.app V s) (Stacks.SectionProduct.map_monoidalUnitSection i))

/-- The section over `U` carried by a morphism out of the unit is the restriction of its global
section. -/
theorem unitSec_eq_map_globalSection {M : X.Modules} (t : 𝟙_ X.Modules ⟶ M) (U : X.Opens) :
    unitSec t U = M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (globalSection X M t) :=
  Stacks.SectionProduct.app_monoidalUnitSection_eq_map_globalSection M t U

/-! ### Bijectivity -/

/-- The value on sections of a composite is the composite of the values. -/
theorem bijective_comp_app {M N K : X.Modules} (f : M ⟶ N) (g : N ⟶ K) {U : X.Opens}
    (hf : Function.Bijective (f.app U)) (hg : Function.Bijective (g.app U)) :
    Function.Bijective ((f ≫ g).app U) :=
  hg.comp hf

variable (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]

/-- **Multiplication by a section of `L ^⊗ d` is bijective on the sections over every open
inside its nonvanishing open.** The section itself is, by the trivialization clause of
Stacks Tag 01CY (`Stacks.TensorPowerDivision.bijective_app_of_le_nonvanishingOpen`); whiskering
preserves stalkwise bijectivity (`Stacks.SectionProduct.BijStalk.whiskerLeft`), which gives back
bijectivity on sections (`Stacks.TensorPowerDivision.bijective_app_of_bijStalk`); the unitor and
the collecting isomorphism are isomorphisms. -/
theorem bijective_twistMul_app (F : X.Modules) {d : ℕ} (a : powSections L d) (m : ℕ)
    {U : X.Opens} (hU : U ≤ nvOpen L a) :
    Function.Bijective ((twistMul (F := F) a m).app U) := by
  have hwhisk : Function.Bijective ((twistPow F L m ◁ a).app U) :=
    Stacks.TensorPowerDivision.bijective_app_of_bijStalk _ (W := nvOpen L a)
      (fun _ hy => Stacks.SectionProduct.BijStalk.whiskerLeft _ a hy
        (fun _ hU' => Stacks.TensorPowerDivision.bijective_app_of_le_nonvanishingOpen
          (natTensorPow L d) a le_rfl hU')) hU
  exact bijective_comp_app _ _
    (Stacks.TensorPowerDivision.bijective_app_of_isIso _ U)
    (bijective_comp_app _ _ hwhisk (Stacks.TensorPowerDivision.bijective_app_of_isIso _ U))

/-! ### Multiplication by the powers of a section -/

/-- **Multiplication by `aᵏ`**, `ℱ ⟶ ℱ ⊙ (d k)`, as the `k`-fold multiplication by `a`. -/
def powMul (F : X.Modules) {d : ℕ} (a : powSections L d) : (k : ℕ) → (F ⟶ twistPow F L (d * k))
  | 0 => 𝟙 F
  | k + 1 => powMul F a k ≫ twistMul a (d * k)

omit [Stacks.Ample.IsInvertibleModule X L] in
/-- Multiplication by `a⁰` is the identity. -/
theorem powMul_zero (F : X.Modules) {d : ℕ} (a : powSections L d) : powMul L F a 0 = 𝟙 F := rfl

omit [Stacks.Ample.IsInvertibleModule X L] in
/-- Multiplication by `a^{k + 1}` is multiplication by `aᵏ` followed by multiplication by `a`. -/
theorem powMul_succ (F : X.Modules) {d : ℕ} (a : powSections L d) (k : ℕ) :
    powMul L F a (k + 1) = powMul L F a k ≫ twistMul a (d * k) := rfl

/-- **Multiplication by `aᵏ` is bijective on the sections over every open inside `X_a`.** -/
theorem bijective_powMul_app (F : X.Modules) {d : ℕ} (a : powSections L d) {U : X.Opens}
    (hU : U ≤ nvOpen L a) : ∀ k : ℕ, Function.Bijective ((powMul L F a k).app U)
  | 0 => Function.bijective_id
  | k + 1 => bijective_comp_app _ _ (bijective_powMul_app F a hU k)
      (bijective_twistMul_app L F a (d * k) hU)

omit [Stacks.Ample.IsInvertibleModule X L] in
/-- **Multiplication by `aᵏ` is multiplication by the section `aᵏ` of `L ^⊗ (d k)`.** -/
theorem powMul_eq_twistMul (F : X.Modules) {d : ℕ} (a : powSections L d) :
    ∀ k : ℕ, powMul L F a k =
      eqToHom (Stacks.TwistedSections.twistPow_zero F L).symm ≫ twistMul (powSec L a k) 0 ≫
        eqToHom (congrArg (twistPow F L) (Nat.zero_add (d * k)))
  | 0 => by
      show 𝟙 F = eqToHom rfl ≫ (ρ_ F).inv ≫ F ◁ 𝟙 (𝟙_ X.Modules) ≫ (ρ_ F).hom ≫ eqToHom rfl
      simp
  | k + 1 => by
      rw [powMul_succ, powMul_eq_twistMul F a k, Category.assoc, Category.assoc,
        eqToHom_comp_twistMul a (Nat.zero_add (d * k)), ← Category.assoc (twistMul _ 0),
        twistMul_comp_twistMul, Category.assoc, eqToHom_trans]
      rfl

/-- If `aⁿ c = q^N` in the section ring, then `q^N` is `aⁿ` followed by `c`, up to reindexing. -/
private theorem powMul_eq_comp_twistMul (L F : X.Modules) {d e j : ℕ} (a : powSections L d)
    (q : powSections L e) (c : powSections L j) (n N : ℕ) (h : d * n + j = e * N)
    (hring : DirectSum.of (powSections L) d a ^ n * DirectSum.of (powSections L) j c =
      DirectSum.of (powSections L) e q ^ N) :
    powMul L F q N = powMul L F a n ≫ twistMul c (d * n) ≫
      eqToHom (congrArg (twistPow F L) h) := by
  have hof : DirectSum.of (powSections L) (d * n + j) (mul (powSec L a n) c) =
      DirectSum.of (powSections L) (e * N) (powSec L q N) := by
    rw [Stacks.SectionRingChartMap.of_mul_eq, Stacks.SectionRingChartMap.of_powSec_eq_pow,
      Stacks.SectionRingChartMap.of_powSec_eq_pow, hring]
  have hcongr := twistMul_congr_of (F := F) h (mul (powSec L a n) c) (powSec L q N) hof 0
  rw [powMul_eq_twistMul L F a n, powMul_eq_twistMul L F q N]
  simp only [Category.assoc]
  rw [eqToHom_comp_twistMul_assoc c (Nat.zero_add (d * n)),
    ← Category.assoc (twistMul _ 0), twistMul_comp_twistMul, ← hcongr]
  simp only [Category.assoc, eqToHom_trans]

omit [Stacks.Ample.IsInvertibleModule X L] in
/-- **`a^{n + k}` is `aⁿ` followed by `aᵏ`.** -/
theorem powMul_comp_twistMul_powSec (F : X.Modules) {d : ℕ} (a : powSections L d) (n k : ℕ) :
    powMul L F a n ≫ twistMul (powSec L a k) (d * n) =
      powMul L F a (n + k) ≫
        eqToHom (congrArg (twistPow F L) (by ring : d * (n + k) = d * n + d * k)) := by
  rw [powMul_eq_comp_twistMul L F a a (powSec L a k) n (n + k) (by ring)
    (by rw [Stacks.SectionRingChartMap.of_powSec_eq_pow, ← pow_add])]
  simp

/-- The value of a morphism of `𝒪_X`-modules on the sections over `U`, as a `Γ(X, U)`-linear
map. -/
def appLinear {M N : X.Modules} (φ : M ⟶ N) (U : X.Opens) : Γ(M, U) →ₗ[Γ(X, U)] Γ(N, U) where
  toFun := φ.app U
  map_add' := map_add _
  map_smul' r x := Scheme.Modules.Hom.app_smul φ r x

/-- The linear map `appLinear φ U` is the value of `φ` on the sections over `U`. -/
@[simp] theorem appLinear_apply {M N : X.Modules} (φ : M ⟶ N) (U : X.Opens) (x : Γ(M, U)) :
    appLinear φ U x = φ.app U x := rfl

/-- **Multiplication by `aᵏ` on the sections over an open inside `X_a`, as a linear
equivalence.** Its inverse is the division by `aᵏ`. -/
def divEquiv (F : X.Modules) {d : ℕ} (a : powSections L d) {U : X.Opens} (hU : U ≤ nvOpen L a)
    (k : ℕ) : Γ(F, U) ≃ₗ[Γ(X, U)] Γ(twistPow F L (d * k), U) :=
  LinearEquiv.ofBijective (appLinear (powMul L F a k) U) (bijective_powMul_app L F a hU k)

/-- The equivalence `divEquiv` sends a section `x` to `aᵏ x`. -/
@[simp] theorem divEquiv_apply (F : X.Modules) {d : ℕ} (a : powSections L d) {U : X.Opens}
    (hU : U ≤ nvOpen L a) (k : ℕ) (x : Γ(F, U)) :
    divEquiv L F a hU k x = (powMul L F a k).app U x := rfl

/-- The section over `U` of a morphism out of the unit, as an additive map. -/
def unitSecHom (M : X.Modules) (U : X.Opens) : (𝟙_ X.Modules ⟶ M) →+ Γ(M, U) where
  toFun t := unitSec t U
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The degree-`i` component of an element of `Γ_*(X, ℱ, L)`. -/
def componentHom (F : X.Modules) (i : ℕ) : twistModule F L →+ twistSections F L i where
  toFun x := x i
  map_zero' := rfl
  map_add' x y := DFinsupp.add_apply x y i

omit [Stacks.Ample.IsInvertibleModule X L] in
/-- The degree-`i` component of the element `t` placed in degree `i` is `t`. -/
theorem componentHom_of (F : X.Modules) (i : ℕ) (t : twistSections F L i) :
    componentHom L F i (DirectSum.of (twistSections F L) i t) = t :=
  DirectSum.of_eq_same i t

/-- **The numerator maps of the division by the powers of `a`.** The `n`-th one takes the
component of degree `n d` of an element of `Γ_*(X, ℱ, L)`, restricts it to `U` and divides it by
`aⁿ`. -/
def numer (F : X.Modules) {d : ℕ} (a : powSections L d) {U : X.Opens} (hU : U ≤ nvOpen L a)
    (n : ℕ) : twistModule F L →+ Γ(F, U) :=
  (divEquiv L F a hU n).symm.toLinearMap.toAddMonoidHom.comp
    ((unitSecHom (twistPow F L (d * n)) U).comp
      (AddMonoidHom.comp
        { toFun := Stacks.TwistedSections.twistCongr (Nat.mul_comm n d)
          map_zero' := Limits.zero_comp
          map_add' := fun _ _ => Preadditive.add_comp _ _ _ _ _ _ }
        (componentHom L F (n * d))))

/-- The `n`-th numerator map sends an element `t` of degree `n d` to the quotient by `aⁿ` of
its section over `U`. -/
theorem numer_of (F : X.Modules) {d : ℕ} (a : powSections L d) {U : X.Opens}
    (hU : U ≤ nvOpen L a) (n : ℕ) (t : twistSections F L (n * d)) :
    numer L F a hU n (DirectSum.of (twistSections F L) (n * d) t) =
      (divEquiv L F a hU n).symm
        (unitSec (Stacks.TwistedSections.twistCongr (Nat.mul_comm n d) t) U) := by
  simp only [numer, AddMonoidHom.comp_apply, componentHom_of]
  rfl

/-- Multiplying a section `t` of degree `n d` by `c` and reindexing agrees with reindexing `t`
first and then multiplying. -/
private theorem twistCongr_twistCongr_comp_twistMul (L F : X.Modules) {d e j n N : ℕ}
    (t : twistSections F L (n * d)) (c : powSections L j) (hdeg : n * d + j = N * e)
    (h : d * n + j = e * N) :
    Stacks.TwistedSections.twistCongr (Nat.mul_comm N e)
        (Stacks.TwistedSections.twistCongr hdeg (t ≫ twistMul c (n * d))) =
      Stacks.TwistedSections.twistCongr (Nat.mul_comm n d) t ≫ twistMul c (d * n) ≫
        eqToHom (congrArg (twistPow F L) h) := by
  simp only [Stacks.TwistedSections.twistCongr, Category.assoc]
  rw [eqToHom_comp_twistMul_assoc c (Nat.mul_comm n d)]
  simp only [eqToHom_trans]

/-- **The numerator maps descend to the degree-zero localization**: dividing `aᵏ t` by
`a^{n+k}` is dividing `t` by `aⁿ`. -/
theorem numer_pow_smul (F : X.Modules) {d : ℕ} (a : powSections L d) {U : X.Opens}
    (hU : U ≤ nvOpen L a) (n k : ℕ) (x : twistModule F L)
    (hx : x ∈ Stacks.TwistedSections.moduleGrading F L ((n * d : ℕ) : ℤ)) :
    numer L F a hU (n + k) (DirectSum.of (powSections L) d a ^ k • x) =
      numer L F a hU n x := by
  obtain ⟨t, rfl⟩ := Stacks.TwistedSections.mem_moduleGrading_natCast_iff.mp hx
  have hdeg : n * d + d * k = (n + k) * d := by ring
  rw [← Stacks.SectionRingChartMap.of_powSec_eq_pow, of_smul_of_eq_twistMul,
    ← of_twistCongr hdeg, numer_of, numer_of, LinearEquiv.symm_apply_eq, divEquiv_apply]
  set u := (divEquiv L F a hU n).symm
    (unitSec (Stacks.TwistedSections.twistCongr (Nat.mul_comm n d) t) U) with hu
  have hpu : (powMul L F a n).app U u =
      unitSec (Stacks.TwistedSections.twistCongr (Nat.mul_comm n d) t) U :=
    (divEquiv L F a hU n).apply_symm_apply _
  have hE : d * n + d * k = d * (n + k) := by ring
  have hmor := powMul_eq_comp_twistMul L F a a (powSec L a k) n (n + k) hE
    (by rw [Stacks.SectionRingChartMap.of_powSec_eq_pow, ← pow_add])
  calc unitSec (Stacks.TwistedSections.twistCongr (Nat.mul_comm (n + k) d)
          (Stacks.TwistedSections.twistCongr hdeg (t ≫ twistMul (powSec L a k) (n * d)))) U
      = unitSec (Stacks.TwistedSections.twistCongr (Nat.mul_comm n d) t ≫
          twistMul (powSec L a k) (d * n) ≫ eqToHom (congrArg (twistPow F L) hE)) U :=
        congrArg (fun s => unitSec s U) (twistCongr_twistCongr_comp_twistMul L F t _ hdeg hE)
    _ = (twistMul (powSec L a k) (d * n) ≫ eqToHom (congrArg (twistPow F L) hE)).app U
          ((powMul L F a n).app U u) := by rw [hpu]; rfl
    _ = (powMul L F a (n + k)).app U u := by rw [hmor]; rfl

/-! ### Changing the section -/

omit [Stacks.Ample.IsInvertibleModule X L] in
/-- **Multiplication by `aⁿ` followed by `c` is multiplication by `q^N`** whenever
`aⁿ c = q^N` in the section ring `Γ_*(X, L)`. -/
theorem powMul_comp_twistMul_eq (F : X.Modules) {d e j : ℕ} (a : powSections L d)
    (q : powSections L e) (c : powSections L j) (n N : ℕ) (h : d * n + j = e * N)
    (hring : DirectSum.of (powSections L) d a ^ n * DirectSum.of (powSections L) j c =
      DirectSum.of (powSections L) e q ^ N) :
    powMul L F a n ≫ twistMul c (d * n) =
      powMul L F q N ≫ eqToHom (congrArg (twistPow F L) h.symm) := by
  rw [powMul_eq_comp_twistMul L F a q c n N h hring]
  simp

/-! ### The division on the degree-zero localization -/

variable (F : X.Modules)

/-- **Stacks Tag 0B5L's map on an open `U ⊆ X_a`**: the degree-zero localization
`Γ_*(X, ℱ, L)_{(a)}` maps to `Γ(U, ℱ)`, by sending `t / aⁿ` to the unique section `u` with
`aⁿ u = t|_U`. -/
def localDivision {d : ℕ} (a : powSections L d) {U : X.Opens} (hU : U ≤ nvOpen L a) :
    GradedModuleDegreeZeroLocalization (grading L) (Stacks.TwistedSections.moduleGrading F L)
      (DirectSum.of (powSections L) d a) →+ Γ(F, U) :=
  Stacks.SheafOfModules.degreeZeroLocalizationLiftOfDegree (grading L)
    (Stacks.TwistedSections.moduleGrading F L) (Stacks.ExternalGrading.of_mem_summand d a)
    (numer L F a hU) (fun n k x hx => numer_pow_smul L F a hU n k x hx)

/-- **The value of the division on a fraction** `t / aⁿ`. -/
theorem localDivision_fraction {d : ℕ} (a : powSections L d) {U : X.Opens}
    (hU : U ≤ nvOpen L a)
    (z : GradedModuleDegreeZeroLocalization (grading L) (Stacks.TwistedSections.moduleGrading F L)
      (DirectSum.of (powSections L) d a))
    (n : ℕ) (t : twistSections F L (n * d))
    (hz : (z : LocalizedModule.Away (DirectSum.of (powSections L) d a) (twistModule F L)) =
      LocalizedModule.mk (S := Submonoid.powers (DirectSum.of (powSections L) d a))
        (DirectSum.of (twistSections F L) (n * d) t)
        ⟨DirectSum.of (powSections L) d a ^ n, by exact ⟨n, rfl⟩⟩) :
    localDivision L F a hU z =
      (divEquiv L F a hU n).symm
        (unitSec (Stacks.TwistedSections.twistCongr (Nat.mul_comm n d) t) U) := by
  rw [localDivision, Stacks.SheafOfModules.degreeZeroLocalizationLiftOfDegree_fraction
    (grading L) (Stacks.TwistedSections.moduleGrading F L)
    (Stacks.ExternalGrading.of_mem_summand d a) _ _ z n _ ⟨t, rfl⟩ hz, numer_of]

/-- **The characterization of the division**: on a fraction `t / aⁿ`, multiplying the value by
`aⁿ` gives back `t|_U`. -/
theorem powMul_app_localDivision {d : ℕ} (a : powSections L d) {U : X.Opens}
    (hU : U ≤ nvOpen L a)
    (z : GradedModuleDegreeZeroLocalization (grading L) (Stacks.TwistedSections.moduleGrading F L)
      (DirectSum.of (powSections L) d a))
    (n : ℕ) (t : twistSections F L (n * d))
    (hz : (z : LocalizedModule.Away (DirectSum.of (powSections L) d a) (twistModule F L)) =
      LocalizedModule.mk (S := Submonoid.powers (DirectSum.of (powSections L) d a))
        (DirectSum.of (twistSections F L) (n * d) t)
        ⟨DirectSum.of (powSections L) d a ^ n, by exact ⟨n, rfl⟩⟩) :
    (powMul L F a n).app U (localDivision L F a hU z) =
      unitSec (Stacks.TwistedSections.twistCongr (Nat.mul_comm n d) t) U := by
  rw [localDivision_fraction L F a hU z n t hz, ← divEquiv_apply L F a hU n,
    LinearEquiv.apply_symm_apply]

/-- **The division is compatible with shrinking the open.** -/
theorem map_localDivision {d : ℕ} (a : powSections L d) {U V : X.Opens} (hU : U ≤ nvOpen L a)
    (i : V ⟶ U)
    (z : GradedModuleDegreeZeroLocalization (grading L) (Stacks.TwistedSections.moduleGrading F L)
      (DirectSum.of (powSections L) d a)) :
    F.presheaf.map i.op (localDivision L F a hU z) =
      localDivision L F a ((leOfHom i).trans hU) z := by
  obtain ⟨n, x, hx, hz⟩ := Stacks.SheafOfModules.degreeZeroLocalization_exists_fraction_of_degree
    (grading L) (Stacks.TwistedSections.moduleGrading F L)
    (Stacks.ExternalGrading.of_mem_summand d a) z
  obtain ⟨t, rfl⟩ := Stacks.TwistedSections.mem_moduleGrading_natCast_iff.mp hx
  rw [localDivision_fraction L F a hU z n t hz,
    localDivision_fraction L F a ((leOfHom i).trans hU) z n t hz, LinearEquiv.eq_symm_apply,
    divEquiv_apply]
  have hnat := PresheafOfModules.naturality_apply ((forgetFun X).map (powMul L F a n)) i.op
    ((divEquiv L F a hU n).symm
      (unitSec (Stacks.TwistedSections.twistCongr (Nat.mul_comm n d) t) U))
  refine hnat.trans ?_
  show (twistPow F L (d * n)).presheaf.map i.op
      ((powMul L F a n).app U ((divEquiv L F a hU n).symm
        (unitSec (Stacks.TwistedSections.twistCongr (Nat.mul_comm n d) t) U))) = _
  rw [← divEquiv_apply L F a hU n, LinearEquiv.apply_symm_apply, map_unitSec]

/-! ### Linearity -/

omit [Stacks.Ample.IsInvertibleModule X L] in
/-- Two sections naming the same element of the section ring in equal degrees have the same
sections over every open, up to the reindexing. -/
theorem eqToHom_app_unitSec_of_of_eq {i j : ℕ} (h : i = j) (x : powSections L i)
    (y : powSections L j)
    (hxy : DirectSum.of (powSections L) i x = DirectSum.of (powSections L) j y) (U : X.Opens) :
    (eqToHom (congrArg (natTensorPow L) h)).app U (unitSec x U) = unitSec y U := by
  subst h
  obtain rfl := DirectSum.of_injective (β := powSections L) i hxy
  rfl

omit [Stacks.Ample.IsInvertibleModule X L] in
/-- A section reindexed along an equality of degrees names the same element of the section
ring. -/
theorem of_comp_eqToHom {i j : ℕ} (h : i = j) (x : powSections L i) :
    DirectSum.of (powSections L) j (x ≫ eqToHom (congrArg (natTensorPow L) h)) =
      DirectSum.of (powSections L) i x := by
  subst h
  simp

/-- **The ratio property of the chart ring map**: the value `c` of the chart ring map of Stacks
Tag 01PZ on the fraction `r / aᵐ` satisfies `c · aᵐ|_U = r|_U`. -/
theorem chartRingMap_smul_unitSec_powSec {d : ℕ} (a : powSections L d) {U : X.Opens}
    (hU : U ≤ nvOpen L a) (m : ℕ) (r : sectionRing L) (hr : r ∈ grading L (m • d))
    (ρ : powSections L (m • d)) (hρ : DirectSum.of (powSections L) (m • d) ρ = r) :
    Stacks.SectionRingChartMap.chartRingMap L a hU
        (HomogeneousLocalization.Away.mk (grading L)
          (Stacks.ExternalGrading.of_mem_summand d a) m r hr) •
        unitSec (powSec L a m) U =
      unitSec (ρ ≫ eqToHom (congrArg (natTensorPow L) (by rw [smul_eq_mul, Nat.mul_comm] :
        m • d = d * m))) U := by
  have hdeg : d + m • d = d * (m + 1) := by rw [smul_eq_mul]; ring
  set t₁ : powSections L (d * (m + 1)) :=
    mul a ρ ≫ eqToHom (congrArg (natTensorPow L) hdeg) with ht₁def
  have ht₁ : DirectSum.of (powSections L) (d * (m + 1)) t₁ =
      DirectSum.of (powSections L) d a * r := by
    rw [ht₁def, of_comp_eqToHom L hdeg, Stacks.SectionRingChartMap.of_mul_eq, hρ]
  set c := Stacks.SectionRingChartMap.chartRingMap L a hU
    (HomogeneousLocalization.Away.mk (grading L)
      (Stacks.ExternalGrading.of_mem_summand d a) m r hr) with hc
  have hratio : c • unitSec (powSec L a (m + 1)) U = unitSec t₁ U := by
    rw [hc, Stacks.SectionRingChartMap.chartRingMap_mk_eq_numMap L a hU m r hr t₁ ht₁,
      unitSec_eq_map_globalSection, unitSec_eq_map_globalSection]
    exact Stacks.SectionRingChartMap.numMap_smul_resTop L a hU (m + 1) (Nat.le_add_left 1 m)
      (globalSection X _ t₁)
  have hinj : Function.Injective ((mulMap a (d * m)).app U) :=
    (Stacks.TensorPowerDivision.bijective_app_mulMap L a (W := nvOpen L a) le_rfl
      (d * m) U hU).1
  refine hinj ?_
  have h1 : d + d * m = d * (m + 1) := by ring
  have hpow : DirectSum.of (powSections L) (d + d * m) (mul a (powSec L a m)) =
      DirectSum.of (powSections L) (d * (m + 1)) (powSec L a (m + 1)) := by
    rw [Stacks.SectionRingChartMap.of_mul_eq, Stacks.SectionRingChartMap.of_powSec_eq_pow,
      Stacks.SectionRingChartMap.of_powSec_eq_pow, pow_succ, mul_comm]
  have hρ' : DirectSum.of (powSections L) (d + d * m) (mul a (ρ ≫ eqToHom
      (congrArg (natTensorPow L) (by rw [smul_eq_mul, Nat.mul_comm] : m • d = d * m)))) =
      DirectSum.of (powSections L) (d * (m + 1)) t₁ := by
    rw [ht₁, Stacks.SectionRingChartMap.of_mul_eq,
      of_comp_eqToHom L (by rw [smul_eq_mul, Nat.mul_comm] : m • d = d * m), hρ]
  have hinj2 : Function.Injective
      ((eqToHom (congrArg (natTensorPow L) h1) : _ ⟶ natTensorPow L (d * (m + 1))).app U) :=
    (Stacks.TensorPowerDivision.bijective_app_of_isIso _ U).1
  refine hinj2 ?_
  calc (eqToHom (congrArg (natTensorPow L) h1)).app U
          ((mulMap a (d * m)).app U (c • unitSec (powSec L a m) U))
      = c • (eqToHom (congrArg (natTensorPow L) h1)).app U
          (unitSec (mul a (powSec L a m)) U) := by
        rw [Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul]; rfl
    _ = c • unitSec (powSec L a (m + 1)) U := by
        rw [eqToHom_app_unitSec_of_of_eq L h1 _ _ hpow U]
    _ = unitSec t₁ U := hratio
    _ = _ := (eqToHom_app_unitSec_of_of_eq L h1 _ _ hρ' U).symm

/-- **The numerator maps are semilinear over the chart ring map of Stacks Tag 01PZ.** -/
theorem numer_smul {d : ℕ} (a : powSections L d) {U : X.Opens} (hU : U ≤ nvOpen L a)
    (m n : ℕ) (r : sectionRing L) (x : twistModule F L) (hr : r ∈ grading L (m • d))
    (hx : x ∈ Stacks.TwistedSections.moduleGrading F L ((n * d : ℕ) : ℤ)) :
    numer L F a hU (m + n) (r • x) =
      Stacks.SectionRingChartMap.chartRingMap L a hU
          (HomogeneousLocalization.Away.mk (grading L)
            (Stacks.ExternalGrading.of_mem_summand d a) m r hr) •
        numer L F a hU n x := by
  obtain ⟨t, rfl⟩ := Stacks.TwistedSections.mem_moduleGrading_natCast_iff.mp hx
  obtain ⟨ρ, hρ⟩ := hr
  have hratio := chartRingMap_smul_unitSec_powSec L a hU m r ⟨ρ, hρ⟩ ρ hρ
  subst hρ
  set c := Stacks.SectionRingChartMap.chartRingMap L a hU
    (HomogeneousLocalization.Away.mk (grading L)
      (Stacks.ExternalGrading.of_mem_summand d a) m (DirectSum.of (powSections L) (m • d) ρ)
      ⟨ρ, rfl⟩) with hc
  have hmd : m • d = d * m := by rw [smul_eq_mul, Nat.mul_comm]
  set ρ' : powSections L (d * m) := ρ ≫ eqToHom (congrArg (natTensorPow L) hmd) with hρ'
  have hdeg : n * d + m • d = (m + n) * d := by rw [smul_eq_mul]; ring
  have h : d * n + d * m = d * (m + n) := by ring
  have hmor := powMul_eq_comp_twistMul L F a a (powSec L a m) n (m + n) h
    (by rw [Stacks.SectionRingChartMap.of_powSec_eq_pow, ← pow_add, Nat.add_comm])
  rw [of_smul_of_eq_twistMul, ← of_twistCongr hdeg, numer_of, numer_of,
    LinearEquiv.symm_apply_eq, divEquiv_apply, Scheme.Modules.Hom.app_smul, hmor]
  set u := (divEquiv L F a hU n).symm
    (unitSec (Stacks.TwistedSections.twistCongr (Nat.mul_comm n d) t) U) with hu
  have hpu : (powMul L F a n).app U u =
      unitSec (Stacks.TwistedSections.twistCongr (Nat.mul_comm n d) t) U :=
    (divEquiv L F a hU n).apply_symm_apply _
  calc unitSec (Stacks.TwistedSections.twistCongr (Nat.mul_comm (m + n) d)
          (Stacks.TwistedSections.twistCongr hdeg (t ≫ twistMul ρ (n * d)))) U
      = (actMap (Stacks.TwistedSections.twistCongr (Nat.mul_comm n d) t) (d * m) ≫
          eqToHom (congrArg (twistPow F L) h)).app U (unitSec ρ' U) := by
        rw [← unitSec_comp]
        refine congrArg (fun s => unitSec s U) ?_
        rw [← comp_twistMul_assoc, hρ', twistMul_comp_eqToHom hmd ρ (d * n)]
        simp only [Stacks.TwistedSections.twistCongr, Category.assoc]
        rw [eqToHom_comp_twistMul_assoc ρ (Nat.mul_comm n d)]
        simp only [eqToHom_trans]
    _ = c • (actMap (Stacks.TwistedSections.twistCongr (Nat.mul_comm n d) t) (d * m) ≫
          eqToHom (congrArg (twistPow F L) h)).app U (unitSec (powSec L a m) U) := by
        rw [← Scheme.Modules.Hom.app_smul, hratio]
    _ = c • (powMul L F a n ≫ twistMul (powSec L a m) (d * n) ≫
          eqToHom (congrArg (twistPow F L) h)).app U u := by
        refine congrArg (fun s => c • s) ?_
        show _ = (twistMul (powSec L a m) (d * n) ≫
          eqToHom (congrArg (twistPow F L) h)).app U ((powMul L F a n).app U u)
        rw [hpu, ← unitSec_comp, ← unitSec_comp, comp_twistMul_assoc]

/-- **The division is semilinear over the chart ring map of Stacks Tag 01PZ.** -/
theorem localDivision_smul {d : ℕ} (a : powSections L d) {U : X.Opens} (hU : U ≤ nvOpen L a)
    (y : HomogeneousLocalization.Away (grading L) (DirectSum.of (powSections L) d a))
    (z : GradedModuleDegreeZeroLocalization (grading L) (Stacks.TwistedSections.moduleGrading F L)
      (DirectSum.of (powSections L) d a)) :
    localDivision L F a hU (y • z) =
      Stacks.SectionRingChartMap.chartRingMap L a hU y • localDivision L F a hU z :=
  Stacks.SheafOfModules.degreeZeroLocalizationLiftOfDegree_smul (grading L)
    (Stacks.TwistedSections.moduleGrading F L) (Stacks.ExternalGrading.of_mem_summand d a) _ _
    (Stacks.SectionRingChartMap.chartRingMap L a hU)
    (fun m n r x hr hx => numer_smul L F a hU m n r x hr hx) y z

/-! ### Changing the section and the module -/

/-- **The divisions at two sections agree.** If `aⁿ c = q^N` in the section ring, then on an
open inside `X_a ∩ X_q` the division of `t` by `aⁿ` is the division of `c t` by `q^N`. -/
theorem localDivision_change {d e j : ℕ} (a : powSections L d) (q : powSections L e)
    (c : powSections L j) {U W : X.Opens} (hU : U ≤ nvOpen L a) (hW : W ≤ nvOpen L q)
    (i : W ⟶ U) (n N : ℕ) (h : d * n + j = e * N)
    (hring : DirectSum.of (powSections L) d a ^ n * DirectSum.of (powSections L) j c =
      DirectSum.of (powSections L) e q ^ N)
    (z : GradedModuleDegreeZeroLocalization (grading L) (Stacks.TwistedSections.moduleGrading F L)
      (DirectSum.of (powSections L) d a))
    (z' : GradedModuleDegreeZeroLocalization (grading L)
      (Stacks.TwistedSections.moduleGrading F L) (DirectSum.of (powSections L) e q))
    (t : twistSections F L (n * d))
    (hz : (z : LocalizedModule.Away (DirectSum.of (powSections L) d a) (twistModule F L)) =
      LocalizedModule.mk (S := Submonoid.powers (DirectSum.of (powSections L) d a))
        (DirectSum.of (twistSections F L) (n * d) t)
        ⟨DirectSum.of (powSections L) d a ^ n, by exact ⟨n, rfl⟩⟩)
    (hz' : (z' : LocalizedModule.Away (DirectSum.of (powSections L) e q) (twistModule F L)) =
      LocalizedModule.mk (S := Submonoid.powers (DirectSum.of (powSections L) e q))
        (DirectSum.of (powSections L) j c • DirectSum.of (twistSections F L) (n * d) t)
        ⟨DirectSum.of (powSections L) e q ^ N, by exact ⟨N, rfl⟩⟩) :
    localDivision L F q hW z' = F.presheaf.map i.op (localDivision L F a hU z) := by
  have hdeg : n * d + j = N * e := by rw [Nat.mul_comm n d, h, Nat.mul_comm]
  rw [of_smul_of_eq_twistMul, ← of_twistCongr hdeg] at hz'
  rw [map_localDivision L F a hU i z, localDivision_fraction L F q hW z' N _ hz',
    LinearEquiv.symm_apply_eq, divEquiv_apply]
  rw [powMul_eq_comp_twistMul L F a q c n N h hring]
  show _ = (twistMul c (d * n) ≫ eqToHom (congrArg (twistPow F L) h)).app W
    ((powMul L F a n).app W (localDivision L F a ((leOfHom i).trans hU) z))
  rw [powMul_app_localDivision L F a _ z n t hz, ← unitSec_comp]
  exact congrArg (fun s => unitSec s W) (twistCongr_twistCongr_comp_twistMul L F t c hdeg h)

omit [Stacks.Ample.IsInvertibleModule X L] in
/-- **Multiplication by `aᵏ` is natural in the module.** -/
theorem powMul_naturality {F G : X.Modules} (φ : F ⟶ G) {d : ℕ} (a : powSections L d) :
    ∀ k : ℕ, powMul L F a k ≫ twistPowMap L φ (d * k) = φ ≫ powMul L G a k
  | 0 => by
      show 𝟙 F ≫ φ = φ ≫ 𝟙 G
      simp
  | k + 1 => by
      rw [powMul_succ, powMul_succ, Category.assoc]
      show powMul L F a k ≫ twistMul a (d * k) ≫ twistPowMap L φ (d * k + d) = _
      rw [twistMul_comp_twistPowMap, ← Category.assoc, powMul_naturality φ a k, Category.assoc]

/-- **The division is natural in the module.** -/
theorem localDivision_naturality {G : X.Modules} (φ : F ⟶ G) {d : ℕ} (a : powSections L d)
    {U : X.Opens} (hU : U ≤ nvOpen L a)
    (z : GradedModuleDegreeZeroLocalization (grading L) (Stacks.TwistedSections.moduleGrading F L)
      (DirectSum.of (powSections L) d a))
    (z' : GradedModuleDegreeZeroLocalization (grading L)
      (Stacks.TwistedSections.moduleGrading G L) (DirectSum.of (powSections L) d a))
    (hz' : (z' : LocalizedModule.Away (DirectSum.of (powSections L) d a) (twistModule G L)) =
      LocalizedModule.map (Submonoid.powers (DirectSum.of (powSections L) d a))
        (Stacks.TwistedSections.twistModuleLinearMap φ)
        (z : LocalizedModule.Away (DirectSum.of (powSections L) d a) (twistModule F L))) :
    localDivision L G a hU z' = φ.app U (localDivision L F a hU z) := by
  obtain ⟨n, x, hx, hz⟩ := Stacks.SheafOfModules.degreeZeroLocalization_exists_fraction_of_degree
    (grading L) (Stacks.TwistedSections.moduleGrading F L)
    (Stacks.ExternalGrading.of_mem_summand d a) z
  obtain ⟨t, rfl⟩ := Stacks.TwistedSections.mem_moduleGrading_natCast_iff.mp hx
  have hz'' : (z' : LocalizedModule.Away (DirectSum.of (powSections L) d a) (twistModule G L)) =
      LocalizedModule.mk (S := Submonoid.powers (DirectSum.of (powSections L) d a))
        (DirectSum.of (twistSections G L) (n * d)
          (Stacks.TwistedSections.twistSectionsMap φ (n * d) t))
        ⟨DirectSum.of (powSections L) d a ^ n, by exact ⟨n, rfl⟩⟩ := by
    rw [hz', hz, LocalizedModule.map_mk, Stacks.TwistedSections.twistModuleLinearMap_apply,
      Stacks.TwistedSections.twistModuleHom_of]
  rw [localDivision_fraction L G a hU z' n _ hz'', LinearEquiv.symm_apply_eq, divEquiv_apply]
  show _ = (φ ≫ powMul L G a n).app U (localDivision L F a hU z)
  rw [← powMul_naturality L φ a n]
  show _ = (twistPowMap L φ (d * n)).app U ((powMul L F a n).app U (localDivision L F a hU z))
  rw [powMul_app_localDivision L F a hU z n t hz, ← unitSec_comp]
  refine congrArg (fun s => unitSec s U) ?_
  simp only [Stacks.TwistedSections.twistCongr, Stacks.TwistedSections.twistSectionsMap,
    Category.assoc]
  rw [Stacks.TwistedSections.twistPowMap_eqToHom φ (Nat.mul_comm n d)]

end Stacks.SectionRingProjQuasicoherent

end
