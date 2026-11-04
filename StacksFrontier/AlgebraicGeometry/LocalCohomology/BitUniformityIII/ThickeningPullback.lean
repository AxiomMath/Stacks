module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import StacksFrontier.AlgebraicGeometry.Blowup.TwistedPullbackSections
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.BlowupSituation
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.PullbackCohomology
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.PullbackDictionary
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.ThickeningVanishingAboveDegree
public import StacksFrontier.AlgebraicGeometry.RegularSequence.ExtVanishing
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.EilenbergWattsUnitor

/-!
# The pullback of an `A/Iⁿ`-module to the blowup

Let `A` be a commutative ring, `I ⊆ A` an ideal, `p : X → Spec(A)` the blowup of `Spec(A)` in `I`
and `Yₙ ⊆ X` the `n`-th thickening of the exceptional divisor, cut out by the `n`-th power of the
inverse image of `I`. The proof of [Stacks, Tag 0GAC] ("A bit of uniformity, III") works with the
pullback `p^*M` of an `A/Iⁿ`-module `M`, and uses that `𝒪_{Yₙ} = p^*(A/Iⁿ)`. This file builds that
pullback and the identification.

Since `M` is killed by `Iⁿ` and so is `𝒪_{Yₙ}`, the pullback `p^*M̃` of the `A`-module underlying
`M` is the same as `𝒪_{Yₙ} ⊗_{𝒪_X} p^*M̃`; we take the latter as the definition, because it is an
instance of the geometric factor
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.geometricFactorFormula`, `M ↦ F ⊗ (f')^*(M̃)`, at
`F = 𝒪_{Yₙ}`, and so comes with additivity, right exactness and `A`-linearity.

The identification `𝒪_{Yₙ} ≅ p^*(A/Iⁿ)` needs no ideal-sheaf geometry beyond the fact that each
`g ∈ Iⁿ` kills `𝒪_{Yₙ}`. The `A`-module `A/Iⁿ` is the cokernel of the map `⨁_{g ∈ Iⁿ} A → A`
whose `g`-th component is multiplication by `g`; the geometric factor is right exact and commutes
with direct sums, it takes `A` to `𝒪_{Yₙ}` (`geometricFactorFormulaObjSelfIso`) and it takes
multiplication by `g` to multiplication by the pulled back function `g`, which is zero on
`𝒪_{Yₙ}`. So the presentation map goes to zero and `A → A/Iⁿ` goes to an isomorphism. No
Noetherian hypothesis is used: the presentation is indexed by all of `Iⁿ`.

## Main definitions

* `Stacks.LocalCohomology.UniformityIII.thickeningPullback`: the functor
  `M ↦ 𝒪_{Yₙ} ⊗ p^*(M̃)` from `A/Iⁿ`-modules to `𝒪_X`-modules, i.e. `M ↦ p^*M`.
* `Stacks.LocalCohomology.UniformityIII.thickeningPullbackUnitIso`: `p^*(A/Iⁿ) ≅ 𝒪_{Yₙ}`.
* `Stacks.LocalCohomology.UniformityIII.thickeningPullbackSection`: the `A`-linear map
  `M → Γ(X, p^*M)` sending `m` to the pullback of the section `m` of `M̃`, multiplied by the unit
  section of `𝒪_{Yₙ}`.

## Main results

* `Stacks.LocalCohomology.UniformityIII.thickeningPullback_map_smul`: `p^*` takes the scalar
  `a` on `M` to multiplication by the pulled back function `a`.
* `Stacks.LocalCohomology.UniformityIII.isQuasicoherent_thickeningPullback`: `p^*M` is
  quasi-coherent.
* `Stacks.LocalCohomology.UniformityIII.globalSmulCenter_pullbackCoeff_app_thickeningSheaf`:
  every `g ∈ Iⁿ` acts as zero on `𝒪_{Yₙ}`.
* `Stacks.LocalCohomology.UniformityIII.blowupΓmod_map_thickeningPullbackSection` and
  `Stacks.LocalCohomology.UniformityIII.blowupΓmod_map_thickeningPullbackUnitIso_hom_section_one`:
  the sections attached to elements are natural, and the section attached to `1 ∈ A/Iⁿ` is the
  unit section of `𝒪_{Yₙ}`.
* `Stacks.LocalCohomology.UniformityIII.isZero_thickeningSheaf_zero`: `𝒪_{Y₀} = 0`.

## References

* [Stacks Project, Tag 0GA6](https://stacks.math.columbia.edu/tag/0GA6)
* [Stacks Project, Tag 0GAC](https://stacks.math.columbia.edu/tag/0GAC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.TopDegreeBaseChange
open Stacks.RegularSequence (globalSmulCenter globalSmulCenter_app_app)

universe u

namespace Stacks.LocalCohomology.UniformityIII

variable {A : Type u} [CommRing A] (I : Ideal A)

/-! ### `Iⁿ` kills `𝒪_{Yₙ}` -/

/-- **The `n`-th thickening is cut out by the inverse image of `Iⁿ`.** Both sides are computed on
affine opens of the blowup: the left by `ideal_thickeningIdeal_affineOpens`, the right by
`Stacks.IdealSheaf.ideal_comap_appLE`, and they agree by `Ideal.map_pow`. -/
theorem thickeningIdeal_eq_comap (n : ℕ) :
    thickeningIdeal I n = (Scheme.IdealSheafData.ofIdealTop
      (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (I ^ n))).comap
        (Stacks.Blowup.toSpec I) := by
  apply Scheme.IdealSheafData.ext
  funext V
  rw [ideal_thickeningIdeal_affineOpens I n V, Stacks.IdealSheaf.ideal_comap_appLE _
    (Stacks.Blowup.toSpec I) ⟨⊤, isAffineOpen_top _⟩ V le_top,
    Scheme.IdealSheafData.ofIdealTop_ideal, Ideal.map_map, Ideal.map_map, Ideal.map_pow]
  rfl

/-- **The pullback of an element of `Iⁿ` vanishes on `Yₙ`**: its image under `𝒪_X ⟶ 𝒪_{Yₙ}` on
global sections is zero. -/
theorem app_top_thickeningProj_pullbackCoeff (n : ℕ) {g : A} (hg : g ∈ I ^ n) :
    (thickeningProj I n).val.app (op ⊤) (pullbackCoeff I g) = 0 :=
  app_top_unitToPushforwardObjUnit_eq_zero_of_comap (Stacks.Blowup.toSpec I)
    (Scheme.IdealSheafData.ofIdealTop
      (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (I ^ n)))
    (thickeningIdeal I n) (thickeningIdeal_eq_comap I n) _
    (by simpa using Ideal.mem_map_of_mem (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom hg)

/-- **Every `g ∈ Iⁿ` kills `𝒪_{Yₙ}`**: multiplication by the global function `g` pulls back to is
zero on `𝒪_{Yₙ}`. On sections over `U` it is multiplication by the image of `g|_U` in
`Γ(Yₙ, U ∩ Yₙ)`, which is the restriction of the image of `g` on global sections, and that is zero
by `app_top_thickeningProj_pullbackCoeff`. -/
theorem globalSmulCenter_pullbackCoeff_app_thickeningSheaf (n : ℕ) {g : A} (hg : g ∈ I ^ n) :
    (globalSmulCenter (blowupScheme I) (pullbackCoeff I g)).app (thickeningSheaf I n) = 0 := by
  have h0 := app_top_thickeningProj_pullbackCoeff I n hg
  apply Scheme.Modules.hom_ext
  intro U
  ext m
  rw [globalSmulCenter_app_app]
  have h1 : (thickeningIdeal I n).subschemeι.app U
      ((blowupScheme I).presheaf.map U.leTop.op (pullbackCoeff I g)) = 0 := by
    rw [← CommRingCat.comp_apply, Scheme.Hom.naturality, CommRingCat.comp_apply]
    rw [show ((thickeningIdeal I n).subschemeι.app ⊤).hom (pullbackCoeff I g) = 0 from h0,
      map_zero]
  change Γ((thickeningIdeal I n).subscheme, (thickeningIdeal I n).subschemeι ⁻¹ᵁ U) at m
  show ((thickeningIdeal I n).subschemeι.app U
      ((blowupScheme I).presheaf.map U.leTop.op (pullbackCoeff I g))) • m =
    (0 : Γ((thickeningIdeal I n).subscheme, (thickeningIdeal I n).subschemeι ⁻¹ᵁ U))
  rw [h1, zero_smul]

/-! ### The functor `p^*` -/

/-- **The geometric factor `N ↦ 𝒪_{Yₙ} ⊗ p^*(Ñ)`** on `A`-modules. -/
def thickeningFactor (n : ℕ) : ModuleCat.{u} A ⥤ (blowupScheme I).Modules :=
  geometricFactorFormula A (Stacks.Blowup.blowUpOver I) (thickeningSheaf I n)

/-- **`N ↦ 𝒪_{Yₙ} ⊗ p^*(Ñ)` is built from the pullback `blowupPullback`** of
`StacksFrontier/AlgebraicGeometry/LocalCohomology/BitUniformityIII/PullbackDictionary.lean`, followed
by tensoring with `𝒪_{Yₙ}`: it is not a second model of `p^*`. -/
theorem thickeningFactor_eq_comp (n : ℕ) :
    thickeningFactor I n = blowupPullback I ⋙
      Stacks.AlgebraicGeometry.TopDegreeBaseChange.tensorFactor A (Stacks.Blowup.blowUpOver I)
        (thickeningSheaf I n) :=
  rfl

/-- `N ↦ 𝒪_{Yₙ} ⊗ p^*(Ñ)` is additive. -/
instance additive_thickeningFactor (n : ℕ) : (thickeningFactor I n).Additive :=
  additive_geometricFactorFormula A (Stacks.Blowup.blowUpOver I) (thickeningSheaf I n)

/-- `N ↦ 𝒪_{Yₙ} ⊗ p^*(Ñ)` preserves small colimits. -/
instance preservesColimitsOfSize_thickeningFactor (n : ℕ) :
    PreservesColimitsOfSize.{u, u} (thickeningFactor I n) :=
  preservesColimitsOfSize_geometricFactorFormula A (Stacks.Blowup.blowUpOver I)
    (thickeningSheaf I n)

/-- `N ↦ 𝒪_{Yₙ} ⊗ p^*(Ñ)` is right exact. -/
instance preservesFiniteColimits_thickeningFactor (n : ℕ) :
    PreservesFiniteColimits (thickeningFactor I n) :=
  preservesFiniteColimits_geometricFactorFormula A (Stacks.Blowup.blowUpOver I)
    (thickeningSheaf I n)

/-- **The pullback `p^*M` of an `A/Iⁿ`-module `M` to the blowup**, in the form
`𝒪_{Yₙ} ⊗_{𝒪_X} p^*(M̃)`, where `M̃` is the sheaf on `Spec(A)` of `M` viewed as an `A`-module.
As `M` is killed by `Iⁿ` this is `p^*M̃`; the factor `𝒪_{Yₙ}` records that the pullback lives on
the thickening `Yₙ`, and it is what makes `p^*(A/Iⁿ) = 𝒪_{Yₙ}` (`thickeningPullbackUnitIso`). -/
def thickeningPullback (n : ℕ) : ModuleCat.{u} (A ⧸ I ^ n) ⥤ (blowupScheme I).Modules :=
  ModuleCat.restrictScalars.{u} (Ideal.Quotient.mk (I ^ n)) ⋙ thickeningFactor I n

/-- `p^*` is restriction of scalars along `A → A/Iⁿ` followed by the geometric factor
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.geometricFactorFormula` at `F = 𝒪_{Yₙ}`. -/
theorem thickeningPullback_eq (n : ℕ) :
    thickeningPullback I n = ModuleCat.restrictScalars.{u} (Ideal.Quotient.mk (I ^ n)) ⋙
      geometricFactorFormula A (Stacks.Blowup.blowUpOver I) (thickeningSheaf I n) :=
  rfl

/-- `p^*` is additive. -/
instance additive_thickeningPullback (n : ℕ) : (thickeningPullback I n).Additive :=
  inferInstanceAs (ModuleCat.restrictScalars.{u} (Ideal.Quotient.mk (I ^ n)) ⋙
    thickeningFactor I n).Additive

/-- `p^*` is right exact: restriction of scalars is exact and the geometric factor is right
exact. -/
instance preservesFiniteColimits_thickeningPullback (n : ℕ) :
    PreservesFiniteColimits (thickeningPullback I n) :=
  inferInstanceAs (PreservesFiniteColimits
    (ModuleCat.restrictScalars.{u} (Ideal.Quotient.mk (I ^ n)) ⋙ thickeningFactor I n))

/-- **The `A`-linear structure of `𝒪_X`-modules is multiplication by pulled back functions**: the
centre element by which `a ∈ A` acts in `AlgebraicGeometry.modulesLinear` is
`globalSmulCenter` of the global function `a` pulls back to. -/
theorem baseRingToCenter_app_eq_globalSmulCenter (a : A) (M : (blowupScheme I).Modules) :
    (baseRingToCenter A (Stacks.Blowup.blowUpOver I) a).app M =
      (globalSmulCenter (blowupScheme I) (pullbackCoeff I a)).app M :=
  rfl

/-- **`N ↦ 𝒪_{Yₙ} ⊗ p^*(Ñ)` takes the scalar `a` to multiplication by the pulled back function
`a`.** This is `linear_geometricFactorFormula` read through
`baseRingToCenter_app_eq_globalSmulCenter`. -/
theorem thickeningFactor_map_smul (n : ℕ) {M M' : ModuleCat.{u} A} (f : M ⟶ M') (a : A) :
    (thickeningFactor I n).map (a • f) =
      (globalSmulCenter (blowupScheme I) (pullbackCoeff I a)).app _ ≫
        (thickeningFactor I n).map f := by
  let : Linear A (blowupScheme I).Modules := modulesLinear A (Stacks.Blowup.blowUpOver I)
  have : (thickeningFactor I n).Linear A :=
    linear_geometricFactorFormula A (Stacks.Blowup.blowUpOver I) (thickeningSheaf I n)
  rw [Functor.map_smul]
  rfl

/-- Restriction of scalars along `A → A/Iⁿ` takes the scalar `[a]` to the scalar `a`. -/
private theorem restrictScalars_map_mk_smul (n : ℕ) {N N' : ModuleCat.{u} (A ⧸ I ^ n)}
    (f : N ⟶ N') (a : A) :
    (ModuleCat.restrictScalars.{u} (Ideal.Quotient.mk (I ^ n))).map
      ((Ideal.Quotient.mk (I ^ n) a) • f) =
        a • (ModuleCat.restrictScalars.{u} (Ideal.Quotient.mk (I ^ n))).map f := rfl

/-- **`p^*` is `A`-linear**: it takes the scalar `a` on a morphism of `A/Iⁿ`-modules to
multiplication by the global function `a` pulls back to. -/
theorem thickeningPullback_map_smul (n : ℕ) {N N' : ModuleCat.{u} (A ⧸ I ^ n)} (f : N ⟶ N')
    (a : A) :
    (thickeningPullback I n).map ((Ideal.Quotient.mk (I ^ n) a) • f) =
      (globalSmulCenter (blowupScheme I) (pullbackCoeff I a)).app _ ≫
        (thickeningPullback I n).map f := by
  show (thickeningFactor I n).map
    ((ModuleCat.restrictScalars.{u} (Ideal.Quotient.mk (I ^ n))).map _) = _
  rw [restrictScalars_map_mk_smul, thickeningFactor_map_smul]
  rfl

/-- **`p^*M` is quasi-coherent**: it is the tensor product of the quasi-coherent `𝒪_{Yₙ}` with the
pullback of a quasi-coherent sheaf on `Spec(A)`. -/
instance isQuasicoherent_thickeningPullback (n : ℕ) (N : ModuleCat.{u} (A ⧸ I ^ n)) :
    ((thickeningPullback I n).obj N).IsQuasicoherent :=
  isQuasicoherent_geometricFactorFormula A (Stacks.Blowup.blowUpOver I)
    ⟨thickeningSheaf I n, (inferInstance : (thickeningSheaf I n).IsQuasicoherent)⟩ _

/-! ### `𝒪_{Yₙ} = p^*(A/Iⁿ)` -/

/-- `𝒪_{Yₙ} ⊗ p^*(Ã) ≅ 𝒪_{Yₙ}`: `geometricFactorFormulaObjSelfIso` at `F = 𝒪_{Yₙ}`. -/
def thickeningFactorObjSelfIso (n : ℕ) :
    (thickeningFactor I n).obj (ModuleCat.of A A) ≅ thickeningSheaf I n :=
  geometricFactorFormulaObjSelfIso A (Stacks.Blowup.blowUpOver I) (thickeningSheaf I n)

/-- **Multiplication by `g ∈ Iⁿ` on `A` goes to zero** under `N ↦ 𝒪_{Yₙ} ⊗ p^*(Ñ)`: it goes to
multiplication by the pulled back function `g` on `𝒪_{Yₙ} ⊗ p^*(Ã) ≅ 𝒪_{Yₙ}`, which is zero by
`globalSmulCenter_pullbackCoeff_app_thickeningSheaf`. -/
theorem thickeningFactor_map_smul_id_eq_zero (n : ℕ) {g : A} (hg : g ∈ I ^ n) :
    (thickeningFactor I n).map (g • 𝟙 (ModuleCat.of A A)) = 0 := by
  rw [thickeningFactor_map_smul, CategoryTheory.Functor.map_id, Category.comp_id]
  refine (cancel_mono (thickeningFactorObjSelfIso I n).hom).1 ?_
  rw [zero_comp]
  have hnat := (globalSmulCenter (blowupScheme I) (pullbackCoeff I g)).naturality
    (thickeningFactorObjSelfIso I n).hom
  rw [← hnat, globalSmulCenter_pullbackCoeff_app_thickeningSheaf I n hg, comp_zero]

/-- The quotient map `A → A/Iⁿ`, as a map of `A`-modules. -/
def quotPowMap (n : ℕ) :
    ModuleCat.of A A ⟶ resModule I n (ModuleCat.of (A ⧸ I ^ n) (A ⧸ I ^ n)) :=
  ModuleCat.ofHom
    { toFun := Ideal.Quotient.mk (I ^ n)
      map_add' := map_add _
      map_smul' := fun a b => map_mul (Ideal.Quotient.mk (I ^ n)) a b }

/-- `A → A/Iⁿ` is surjective. -/
instance epi_quotPowMap (n : ℕ) : Epi (quotPowMap I n) :=
  (ModuleCat.epi_iff_surjective _).2 Ideal.Quotient.mk_surjective

/-- **The presentation map `⨁_{g ∈ Iⁿ} A → A`**, whose `g`-th component is multiplication by `g`.
Its cokernel is `A/Iⁿ` (`exact_quotPowPresentation`). -/
def quotPowPresentation (n : ℕ) :
    ∐ (fun _ : (I ^ n : Ideal A) => ModuleCat.of A A) ⟶ ModuleCat.of A A :=
  Sigma.desc fun k => (k : A) • 𝟙 (ModuleCat.of A A)

/-- The `g`-th component of the presentation map is multiplication by `g`. -/
theorem ι_quotPowPresentation (n : ℕ) (k : (I ^ n : Ideal A)) :
    Sigma.ι (fun _ : (I ^ n : Ideal A) => ModuleCat.of A A) k ≫ quotPowPresentation I n =
      (k : A) • 𝟙 (ModuleCat.of A A) :=
  Sigma.ι_desc _ _

/-- `⨁_{g ∈ Iⁿ} A → A → A/Iⁿ` is zero. -/
theorem quotPowPresentation_comp_quotPowMap (n : ℕ) :
    quotPowPresentation I n ≫ quotPowMap I n = 0 := by
  refine Sigma.hom_ext _ _ fun k => ?_
  rw [reassoc_of% (ι_quotPowPresentation I n k), comp_zero]
  ext
  show Ideal.Quotient.mk (I ^ n) ((k : A) * 1) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mul_mem_right _ _ k.2)

/-- `⨁_{g ∈ Iⁿ} A → A → A/Iⁿ` is exact: an element of `A` with zero image in `A/Iⁿ` is some
`x ∈ Iⁿ`, the image of the basis vector `e_x`. -/
theorem exact_quotPowPresentation (n : ℕ) :
    (ShortComplex.mk _ _ (quotPowPresentation_comp_quotPowMap I n)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  have hx' : x ∈ I ^ n := Ideal.Quotient.eq_zero_iff_mem.1 hx
  refine ⟨(Sigma.ι (fun _ : (I ^ n : Ideal A) => ModuleCat.of A A) ⟨x, hx'⟩).hom 1, ?_⟩
  show ((Sigma.ι (fun _ : (I ^ n : Ideal A) => ModuleCat.of A A) ⟨x, hx'⟩ ≫
    quotPowPresentation I n).hom) 1 = x
  rw [ι_quotPowPresentation]
  show (x : A) * 1 = x
  exact mul_one x

/-- **The presentation map goes to zero.** `N ↦ 𝒪_{Yₙ} ⊗ p^*(Ñ)` commutes with direct sums, so it
suffices that each component does, and that is `thickeningFactor_map_smul_id_eq_zero`. -/
theorem thickeningFactor_map_quotPowPresentation (n : ℕ) :
    (thickeningFactor I n).map (quotPowPresentation I n) = 0 := by
  refine (isColimitOfPreserves (thickeningFactor I n) (colimit.isColimit
    (Discrete.functor fun _ : (I ^ n : Ideal A) => ModuleCat.of A A))).hom_ext fun ⟨k⟩ => ?_
  show (thickeningFactor I n).map (Sigma.ι _ k) ≫ (thickeningFactor I n).map _ =
    (thickeningFactor I n).map (Sigma.ι _ k) ≫ 0
  rw [← CategoryTheory.Functor.map_comp, ι_quotPowPresentation, comp_zero,
    thickeningFactor_map_smul_id_eq_zero I n k.2]

/-- **`A → A/Iⁿ` goes to an isomorphism**: its image is a cokernel of the image of the
presentation map, by right exactness, and that image is zero. -/
instance isIso_thickeningFactor_map_quotPowMap (n : ℕ) :
    IsIso ((thickeningFactor I n).map (quotPowMap I n)) :=
  CokernelCofork.IsColimit.isIso_π _
    (isColimitCoforkMapOfIsColimit' (thickeningFactor I n) _
      (exact_quotPowPresentation I n).gIsCokernel)
    (thickeningFactor_map_quotPowPresentation I n)

/-- **`𝒪_{Yₙ} = p^*(A/Iⁿ)`.** The image of `A → A/Iⁿ` is invertible
(`isIso_thickeningFactor_map_quotPowMap`), and `p^*` of `A` is `𝒪_{Yₙ}` by
`thickeningFactorObjSelfIso`. -/
def thickeningPullbackUnitIso (n : ℕ) :
    (thickeningPullback I n).obj (ModuleCat.of (A ⧸ I ^ n) (A ⧸ I ^ n)) ≅ thickeningSheaf I n :=
  (asIso ((thickeningFactor I n).map (quotPowMap I n))).symm ≪≫ thickeningFactorObjSelfIso I n

/-- The forward map of `thickeningPullbackUnitIso`: the inverse of the image of `A → A/Iⁿ`,
followed by `𝒪_{Yₙ} ⊗ p^*(Ã) ≅ 𝒪_{Yₙ}`. -/
theorem thickeningPullbackUnitIso_hom (n : ℕ) :
    (thickeningPullbackUnitIso I n).hom =
      inv ((thickeningFactor I n).map (quotPowMap I n)) ≫ (thickeningFactorObjSelfIso I n).hom :=
  rfl

/-- **`𝒪_{Y₀} = 0`.** `Y₀` is cut out by the unit ideal; concretely `1 ∈ I⁰` acts on `𝒪_{Y₀}` both
as the identity and, by `globalSmulCenter_pullbackCoeff_app_thickeningSheaf`, as zero. -/
theorem isZero_thickeningSheaf_zero : IsZero (thickeningSheaf I 0) := by
  rw [IsZero.iff_id_eq_zero, ← globalSmulCenter_pullbackCoeff_app_thickeningSheaf I 0
    (g := 1) (by simp)]
  refine Scheme.Modules.hom_ext _ _ fun U => ?_
  ext m
  rw [globalSmulCenter_app_app, show pullbackCoeff I 1 = 1 by simp [pullbackCoeff], map_one,
    one_smul]
  rfl

/-! ### Global sections attached to elements -/

/-- On `A`-linear global sections, multiplication by the global function `a` pulls back to is the
scalar `a`. -/
theorem blowupΓmod_map_globalSmulCenter (a : A) (M : (blowupScheme I).Modules)
    (x : (blowupΓmod I).obj M) :
    (blowupΓmod I).map ((globalSmulCenter (blowupScheme I) (pullbackCoeff I a)).app M) x =
      a • x := by
  show (blowupScheme I).presheaf.map (⊤ : (blowupScheme I).Opens).leTop.op
      (pullbackCoeff I a) • (show Γ(M, ⊤) from x) =
    (pullbackCoeff I a) • (show Γ(M, ⊤) from x)
  rw [show (⊤ : (blowupScheme I).Opens).leTop.op = 𝟙 _ from Subsingleton.elim _ _,
    CategoryTheory.Functor.map_id]
  rfl

/-- The map `A/Iⁿ → N`, `1 ↦ m`, of `A/Iⁿ`-modules. -/
def quotPointMap (n : ℕ) (N : ModuleCat.{u} (A ⧸ I ^ n)) (m : N) :
    ModuleCat.of (A ⧸ I ^ n) (A ⧸ I ^ n) ⟶ N :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton (A ⧸ I ^ n) N m)

/-- The map `A → N`, `1 ↦ m`, of `A`-modules, factored through `A → A/Iⁿ`. -/
def resModulePointMap (n : ℕ) (N : ModuleCat.{u} (A ⧸ I ^ n)) (m : resModule I n N) :
    ModuleCat.of A A ⟶ resModule I n N :=
  quotPowMap I n ≫ (ModuleCat.restrictScalars.{u} (Ideal.Quotient.mk (I ^ n))).map
    (quotPointMap I n N m)

/-- `m ↦ (1 ↦ m)` is additive. -/
theorem resModulePointMap_add (n : ℕ) (N : ModuleCat.{u} (A ⧸ I ^ n))
    (m m' : resModule I n N) :
    resModulePointMap I n N (m + m') = resModulePointMap I n N m + resModulePointMap I n N m' := by
  have h : quotPointMap I n N (m + m') = quotPointMap I n N m + quotPointMap I n N m' :=
    ModuleCat.hom_ext (LinearMap.toSpanSingleton_add (R := A ⧸ I ^ n) (M := N) m m')
  rw [resModulePointMap, resModulePointMap, resModulePointMap, h, Functor.map_add,
    Preadditive.comp_add]

/-- `m ↦ (1 ↦ m)` is `A`-linear. -/
theorem resModulePointMap_smul (n : ℕ) (N : ModuleCat.{u} (A ⧸ I ^ n)) (a : A)
    (m : resModule I n N) :
    resModulePointMap I n N (a • m) = a • resModulePointMap I n N m := by
  have h : quotPointMap I n N (a • m) = Ideal.Quotient.mk (I ^ n) a • quotPointMap I n N m :=
    ModuleCat.hom_ext (LinearMap.toSpanSingleton_smul (R := A ⧸ I ^ n) (M := N)
      (Ideal.Quotient.mk (I ^ n) a) m)
  rw [resModulePointMap, resModulePointMap, h, restrictScalars_map_mk_smul, Linear.comp_smul]

/-- `m ↦ (1 ↦ m)` is natural in `N`. -/
theorem resModulePointMap_comp (n : ℕ) {N N' : ModuleCat.{u} (A ⧸ I ^ n)} (f : N ⟶ N')
    (m : resModule I n N) :
    resModulePointMap I n N m ≫ (ModuleCat.restrictScalars.{u} (Ideal.Quotient.mk (I ^ n))).map f =
      resModulePointMap I n N' (f m) := by
  have h : quotPointMap I n N m ≫ f = quotPointMap I n N' (f m) :=
    ModuleCat.hom_ext (LinearMap.ext_ring (by
      show f ((1 : A ⧸ I ^ n) • m) = (1 : A ⧸ I ^ n) • f m
      rw [one_smul, one_smul]))
  unfold resModulePointMap
  rw [Category.assoc, ← CategoryTheory.Functor.map_comp, h]

/-- For `N = A/Iⁿ`, the map `1 ↦ 1` is the quotient map `A → A/Iⁿ`. -/
theorem resModulePointMap_one (n : ℕ) :
    resModulePointMap I n (ModuleCat.of (A ⧸ I ^ n) (A ⧸ I ^ n))
      (show resModule I n (ModuleCat.of (A ⧸ I ^ n) (A ⧸ I ^ n)) from (1 : A ⧸ I ^ n)) =
        quotPowMap I n := by
  have h : quotPointMap I n (ModuleCat.of (A ⧸ I ^ n) (A ⧸ I ^ n)) (1 : A ⧸ I ^ n) = 𝟙 _ :=
    ModuleCat.hom_ext (LinearMap.ext_ring (by
      show (1 : A ⧸ I ^ n) * 1 = 1
      rw [mul_one]))
  unfold resModulePointMap
  rw [h, CategoryTheory.Functor.map_id, Category.comp_id]

/-- The unit section of `𝒪_{Yₙ}`, the image of `1 ∈ Γ(X, 𝒪_X)`, read as a global section of
`𝒪_{Yₙ} ⊗ p^*(Ã)`. -/
def thickeningBaseSection (n : ℕ) :
    (blowupΓmod I).obj ((thickeningFactor I n).obj (ModuleCat.of A A)) :=
  (blowupΓmod I).map (thickeningFactorObjSelfIso I n).inv
    (((thickeningProj I n).val.app (op ⊤)).hom
      (1 : (blowupScheme I).ringCatSheaf.obj.obj (op ⊤)))

/-- **The global section of `p^*M` attached to an element `m ∈ M`**: the image of `m` under
`M → Γ(Spec(A), M̃) → Γ(X, p^*M̃) → Γ(X, 𝒪_{Yₙ} ⊗ p^*M̃)`, the last map tensoring with the unit
section of `𝒪_{Yₙ}`. It is computed as the image of the unit section of `𝒪_{Yₙ} ⊗ p^*(Ã)` under
`p^*` of the map `A → M`, `1 ↦ m`. -/
def thickeningPullbackSection (n : ℕ) (N : ModuleCat.{u} (A ⧸ I ^ n)) :
    resModule I n N →ₗ[A] (blowupΓmod I).obj ((thickeningPullback I n).obj N) where
  toFun m := (blowupΓmod I).map ((thickeningFactor I n).map (resModulePointMap I n N m))
    (thickeningBaseSection I n)
  map_add' m m' := by
    rw [resModulePointMap_add, Functor.map_add]
    rfl
  map_smul' a m := by
    rw [resModulePointMap_smul, thickeningFactor_map_smul]
    change (blowupΓmod I).map ((thickeningFactor I n).map (resModulePointMap I n N m))
      ((blowupΓmod I).map ((globalSmulCenter (blowupScheme I) (pullbackCoeff I a)).app _)
        (thickeningBaseSection I n)) = _
    rw [blowupΓmod_map_globalSmulCenter, map_smul]
    rfl

/-- The defining formula of `thickeningPullbackSection`. -/
theorem thickeningPullbackSection_apply (n : ℕ) (N : ModuleCat.{u} (A ⧸ I ^ n))
    (m : resModule I n N) :
    thickeningPullbackSection I n N m =
      (blowupΓmod I).map ((thickeningFactor I n).map (resModulePointMap I n N m))
        (thickeningBaseSection I n) :=
  rfl

/-- `A`-linear global sections is a functor, elementwise. -/
theorem blowupΓmod_map_map {M M' M'' : (blowupScheme I).Modules} (φ : M ⟶ M') (ψ : M' ⟶ M'')
    (x : (blowupΓmod I).obj M) :
    (blowupΓmod I).map ψ ((blowupΓmod I).map φ x) = (blowupΓmod I).map (φ ≫ ψ) x :=
  rfl

/-- **The sections attached to elements are natural**: `p^*f` takes the section attached to `m`
to the section attached to `f m`. -/
theorem blowupΓmod_map_thickeningPullbackSection (n : ℕ) {N N' : ModuleCat.{u} (A ⧸ I ^ n)}
    (f : N ⟶ N') (m : resModule I n N) :
    (blowupΓmod I).map ((thickeningPullback I n).map f) (thickeningPullbackSection I n N m) =
      thickeningPullbackSection I n N' (f m) := by
  have key : (thickeningFactor I n).map (resModulePointMap I n N m) ≫
      (thickeningPullback I n).map f =
      (thickeningFactor I n).map (resModulePointMap I n N' (f m)) := by
    rw [← resModulePointMap_comp, CategoryTheory.Functor.map_comp]
    rfl
  exact congrArg (fun φ => (blowupΓmod I).map φ (thickeningBaseSection I n)) key

/-- **The section attached to `1 ∈ A/Iⁿ` is the unit section of `𝒪_{Yₙ}`** under
`p^*(A/Iⁿ) ≅ 𝒪_{Yₙ}`. -/
theorem blowupΓmod_map_thickeningPullbackUnitIso_hom_section_one (n : ℕ) :
    (blowupΓmod I).map (thickeningPullbackUnitIso I n).hom
        (thickeningPullbackSection I n (ModuleCat.of (A ⧸ I ^ n) (A ⧸ I ^ n))
          (show resModule I n (ModuleCat.of (A ⧸ I ^ n) (A ⧸ I ^ n)) from (1 : A ⧸ I ^ n))) =
      ((thickeningProj I n).val.app (op ⊤)).hom
        (1 : (blowupScheme I).ringCatSheaf.obj.obj (op ⊤)) := by
  have h1 := congrArg (fun φ => (blowupΓmod I).map ((thickeningFactor I n).map φ ≫
    (thickeningPullbackUnitIso I n).hom) (thickeningBaseSection I n)) (resModulePointMap_one I n)
  have h2 : (thickeningFactorObjSelfIso I n).inv ≫ (thickeningFactor I n).map (quotPowMap I n) ≫
      (thickeningPullbackUnitIso I n).hom = 𝟙 _ := by
    rw [thickeningPullbackUnitIso_hom, IsIso.hom_inv_id_assoc, Iso.inv_hom_id]
  exact h1.trans (congrArg (fun φ : thickeningSheaf I n ⟶ thickeningSheaf I n =>
    (blowupΓmod I).map φ (show (blowupΓmod I).obj (thickeningSheaf I n) from
      ((thickeningProj I n).val.app (op ⊤)).hom
        (1 : (blowupScheme I).ringCatSheaf.obj.obj (op ⊤)))) h2)

end Stacks.LocalCohomology.UniformityIII

end
