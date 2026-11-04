module

public import StacksFrontier.AlgebraicGeometry.IdealOfClosedSubscheme.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleImmersionReduction.Charts
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.PullbackSections
public import StacksFrontier.AlgebraicGeometry.Divisors.ProjClosedSubschemeKernel
public import StacksFrontier.AlgebraicGeometry.ProjectiveFromSections.PinnedTwist
public import StacksFrontier.AlgebraicGeometry.TwistPullbackRatio.Comparison
public import StacksFrontier.AlgebraicGeometry.Descent.EffectiveEpi.QuasicoherentSectionsEqualizer
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Projective space represents invertible modules with generating sections

The scheme `ℙⁿ_ℤ = Proj ℤ[T₀, …, Tₙ]` represents the functor sending a scheme `X` to the set of
pairs `(L, (s₀, …, sₙ))` with `L` an invertible `𝒪_X`-module and the `sᵢ` global sections
generating `L`, two pairs being identified when an isomorphism of invertible modules carries one
family of sections to the other.

## Main definitions

* `Stacks.ProjectiveSpaceModuli.GeneratingTuple`: an invertible module with an ordered family of
  `n + 1` generating global sections.
* `Stacks.ProjectiveSpaceModuli.setoid`, `Stacks.ProjectiveSpaceModuli.Points`: the identification
  of such pairs by an isomorphism matching the sections, and the quotient.
* `Stacks.ProjectiveSpaceModuli.tautological`: the pair `(g ^* 𝒪(1), (g ^* T₀, …, g ^* Tₙ))`
  attached to a morphism `g : X ⟶ ℙⁿ_ℤ`.
* `Stacks.ProjectiveSpaceModuli.pointsOfHom`, `Stacks.ProjectiveSpaceModuli.pullbackPoints`: the
  classifying map and the contravariant action by pullback.

## Main results

* `Stacks.ProjectiveSpaceModuli.bijective_pointsOfHom` and
  `Stacks.ProjectiveSpaceModuli.pointsEquiv`: the bijection between morphisms `X ⟶ ℙⁿ_ℤ` and
  such pairs up to the above identification.
* `Stacks.ProjectiveSpaceModuli.pointsOfHom_comp`: naturality of that bijection in the test
  scheme: the pair attached to `h ≫ g` is the pullback along `h` of the pair attached to `g`.

## Implementation notes

Injectivity of the classifying map goes through the *pinning* relation
`Stacks.ProjectiveSpaceModuli.IsPinned`: a morphism is pinned by a pair when, on each chart
`X_{sᵢ}`, it is the morphism attached to the ratios `sₖ/sᵢ`. A morphism is pinned by its own
tautological pair, pinning only depends on the pair up to isomorphism, and a pinned morphism is
unique because the charts cover; surjectivity is
`Stacks.TwistPullbackPinned.exists_hom_and_iso_pullback_twistingSheafAtUniverse`.

## References

* [Stacks Project, Tag 01NE](https://stacks.math.columbia.edu/tag/01NE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.AmpleProjectiveImmersion Stacks.ProjectiveFromSections
open Stacks.SectionsToProjectiveSpace Stacks.TwistPullbackPinned

universe u

namespace Stacks.ProjectiveSpaceModuli

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] AlgebraicGeometry.projectiveSpaceAtUniverse

/-! ### Inputs about the tautological coordinates -/

/-- The nonvanishing open of the pulled-back `i`-th homogeneous coordinate is the preimage of
the `i`-th standard chart `D₊(Tᵢ)`. -/
theorem nvOpen_pullbackCoordSection {X : Scheme.{u}} {n : ℕ}
    (g : X ⟶ projectiveSpaceAtUniverse.{u} n) (i : Fin (n + 1)) :
    nvOpen ((Scheme.Modules.pullback g).obj (twistingSheafAtUniverse.{u} n))
        (pullbackCoordSection.{u} g i) =
      g ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i) := by
  refine TopologicalSpace.Opens.ext (Set.ext fun x => ?_)
  have hsec : pullbackCoordSection.{u} g i =
      Stacks.NonvanishingPullback.pullbackGlobalSection g (twistingSheafAtUniverse.{u} n)
        (coordGlobalSection.{u} n i) := by
    show ((Scheme.Modules.pullback g).obj (twistingSheafAtUniverse.{u} n)).presheaf.map
        (eqToHom (show g ⁻¹ᵁ (⊤ : (projectiveSpaceAtUniverse.{u} n).Opens) = ⊤ from rfl)).op
        (Stacks.NonvanishingPullback.pullbackGlobalSection g (twistingSheafAtUniverse.{u} n)
          (coordGlobalSection.{u} n i)) = _
    exact Functor.map_id_apply _ _ _
  have h1 : x ∈ Stacks.Ample.nonvanishingLocus
        ((Scheme.Modules.pullback g).obj (twistingSheafAtUniverse.{u} n))
        (pullbackCoordSection.{u} g i) ↔
      g.base x ∈ Stacks.Ample.nonvanishingLocus (twistingSheafAtUniverse.{u} n)
        (coordGlobalSection.{u} n i) := by
    rw [hsec]
    exact Stacks.NonvanishingPullback.mem_nonvanishingLocus_pullback_iff g _ _ x
  refine h1.trans ?_
  exact Stacks.AlgebraicGeometry.CommonDegreeTwist.mem_nonvanishingLocus_degreeSection_iff'
    (coordGrading.{u} n) 1 1 ⟨MvPolynomial.X i, X_mem_coordGrading_one i⟩
    (by rw [whereInvertible_coordGrading_eq_top]; trivial)

/-- The pulled-back homogeneous coordinates generate `g ^* 𝒪(1)` at every stalk. -/
theorem taut_generates {X : Scheme.{u}} {n : ℕ} (g : X ⟶ projectiveSpaceAtUniverse.{u} n) :
    GeneratesStalks (pullbackCoordSection.{u} g) := by
  refine Stacks.AmpleImmersionReduction.generatesStalks_of_forall_exists_mem _ fun x => ?_
  have hint : ⨆ i : Fin (n + 1),
      AlgebraicGeometry.Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i) = ⊤ :=
    AlgebraicGeometry.Proj.iSup_basicOpen_eq_top _ _
      (AlgebraicGeometry.projectiveSpaceOver.irrelevant_coordGrading_le_span_X n)
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hint.ge
    (show g.base x ∈ (⊤ : (projectiveSpaceAtUniverse.{u} n).Opens) from trivial))
  exact ⟨i, (nvOpen_pullbackCoordSection g i).ge hi⟩

/-- The transition identity for the pulled-back coordinates: on every open inside
`g ⁻¹ D₊(Tᵢ)` one has `g ^* Tⱼ = g ^* (Tⱼ/Tᵢ) · g ^* Tᵢ`. -/
theorem resT_pullbackCoordSection_of_le {X : Scheme.{u}} {n : ℕ}
    (g : X ⟶ projectiveSpaceAtUniverse.{u} n) (i j : Fin (n + 1)) {W : X.Opens}
    (hle : W ≤ g ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i)) :
    resT W (pullbackCoordSection.{u} g j) =
      g.appLE (AlgebraicGeometry.Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i)) W hle
          ((AlgebraicGeometry.Proj.awayToSection (coordGrading.{u} n)
            (MvPolynomial.X i)).hom (coordFrac.{u} i j)) •
        resT W (pullbackCoordSection.{u} g i) := by
  have key := congrArg (pullbackSectionOn g (twistingSheafAtUniverse.{u} n)
    (AlgebraicGeometry.Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i)))
    (coordGlobalSection_res_eq.{u} n i j)
  rw [pullbackSectionOn_smul, pullbackGlobalSections_res, pullbackGlobalSections_res] at key
  have h2 := congrArg (resM hle) key
  rw [resM_smul, resM_resT, resM_resT] at h2
  rw [appLE_apply]
  exact h2

/-- **The coordinates `T₀, …, Tₙ` generate `ℤ[T₀, …, Tₙ]` over its degree-zero part.** -/
private theorem adjoin_range_X_eq_top {n : ℕ} :
    Algebra.adjoin (coordGrading.{u} n 0)
      (Set.range (MvPolynomial.X : Fin (n + 1) → coordRing.{u} n)) = ⊤ := by
  rw [← top_le_iff]
  rintro p -
  induction p using MvPolynomial.induction_on with
  | C a =>
      exact Subalgebra.algebraMap_mem _
        (⟨MvPolynomial.C a, MvPolynomial.isHomogeneous_C _ _⟩ : coordGrading.{u} n 0)
  | add p q hp hq => exact add_mem hp hq
  | mul_X p j hp => exact mul_mem hp (Algebra.subset_adjoin ⟨j, rfl⟩)

/-- **A monomial fraction is the corresponding product of the coordinate fractions `Tⱼ/Tᵢ`**:
if `∑ j, eⱼ = a` then `(∏ j, Tⱼ ^ eⱼ) / Tᵢ ^ a = ∏ j, (Tⱼ / Tᵢ) ^ eⱼ`. -/
private theorem mk_prod_pow_eq_prod_coordFrac {n : ℕ} (i : Fin (n + 1)) (a : ℕ)
    (e : Fin (n + 1) → ℕ) (hae : ∑ j, e j • 1 = a • 1)
    (hp : (∏ j, (MvPolynomial.X j : coordRing.{u} n) ^ e j) ∈ coordGrading.{u} n (a • 1)) :
    HomogeneousLocalization.Away.mk (coordGrading.{u} n) (X_mem_coordGrading_one.{u} i) a
        (∏ j, (MvPolynomial.X j : coordRing.{u} n) ^ e j) hp =
      ∏ j, coordFrac.{u} i j ^ e j := by
  apply (show Function.Injective
      (algebraMap (HomogeneousLocalization.Away (coordGrading.{u} n) (MvPolynomial.X i))
        (Localization.Away (MvPolynomial.X i : coordRing.{u} n))) from
    HomogeneousLocalization.val_injective _)
  simp only [map_prod, map_pow, HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.Away.val_mk, coordFrac, Localization.mk_pow, Localization.mk_prod]
  have ha : ∑ j, e j = a := by simpa using hae
  congr 1
  ext
  simp only [SubmonoidClass.coe_pow, pow_one, Finset.prod_pow_eq_pow_sum, ha]

/-- **A ring homomorphism out of the degree-zero part of the localization of `ℤ[T₀, …, Tₙ]` at
`Tᵢ` is determined by its values on the fractions `Tⱼ/Tᵢ`.** -/
theorem away_ringHom_ext_coordFrac {n : ℕ} (i : Fin (n + 1)) {R : Type*} [CommRing R]
    {φ ψ : HomogeneousLocalization.Away (coordGrading.{u} n) (MvPolynomial.X i) →+* R}
    (h : ∀ j : Fin (n + 1), φ (coordFrac.{u} i j) = ψ (coordFrac.{u} i j)) : φ = ψ := by
  refine RingHom.ext fun z => ?_
  have hz : z ∈ (⊤ : Subalgebra (coordGrading.{u} n 0)
      (HomogeneousLocalization.Away (coordGrading.{u} n) (MvPolynomial.X i))) := trivial
  rw [← HomogeneousLocalization.Away.adjoin_mk_prod_pow_eq_top
    (X_mem_coordGrading_one.{u} i) (Fin (n + 1))
    MvPolynomial.X adjoin_range_X_eq_top (fun _ => 1)
    (fun j => X_mem_coordGrading_one.{u} j)] at hz
  induction hz using Algebra.adjoin_induction with
  | mem x hx =>
      obtain ⟨a, e, hae, hae', rfl⟩ := hx
      rw [mk_prod_pow_eq_prod_coordFrac i a e hae]
      simp only [map_prod, map_pow, h]
  | algebraMap r =>
      obtain ⟨c, hc⟩ := (Submodule.mem_one).1
        (by simpa only [MvPolynomial.homogeneousSubmodule_zero] using r.2)
      have hr : r = ((c.down : ℤ) : coordGrading.{u} n 0) := by
        apply Subtype.ext
        rw [← hc, SetLike.GradeZero.coe_intCast, MvPolynomial.algebraMap_eq,
          ← map_intCast (MvPolynomial.C : ULift.{u} ℤ →+* coordRing.{u} n) c.down]
        norm_cast
      rw [hr, map_intCast, map_intCast, map_intCast]
  | add x y hx hy ihx ihy => simp [ihx, ihy]
  | mul x y hx hy ihx ihy => simp [ihx, ihy]

/-- The canonical map `(A_{Tᵢ})₀ ⟶ Γ(ℙⁿ_ℤ, D₊(Tᵢ))` is an isomorphism, `Tᵢ` being homogeneous
of degree one. -/
private theorem isIso_awayToSection (n : ℕ) (i : Fin (n + 1)) :
    IsIso (AlgebraicGeometry.Proj.awayToSection (coordGrading.{u} n) (MvPolynomial.X i)) := by
  rw [← AlgebraicGeometry.Proj.basicOpenIsoAway_hom (coordGrading.{u} n) (MvPolynomial.X i)
    (X_mem_coordGrading_one i) Nat.one_pos]
  infer_instance

/-- **The pullback of the fraction `Tⱼ/Tᵢ` along `g` is the ratio of the tautological
coordinates.** The transition identity says the pulled-back fraction multiplies `g ^* Tᵢ` to
`g ^* Tⱼ` on the chart, and the ratio is the only section doing that. -/
private theorem appLE_coordFrac_taut {X : Scheme.{u}} {n : ℕ}
    (g : X ⟶ projectiveSpaceAtUniverse.{u} n) (i j : Fin (n + 1)) :
    g.appLE (AlgebraicGeometry.Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i))
        (nvCover (pullbackCoordSection.{u} g) i) (nvOpen_pullbackCoordSection g i).le
        ((AlgebraicGeometry.Proj.awayToSection (coordGrading.{u} n) (MvPolynomial.X i)).hom
          (coordFrac.{u} i j)) = ratio (pullbackCoordSection.{u} g) i j :=
  eq_div _ le_rfl
    (resT_pullbackCoordSection_of_le g i j (nvOpen_pullbackCoordSection g i).le).symm

/-- **Two morphisms to `ℙⁿ_ℤ` that land in the chart `D₊(Tᵢ)` and agree on the sections of that
chart are equal.** The chart is affine, so a morphism into it is determined by its effect on
global sections, and the inclusion of the top open is an isomorphism. -/
private theorem eq_of_appLE_chart {W : Scheme.{u}} {n : ℕ} (i : Fin (n + 1))
    (f₁ f₂ : W ⟶ projectiveSpaceAtUniverse.{u} n)
    (e₁ : (⊤ : W.Opens) ≤
      f₁ ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i))
    (e₂ : (⊤ : W.Opens) ≤
      f₂ ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i))
    (h : f₁.appLE (AlgebraicGeometry.Proj.basicOpen (coordGrading.{u} n)
          (MvPolynomial.X i)) ⊤ e₁ =
      f₂.appLE (AlgebraicGeometry.Proj.basicOpen (coordGrading.{u} n)
        (MvPolynomial.X i)) ⊤ e₂) :
    f₁ = f₂ := by
  have hc : f₁.resLE (AlgebraicGeometry.Proj.basicOpen (coordGrading.{u} n)
        (MvPolynomial.X i)) ⊤ e₁ =
      f₂.resLE (AlgebraicGeometry.Proj.basicOpen (coordGrading.{u} n)
        (MvPolynomial.X i)) ⊤ e₂ := by
    refine Stacks.ProjGlobalSectionsAppTop.ext_of_appTop_basicOpen (coordGrading.{u} n)
      Nat.one_pos (X_mem_coordGrading_one i) ?_
    rw [Scheme.Hom.appTop, Scheme.Hom.appTop, Scheme.Hom.resLE_app_top,
      Scheme.Hom.resLE_app_top, h]
  have h1 := congrArg (fun c => c ≫ (AlgebraicGeometry.Proj.basicOpen (coordGrading.{u} n)
    (MvPolynomial.X i)).ι) hc
  simp only [Scheme.Hom.resLE_comp_ι] at h1
  have : IsIso (Scheme.Opens.ι (⊤ : W.Opens)) := by
    rw [← Scheme.topIso_hom W]; infer_instance
  exact (cancel_epi _).mp h1

/-- **The chart `X_{g ^* Tᵢ}` maps into `D₊(Tᵢ)` along `g`**, the chart being the whole preimage
of `D₊(Tᵢ)`. -/
private theorem top_le_preimage_ι_comp {X : Scheme.{u}} {n : ℕ}
    (g : X ⟶ projectiveSpaceAtUniverse.{u} n) (i : Fin (n + 1)) :
    (⊤ : (nvCover (pullbackCoordSection.{u} g) i).toScheme.Opens) ≤
      ((nvCover (pullbackCoordSection.{u} g) i).ι ≫ g) ⁻¹ᵁ
        AlgebraicGeometry.Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i) :=
  le_trans (Scheme.Opens.ι_preimage_self _).ge
    ((Opens.map (nvCover (pullbackCoordSection.{u} g) i).ι.base).map
      (homOfLE (nvOpen_pullbackCoordSection g i).le)).le

/-- **The morphism of the ratio family out of `g ^* Tᵢ` maps into `D₊(Tᵢ)`**, its `i`-th ratio
being `1`. -/
private theorem top_le_preimage_toProj {X : Scheme.{u}} {n : ℕ}
    (g : X ⟶ projectiveSpaceAtUniverse.{u} n) (i : Fin (n + 1)) :
    (⊤ : (nvCover (pullbackCoordSection.{u} g) i).toScheme.Opens) ≤
      toProjectiveSpaceAtUniverse (chartRatio (pullbackCoordSection.{u} g) i)
          (span_range_chartRatio (pullbackCoordSection.{u} g) i) ⁻¹ᵁ
        AlgebraicGeometry.Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i) := by
  rw [preimage_basicOpen (chartRatio (pullbackCoordSection.{u} g) i)
      (span_range_chartRatio (pullbackCoordSection.{u} g) i) i, chartRatio_self,
    Scheme.basicOpen_one (nvCover (pullbackCoordSection.{u} g) i).toScheme]

/-- **The pullback of `Tⱼ/Tᵢ` along the restriction of `g` to the chart is the chart ratio
`(g ^* Tⱼ)/(g ^* Tᵢ)`**, read through
`AlgebraicGeometry.Scheme.Opens.topIso`. -/
private theorem appLE_top_coordFrac_ι_comp {X : Scheme.{u}} {n : ℕ}
    (g : X ⟶ projectiveSpaceAtUniverse.{u} n) (i j : Fin (n + 1)) :
    ((nvCover (pullbackCoordSection.{u} g) i).ι ≫ g).appLE
        (AlgebraicGeometry.Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i)) ⊤
        (top_le_preimage_ι_comp g i)
        ((AlgebraicGeometry.Proj.awayToSection (coordGrading.{u} n) (MvPolynomial.X i)).hom
          (coordFrac.{u} i j)) = chartRatio (pullbackCoordSection.{u} g) i j := by
  have h1 := CategoryTheory.ConcreteCategory.congr_hom
    (appLE_comp_topIso_inv g (nvCover (pullbackCoordSection.{u} g) i)
      (AlgebraicGeometry.Proj.basicOpen (coordGrading.{u} n) (MvPolynomial.X i))
      (nvOpen_pullbackCoordSection g i).le)
    ((AlgebraicGeometry.Proj.awayToSection (coordGrading.{u} n) (MvPolynomial.X i)).hom
      (coordFrac.{u} i j))
  rw [CategoryTheory.ConcreteCategory.comp_apply, appLE_coordFrac_taut g i j] at h1
  exact h1.symm

/-- **Every morphism to projective space is pinned by its own tautological coordinates**: on the
chart where `g ^* Tᵢ` does not vanish, `g` is the morphism attached to the ratio family
`(g ^* Tₖ)/(g ^* Tᵢ)`. -/
theorem taut_pin {X : Scheme.{u}} {n : ℕ} (g : X ⟶ projectiveSpaceAtUniverse.{u} n)
    (i : Fin (n + 1)) :
    (nvCover (pullbackCoordSection.{u} g) i).ι ≫ g =
      toProjectiveSpaceAtUniverse (chartRatio (pullbackCoordSection.{u} g) i)
        (span_range_chartRatio (pullbackCoordSection.{u} g) i) := by
  refine eq_of_appLE_chart i _ _ (top_le_preimage_ι_comp g i) (top_le_preimage_toProj g i) ?_
  have : IsIso (AlgebraicGeometry.Proj.awayToSection (coordGrading.{u} n) (MvPolynomial.X i)) :=
    isIso_awayToSection.{u} n i
  rw [← cancel_epi (AlgebraicGeometry.Proj.awayToSection (coordGrading.{u} n)
    (MvPolynomial.X i))]
  refine CommRingCat.hom_ext (away_ringHom_ext_coordFrac i fun j => ?_)
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  rw [appLE_top_coordFrac_ι_comp g i j,
    appLE_top_coordFrac (chartRatio (pullbackCoordSection.{u} g) i)
      (span_range_chartRatio (pullbackCoordSection.{u} g) i) i j
      (chartRatio_self (pullbackCoordSection.{u} g) i) (top_le_preimage_toProj g i)]

/-- **A morphism pinned by a generating family is unique**: the charts `X_{sᵢ}` cover `X`. -/
theorem eq_of_pin {X : Scheme.{u}} {n : ℕ} {M : X.Modules}
    [Stacks.Ample.IsInvertibleModule X M] (s : Fin (n + 1) → Γ(M, ⊤))
    (hs : GeneratesStalks s) (g g' : X ⟶ projectiveSpaceAtUniverse.{u} n)
    (h : ∀ i, (nvCover s i).ι ≫ g =
      toProjectiveSpaceAtUniverse (chartRatio s i) (span_range_chartRatio s i))
    (h' : ∀ i, (nvCover s i).ι ≫ g' =
      toProjectiveSpaceAtUniverse (chartRatio s i) (span_range_chartRatio s i)) :
    g = g' := by
  refine Scheme.Cover.hom_ext (X.openCoverOfIsOpenCover (nvCover s)
    (isOpenCover_nvCover_of_generatesStalks s hs)) g g' fun i => ?_
  exact (h i).trans (h' i).symm

/-- The action on sections of an isomorphism of `𝒪_X`-modules is injective. -/
private theorem app_injective {X : Scheme.{u}} {M N : X.Modules} (β : M ≅ N) (U : X.Opens) :
    Function.Injective (Scheme.Modules.Hom.app β.hom U) :=
  ((CategoryTheory.ConcreteCategory.isIso_iff_bijective
    (Scheme.Modules.Hom.app β.hom U)).mp inferInstance).injective

/-- A morphism of `𝒪_X`-modules commutes with the restriction of a global section. -/
private theorem app_resT {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N) (U : X.Opens)
    (x : Γ(M, ⊤)) :
    Scheme.Modules.Hom.app φ U (resT U x) = resT U (Scheme.Modules.Hom.app φ ⊤ x) :=
  PresheafOfModules.app_resLE φ.val le_top x

/-- **An isomorphism matching the sections matches the charts**: the nonvanishing locus of a
section is unchanged by transporting it along an isomorphism of `𝒪_X`-modules. -/
private theorem nvCover_eq {X : Scheme.{u}} {n : ℕ} {M N : X.Modules}
    [Stacks.Ample.IsInvertibleModule X M] [Stacks.Ample.IsInvertibleModule X N]
    (s : Fin (n + 1) → Γ(M, ⊤)) (tt : Fin (n + 1) → Γ(N, ⊤)) (β : M ≅ N)
    (hβ : ∀ i, Scheme.Modules.Hom.app β.hom ⊤ (s i) = tt i) (i : Fin (n + 1)) :
    nvCover tt i = nvCover s i := by
  refine TopologicalSpace.Opens.ext (Set.ext fun x => ?_)
  show x ∈ Stacks.Ample.nonvanishingLocus N (tt i) ↔
    x ∈ Stacks.Ample.nonvanishingLocus M (s i)
  rw [← hβ i, Stacks.Ample.nonvanishingLocus_congr β (s i)]

/-- **An isomorphism matching the sections matches the ratios**: the ratio of the transported
family multiplies `sᵢ` to `sₖ`, because the isomorphism is semilinear and injective. -/
private theorem ratio_smul_of_iso {X : Scheme.{u}} {n : ℕ} {M N : X.Modules}
    [Stacks.Ample.IsInvertibleModule X N]
    (s : Fin (n + 1) → Γ(M, ⊤)) (tt : Fin (n + 1) → Γ(N, ⊤)) (β : M ≅ N)
    (hβ : ∀ i, Scheme.Modules.Hom.app β.hom ⊤ (s i) = tt i) (i k : Fin (n + 1)) :
    ratio tt i k • resT (nvCover tt i) (s i) = resT (nvCover tt i) (s k) := by
  refine app_injective β (nvCover tt i) ?_
  rw [Scheme.Modules.Hom.app_smul, app_resT, app_resT, hβ i, hβ k]
  exact ratio_smul tt i k

/-- **Pinning only depends on the chart and on the ratios.** -/
private theorem pin_of_eq {X : Scheme.{u}} {n : ℕ} {M : X.Modules}
    [Stacks.Ample.IsInvertibleModule X M]
    (s : Fin (n + 1) → Γ(M, ⊤)) (g : X ⟶ projectiveSpaceAtUniverse.{u} n) (i : Fin (n + 1))
    (hpin : (nvCover s i).ι ≫ g =
      toProjectiveSpaceAtUniverse (chartRatio s i) (span_range_chartRatio s i))
    {U : X.Opens} (hU : U = nvCover s i) {b : Fin (n + 1) → Γ(U.toScheme, ⊤)}
    (hb : Ideal.span (Set.range b) = ⊤) (a : Fin (n + 1) → Γ(X, U))
    (hab : ∀ k, b k = U.topIso.inv (a k)) (ha : ∀ k, a k • resT U (s i) = resT U (s k)) :
    U.ι ≫ g = toProjectiveSpaceAtUniverse b hb := by
  subst hU
  have hbk : b = chartRatio s i := funext fun k => by
    rw [hab k, show a k = ratio s i k from eq_div (s i) le_rfl (ha k)]
    rfl
  subst hbk
  exact hpin

/-- **Pinning transports along an isomorphism matching the sections.** -/
theorem pin_of_iso {X : Scheme.{u}} {n : ℕ} {M N : X.Modules}
    [Stacks.Ample.IsInvertibleModule X M] [Stacks.Ample.IsInvertibleModule X N]
    (s : Fin (n + 1) → Γ(M, ⊤)) (tt : Fin (n + 1) → Γ(N, ⊤)) (β : M ≅ N)
    (hβ : ∀ i, Scheme.Modules.Hom.app β.hom ⊤ (s i) = tt i)
    (g : X ⟶ projectiveSpaceAtUniverse.{u} n)
    (h : ∀ i, (nvCover s i).ι ≫ g =
      toProjectiveSpaceAtUniverse (chartRatio s i) (span_range_chartRatio s i))
    (i : Fin (n + 1)) :
    (nvCover tt i).ι ≫ g =
      toProjectiveSpaceAtUniverse (chartRatio tt i) (span_range_chartRatio tt i) :=
  pin_of_eq s g i (h i) (nvCover_eq s tt β hβ i) (span_range_chartRatio tt i) (ratio tt i)
    (fun _ => rfl) (ratio_smul_of_iso s tt β hβ i)


/-- On global sections, an isomorphism of modules undoes its inverse. -/
private theorem moduleIso_hom_inv_app {X : Scheme.{u}} {F G : X.Modules} (e : F ≅ G)
    (y : Γ(G, ⊤)) :
    Scheme.Modules.Hom.app e.hom ⊤ (Scheme.Modules.Hom.app e.inv ⊤ y) = y :=
  (CategoryTheory.ConcreteCategory.congr_hom
    (congrArg (fun t => Scheme.Modules.Hom.app t ⊤) (Iso.inv_hom_id e)) y).trans
      (CategoryTheory.id_apply y)


/-- An invertible `𝒪_X`-module together with an ordered family of `n + 1` global sections
generating it. This is the datum Stacks Tag 01NE attaches to a scheme. -/
structure GeneratingTuple (X : Scheme.{u}) (n : ℕ) where
  /-- The underlying module. -/
  bundle : X.Modules
  /-- The module is invertible. -/
  isInvertible : Stacks.Ample.IsInvertibleModule X bundle
  /-- The ordered family of global sections. -/
  coord : Fin (n + 1) → Γ(bundle, ⊤)
  /-- The sections generate the module at every stalk. -/
  generates : GeneratesStalks coord

attribute [instance] GeneratingTuple.isInvertible

variable {X Y : Scheme.{u}} {n : ℕ}

/-- Two pairs are identified when an isomorphism of the underlying modules carries each section
of the first to the corresponding section of the second. This is the equivalence of Tag 01NE. -/
def Isomorphic (t t' : GeneratingTuple X n) : Prop :=
  ∃ β : t.bundle ≅ t'.bundle, ∀ i, Scheme.Modules.Hom.app β.hom ⊤ (t.coord i) = t'.coord i

/-- Every pair is identified with itself. -/
theorem isomorphic_refl (t : GeneratingTuple X n) : Isomorphic t t :=
  ⟨Iso.refl _, fun i => by simp⟩

/-- The identification of pairs is symmetric. -/
theorem isomorphic_symm {t t' : GeneratingTuple X n} (h : Isomorphic t t') : Isomorphic t' t := by
  obtain ⟨β, hβ⟩ := h
  refine ⟨β.symm, fun i => ?_⟩
  rw [← hβ i]
  exact AlgebraicGeometry.SectionsEqualizer.moduleIso_hom_inv_app β.symm (t.coord i)

/-- The identification of pairs is transitive. -/
theorem isomorphic_trans {t t' t'' : GeneratingTuple X n} (h : Isomorphic t t')
    (h' : Isomorphic t' t'') : Isomorphic t t'' := by
  obtain ⟨β, hβ⟩ := h
  obtain ⟨γ, hγ⟩ := h'
  refine ⟨β.trans γ, fun i => ?_⟩
  rw [show (β.trans γ).hom = β.hom ≫ γ.hom from rfl,
    show Scheme.Modules.Hom.app (β.hom ≫ γ.hom) ⊤ =
      Scheme.Modules.Hom.app β.hom ⊤ ≫ Scheme.Modules.Hom.app γ.hom ⊤ from rfl,
    CategoryTheory.ConcreteCategory.comp_apply, hβ i, hγ i]

/-- The identification of pairs of Tag 01NE, as an equivalence relation. -/
def setoid (X : Scheme.{u}) (n : ℕ) : Setoid (GeneratingTuple X n) where
  r := Isomorphic
  iseqv := ⟨isomorphic_refl, isomorphic_symm, isomorphic_trans⟩

/-- The set of pairs `(L, (s₀, …, sₙ))` on `X` up to the identification of Tag 01NE. -/
abbrev Points (X : Scheme.{u}) (n : ℕ) : Type _ := Quotient (setoid X n)

/-! ### The tautological pair of a morphism -/

/-- **The pair attached to a morphism to projective space**: the pullback of the twisting sheaf
`𝒪(1)` together with the pullbacks of the homogeneous coordinates `T₀, …, Tₙ`. -/
def tautological (g : X ⟶ projectiveSpaceAtUniverse.{u} n) : GeneratingTuple X n where
  bundle := (Scheme.Modules.pullback g).obj (twistingSheafAtUniverse.{u} n)
  isInvertible := isInvertibleModule_pullback_twistingSheafAtUniverse g
  coord := pullbackCoordSection.{u} g
  generates := taut_generates g

/-- The class of the pair attached to a morphism: the classifying map of Tag 01NE. -/
def pointsOfHom (g : X ⟶ projectiveSpaceAtUniverse.{u} n) : Points X n := ⟦tautological g⟧

/-! ### Pinning -/

/-- A morphism is *pinned* by a pair `(L, s)` when on each chart `X_{sᵢ}` it is the morphism
attached to the family of ratios `sₖ/sᵢ`. This is the chartwise description of the morphism
Tag 01NE attaches to a pair. -/
def IsPinned (t : GeneratingTuple X n) (g : X ⟶ projectiveSpaceAtUniverse.{u} n) : Prop :=
  ∀ i, (nvCover t.coord i).ι ≫ g =
    toProjectiveSpaceAtUniverse (chartRatio t.coord i) (span_range_chartRatio t.coord i)

/-- **A morphism is pinned by its own tautological pair.** -/
theorem isPinned_tautological (g : X ⟶ projectiveSpaceAtUniverse.{u} n) :
    IsPinned (tautological g) g := fun i => taut_pin g i

/-- **Pinning only depends on the pair up to the identification of Tag 01NE.** -/
theorem isPinned_of_isomorphic {t t' : GeneratingTuple X n} (h : Isomorphic t t')
    {g : X ⟶ projectiveSpaceAtUniverse.{u} n} (hg : IsPinned t g) : IsPinned t' g := by
  obtain ⟨β, hβ⟩ := h
  exact fun i => pin_of_iso t.coord t'.coord β hβ g hg i

/-- **A pinned morphism is unique**: the charts `X_{sᵢ}` cover `X`. -/
theorem eq_of_isPinned {t : GeneratingTuple X n} {g g' : X ⟶ projectiveSpaceAtUniverse.{u} n}
    (hg : IsPinned t g) (hg' : IsPinned t g') : g = g' :=
  eq_of_pin t.coord t.generates g g' hg hg'

/-! ### The bijection -/

/-- **The classifying map of Tag 01NE is injective.** -/
theorem pointsOfHom_injective :
    Function.Injective (pointsOfHom (X := X) (n := n)) := by
  intro g g' h
  have h' : Isomorphic (tautological g) (tautological g') := Quotient.exact h
  exact eq_of_isPinned (isPinned_of_isomorphic h' (isPinned_tautological g))
    (isPinned_tautological g')

/-- **The classifying map of Tag 01NE is surjective**: every invertible module with `n + 1`
generating global sections is the pullback of `𝒪(1)` with its homogeneous coordinates. -/
@[ega "II 7.3.9" "more general"]
theorem pointsOfHom_surjective :
    Function.Surjective (pointsOfHom (X := X) (n := n)) := by
  refine Quotient.ind fun t => ?_
  obtain ⟨g, α, hα, hsec⟩ :=
    exists_hom_and_iso_pullback_twistingSheafAtUniverse t.coord t.generates
  refine ⟨g, Quotient.sound ⟨@asIso _ _ _ _ α hα, fun i => hsec i⟩⟩

/-- Projective `n`-space over the integers represents the functor sending a scheme `X` to the
set of pairs `(L, (s₀, …, sₙ))` with `L` an invertible `𝒪_X`-module and the `sᵢ` generating
global sections, up to an isomorphism matching the sections: the classifying map is a
bijection. -/
@[stacks 01NE "the bijection on points"]
theorem bijective_pointsOfHom :
    Function.Bijective (pointsOfHom (X := X) (n := n)) :=
  ⟨pointsOfHom_injective, pointsOfHom_surjective⟩

/-- The bijection between morphisms `X ⟶ ℙⁿ_ℤ` and invertible modules with `n + 1` generating
global sections up to isomorphism. -/
@[stacks 01NE "the representing bijection"]
def pointsEquiv (X : Scheme.{u}) (n : ℕ) :
    (X ⟶ projectiveSpaceAtUniverse.{u} n) ≃ Points X n :=
  Equiv.ofBijective _ bijective_pointsOfHom

/-- The bijection `pointsEquiv` sends a morphism `g` to the class of its tautological pair. -/
@[simp] theorem pointsEquiv_apply (g : X ⟶ projectiveSpaceAtUniverse.{u} n) :
    pointsEquiv X n g = ⟦tautological g⟧ := rfl

/-- **A pair that pins a morphism is the tautological pair of that morphism**, up to the
identification of Tag 01NE. -/
theorem isomorphic_tautological_of_isPinned {t : GeneratingTuple X n}
    {g : X ⟶ projectiveSpaceAtUniverse.{u} n} (hg : IsPinned t g) :
    Isomorphic (tautological g) t := by
  obtain ⟨α, hα, hsec⟩ := exists_iso_pullback_twistingSheafAtUniverse t.coord g
    (isOpenCover_nvCover_of_generatesStalks t.coord t.generates) hg
  exact ⟨@asIso _ _ _ _ α hα, fun i => hsec i⟩

/-- The morphism classifying a pair is the unique morphism pinned by it. -/
theorem pointsEquiv_symm_eq {t : GeneratingTuple X n}
    {g : X ⟶ projectiveSpaceAtUniverse.{u} n} (hg : IsPinned t g) :
    (pointsEquiv X n).symm ⟦t⟧ = g := by
  have h : pointsEquiv X n g = ⟦t⟧ :=
    Quotient.sound (isomorphic_tautological_of_isPinned hg)
  rw [← h, Equiv.symm_apply_apply]

/-! ### Functoriality in the test scheme -/

/-- The pullback of an invertible module with generating sections along a morphism of schemes. -/
def pullbackTuple (h : Y ⟶ X) (t : GeneratingTuple X n) : GeneratingTuple Y n where
  bundle := (Scheme.Modules.pullback h).obj t.bundle
  isInvertible := Stacks.InvertiblePullback.isInvertibleModule_pullback h t.bundle
  coord := fun i => pullbackGlobalSections h t.bundle (t.coord i)
  generates := by
    let _ : Stacks.Ample.IsInvertibleModule Y ((Scheme.Modules.pullback h).obj t.bundle) :=
      Stacks.InvertiblePullback.isInvertibleModule_pullback h t.bundle
    refine Stacks.AmpleImmersionReduction.generatesStalks_of_forall_exists_mem _ fun y => ?_
    obtain ⟨i, hi⟩ := exists_mem_nvCover_of_generatesStalks t.coord t.generates (h.base y)
    exact ⟨i, mem_nonvanishingLocus_pullbackGlobalSections h t.bundle (t.coord i) hi⟩

/-- Pulling back respects the identification of Tag 01NE. -/
theorem pullbackTuple_isomorphic (h : Y ⟶ X) {t t' : GeneratingTuple X n}
    (ht : Isomorphic t t') : Isomorphic (pullbackTuple h t) (pullbackTuple h t') := by
  obtain ⟨β, hβ⟩ := ht
  refine ⟨(Scheme.Modules.pullback h).mapIso β, fun i => ?_⟩
  have hnat := CategoryTheory.ConcreteCategory.congr_hom
    (Stacks.AlgebraicGeometry.IdealOfClosedSubscheme.pullbackGlobalSections_naturality_app
      h β.hom) (t.coord i)
  rw [CategoryTheory.ConcreteCategory.comp_apply,
    CategoryTheory.ConcreteCategory.comp_apply, hβ i] at hnat
  exact hnat

/-- The contravariant action of Tag 01NE's functor on morphisms: pullback of pairs. -/
def pullbackPoints (h : Y ⟶ X) : Points X n → Points Y n :=
  Quotient.map (pullbackTuple h) fun _ _ ht => pullbackTuple_isomorphic h ht

/-- The pullback of the class of a pair is the class of its pullback. -/
@[simp] theorem pullbackPoints_mk (h : Y ⟶ X) (t : GeneratingTuple X n) :
    pullbackPoints h ⟦t⟧ = ⟦pullbackTuple h t⟧ := rfl

/-- The classifying map is natural in the test scheme: the pair attached to `h ≫ g` is the
pullback along `h` of the pair attached to `g`. -/
@[stacks 01NE "naturality of the bijection in the test scheme"]
theorem pointsOfHom_comp (h : Y ⟶ X) (g : X ⟶ projectiveSpaceAtUniverse.{u} n) :
    pointsOfHom (h ≫ g) = pullbackPoints h (pointsOfHom g) := by
  refine Quotient.sound (isomorphic_symm ⟨?_, ?_⟩)
  · exact (Scheme.Modules.pullbackComp h g).app (twistingSheafAtUniverse.{u} n)
  · intro i
    exact AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_comp h g
      (twistingSheafAtUniverse.{u} n)
      (coordGlobalSection.{u} n i)

end Stacks.ProjectiveSpaceModuli

end
