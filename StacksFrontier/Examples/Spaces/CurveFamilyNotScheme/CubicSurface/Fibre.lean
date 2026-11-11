module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.SmoothPlaneConic
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.SmoothProperCurveCriteria
public import StacksFrontier.Examples.Spaces.CurveFamilyNotScheme.CubicSurface.Smooth
public import StacksFrontier.Examples.Spaces.CurveFamilyNotScheme.FermatCurveProperties

/-!
# The fibre of the cubic surface over the origin: the Fermat cubic

The fibre of `Y : T₀³ + T₁³ + T₂³ - t T₀T₁T₂ = 0` over the origin `t = 0` of the affine line is
the Fermat cubic `E = Stacks.Examples.CurveFamilyNotScheme.fermatCurve k`, the plane curve
`T₀³ + T₁³ + T₂³ = 0` in `ℙ²_k`. This file identifies `E` with the base change of `Y ⟶ A¹_k`
along `Spec k ⟶ A¹_k`, `t ↦ 0`, whose image is `Stacks.Examples.CurveFamilyNotScheme.originPoint`,
and completes the description of `E` as a curve over `k`: `H⁰(E, 𝒪_E) = k`, read off the sequence
`0 → 𝒪(-3) → 𝒪 → 𝒪_E → 0` on `ℙ²_k`, and, when the characteristic of `k` is not three, `E` is
geometrically integral (Stacks 0E81: it is smooth and proper of dimension one with `H⁰ = k`) and
projective over `k`.

Both steps go through `Stacks.Models.PlaneCurveModel`: `E` is `Proj` of the graded ring
`k[T₀, T₁, T₂]/(T₀³ + T₁³ + T₂³)` graded by submodules, and
`Stacks.Models.PlaneCurveModel.moduleGradingIso` identifies it, over `Spec k`, with the plane curve
model, for which base change (`Stacks.Models.PlaneCurveModel.isPullback_mapMap`) and the global
sections are available.

## Main definitions

* `Stacks.Examples.CurveFamilyNotScheme.fermatModelIso`: `E` as the plane curve model of the
  Fermat cubic.
* `Stacks.Examples.CurveFamilyNotScheme.fermatToCubicSurface`: the inclusion `E ⟶ Y` of the fibre
  over the origin.

## Main results

* `Stacks.Examples.CurveFamilyNotScheme.isPullback_fermatToCubicSurface`: `E` is the base change
  of `Y ⟶ A¹_k` along `Spec k ⟶ A¹_k`, `t ↦ 0`.
* `Stacks.Examples.CurveFamilyNotScheme.range_specMap_evalZero`: that point of `A¹_k` is
  `originPoint k`.
* `Stacks.Examples.CurveFamilyNotScheme.fermatCurveIsoFiber`: `E` is the scheme-theoretic fibre
  `(cubicSurfaceToLine k).fiber (originPoint k)`, compatibly with the inclusions into `Y`
  (`fermatCurveIsoFiber_hom_fiberι`) and with `Spec κ(origin) ≅ Spec k`
  (`fermatCurveIsoFiber_hom_fiberToSpecResidueField`).
* `Stacks.Examples.CurveFamilyNotScheme.isIso_globalSections_fermatCurve`: `H⁰(E, 𝒪_E) = k`.
* `Stacks.Examples.CurveFamilyNotScheme.geometricallyIntegral_fermatCurveToSpec`: `E` is
  geometrically integral over `k`.
* `Stacks.Examples.CurveFamilyNotScheme.isHProjective_fermatCurveToSpec`: `E` is projective over
  `k`.

## References

* [Stacks Project, Tag 0D5E](https://stacks.math.columbia.edu/tag/0D5E)
* [Stacks Project, Tag 0BYD](https://stacks.math.columbia.edu/tag/0BYD)
* [Stacks Project, Tag 0E81](https://stacks.math.columbia.edu/tag/0E81)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial
open AlgebraicGeometry.ProjectiveSpectrum.Proj
  (projectiveSpace_ker_eq_zeroScheme_of_idealOfClosedSubscheme_eq_span)
open Stacks.ProjectiveSpace.Cohomology
open Stacks.RingTheory.HomogeneousQuotient (quotientGrading quotientMk)

universe u

namespace Stacks.Examples.CurveFamilyNotScheme

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k]

/-! ### The Fermat cubic as a plane curve model -/

/-- The Fermat cubic as the plane curve model `V(T₀³ + T₁³ + T₂³)` of
`Stacks.Models.PlaneCurveModel`. -/
abbrev fermatModel : Scheme.{u} :=
  Stacks.Models.PlaneCurveModel.scheme (fermatCubic k) (fermatCubic_isHomogeneous k)

/-- The structure morphism of the plane curve model of the Fermat cubic. -/
abbrev fermatModelToSpec : fermatModel k ⟶ Spec (CommRingCat.of k) :=
  Stacks.Models.PlaneCurveModel.toSpec (fermatCubic k) (fermatCubic_isHomogeneous k)

/-- The Fermat cubic curve is its plane curve model: the two are `Proj` of the same ring, graded
by the same pieces, once by submodules and once by additive subgroups. -/
def fermatModelIso : fermatCurve k ≅ fermatModel k :=
  Stacks.Models.PlaneCurveModel.moduleGradingIso (fermatCubic k) (fermatCubic_isHomogeneous k)

/-- **The identification of the Fermat cubic with its plane curve model lies over `Spec k`.** -/
theorem fermatModelIso_hom_toSpec :
    (fermatModelIso k).hom ≫ fermatModelToSpec k = fermatCurveToSpec k := by
  have key : CommRingCat.ofHom (algebraMap k
        ↥(quotientGrading (homogeneousSubmodule (Fin 3) k) (fermatIdeal k) 0)) =
      CommRingCat.ofHom ((GradedRing.projZeroRingHom' (homogeneousSubmodule (Fin 3) k)).comp
          (algebraMap k (MvPolynomial (Fin 3) k))) ≫
        CommRingCat.ofHom
          (quotientMk (homogeneousSubmodule (Fin 3) k) (fermatIdeal k)).gradedZeroRingHom := by
    refine CommRingCat.hom_ext (RingHom.ext fun a => Subtype.ext ?_)
    change algebraMap k (MvPolynomial (Fin 3) k ⧸ (fermatIdeal k).toIdeal) a =
      Ideal.Quotient.mk _ (DirectSum.decompose (homogeneousSubmodule (Fin 3) k)
        (algebraMap k (MvPolynomial (Fin 3) k) a) 0 : MvPolynomial (Fin 3) k)
    rw [DirectSum.decompose_of_mem_same _ (SetLike.algebraMap_mem_graded _ a)]
    rfl
  refine (Stacks.Models.PlaneCurveModel.moduleGradingIso_hom_toSpec _ _).trans ?_
  change Proj.toSpecZero (quotientGrading (homogeneousSubmodule (Fin 3) k) (fermatIdeal k)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k _)) =
    Proj.map (quotientMk (homogeneousSubmodule (Fin 3) k) (fermatIdeal k)) _ ≫
      (Proj.toSpecZero (homogeneousSubmodule (Fin 3) k) ≫
        Spec.map (CommRingCat.ofHom ((GradedRing.projZeroRingHom'
          (homogeneousSubmodule (Fin 3) k)).comp (algebraMap k (MvPolynomial (Fin 3) k)))))
  rw [key, Spec.map_comp, ← Category.assoc, ← Proj.map_toSpecZero, Category.assoc]

/-- The structure morphism of the Fermat cubic through its plane curve model. -/
theorem fermatModelIso_inv_toSpec :
    (fermatModelIso k).inv ≫ fermatCurveToSpec k = fermatModelToSpec k := by
  rw [← fermatModelIso_hom_toSpec, Iso.inv_hom_id_assoc]

/-! ### Global functions -/

/-- The Fermat cubic is nonzero. -/
theorem fermatCubic_ne_zero : fermatCubic k ≠ 0 := fun h =>
  not_X_dvd_fermat k 0 (show (X 0 : MvPolynomial (Fin 3) k) ∣ fermatCubic k by
    rw [h]; exact dvd_zero _)

/-- The coordinate `T₀` does not divide the Fermat cubic. -/
theorem not_X_zero_dvd_fermatCubic : ¬ (X 0 : MvPolynomial (Fin 3) k) ∣ fermatCubic k :=
  not_X_dvd_fermat k 0

/-- The Fermat cubic lies in the degree-three homogeneous submodule. -/
theorem fermatCubic_mem_homogeneousSubmodule :
    fermatCubic k ∈ homogeneousSubmodule (Fin 3) k 3 :=
  (mem_homogeneousSubmodule 3 _).2 (fermatCubic_isHomogeneous k)

/-- The kernel of the embedding of the plane curve model of the Fermat cubic into `ℙ²_k` is the
zero scheme of its equation. -/
theorem ker_embedding_fermatModel :
    (Stacks.Models.PlaneCurveModel.embedding (fermatCubic k)
        (fermatCubic_isHomogeneous k)).ker =
      AlgebraicGeometry.zeroScheme
        (Proj (homogeneousSubmodule (Fin 3) k))
        (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheafModule
          (homogeneousSubmodule (Fin 3) k) ((3 : ℕ) : ℤ))
        (AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection
          (homogeneousSubmodule (Fin 3) k) 3
          ⟨fermatCubic k, fermatCubic_mem_homogeneousSubmodule k⟩) :=
  projectiveSpace_ker_eq_zeroScheme_of_idealOfClosedSubscheme_eq_span k 3
    (Stacks.Models.PlaneCurveModel.embedding (fermatCubic k) (fermatCubic_isHomogeneous k))
    ⟨fermatCubic k, fermatCubic_mem_homogeneousSubmodule k⟩
    (Stacks.Models.PlaneCurveModel.idealOfClosedSubscheme_embedding (fermatCubic k)
      (fermatCubic_isHomogeneous k) 0 (not_X_zero_dvd_fermatCubic k))

/-- **`dim_k H⁰(E, 𝒪_E) = 1`** for the plane curve model of the Fermat cubic, from the sequence
`0 → 𝒪(-3) → 𝒪 → 𝒪_E → 0` on `ℙ²_k`. -/
theorem finrank_structureSheafCohomology_zero_fermatModelToSpec :
    Module.finrank k (structureSheafCohomology (fermatModelToSpec k) 0) = 1 := by
  obtain ⟨e⟩ := nonempty_structureSheafCohomologyIsoTwistCohomologyZero k 2 0 3
    (Stacks.Models.PlaneCurveModel.embedding (fermatCubic k) (fermatCubic_isHomogeneous k))
    ⟨fermatCubic k, fermatCubic_mem_homogeneousSubmodule k⟩ (fermatCubic_ne_zero k)
    (ker_embedding_fermatModel k)
    (isZero_twistCohomology_plane_zero k (by norm_num)) (isZero_twistCohomology_plane_one k _)
  exact (e.toLinearEquiv.trans (twistCohomologyZeroEquivBase k 2)).finrank_eq.trans
    (Module.finrank_self k)

/-- `H⁰ = k` for the plane curve model of the Fermat cubic, in characteristic not three (where it
is nonempty). -/
theorem isIso_globalSections_fermatModel (hk : ringChar k ≠ 3) :
    IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (fermatModelToSpec k).appTop) := by
  obtain ⟨z⟩ := nonempty_fermatCurve hk
  have hne : Nonempty ((⊤ : (fermatModel k).Opens) : Type u) :=
    ⟨⟨(fermatModelIso k).hom z, trivial⟩⟩
  refine Stacks.Models.isIso_constants_of_finrank_globalSections_eq_one (fermatModelToSpec k) ?_
  rw [← finrank_structureSheafCohomology_zero_eq_finrank_globalSections k (fermatModelToSpec k),
    finrank_structureSheafCohomology_zero_fermatModelToSpec k]

/-- **`H⁰(E, 𝒪_E) = k`** for the Fermat cubic, in characteristic not three. -/
theorem isIso_globalSections_fermatCurve (hk : ringChar k ≠ 3) :
    IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (fermatCurveToSpec k).appTop) := by
  have := isIso_globalSections_fermatModel k hk
  have : IsIso (fermatModelIso k).hom.appTop :=
    inferInstanceAs (IsIso ((fermatModelIso k).hom.app ⊤))
  rw [← fermatModelIso_hom_toSpec, Scheme.Hom.comp_appTop, ← Category.assoc]
  exact IsIso.comp_isIso

/-! ### The Fermat cubic is a geometrically integral projective curve -/

/-- **The Fermat cubic is geometrically integral over `k`** (Stacks 0E81) when the characteristic
of `k` is not three: it is smooth and proper of dimension one with `H⁰(E, 𝒪_E) = k`. -/
theorem geometricallyIntegral_fermatCurveToSpec (hk : ringChar k ≠ 3) :
    GeometricallyIntegral (fermatCurveToSpec k) := by
  have h : (Smooth (fermatCurveToSpec k) ∧ topologicalKrullDim (fermatCurve k) = 1 ∧
        IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (fermatCurveToSpec k).appTop)) ↔
      (Smooth (fermatCurveToSpec k) ∧ topologicalKrullDim (fermatCurve k) = 1 ∧
        GeometricallyIntegral (fermatCurveToSpec k)) :=
    (smooth_dimOne_tfae_geometricallyConnected_isCurve_algebraicClosure k
      (fermatCurveToSpec k)).out 1 3
  exact (h.mp ⟨smooth_fermatCurveToSpec_of_three_ne_zero (three_ne_zero_of_ringChar_ne_three hk),
    topologicalKrullDim_fermatCurve k, isIso_globalSections_fermatCurve k hk⟩).2.2

/-- **The Fermat cubic is projective over `k`**: it is a closed subscheme of `ℙ²_k`. -/
theorem isHProjective_fermatCurveToSpec :
    Stacks.HProjective.IsHProjective (fermatCurveToSpec k) := by
  refine ⟨2, fermatEmbedding k ≫ (Stacks.ProjectiveCohomology.projModelIso k 2).hom,
    inferInstance, ?_⟩
  rw [Category.assoc, Stacks.CoefficientProj.projModelIso_hom_structure,
    ← Stacks.ProjectiveCohomology.projToSpecCoeff_eq_projModelToSpec]

/-! ### The Fermat cubic is the fibre of `Y` over the origin -/

/-- The cubic of `Y` at `t = 0` is the Fermat cubic. -/
theorem map_evalZero_cubicEquation :
    MvPolynomial.map (Polynomial.evalRingHom (0 : k)) (cubicEquation k) = fermatCubic k :=
  cubicEquation_map_eval_zero k

/-- The identification of the base change of `V(F)` along `t ↦ 0` with the Fermat cubic. -/
def fermatBaseChangeIso :
    Stacks.Models.PlaneCurveModel.scheme
        (MvPolynomial.map (Polynomial.evalRingHom (0 : k)) (cubicEquation k))
        ((isHomogeneous_cubicEquation k).map _) ≅ fermatCurve k :=
  Stacks.Models.PlaneCurveModel.schemeCongr _ _ (map_evalZero_cubicEquation k) ≪≫
    (fermatModelIso k).symm

/-- **The inclusion of the Fermat cubic into `Y`** as the fibre over the origin. -/
def fermatToCubicSurface : fermatCurve k ⟶ cubicSurface k :=
  (fermatBaseChangeIso k).inv ≫
    Stacks.Models.PlaneCurveModel.mapMap (cubicEquation k) (isHomogeneous_cubicEquation k)
      (Polynomial.evalRingHom (0 : k)) ≫ (cubicSurfaceIso k).inv

/-- **The fibre of `Y ⟶ A¹_k` over the origin is the Fermat cubic.** The square formed by the
inclusion `E ⟶ Y`, the structure morphisms and `Spec k ⟶ A¹_k`, `t ↦ 0`, is cartesian. -/
theorem isPullback_fermatToCubicSurface :
    IsPullback (fermatToCubicSurface k) (fermatCurveToSpec k) (cubicSurfaceToLine k)
      (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k)))) := by
  refine (Stacks.Models.PlaneCurveModel.isPullback_mapMap (cubicEquation k)
    (isHomogeneous_cubicEquation k) (Polynomial.evalRingHom (0 : k))).of_iso
    (fermatBaseChangeIso k) (cubicSurfaceIso k).symm (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp [fermatToCubicSurface]
  · rw [Iso.refl_hom, Category.comp_id, fermatBaseChangeIso, Iso.trans_hom, Iso.symm_hom,
      Category.assoc, fermatModelIso_inv_toSpec,
      Stacks.Models.PlaneCurveModel.schemeCongr_hom_toSpec]
  · rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, cubicSurfaceIso_inv_toLine]
  · simp

/-- The point `Spec k ⟶ A¹_k`, `t ↦ 0`, is the origin. -/
theorem specMap_evalZero_apply (q : Spec (CommRingCat.of k)) :
    Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k))) q = originPoint k := by
  have := q.isPrime
  refine PrimeSpectrum.ext ?_
  change Ideal.comap (Polynomial.evalRingHom (0 : k)) q.asIdeal = Ideal.span {Polynomial.X}
  rw [Ideal.eq_bot_of_prime q.asIdeal, ← RingHom.ker_eq_comap_bot, Polynomial.ker_evalRingHom,
    map_zero, sub_zero]

/-- The image of `Spec k ⟶ A¹_k`, `t ↦ 0`, is the origin. -/
theorem range_specMap_evalZero :
    Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k)))) =
      {originPoint k} := by
  ext p
  simp only [Set.mem_range, Set.mem_singleton_iff]
  constructor
  · rintro ⟨q, rfl⟩
    exact specMap_evalZero_apply k q
  · rintro rfl
    obtain ⟨q⟩ : Nonempty (Spec (CommRingCat.of k)) := inferInstance
    exact ⟨q, specMap_evalZero_apply k q⟩

/-- Every point of the Fermat cubic lies over the origin. -/
theorem cubicSurfaceToLine_fermatToCubicSurface (x : fermatCurve k) :
    cubicSurfaceToLine k (fermatToCubicSurface k x) = originPoint k := by
  rw [← Scheme.Hom.comp_apply, (isPullback_fermatToCubicSurface k).w, Scheme.Hom.comp_apply,
    specMap_evalZero_apply]

/-! ### The Fermat cubic is the scheme-theoretic fibre over the origin -/

/-- The ideal `(t)` of the origin is prime. -/
instance isPrime_originPoint : (originPoint k).asIdeal.IsPrime :=
  (originPoint k).isPrime

/-- Evaluation at `0` kills the ideal `(t)` of the origin. -/
theorem originPoint_le_ker_evalRingHom :
    (originPoint k).asIdeal ≤ RingHom.ker (Polynomial.evalRingHom (0 : k)) := by
  change Ideal.span {Polynomial.X} ≤ _
  rw [Ideal.span_le, Set.singleton_subset_iff]
  simp

/-- Evaluation at `0` sends polynomials outside `(t)` to units. -/
theorem originPoint_primeCompl_le :
    (originPoint k).asIdeal.primeCompl ≤
      (IsUnit.submonoid k).comap (Polynomial.evalRingHom (0 : k)) := by
  intro r hr
  have hr' : ¬ Polynomial.X ∣ r := fun h => hr (Ideal.mem_span_singleton.mpr h)
  rw [Polynomial.X_dvd_iff, Polynomial.coeff_zero_eq_eval_zero] at hr'
  exact isUnit_iff_ne_zero.mpr hr'

/-- Evaluation at `0` as a homomorphism out of the residue field of `k[t]` at `(t)`. -/
def originResidueFieldLift : (originPoint k).asIdeal.ResidueField →+* k :=
  Ideal.ResidueField.lift (originPoint k).asIdeal (Polynomial.evalRingHom (0 : k))
    (originPoint_le_ker_evalRingHom k) (originPoint_primeCompl_le k)

/-- `originResidueFieldLift` is evaluation at `0` on polynomials. -/
theorem originResidueFieldLift_algebraMap (r : Polynomial k) :
    originResidueFieldLift k (algebraMap _ _ r) = Polynomial.evalRingHom (0 : k) r :=
  Ideal.ResidueField.lift_algebraMap _ _ _ _ r

/-- The residue field of `k[t]` at `(t)` is `k`, by evaluation at `0`. -/
def originResidueFieldEquiv : (originPoint k).asIdeal.ResidueField ≃+* k :=
  RingEquiv.ofBijective (originResidueFieldLift k) ⟨RingHom.injective _, fun a =>
    ⟨algebraMap _ _ (Polynomial.C a), by rw [originResidueFieldLift_algebraMap]; simp⟩⟩

/-- The residue field of the affine line at the origin is `k`. -/
def originResidueIso : (affineLine k).residueField (originPoint k) ≅ CommRingCat.of k :=
  Scheme.Spec.residueFieldIso _ _ ≪≫ (originResidueFieldEquiv k).toCommRingCatIso

/-- `Spec k ≅ Spec κ(origin)`. -/
def originSpecIso : Spec (CommRingCat.of k) ≅ Spec ((affineLine k).residueField (originPoint k)) :=
  Scheme.Spec.mapIso (originResidueIso k).op

/-- Under `Spec k ≅ Spec κ(origin)`, the point `t ↦ 0` is the inclusion of the residue field. -/
theorem originSpecIso_hom_fromSpecResidueField :
    (originSpecIso k).hom ≫ (affineLine k).fromSpecResidueField (originPoint k) =
      Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k))) := by
  have h : CommRingCat.ofHom (algebraMap (Polynomial k) (originPoint k).asIdeal.ResidueField) ≫
      (originResidueFieldEquiv k).toCommRingCatIso.hom =
      CommRingCat.ofHom (Polynomial.evalRingHom (0 : k)) := by
    exact CommRingCat.hom_ext (RingHom.ext fun r => originResidueFieldLift_algebraMap k r)
  change Spec.map (Scheme.Spec.residueFieldIso _ _ ≪≫
      (originResidueFieldEquiv k).toCommRingCatIso).hom ≫ _ = _
  rw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField, Iso.trans_hom,
    Spec.map_comp, Category.assoc,
    ← Category.assoc (Spec.map (Scheme.Spec.residueFieldIso _ _).hom), ← Spec.map_comp,
    Iso.inv_hom_id, Spec.map_id, Category.id_comp, ← Spec.map_comp, h]

/-- **The Fermat cubic is the scheme-theoretic fibre of `Y ⟶ A¹_k` over the origin**, as a
cartesian square over `Spec κ(origin) ≅ Spec k`. -/
theorem isPullback_fermatToCubicSurface_fromSpecResidueField :
    IsPullback (fermatToCubicSurface k) (fermatCurveToSpec k ≫ (originSpecIso k).hom)
      (cubicSurfaceToLine k) ((affineLine k).fromSpecResidueField (originPoint k)) :=
  (isPullback_fermatToCubicSurface k).of_iso (Iso.refl _) (Iso.refl _) (originSpecIso k)
    (Iso.refl _) (by simp) (by simp) (by simp)
    (by rw [Iso.refl_hom, Category.comp_id, originSpecIso_hom_fromSpecResidueField])

/-- **The fibre of `Y ⟶ A¹_k` over the origin is the Fermat cubic.** -/
def fermatCurveIsoFiber : fermatCurve k ≅ (cubicSurfaceToLine k).fiber (originPoint k) :=
  (isPullback_fermatToCubicSurface_fromSpecResidueField k).isoPullback

/-- The identification of the fibre with the Fermat cubic is compatible with the inclusions into
`Y`. -/
@[reassoc]
theorem fermatCurveIsoFiber_hom_fiberι :
    (fermatCurveIsoFiber k).hom ≫ (cubicSurfaceToLine k).fiberι (originPoint k) =
      fermatToCubicSurface k :=
  (isPullback_fermatToCubicSurface_fromSpecResidueField k).isoPullback_hom_fst

/-- The identification of the fibre with the Fermat cubic is compatible with the structure
morphisms to `Spec κ(origin) ≅ Spec k`. -/
@[reassoc]
theorem fermatCurveIsoFiber_hom_fiberToSpecResidueField :
    (fermatCurveIsoFiber k).hom ≫ (cubicSurfaceToLine k).fiberToSpecResidueField (originPoint k) =
      fermatCurveToSpec k ≫ (originSpecIso k).hom :=
  (isPullback_fermatToCubicSurface_fromSpecResidueField k).isoPullback_hom_snd

end Stacks.Examples.CurveFamilyNotScheme

end
