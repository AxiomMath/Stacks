module

public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.ProjectiveLine
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.RiemannRoch
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.GenusZeroVanishing
public import StacksFrontier.AlgebraicGeometry.Curves.PlaneCurveGenus
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.SchemeIsoDegree
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.KoszulRegularSmoothCover
public import StacksFrontier.AlgebraicGeometry.ProjChartKernel.Basic
public import StacksFrontier.AlgebraicGeometry.ProjCoherentCohomologyFinite.Basic
public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Smooth
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.AmpleTwistingSheaf
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.CoefficientScalars
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.GlobalFunctions
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceChartRatio.PolynomialModel
public import StacksFrontier.AlgebraicGeometry.PullbackInvertible.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ProperGlobalSections
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.GeometricallyRegularNormal
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.RegularStalk
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleCompare
public import StacksFrontier.RingTheory.IntegrallyClosed.Stability

/-!
# The projective line satisfies the conditions characterizing it

Let `k` be a field and let `X` be a scheme over `k` isomorphic over `k` to the projective line
`𝐏¹_k = Proj k[T₀, T₁]`. This file records that `X` has each of the properties which
[Stacks, Tag 0C6U] lists as equivalent to `X ≅ 𝐏¹_k`: it is smooth and geometrically integral
over `k`, of genus `0`, with `H¹(X, 𝒪_X) = 0`, it carries an invertible module of degree `1`, and
it has a `k`-rational closed point with a normal local ring.

## Main results

* `AlgebraicGeometry.isIso_globalSections_projToSpecCoeff`: `H⁰(𝐏ⁿ_k, 𝒪) = k`.
* `AlgebraicGeometry.invertibleCurveDegree_twistingSheaf_one`: `deg 𝒪_{𝐏¹_k}(1) = 1`.
* `AlgebraicGeometry.isCurve_of_iso_projectiveLine`: a scheme isomorphic to `𝐏¹_k` is a curve.
* `AlgebraicGeometry.smooth_geometricallyIrreducible_genus_odd_of_iso_projectiveLine`,
  `AlgebraicGeometry.geometricallyIntegral_genus_degree_one_of_iso_projectiveLine`,
  `AlgebraicGeometry.isZero_h1_degree_one_of_iso_projectiveLine` and
  `AlgebraicGeometry.isZero_h1_rationalNormalPoint_of_iso_projectiveLine`: the conditions (2),
  (5), (7) and (8) of [Stacks, Tag 0C6U] for a scheme isomorphic to `𝐏¹_k` over `k`.

## Implementation notes

The degree of `𝒪(1)` is read off Riemann-Roch: `H⁰(𝐏¹_k, 𝒪(1))` is the space of linear forms in
`T₀, T₁` and `H¹(𝐏¹_k, 𝒪(1)) = 0` ([Stacks, Tag 01XT]), so `2 - 0 = deg 𝒪(1) + 1 - 0`. Everything
is transported to `X` along the isomorphism: cohomology dimensions by
`AlgebraicGeometry.finrank_cohomologyOverField_pullback` and
`AlgebraicGeometry.finrank_cohomologyOverField_unit_pushforward`, and geometric irreducibility and
integrality through [Stacks, Tag 0FD3] for the smooth, hence geometrically normal, `X`.

## References

* [Stacks Project, Tag 0C6U](https://stacks.math.columbia.edu/tag/0C6U)
* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
* [Stacks Project, Tag 0FD3](https://stacks.math.columbia.edu/tag/0FD3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading projToSpecCoeff)

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry

variable {k : Type u} [Field k]

/-- **`H⁰(𝐏ⁿ_k, 𝒪) = k`**, in the idiom `IsIso ((Γ(Spec k) ≅ k)⁻¹ ≫ appTop)`. -/
theorem isIso_globalSections_projToSpecCoeff (n : ℕ) :
    IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (projToSpecCoeff k n).appTop) :=
  (ConcreteCategory.isIso_iff_bijective _).2
    (Stacks.ProjectiveSpace.Cohomology.bijective_coeffToGlobalSections k n)

/-- **The degree of `𝒪(1)` on the projective line is one.** `H⁰(𝐏¹_k, 𝒪(1))` is the
two-dimensional space of linear forms and `H¹(𝐏¹_k, 𝒪(1)) = 0` ([Stacks, Tag 01XT]); the genus
is zero and `H⁰(𝐏¹_k, 𝒪) = k`, so Riemann-Roch gives `2 - 0 = deg 𝒪(1) + 1`. -/
theorem invertibleCurveDegree_twistingSheaf_one :
    letI := Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff k 1
    invertibleCurveDegree k (projToSpecCoeff k 1)
      (Stacks.ProjectiveSpace.topologicalKrullDim_proj_fin k (r := 2) two_pos).le
      (ProjectiveSpectrum.Proj.twistingSheafModule (polyGrading k 1) 1) = 1 := by
  let := Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff k 1
  have := isIso_globalSections_projToSpecCoeff (k := k) 1
  have hRR := finrank_sub_finrank_eq_invertibleCurveDegree_add_genus k (projToSpecCoeff k 1)
    (Stacks.ProjectiveSpace.topologicalKrullDim_proj_fin k (r := 2) two_pos).le
    (ProjectiveSpectrum.Proj.twistingSheafModule (polyGrading k 1) 1)
  have h0 : Module.finrank k (cohomologyOverField k (projToSpecCoeff k 1)
      (ProjectiveSpectrum.Proj.twistingSheafModule (polyGrading k 1) 1) 0) = 2 := by
    rw [(Stacks.ProjectiveSpace.Cohomology.cohomologyOverFieldIsoRestrictScalarsCoeffScalar k 1
        _ 0).toLinearEquiv.finrank_eq]
    show Module.finrank k (Stacks.ProjectiveSpace.Cohomology.twistCohomology k 1 1 0) = 2
    rw [(Stacks.ProjectiveSpace.Cohomology.twistCohomologyIsoHomogeneous k 1 1
        (by norm_num)).toLinearEquiv.finrank_eq]
    simp [MvPolynomial.finrank_homogeneousSubmodule]
  have h1 : Module.finrank k (cohomologyOverField k (projToSpecCoeff k 1)
      (ProjectiveSpectrum.Proj.twistingSheafModule (polyGrading k 1) 1) 1) = 0 := by
    rw [(Stacks.ProjectiveSpace.Cohomology.cohomologyOverFieldIsoRestrictScalarsCoeffScalar k 1
        _ 1).toLinearEquiv.finrank_eq]
    have hz := Stacks.ProjectiveSpace.Cohomology.isZero_twistCohomology k 1 1 1 (by omega)
    have := ModuleCat.subsingleton_of_isZero hz
    exact Module.finrank_zero_of_subsingleton
  rw [h0, h1, Stacks.Curves.genus_projToSpecCoeff_one] at hRR
  push_cast at hRR
  linarith

variable {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  (e : X ≅ AlgebraicGeometry.Proj (polyGrading k 1)) (he : e.hom ≫ projToSpecCoeff k 1 = f)

include he in
/-- A scheme isomorphic over `k` to `𝐏¹_k` is proper over `k`. -/
theorem isProper_of_iso_projectiveLine : IsProper f := by
  subst he
  have := Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff k 1
  infer_instance

include he in
/-- A scheme isomorphic over `k` to `𝐏¹_k` is smooth over `k`. -/
theorem smooth_of_iso_projectiveLine : Smooth f := by
  subst he
  have := Stacks.AlgebraicGeometry.ProjPolyChart.smooth_projToSpecCoeff k 1
  infer_instance

include he in
/-- A scheme isomorphic over `k` to `𝐏¹_k` has `H⁰(X, 𝒪_X) = k`. -/
theorem isIso_globalSections_of_iso_projectiveLine :
    IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) := by
  subst he
  have := isIso_globalSections_projToSpecCoeff (k := k) 1
  have := Stacks.AlgebraicGeometry.isIso_appTop_of_isIso e.hom
  rw [Scheme.Hom.comp_appTop, ← Category.assoc]
  infer_instance

include e in
/-- A scheme isomorphic to `𝐏¹_k` has dimension one. -/
theorem topologicalKrullDim_of_iso_projectiveLine : topologicalKrullDim X = 1 :=
  (IsHomeomorph.topologicalKrullDim_eq _ e.hom.homeomorph.isHomeomorph).trans
    (Stacks.ProjectiveSpace.topologicalKrullDim_proj_fin k (r := 2) two_pos)

include he in
/-- A scheme isomorphic over `k` to `𝐏¹_k` is a curve over `k`. -/
theorem isCurve_of_iso_projectiveLine : IsCurve k f := by
  have := isProper_of_iso_projectiveLine f e he
  have := Stacks.AlgebraicGeometry.ProjPolyChart.isIntegral_proj k 1
  have : Nonempty X := ⟨e.inv (Nonempty.some inferInstance)⟩
  have : IsIntegral X := isIntegral_of_isOpenImmersion e.hom
  exact (isCurve_iff k f).mpr ⟨{ }, topologicalKrullDim_of_iso_projectiveLine e⟩

include he in
/-- A scheme isomorphic over `k` to `𝐏¹_k` has genus zero. -/
theorem genus_of_iso_projectiveLine : genus f = 0 := by
  subst he
  rw [← finrank_cohomologyOverField_one_unit_eq_genus,
    finrank_cohomologyOverField_unit_pushforward k e.hom,
    finrank_cohomologyOverField_one_unit_eq_genus,
    Stacks.Curves.genus_projToSpecCoeff_one]

include he in
/-- A scheme isomorphic over `k` to `𝐏¹_k` has `H¹(X, 𝒪_X) = 0`. -/
theorem isZero_cohomologyOverField_one_unit_of_iso_projectiveLine :
    IsZero (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) 1) := by
  have := isProper_of_iso_projectiveLine f e he
  exact isZero_cohomologyOverField_unit_one_of_genus_eq_zero k f
    (genus_of_iso_projectiveLine f e he)

include he in
/-- **A scheme isomorphic over `k` to `𝐏¹_k` carries an invertible module of degree one**: the
pullback of `𝒪(1)`. -/
theorem exists_invertibleCurveDegree_eq_one_of_iso_projectiveLine :
    letI := isProper_of_iso_projectiveLine f e he
    ∃ (L : X.Modules) (_ : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L),
      invertibleCurveDegree k f (topologicalKrullDim_of_iso_projectiveLine e).le L = 1 := by
  subst he
  let := Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff k 1
  set O1 := ProjectiveSpectrum.Proj.twistingSheafModule (polyGrading k 1) 1
  have hL : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      ((Scheme.Modules.pullback e.hom).obj O1) :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mp
      (Stacks.Modules.isInvertible_pullback e.hom O1)
  refine ⟨(Scheme.Modules.pullback e.hom).obj O1, hL, ?_⟩
  have key := invertibleCurveDegree_twistingSheaf_one (k := k)
  simp only [invertibleCurveDegree] at key ⊢
  simp only [finrank_cohomologyOverField_pullback k e.hom,
    finrank_cohomologyOverField_unit_pushforward k e.hom]
  exact key

include he in
/-- **Condition (2) of [Stacks, Tag 0C6U] for a scheme isomorphic to `𝐏¹_k`**: smooth and
geometrically irreducible over `k`, of genus `0`, with an invertible module of odd degree. -/
theorem smooth_geometricallyIrreducible_genus_odd_of_iso_projectiveLine :
    letI := isProper_of_iso_projectiveLine f e he
    Smooth f ∧ GeometricallyIrreducible f ∧ genus f = 0 ∧
      ∃ (L : X.Modules) (_ : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L),
        Odd (invertibleCurveDegree k f (topologicalKrullDim_of_iso_projectiveLine e).le L) := by
  let := isProper_of_iso_projectiveLine f e he
  have := smooth_of_iso_projectiveLine f e he
  have := isIso_globalSections_of_iso_projectiveLine f e he
  obtain ⟨L, hL, hdeg⟩ := exists_invertibleCurveDegree_eq_one_of_iso_projectiveLine f e he
  refine ⟨inferInstance, ?_, genus_of_iso_projectiveLine f e he, L, hL, ?_⟩
  · exact ((isIso_globalSections_tfae_geometricallyConnected_irreducible_integral k f
      (isGeometricallyNormal_of_smooth f)).out 1 3).mp
        (isIso_globalSections_of_iso_projectiveLine f e he)
  · rw [hdeg]; exact odd_one

include he in
/-- **Condition (5) of [Stacks, Tag 0C6U] for a scheme isomorphic to `𝐏¹_k`**: geometrically
integral over `k`, of genus `0`, with an invertible module of degree `1`. -/
theorem geometricallyIntegral_genus_degree_one_of_iso_projectiveLine :
    letI := isProper_of_iso_projectiveLine f e he
    GeometricallyIntegral f ∧ genus f = 0 ∧
      ∃ (L : X.Modules) (_ : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L),
        invertibleCurveDegree k f (topologicalKrullDim_of_iso_projectiveLine e).le L = 1 := by
  let := isProper_of_iso_projectiveLine f e he
  have := smooth_of_iso_projectiveLine f e he
  have := isIso_globalSections_of_iso_projectiveLine f e he
  refine ⟨?_, genus_of_iso_projectiveLine f e he,
    exists_invertibleCurveDegree_eq_one_of_iso_projectiveLine f e he⟩
  exact ((isIso_globalSections_tfae_geometricallyConnected_irreducible_integral k f
    (isGeometricallyNormal_of_smooth f)).out 1 4).mp
      (isIso_globalSections_of_iso_projectiveLine f e he)

include he in
/-- **Condition (7) of [Stacks, Tag 0C6U] for a scheme isomorphic to `𝐏¹_k`**: `H¹(X, 𝒪_X) = 0`
and an invertible module of degree `1`. -/
theorem isZero_h1_degree_one_of_iso_projectiveLine :
    letI := isProper_of_iso_projectiveLine f e he
    IsZero (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) 1) ∧
      ∃ (L : X.Modules) (_ : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L),
        invertibleCurveDegree k f (topologicalKrullDim_of_iso_projectiveLine e).le L = 1 :=
  ⟨isZero_cohomologyOverField_one_unit_of_iso_projectiveLine f e he,
    exists_invertibleCurveDegree_eq_one_of_iso_projectiveLine f e he⟩

/-- **A section of a separated scheme over `k` gives a closed point with residue field `k`.** For
`σ : Spec k ⟶ X` with `σ ≫ f = 𝟙`, the image of the point is closed and its residue field has
degree one over `k`. -/
theorem isClosed_and_finrank_residueField_of_section [IsSeparated f]
    (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ f = 𝟙 _) (p : Spec (.of k)) :
    letI : Algebra k (X.residueField (σ p)) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation (σ p)).hom.toAlgebra
    IsClosed ({σ p} : Set X) ∧ Module.finrank k (X.residueField (σ p)) = 1 := by
  let : Algebra k (X.residueField (σ p)) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation (σ p)).hom.toAlgebra
  have : IsClosedImmersion (σ ≫ f) := by rw [hσ]; infer_instance
  have : IsClosedImmersion σ := IsClosedImmersion.of_comp σ f
  refine ⟨?_, ?_⟩
  · have hr : Set.range σ = {σ p} := by
      ext y
      refine ⟨?_, fun hy => ⟨p, hy.symm⟩⟩
      rintro ⟨q, rfl⟩
      rw [Subsingleton.elim q p]
      rfl
    rw [← hr]
    exact σ.isClosedEmbedding.isClosed_range
  · -- `c ↦ c(p)` is surjective onto `κ(p)`, and it factors through `κ(σ p)`
    have hSpec : Function.Surjective (fun c : k =>
        (Spec (.of k)).Γevaluation p ((Scheme.ΓSpecIso (.of k)).inv.hom c)) := by
      have hmax : p.asIdeal.IsMaximal := by
        have := p.isPrime
        rw [show p.asIdeal = ⊥ from Ideal.eq_bot_of_prime _]; exact Ideal.bot_isMaximal
      intro y
      obtain ⟨c, hc⟩ := Ideal.algebraMap_residueField_surjective p.asIdeal
        ((Scheme.Spec.residueFieldIso (.of k) p).hom y)
      refine ⟨c, ?_⟩
      have h := ConcreteCategory.congr_hom (Scheme.Spec.algebraMap_residueFieldIso_inv (.of k) p) c
      change (Scheme.Spec.residueFieldIso (.of k) p).inv (algebraMap k _ c) = _ at h
      rw [hc, Iso.hom_inv_id_apply] at h
      exact h.symm
    have hnat : ∀ c : k, (σ.residueFieldMap p).hom (algebraMap k (X.residueField (σ p)) c) =
        (Spec (.of k)).Γevaluation p ((Scheme.ΓSpecIso (.of k)).inv.hom c) := by
      intro c
      rw [RingHom.algebraMap_toAlgebra]
      simp only [CommRingCat.hom_comp, RingHom.comp_apply]
      have hid : ∀ a, σ.appTop.hom (f.appTop.hom a) = a := fun a => by
        have := ConcreteCategory.congr_hom (Scheme.Hom.comp_appTop σ f) a
        rw [hσ, Scheme.Hom.id_appTop] at this
        exact this.symm
      rw [Scheme.Γevaluation_naturality_apply (f := σ) p, hid]
    have hsurj : Function.Surjective (algebraMap k (X.residueField (σ p))) := by
      intro y
      obtain ⟨c, hc⟩ := hSpec ((σ.residueFieldMap p).hom y)
      refine ⟨c, (σ.residueFieldMap p).hom.injective ?_⟩
      rw [hnat]; exact hc
    have e' : k ≃ₐ[k] X.residueField (σ p) :=
      AlgEquiv.ofBijective (Algebra.ofId k _) ⟨(algebraMap k _).injective, hsurj⟩
    rw [← e'.toLinearEquiv.finrank_eq, Module.finrank_self]

/-- The coordinates `(1, 0)` span the unit ideal. -/
theorem span_range_one_zero :
    Ideal.span (Set.range (![1, 0] : Fin 2 → Γ(Spec (.of k), ⊤))) = ⊤ := by
  rw [Ideal.eq_top_iff_one]; exact Ideal.subset_span ⟨0, by simp⟩

/-- **A `k`-point of the projective line.** The point `(1 : 0)`, as a section of the structure
morphism. -/
def projectiveLinePoint : Spec (.of k) ⟶ AlgebraicGeometry.Proj (polyGrading k 1) :=
  AlgebraicGeometry.Proj.fromOfGlobalSections (polyGrading k 1)
    (MvPolynomial.eval₂Hom (Scheme.ΓSpecIso (.of k)).inv.hom ![1, 0])
    (Stacks.ProjectiveSpaceChartRatio.map_irrelevant_eval₂Hom_eq_top _ _ span_range_one_zero)

/-- The point `(1 : 0)` lies over `Spec k`. -/
theorem projectiveLinePoint_comp_projToSpecCoeff :
    projectiveLinePoint (k := k) ≫ projToSpecCoeff k 1 = 𝟙 _ := by
  rw [projectiveLinePoint,
    Stacks.ProjectiveSpaceChartRatio.fromOfGlobalSections_comp_projToSpecCoeff _ _
      span_range_one_zero,
    CommRingCat.ofHom_hom, toSpecΓ_SpecMap_ΓSpecIso_inv]

include he in
/-- **Condition (8) of [Stacks, Tag 0C6U] for a scheme isomorphic to `𝐏¹_k`**: `H¹(X, 𝒪_X) = 0`,
and finitely many closed points with normal local rings whose residue degrees over `k` have
greatest common divisor `1` — here a single `k`-rational point. -/
theorem isZero_h1_rationalNormalPoint_of_iso_projectiveLine :
    IsZero (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) 1) ∧
      ∃ (n : ℕ) (x : Fin n → X), (∀ i, IsClosed ({x i} : Set X)) ∧
        (∀ i, IsIntegrallyClosed (X.presheaf.stalk (x i))) ∧
        Finset.univ.gcd (fun i => letI : Algebra k (X.residueField (x i)) :=
          ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation (x i)).hom.toAlgebra
          Module.finrank k (X.residueField (x i))) = 1 := by
  have := isProper_of_iso_projectiveLine f e he
  have := smooth_of_iso_projectiveLine f e he
  refine ⟨isZero_cohomologyOverField_one_unit_of_iso_projectiveLine f e he, ?_⟩
  set σ : Spec (.of k) ⟶ X := projectiveLinePoint ≫ e.inv with hσdef
  have hσ : σ ≫ f = 𝟙 _ := by
    rw [hσdef, ← he, Category.assoc, e.inv_hom_id_assoc, projectiveLinePoint_comp_projToSpecCoeff]
  obtain ⟨p⟩ : Nonempty (Spec (.of k)) := inferInstance
  obtain ⟨hcl, hdeg⟩ := isClosed_and_finrank_residueField_of_section f σ hσ p
  refine ⟨1, fun _ => σ p, fun _ => hcl, fun _ => ?_, ?_⟩
  · have := isRegularLocalRing_stalk_of_smooth_over_field f (σ p)
    exact isIntegrallyClosed_of_isRegularLocalRing _
  · simp only [Finset.univ_unique, Finset.gcd_singleton]
    rw [hdeg]
    rfl

end AlgebraicGeometry

end
