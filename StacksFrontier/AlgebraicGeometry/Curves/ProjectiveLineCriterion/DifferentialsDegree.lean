module

public import StacksFrontier.AlgebraicGeometry.CurveDegreeDeterminant
public import StacksFrontier.AlgebraicGeometry.DeRham.ProjectiveSpaceHodgeCohomology
public import StacksFrontier.AlgebraicGeometry.DeRham.SchemeComplex
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.ModuleFacts
public import StacksFrontier.AlgebraicGeometry.F6Rank136.SmoothIsNodal
public import StacksFrontier.AlgebraicGeometry.ProjCoherentCohomologyFinite.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.SmoothOfRelativeDimension
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.CoefficientScalars
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Degree
public import StacksFrontier.AlgebraicGeometry.Curves.NodalUnramifiedSingularSubscheme
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingTwistSectionCount
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Equidimensional
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertSchemeSmoothness
public import StacksFrontier.AlgebraicGeometry.ProjBaseChange.IsIso
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.SmoothRelativeDimension
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.InvertibleDegreeFieldExtension

/-!
# The degree of the sheaf of differentials of a form of the projective line

Let `X` be a proper scheme over a field `k` which is smooth of relative dimension one. Its sheaf
of relative differentials `Ω_{X/k}` is invertible, its formation commutes with extension of the
ground field, and the degree of an invertible module does not change under extension of the
ground field. On the projective line `𝐏¹_k` the sheaf `Ω` has `H⁰ = 0` and `H¹ = k`, while `𝒪`
has `H⁰ = k` and `H¹ = 0`, so `deg Ω_{𝐏¹_k/k} = -2`. Consequently, if `X_K ≅ 𝐏¹_K` over `K` for
some extension `K/k`, then `deg Ω_{X/k} = -2`, and `X` carries invertible modules of degree `-2`
and `2`. This replaces the dualizing sheaf in the source's construction of an invertible module
of degree `2` on a curve of genus zero ([Stacks, Tag 0C6U]): for a smooth curve over a field the
dualizing sheaf is `Ω_{X/k}`.

## Main results

All in the namespace `AlgebraicGeometry.ProjectiveLineCriterion`:

* `isInvertible_relativeDifferentials`: `Ω_{X/S}` is invertible for a morphism smooth of relative
  dimension one.
* `invertibleCurveDegree_relativeDifferentials_projToSpecCoeff` and
  `invertibleCurveDegree_relativeDifferentials_projectiveLine`: `deg Ω_{𝐏¹_k/k} = -2`, on the
  polynomial model `Proj k[T₀, T₁]` and on `projectiveSpaceOver 1 (Spec k)`.
* `invertibleCurveDegree_relativeDifferentials_baseChange`: `deg Ω_{X_{k'}/k'} = deg Ω_{X/k}`.
* `invertibleCurveDegree_relativeDifferentials_eq_neg_two_of_iso`: if `X ≅ 𝐏¹_k` over `k` then
  `deg Ω_{X/k} = -2`.
* `invertibleCurveDegree_relativeDifferentials_eq_neg_two`: if `X_K ≅ 𝐏¹_K` over `K` then
  `deg Ω_{X/k} = -2`.
* `exists_invertible_degree_neg_two_and_two`: a smooth proper curve over `k` with `X_K ≅ 𝐏¹_K`
  has invertible modules of degrees `-2` and `2`.

## Implementation notes

The cohomology of `Ω` and `𝒪` on `𝐏¹_k` is read off the twisted Hodge cohomology of projective
space ([Stacks, Tag 0FUK]) through `Ω ≅ Ω¹` and `𝒪 ≅ Ω⁰`. Base change of differentials is
[Stacks, Tag 01V0] (`AlgebraicGeometry.Scheme.Hom.isIso_relativeDifferentialsMap_of_isPullback`)
and invariance of the degree is [Stacks, Tag 0B59]
(`AlgebraicGeometry.invertibleCurveDegree_baseChange_field`). The degree of the inverse is
[Stacks, Tag 0AYX] through
`AlgebraicGeometry.invertibleCurveDegree_tensorPowerModule_neg_one_of_topologicalKrullDim_le_one`.

## References

* [Stacks Project, Tag 0C6U](https://stacks.math.columbia.edu/tag/0C6U)
* [Stacks Project, Tag 0FUK](https://stacks.math.columbia.edu/tag/0FUK)
* [Stacks Project, Tag 01V0](https://stacks.math.columbia.edu/tag/01V0)
* [Stacks Project, Tag 0B59](https://stacks.math.columbia.edu/tag/0B59)
* [Stacks Project, Tag 02G1](https://stacks.math.columbia.edu/tag/02G1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading projToSpecCoeff)

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.ProjectiveLineCriterion

open Stacks.AlgebraicGeometry.ProjectiveSpaceHodge in
/-- On the polynomial model `𝐏¹_k = Proj k[T₀, T₁]`, `dim_k Hⁿ(𝐏¹_k, Ωᵖ)` is `1` when `n = p` and
`0` otherwise, for `p ≤ 1`. -/
theorem finrank_cohomologyOverField_forms (k : Type u) [Field k] (p : ℕ) (hp : p ≤ 1) (n : ℕ) :
    Module.finrank k (cohomologyOverField k (projToSpecCoeff k 1) (forms k 0 p) n) =
      if n = p then 1 else 0 := by
  rw [(Stacks.ProjectiveSpace.Cohomology.cohomologyOverFieldIsoRestrictScalarsCoeffScalar
    k 1 (forms k 0 p) n).toLinearEquiv.finrank_eq]
  split_ifs with h
  · subst h
    obtain ⟨e'⟩ := nonempty_hodgeCohomology_diag_iso (A := k) (m := 0) n hp
    exact e'.toLinearEquiv.finrank_eq.trans (Module.finrank_self k)
  · have := ModuleCat.subsingleton_of_isZero
      (isZero_hodgeCohomology (A := k) (m := 0) p n (fun h' => h h'.1.symm))
    exact Module.finrank_zero_of_subsingleton

/-- **The sheaf of relative differentials of a morphism smooth of relative dimension one is
invertible**: it is finite locally free of rank one (Tag 02G1), and a module of rank one is
invertible (Tag 0B8M). -/
instance isInvertible_relativeDifferentials {X S : Scheme.{u}} (f : X ⟶ S)
    [SmoothOfRelativeDimension 1 f] :
    SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (Scheme.Hom.relativeDifferentials f) :=
  have := Scheme.Hom.isFiniteLocallyFreeOfRank_one_relativeDifferentials f
  Stacks.Chow.GenuineChern.isInvertible_of_isFiniteLocallyFreeOfRank_one _

/-- The `n`-th dimension of the cohomology of `𝒪` on `𝐏¹_k = Proj k[T₀, T₁]` is `1` for `n = 0`
and `0` otherwise. -/
theorem finrank_cohomologyOverField_unit_projToSpecCoeff (k : Type u) [Field k] (n : ℕ) :
    Module.finrank k (cohomologyOverField k (projToSpecCoeff k 1)
      (SheafOfModules.unit (Proj (polyGrading k 1)).ringCatSheaf) n) = if n = 0 then 1 else 0 := by
  rw [← finrank_cohomologyOverField_eq_of_iso k (projToSpecCoeff k 1)
    (Scheme.Hom.relativeDifferentialFormsZeroIso (projToSpecCoeff k 1)) n]
  exact finrank_cohomologyOverField_forms k 0 zero_le_one n

/-- The `n`-th dimension of the cohomology of `Ω_{𝐏¹_k/k}` on `𝐏¹_k = Proj k[T₀, T₁]` is `1` for
`n = 1` and `0` otherwise. -/
theorem finrank_cohomologyOverField_relativeDifferentials_projToSpecCoeff (k : Type u) [Field k]
    (n : ℕ) :
    Module.finrank k (cohomologyOverField k (projToSpecCoeff k 1)
      (Scheme.Hom.relativeDifferentials (projToSpecCoeff k 1)) n) = if n = 1 then 1 else 0 := by
  rw [← finrank_cohomologyOverField_eq_of_iso k (projToSpecCoeff k 1)
    (Scheme.Modules.exteriorPowerOneIsoSelf
      (Scheme.Hom.relativeDifferentials (projToSpecCoeff k 1))) n]
  exact finrank_cohomologyOverField_forms k 1 le_rfl n

/-- An alternating sum with a single nonzero dimension, in degree `p`. -/
theorem finsum_neg_one_pow_mul_ite (p : ℕ) :
    (∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (((if n = p then 1 else 0 : ℕ)) : ℤ)) = (-1) ^ p := by
  rw [finsum_eq_single _ p (fun n hn => by simp [hn])]
  simp

/-- **The sheaf of differentials of `𝐏¹_k = Proj k[T₀, T₁]` over `k` has degree `-2`**:
`H⁰(𝐏¹, Ω) = 0` and `H¹(𝐏¹, Ω) = k` by Tag 0FUK, while `H⁰(𝐏¹, 𝒪) = k` and `H¹(𝐏¹, 𝒪) = 0`. -/
theorem invertibleCurveDegree_relativeDifferentials_projToSpecCoeff (k : Type u) [Field k]
    (hdim : topologicalKrullDim (Proj (polyGrading k 1)) ≤ 1) :
    haveI := Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff k 1
    haveI := Stacks.AlgebraicGeometry.ProjPolyChart.smoothOfRelativeDimension_projToSpecCoeff k 1
    invertibleCurveDegree k (projToSpecCoeff k 1) hdim
      (Scheme.Hom.relativeDifferentials (projToSpecCoeff k 1)) = -2 := by
  unfold invertibleCurveDegree
  simp_rw [finrank_cohomologyOverField_relativeDifferentials_projToSpecCoeff,
    finrank_cohomologyOverField_unit_projToSpecCoeff, finsum_neg_one_pow_mul_ite]
  norm_num

/-- **The degree of the sheaf of differentials is invariant under extension of the ground
field.** For a cartesian square `X' = X ×_k k'` with `X` proper and smooth of relative dimension
one over `k`, the degree of `Ω_{X'/k'}` over `k'` is the degree of `Ω_{X/k}` over `k`: the
differentials of `X'` are the inverse image of those of `X` (Tag 01V0), and the degree of an
invertible module does not change under extension of the ground field (Tag 0B59). -/
theorem invertibleCurveDegree_relativeDifferentials_baseChange (k k' : Type u) [Field k]
    [Field k'] [Algebra k k'] {X' X : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Spec (.of k')}
    {f : X ⟶ Spec (.of k)} (h : IsPullback g' f' f (Spec.map (CommRingCat.ofHom (algebraMap k k'))))
    [IsProper f] [IsProper f'] [SmoothOfRelativeDimension 1 f] [SmoothOfRelativeDimension 1 f']
    (hdim : topologicalKrullDim X ≤ 1) (hdim' : topologicalKrullDim X' ≤ 1) :
    invertibleCurveDegree k' f' hdim' (Scheme.Hom.relativeDifferentials f') =
      invertibleCurveDegree k f hdim (Scheme.Hom.relativeDifferentials f) := by
  have := Scheme.Hom.isIso_relativeDifferentialsMap_of_isPullback g' f' f _ h
  have : SheafOfModules.IsInvertible X'.presheaf X'.ringCatSheaf.2
      ((Scheme.Modules.pullback g').obj (Scheme.Hom.relativeDifferentials f)) :=
    Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry g'.toLRSHom.toShHom _
      inferInstance
  rw [← invertibleCurveDegree_eq_of_iso k' f' hdim'
    (asIso (Scheme.Hom.relativeDifferentialsMap g' f f' _ h.w))]
  exact invertibleCurveDegree_baseChange_field k k' g' f' f h hdim _

/-- **The degree of the sheaf of differentials is invariant under isomorphism over the field.** -/
theorem invertibleCurveDegree_relativeDifferentials_of_iso (k : Type u) [Field k]
    {X Y : Scheme.{u}} {f : X ⟶ Spec (.of k)} {g : Y ⟶ Spec (.of k)} (e : X ⟶ Y) [IsIso e]
    (w : e ≫ g = f) [IsProper f] [IsProper g] [SmoothOfRelativeDimension 1 f]
    [SmoothOfRelativeDimension 1 g] (hdimX : topologicalKrullDim X ≤ 1)
    (hdimY : topologicalKrullDim Y ≤ 1) :
    invertibleCurveDegree k f hdimX (Scheme.Hom.relativeDifferentials f) =
      invertibleCurveDegree k g hdimY (Scheme.Hom.relativeDifferentials g) := by
  have h : IsPullback e f g (Spec.map (CommRingCat.ofHom (algebraMap k k))) := by
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
    exact IsPullback.of_horiz_isIso ⟨by rw [w, Category.comp_id]⟩
  exact invertibleCurveDegree_relativeDifferentials_baseChange k k h hdimY hdimX

/-- **A scheme isomorphic over `k` to the projective line has differentials of degree `-2`.**
If `X ≅ 𝐏¹_k` over `k`, then `deg Ω_{X/k} = -2`. -/
theorem invertibleCurveDegree_relativeDifferentials_eq_neg_two_of_iso (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    (hdim : topologicalKrullDim X ≤ 1)
    (e : Over.mk f ≅ Over.mk (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k))) :
    invertibleCurveDegree k f hdim (Scheme.Hom.relativeDifferentials f) = -2 := by
  have := Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff k 1
  have := Stacks.AlgebraicGeometry.ProjPolyChart.smoothOfRelativeDimension_projToSpecCoeff k 1
  let φ : X ⟶ Proj (polyGrading k 1) :=
    e.hom.left ≫ (Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison k 1).iso.hom
  have : IsIso φ := inferInstance
  have hw : φ ≫ projToSpecCoeff k 1 = f := by
    have h2 := Over.w e.hom
    simp only [Over.mk_hom] at h2
    simp only [φ, Category.assoc]
    exact (congrArg (e.hom.left ≫ ·)
      (Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison k 1).toBase).trans h2
  have hdimP : topologicalKrullDim (Proj (polyGrading k 1)) ≤ 1 := by
    rwa [← IsHomeomorph.topologicalKrullDim_eq φ (Scheme.homeoOfIso (asIso φ)).isHomeomorph]
  rw [invertibleCurveDegree_relativeDifferentials_of_iso k φ hw hdim hdimP]
  exact invertibleCurveDegree_relativeDifferentials_projToSpecCoeff k hdimP

/-- **The sheaf of differentials of the projective line `𝐏¹_k` over `k` has degree `-2`.** -/
theorem invertibleCurveDegree_relativeDifferentials_projectiveLine (k : Type u) [Field k]
    (hdim : topologicalKrullDim (projectiveSpaceOver 1 (Spec (.of k))) ≤ 1) :
    invertibleCurveDegree k (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k)) hdim
      (Scheme.Hom.relativeDifferentials (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k))) =
      -2 :=
  invertibleCurveDegree_relativeDifferentials_eq_neg_two_of_iso k _ hdim (Iso.refl _)

/-- **A smooth proper curve which becomes the projective line after a field extension has
differentials of degree `-2`.** Let `X` be proper and smooth of relative dimension one over `k`
and let `K/k` be a field extension with `X_K ≅ 𝐏¹_K` over `K`. Then `deg Ω_{X/k} = -2`. -/
theorem invertibleCurveDegree_relativeDifferentials_eq_neg_two (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    (hdim : topologicalKrullDim X ≤ 1) (K : Type u) [Field K] [Algebra k K]
    (e : Over.mk (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) ≅
      Over.mk (projectiveSpaceOver 1 (Spec (.of K)) ↘ Spec (.of K))) :
    invertibleCurveDegree k f hdim (Scheme.Hom.relativeDifferentials f) = -2 := by
  have h := IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  have : IsProper (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :=
    MorphismProperty.of_isPullback (P := @IsProper) h inferInstance
  have : SmoothOfRelativeDimension 1
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback h inferInstance
  have hdim' := (topologicalKrullDim_baseChange k K _ _ f h).trans_le hdim
  rw [← invertibleCurveDegree_relativeDifferentials_baseChange k K h hdim hdim']
  exact invertibleCurveDegree_relativeDifferentials_eq_neg_two_of_iso K _ hdim' e

/-- **A smooth proper curve which becomes the projective line after a field extension has
invertible modules of degrees `-2` and `2`.** Let `X` be a smooth proper curve over `k` and let
`K/k` be a field extension with `X_K ≅ 𝐏¹_K` over `K`. Then `Ω_{X/k}` is an invertible module of
degree `-2`, and its inverse is an invertible module of degree `2`. -/
theorem exists_invertible_degree_neg_two_and_two (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsCurve k f] [Smooth f] [IsProper f] (K : Type u) [Field K]
    [Algebra k K]
    (e : Over.mk (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) ≅
      Over.mk (projectiveSpaceOver 1 (Spec (.of K)) ↘ Spec (.of K))) :
    (∃ (L : X.Modules) (_ : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L),
      invertibleCurveDegree k f (IsCurve.topologicalKrullDim_eq_one (k := k) (f := f)).le L = -2) ∧
    (∃ (L : X.Modules) (_ : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L),
      invertibleCurveDegree k f (IsCurve.topologicalKrullDim_eq_one (k := k) (f := f)).le L =
        2) := by
  have := smoothOfRelativeDimension_one_of_isCurve k f
  have hdim := (IsCurve.topologicalKrullDim_eq_one (k := k) (f := f)).le
  have hΩ := invertibleCurveDegree_relativeDifferentials_eq_neg_two k f hdim K e
  refine ⟨⟨_, inferInstance, hΩ⟩, ⟨_, _,
    (invertibleCurveDegree_tensorPowerModule_neg_one_of_topologicalKrullDim_le_one k f hdim
      (Scheme.Hom.relativeDifferentials f)).trans ?_⟩⟩
  rw [hΩ]
  norm_num

end AlgebraicGeometry.ProjectiveLineCriterion

end
