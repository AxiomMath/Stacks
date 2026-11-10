module

public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.SmoothCurveDifferentials
public import StacksFrontier.AlgebraicGeometry.Curves.NodalVectorFieldsVanishing
public import StacksFrontier.AlgebraicGeometry.Curves.SmoothVectorFields
public import StacksFrontier.AlgebraicGeometry.UnitsNormalProper.GlobalSections
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.SmoothRelativeDimension

/-!
# Vector fields on curves of genus at least two

On a smooth proper curve `X` of genus `g` over an algebraically closed field `k`, the fixed points
of a nonzero vector field lie in the support of the cokernel of `θ : Ω_{X/k} ⟶ 𝒪_X`, which has at
most `-deg(Ω_{X/k}) = 2 - 2g` points ([Stacks, Tag 0C1A]). This bounds the vector fields by the
genus, on smooth curves and, through the normalization, on nodal curves.

## Main results

* `Stacks.Curves.SheafDerivation.smoothCurve_genus_cases` ([Stacks, Tag 0E67]): on a smooth
  proper curve of genus `g` over an algebraically closed field, there are no nonzero vector fields
  if `g ≥ 2`, a nonzero one fixes no closed point if `g = 1`, and at most two if `g = 0`.
* `Stacks.Curves.SheafDerivation.eq_zero_of_hasAtWorstNodalSingularities`
  ([Stacks, Tag 0E69]): `Der_k(𝒪_X, 𝒪_X) = 0` on an at-worst-nodal proper connected curve of
  genus at least two without rational tails or rational bridges.

## References

* [Stacks Project, Tag 0E67](https://stacks.math.columbia.edu/tag/0E67)
* [Stacks Project, Tag 0E69](https://stacks.math.columbia.edu/tag/0E69)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry

universe u

namespace Stacks.Curves

section SmoothCurve

variable {k : Type u} [Field k]

/-- The degree of the sheaf of differentials of a smooth proper curve over `k` is `2g - 2`
([Stacks, Tag 0C1A]). -/
private theorem invertibleCurveDegree_relativeDifferentials_eq {k : Type u} [Field k]
    [IsAlgClosed k] {Y : Scheme.{u}} (q : Y ⟶ Spec (.of k)) [IsCurve k q] [Smooth q]
    [IsProper q] :
    invertibleCurveDegree k q (topologicalKrullDim_le_one_of_isCurve q)
      (Scheme.Hom.relativeDifferentials q) = 2 * (genus q : ℤ) - 2 := by
  have : IsProperVariety k q := ⟨⟩
  have : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ q.appTop) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (Stacks.AlgebraicGeometry.UnitsNormalProper.bijective_structMap k q)
  let := AlgebraicGeometry.smoothOfRelativeDimension_one_of_isCurve k q
  let := Scheme.Hom.isFiniteLocallyFreeOfRank_one_relativeDifferentials q
  rw [invertibleCurveDegree_eq_curveDegree]
  exact curveDegree_relativeDifferentials_eq_two_mul_genus_sub_two q

/-- **[Stacks, Tag 0E67]**: let `X` be a smooth proper curve of genus `g` over an algebraically
closed field `k` (a curve is integral, so connected). If `g ≥ 2` then `Der_k(𝒪_X, 𝒪_X) = 0`; if
`g = 1` a nonzero vector field fixes no closed point; if `g = 0` a nonzero vector field fixes at
most two closed points. -/
@[stacks 0E67]
theorem SheafDerivation.smoothCurve_genus_cases [IsAlgClosed k] (X : Scheme.{u})
    [X.Over (Spec (.of k))] [IsCurve k (X ↘ Spec (.of k))] [Smooth (X ↘ Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))] :
    (2 ≤ genus (X ↘ Spec (.of k)) → ∀ D : SheafDerivation k X, D = 0) ∧
    (genus (X ↘ Spec (.of k)) = 1 → ∀ D : SheafDerivation k X, D ≠ 0 →
      ∀ (x : X) (hx : IsClosed ({x} : Set X)), ¬ D.Fixes x hx) ∧
    (genus (X ↘ Spec (.of k)) = 0 → ∀ D : SheafDerivation k X, D ≠ 0 →
      {x : X | ∃ hx : IsClosed ({x} : Set X), D.Fixes x hx}.encard ≤ 2) := by
  have hdeg := invertibleCurveDegree_relativeDifferentials_eq (k := k) (X ↘ Spec (.of k))
  refine ⟨fun hg D => ?_, fun hg D hD x hx hfix => ?_, fun hg D hD => ?_⟩
  · by_contra hD
    have h := (SheafDerivationOf.encard_setOf_fixes_le (D := D) hD).1
    rw [hdeg] at h
    omega
  · have h := (SheafDerivationOf.encard_setOf_fixes_le (D := D) hD).2
    rw [hdeg, hg] at h
    have h0 : {x : X | ∃ hx : IsClosed ({x} : Set X), D.Fixes x hx}.encard = 0 :=
      nonpos_iff_eq_zero.mp (h.trans (by norm_num))
    exact Set.eq_empty_iff_forall_notMem.mp (Set.encard_eq_zero.mp h0) x ⟨hx, hfix⟩
  · have h := (SheafDerivationOf.encard_setOf_fixes_le (D := D) hD).2
    rw [hdeg, hg] at h
    exact h

end SmoothCurve

/-- **[Stacks, Tag 0E69]**: let `X` be an at-worst-nodal, proper, connected, one-dimensional
scheme over an algebraically closed field `k`, of genus at least two, with no rational tails and
no rational bridges. Then `Der_k(𝒪_X, 𝒪_X) = 0`. -/
@[stacks 0E69]
theorem SheafDerivation.eq_zero_of_hasAtWorstNodalSingularities (k : Type u) [Field k]
    [IsAlgClosed k] (X : Scheme.{u}) [X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
    [ConnectedSpace X] (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X) (hg : 2 ≤ genus (X ↘ Spec (.of k)))
    (htail : ∀ C : X.IdealSheafData, ¬ IsRationalTail k X C)
    (hbridge : ∀ C : X.IdealSheafData, ¬ IsRationalBridge k X C) (D : SheafDerivation k X) :
    D = 0 := by
  have : IsReduced X := isReduced_of_hasAtWorstNodalSingularities k X hnodal
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : IsNoetherian X := ⟨⟩
  have hequi : TopologicalSpace.Equidimensional X :=
    equidimensional_of_connectedSpace_of_topologicalKrullDim_eq_one hdim
  obtain ⟨e, he, h⟩ := exists_restrictOpens_fixes_and_eq_zero (k := k) hdim hnodal
  obtain ⟨D', hfix, hzero⟩ := h D
  refine hzero fun Z => ?_
  by_contra hE
  set fC := componentStructure (k := k) Z
  have : IsCurve k fC := isCurve_componentStructure hequi hdim Z
  have hstr : (Limits.Sigma.ι _ Z ≫ e.hom) ≫ normalizationOverField k (X ↘ Spec (.of k)) ≫
      (X ↘ Spec (.of k)) = normalizationOverField k fC ≫ fC := by
    rw [show (Limits.Sigma.ι _ Z ≫ e.hom) ≫ normalizationOverField k (X ↘ Spec (.of k)) ≫
        (X ↘ Spec (.of k)) = (Limits.Sigma.ι _ Z ≫ (e.hom ≫ normalizationOverField k
          (X ↘ Spec (.of k)))) ≫ (X ↘ Spec (.of k)) by simp only [Category.assoc], he,
      Limits.Sigma.ι_comp_desc, Category.assoc]
  have hC : IsCurve k (normalizationOverField k fC ≫ fC) :=
    isCurve_normalizationOverField_comp k fC
  have hS : Smooth (normalizationOverField k fC ≫ fC) :=
    smooth_normalizationOverField_of_isCurve fC
  have hP : IsProper (normalizationOverField k fC ≫ fC) :=
    isProper_normalizationOverField_comp k fC
  have hK := three_le_two_mul_genus_add_encard_nodePoints hdim hnodal hg htail hbridge Z
  have : IsCurve k ((Limits.Sigma.ι _ Z ≫ e.hom) ≫ normalizationOverField k (X ↘ Spec (.of k)) ≫
      (X ↘ Spec (.of k))) := hstr ▸ hC
  have : Smooth ((Limits.Sigma.ι _ Z ≫ e.hom) ≫ normalizationOverField k (X ↘ Spec (.of k)) ≫
      (X ↘ Spec (.of k))) := hstr ▸ hS
  have : IsProper ((Limits.Sigma.ι _ Z ≫ e.hom) ≫ normalizationOverField k (X ↘ Spec (.of k)) ≫
      (X ↘ Spec (.of k))) := hstr ▸ hP
  have hdeg := invertibleCurveDegree_relativeDifferentials_eq (k := k)
    ((Limits.Sigma.ι _ Z ≫ e.hom) ≫ normalizationOverField k (X ↘ Spec (.of k)) ≫
      (X ↘ Spec (.of k)))
  rw [congrArg genus hstr] at hdeg
  obtain ⟨h0, h1⟩ := SheafDerivationOf.encard_setOf_fixes_le _ hE
  rw [hdeg] at h0 h1
  have hT : (nodePoints (k := k) Z).encard ≤
      ((-(2 * (genus (normalizationOverField k fC ≫ fC) : ℤ) - 2)).toNat : ℕ∞) :=
    le_trans (Set.encard_le_encard fun z hz => hfix Z z hz) h1
  generalize genus (normalizationOverField k fC ≫ fC) = gN at hK hT h0
  have hg1 : gN ≤ 1 := by omega
  interval_cases gN
  · have : (nodePoints (k := k) Z).encard ≤ 2 := by simpa using hT
    have := hK.trans (by simpa using this)
    norm_num at this
  · have h0' : (nodePoints (k := k) Z).encard = 0 := by
      have := hT; simp at this; simp [this]
    rw [h0'] at hK
    norm_num at hK

end Stacks.Curves

end
