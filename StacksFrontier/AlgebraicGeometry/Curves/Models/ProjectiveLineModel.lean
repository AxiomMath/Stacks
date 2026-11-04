module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.IntegralSpecialFibre
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.SmoothProjectiveVariety
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Projective
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.RegularSchemes
public import StacksFrontier.AlgebraicGeometry.Descent.SchemeProperty.Regular
public import StacksFrontier.AlgebraicGeometry.HProjective.Basic

/-!
# The projective line over a discrete valuation ring is a minimal model

Let `R` be a discrete valuation ring with fraction field `K`. The projective line `ℙ¹_R` is a
minimal model of `ℙ¹_K` ([Stacks, Tag 0C2V]), for every identification of its generic fibre with
`ℙ¹_K` over `K`.

## Main definitions

* `Stacks.Models.projectiveLineGenericFibreIso`: the canonical identification of the generic
  fibre of `ℙ¹_R` with `ℙ¹_K`.

## Main results

* `Stacks.Models.isMinimalModel_projectiveLine`: `ℙ¹_R` is a minimal model of `ℙ¹_K`, for every
  identification of its generic fibre with `ℙ¹_K` over `K`.

## Implementation notes

`ℙ¹_K` is a smooth projective curve with `H⁰(ℙ¹_K, 𝒪) = K`, and `ℙ¹_R` is smooth and proper
over `R`, hence flat, of finite type, and regular, smoothness carrying regularity up from `R`.
Its special fibre is `ℙ¹_k`, which is integral of dimension one, so it contains no exceptional
curve of the first kind
(`AlgebraicGeometry.not_hasExceptionalCurveOfFirstKind_of_isIntegral_specialFibre`).

## References

* [Stacks Project, Tag 0C2V](https://stacks.math.columbia.edu/tag/0C2V)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Models

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

attribute [local instance] AlgebraicGeometry.isCurve_projectiveSpaceOver_one

/-- The canonical identification of the generic fibre of `ℙ¹_R` with `ℙ¹_K`. -/
noncomputable def projectiveLineGenericFibreIso :
    projectiveSpaceOverRing 1 (.of K) ≅
      pullback (projectiveSpaceOverRing 1 (.of R) ↘ Spec (.of R))
        (Spec.map (CommRingCat.ofHom (algebraMap R K))) :=
  (projectiveSpaceOverBaseChangeIso 1 (Spec.map (CommRingCat.ofHom (algebraMap R K)))).symm

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
/-- The canonical identification of the generic fibre of `ℙ¹_R` with `ℙ¹_K` lies over `K`. -/
theorem projectiveLineGenericFibreIso_hom_snd :
    (projectiveLineGenericFibreIso (R := R) (K := K)).hom ≫
        pullback.snd (projectiveSpaceOverRing 1 (.of R) ↘ Spec (.of R))
          (Spec.map (CommRingCat.ofHom (algebraMap R K))) =
      projectiveSpaceOverRing 1 (.of K) ↘ Spec (.of K) := by
  rw [projectiveLineGenericFibreIso, Iso.symm_hom, ← projectiveSpaceOverBaseChangeIso_hom_over,
    Iso.inv_hom_id_assoc]

/-- `ℙ¹_R` is a regular scheme: it is smooth over the regular scheme `Spec R`. -/
theorem isRegular_projectiveLine : IsRegular (projectiveSpaceOverRing 1 (.of R)) :=
  isRegular_of_smooth (projectiveSpaceOverRing 1 (.of R) ↘ Spec (.of R)) inferInstance
    ((isRegular_spec_iff R).2 inferInstance)

/-- The projective line over a discrete valuation ring contains no exceptional curve of the first
kind: its special fibre is the projective line over the residue field, integral of dimension
one. -/
theorem projectiveLine_not_hasExceptionalCurveOfFirstKind :
    ¬ (projectiveSpaceOverRing 1 (.of R)).HasExceptionalCurveOfFirstKind := by
  let p := projectiveSpaceOverRing 1 (.of R) ↘ Spec (.of R)
  let eK := projectiveSpaceOverBaseChangeIso 1 (residueSpecMap R)
  have : IsProper p := isProper_projectiveSpaceOver 1 _
  have : IsIntegral (projectiveSpaceOverRing 1 (.of (IsLocalRing.ResidueField R))) :=
    isIntegral_projectiveSpace_one _
  have : Nonempty (pullback p (residueSpecMap R) : Scheme.{u}) :=
    ⟨eK.inv (Nonempty.some inferInstance)⟩
  have : IsIntegral (pullback p (residueSpecMap R)) := isIntegral_of_isOpenImmersion eK.hom
  refine not_hasExceptionalCurveOfFirstKind_of_isIntegral_specialFibre p ?_
  rw [IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso eK).isHomeomorph]
  exact (topologicalKrullDim_projectiveSpace_one _).le

omit [IsFractionRing R K] in
/-- **The projective line over a discrete valuation ring is a minimal model of the projective
line over its fraction field** ([Stacks, Tag 0C2V]), for every identification `e` of its generic
fibre with `ℙ¹_K` over `K`. -/
theorem isMinimalModel_projectiveLine
    (e : projectiveSpaceOverRing 1 (.of K) ≅
      pullback (projectiveSpaceOverRing 1 (.of R) ↘ Spec (.of R))
        (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (he : e.hom ≫ pullback.snd (projectiveSpaceOverRing 1 (.of R) ↘ Spec (.of R))
        (Spec.map (CommRingCat.ofHom (algebraMap R K))) =
      projectiveSpaceOverRing 1 (.of K) ↘ Spec (.of K)) :
    IsMinimalModel (projectiveSpaceOverRing 1 (.of K) ↘ Spec (.of K))
      (projectiveSpaceOverRing 1 (.of R) ↘ Spec (.of R)) e where
  curveProjective := Stacks.HProjective.isHProjective_over 1 _
  isIso_globalSections := isIso_ΓSpecIso_inv_comp_appTop_projectiveSpaceOverRing K 1
  isModel := ⟨inferInstance, inferInstance, inferInstance, he⟩
  isProper := isProper_projectiveSpaceOver 1 _
  regular := isRegular_projectiveLine
  not_hasExceptionalCurveOfFirstKind := projectiveLine_not_hasExceptionalCurveOfFirstKind

end Stacks.Models

end
