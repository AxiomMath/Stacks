module

public import StacksFrontier.AlgebraicGeometry.Curves.StableContraction.AmpleNoRationalTail
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.SubcurveDegreeBound
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.VeryAmpleLargeDegree
public import StacksFrontier.AlgebraicGeometry.Curves.GenusZeroPositiveDegree.CanonicalNodal
public import StacksFrontier.AlgebraicGeometry.AmplePullback.Affine
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingComplexBaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The tricanonical sheaf of a nodal curve with ample dualizing sheaf

Let `X` be a proper scheme of dimension one over a field `k` with `H⁰(X, 𝒪_X) = k`, of genus
`g ≥ 2`, with at-worst-nodal singularities and ample dualizing sheaf `ω_X`. [Stacks, Tag 0E8X]
asserts that `ω_X^{⊗ 3}` is very ample and `H¹(X, ω_X^{⊗ 3}) = 0`.

## Main results

* `AlgebraicGeometry.forall_not_isRationalTail_of_isAmple_dualizingSheafOverField`: `X` has no
  rational tail, since `deg(ω_X|_C) < 0` on a rational tail `C` ([Stacks, Tag 0E63]) while an
  ample invertible module has positive degree on every integral subcurve.
* `AlgebraicGeometry.isZero_cohomology_one_idealTwist_tensorPower_three_dualizingSheafOverField`:
  `H¹(X, ℐ_Z ω_X^{⊗ 3}) = 0` for every zero-dimensional closed subscheme `Z` of degree at most two,
  by [Stacks, Tag 0E3E] and [Stacks, Tag 0E3J].
* `AlgebraicGeometry.isZero_cohomology_one_tensorPower_three_dualizingSheafOverField`:
  `H¹(X, ω_X^{⊗ 3}) = 0`, the case `Z = ∅`.
* `AlgebraicGeometry.surjectsOnDegreeTwo_tensorPower_three_dualizingSheafOverField` and
  `AlgebraicGeometry.surjectsOnDegreeTwo_pullback_tensorPower_three_dualizingSheafOverField`:
  `ω_X^{⊗ 3}` restricts surjectively to every degree-two closed subscheme, the hypothesis of
  [Stacks, Tag 0E8T], on `X` and on every base change `X_K`.
* [Stacks, Tag 0E8X]:
  `isRelativelyVeryAmple_tensorPower_three_dualizingSheafOverField_and_isZero_cohomology_one`.

## References

* [Stacks Project, Tag 0E8X](https://stacks.math.columbia.edu/tag/0E8X)
* [Stacks Project, Tag 0E3E](https://stacks.math.columbia.edu/tag/0E3E)
* [Stacks Project, Tag 0E3J](https://stacks.math.columbia.edu/tag/0E3J)
* [Stacks Project, Tag 0E3K](https://stacks.math.columbia.edu/tag/0E3K)
* [Stacks Project, Tag 0E32](https://stacks.math.columbia.edu/tag/0E32)
* [Stacks Project, Tag 0E63](https://stacks.math.columbia.edu/tag/0E63)
* [Stacks Project, Tag 0E8T](https://stacks.math.columbia.edu/tag/0E8T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsProper (X ↘ Spec (.of k))] [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]

/-- **A nodal curve with ample dualizing sheaf has no rational tail.** Let `X` be a proper
scheme of dimension one over `k` with `H⁰(X, 𝒪_X) = k` and at-worst-nodal singularities whose
dualizing sheaf `ω_X` is ample. On a rational tail `C` the degree of `ω_X|_C` is negative
([Stacks, Tag 0E63]), while the pullback of an ample invertible module along the affine morphism
`C ⟶ X` has positive degree. -/
theorem forall_not_isRationalTail_of_isAmple_dualizingSheafOverField
    (hdim : topologicalKrullDim X = 1) (hnodal : Stacks.Curves.HasAtWorstNodalSingularities k X)
    (hω : haveI := connectedSpace_of_isIso_globalSections k (X ↘ Spec (.of k))
      letI := isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities k X hdim hnodal
      Scheme.Modules.IsAmple X (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k))))
    (C : X.IdealSheafData) : ¬ IsRationalTail k X C := by
  have := connectedSpace_of_isIso_globalSections k (X ↘ Spec (.of k))
  let := isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities k X hdim hnodal
  intro hC
  have : IsIntegral C.subscheme := hC.isIntegral
  exact lt_asymm
    (invertibleCurveDegree_pullback_dualizingSheafOverField_neg_of_isRationalTail hdim hnodal C hC)
    (invertibleCurveDegree_pullback_pos_of_isAmple_of_isAffineHom k
      (C.subschemeι ≫ (X ↘ Spec (.of k)))
      (Stacks.Curves.topologicalKrullDim_subscheme_eq_one_of_isRationalTail k X hdim C hC)
      C.subschemeι _ hω)

/-- **`H¹(X, ℐ_Z ω_X^{⊗ 3}) = 0` for `Z` of degree at most two.** Let `X` be a proper scheme of
dimension one over `k` with `H⁰(X, 𝒪_X) = k`, of genus `g ≥ 2`, with at-worst-nodal
singularities and ample dualizing sheaf `ω_X`, and let `Z ⊆ X` be a zero-dimensional closed
subscheme with `dim_k Γ(Z, 𝒪_Z) ≤ 2`. Otherwise [Stacks, Tag 0E3E] gives a reduced connected
subcurve `Y` with `deg(ω_X^{⊗ 3}|_Y) ≤ -2 χ(Y, 𝒪_Y) + deg(Z ∩ Y)`; for `Y = X` this contradicts
`deg ω_X = 2g - 2`, and for `Y ≠ X` it contradicts `deg(ω_X|_Y) > 0` (ampleness) together with
`deg(ω_X|_Y) ≥ h¹(Y, 𝒪_Y)` ([Stacks, Tag 0E3J], as `X` has no rational tail). -/
theorem isZero_cohomology_one_idealTwist_tensorPower_three_dualizingSheafOverField
    (hdim : topologicalKrullDim X = 1) (hg : 2 ≤ genus (X ↘ Spec (.of k)))
    (hnodal : Stacks.Curves.HasAtWorstNodalSingularities k X)
    (hω : haveI := connectedSpace_of_isIso_globalSections k (X ↘ Spec (.of k))
      letI := isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities k X hdim hnodal
      Scheme.Modules.IsAmple X (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k))))
    (Z : X.IdealSheafData) (hZ : topologicalKrullDim Z.subscheme ≤ 0)
    (hZdeg : letI : Algebra k Γ(Z.subscheme, ⊤) :=
        ((Scheme.ΓSpecIso (.of k)).inv ≫ (Z.subschemeι ≫ (X ↘ Spec (.of k))).appTop).hom.toAlgebra
      Module.finrank k Γ(Z.subscheme, ⊤) ≤ 2) :
    haveI := connectedSpace_of_isIso_globalSections k (X ↘ Spec (.of k))
    letI := isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities k X hdim hnodal
    IsZero (cohomologyOverField k (X ↘ Spec (.of k))
      ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj
          (Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2
            (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k))) 3)).obj
        (Stacks.ClosedImmersion.idealSheaf Z.subschemeι.toLRSHom.toShHom))) 1) := by
  have := connectedSpace_of_isIso_globalSections k (X ↘ Spec (.of k))
  let := isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities k X hdim hnodal
  have : IsReduced X := Stacks.Curves.isReduced_of_hasAtWorstNodalSingularities k X hnodal
  let := Stacks.SheafOfModules.Invertible.tensorPower_isInvertible X.presheaf
    X.ringCatSheaf.2 (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k))) 3
  by_contra h
  obtain ⟨Y, hYred, hYconn, hY, hle⟩ :=
    exists_subcurve_invertibleCurveDegree_le_of_not_isZero_cohomology_idealTwist
      (X ↘ Spec (.of k)) hdim _ Z hZ h
  by_cases hbot : Y = ⊥
  · subst hbot
    exact absurd hle (not_le.mpr
      (neg_two_mul_finsum_add_finrank_lt_invertibleCurveDegree_bot (X ↘ Spec (.of k)) hdim.le hg
        Z hZ hZdeg hY.le))
  · have : Nonempty Y.subscheme := by
      by_contra hne
      rw [not_nonempty_iff, ← topologicalKrullDim_eq_bot_iff_isEmpty] at hne
      rw [hne] at hY
      exact absurd hY (by decide)
    have hYpos := invertibleCurveDegree_subscheme_pos_of_forall_isIntegral (X ↘ Spec (.of k))
      (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k)))
      (fun C _ hC => invertibleCurveDegree_pullback_pos_of_isAmple_of_isAffineHom k
        (C.subschemeι ≫ (X ↘ Spec (.of k))) hC C.subschemeι _ hω) Y hY
    exact absurd hle (not_le.mpr (neg_two_mul_finsum_add_finrank_lt_invertibleCurveDegree
      (X ↘ Spec (.of k)) (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k))) Z hZ hZdeg
      Y hY.le hYpos
      (finrank_cohomologyOverField_one_le_invertibleCurveDegree_of_forall_not_isRationalTail
        hdim hnodal (forall_not_isRationalTail_of_isAmple_dualizingSheafOverField hdim hnodal hω)
        Y hY hbot)))

/-- **The vanishing `H¹(X, ω_X^{⊗ 3}) = 0` of [Stacks, Tag 0E8X].** Let `X` be a proper scheme
of dimension one over `k` with `H⁰(X, 𝒪_X) = k`, of genus `g ≥ 2`, with at-worst-nodal
singularities and ample dualizing sheaf `ω_X`. Then `H¹(X, ω_X^{⊗ 3}) = 0`: this is
`AlgebraicGeometry.isZero_cohomology_one_idealTwist_tensorPower_three_dualizingSheafOverField` for
the empty closed subscheme, whose ideal is `𝒪_X`. -/
@[sga "7 I 5.1" "Clause (1), special case"]
theorem isZero_cohomology_one_tensorPower_three_dualizingSheafOverField
    (hdim : topologicalKrullDim X = 1) (hg : 2 ≤ genus (X ↘ Spec (.of k)))
    (hnodal : Stacks.Curves.HasAtWorstNodalSingularities k X)
    (hω : haveI := connectedSpace_of_isIso_globalSections k (X ↘ Spec (.of k))
      letI := isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities k X hdim hnodal
      Scheme.Modules.IsAmple X (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k)))) :
    haveI := connectedSpace_of_isIso_globalSections k (X ↘ Spec (.of k))
    letI := isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities k X hdim hnodal
    IsZero (cohomologyOverField k (X ↘ Spec (.of k))
      (Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2
        (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k))) 3) 1) := by
  have := connectedSpace_of_isIso_globalSections k (X ↘ Spec (.of k))
  let := isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities k X hdim hnodal
  let S : CohenMacaulayCurveSituation.{u} := ⟨k, X, X ↘ Spec (.of k), hdim⟩
  have hZ : topologicalKrullDim (⊤ : X.IdealSheafData).subscheme ≤ 0 :=
    ((topologicalKrullDim_eq_bot_iff_isEmpty _).mpr inferInstance).trans_le bot_le
  have h := isZero_cohomology_one_idealTwist_tensorPower_three_dualizingSheafOverField hdim hg
    hnodal hω ⊤ hZ (by
      let : Algebra k Γ((⊤ : X.IdealSheafData).subscheme, ⊤) :=
        ((Scheme.ΓSpecIso (.of k)).inv ≫
          ((⊤ : X.IdealSheafData).subschemeι ≫ (X ↘ Spec (.of k))).appTop).hom.toAlgebra
      have : Subsingleton Γ((⊤ : X.IdealSheafData).subscheme, ⊤) :=
        inferInstanceAs (Subsingleton Γ((⊤ : X.IdealSheafData).subscheme, _))
      rw [Module.finrank_zero_of_subsingleton]
      norm_num)
  have := S.isIso_idealTwistι_top (Stacks.SheafOfModules.Invertible.tensorPower X.presheaf
    X.ringCatSheaf.2 (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k))) 3)
  exact h.of_iso (cohomologyOverFieldIso k (X ↘ Spec (.of k))
    (asIso (S.idealTwistι ⊤ _)) 1).symm

/-- **`ω_X^{⊗ 3}` restricts surjectively to every degree-two closed subscheme**, the hypothesis of
[Stacks, Tag 0E8T], for `X` proper of dimension one over `k` with `H⁰(X, 𝒪_X) = k`, of genus
`g ≥ 2`, with at-worst-nodal singularities and ample `ω_X`: for such a subscheme `Z` the
sequence `0 ⟶ ℐ_Z ω_X^{⊗ 3} ⟶ ω_X^{⊗ 3} ⟶ ω_X^{⊗ 3}|_Z ⟶ 0` and
`H¹(X, ℐ_Z ω_X^{⊗ 3}) = 0`. -/
theorem surjectsOnDegreeTwo_tensorPower_three_dualizingSheafOverField
    (hdim : topologicalKrullDim X = 1) (hg : 2 ≤ genus (X ↘ Spec (.of k)))
    (hnodal : Stacks.Curves.HasAtWorstNodalSingularities k X)
    (hω : haveI := connectedSpace_of_isIso_globalSections k (X ↘ Spec (.of k))
      letI := isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities k X hdim hnodal
      Scheme.Modules.IsAmple X (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k)))) :
    haveI := connectedSpace_of_isIso_globalSections k (X ↘ Spec (.of k))
    letI := isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities k X hdim hnodal
    SurjectsOnDegreeTwo (X ↘ Spec (.of k))
      (Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2
        (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k))) 3) := by
  have := connectedSpace_of_isIso_globalSections k (X ↘ Spec (.of k))
  let := isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities k X hdim hnodal
  let := Stacks.SheafOfModules.Invertible.tensorPower_isInvertible X.presheaf
    X.ringCatSheaf.2 (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k))) 3
  let S : CohenMacaulayCurveSituation.{u} := ⟨k, X, X ↘ Spec (.of k), hdim⟩
  exact S.surjectsOnDegreeTwo_of_forall_isZero_cohomology_idealTwist _ fun Z hZ _ hd =>
    isZero_cohomology_one_idealTwist_tensorPower_three_dualizingSheafOverField hdim hg hnodal hω
      Z hZ hd.le

/-- **The hypothesis of [Stacks, Tag 0E8T] for `ω_X^{⊗ 3}` after extension of the ground field.**
For `X` as in [Stacks, Tag 0E8X] and a field extension `K/k`, the pullback of `ω_X^{⊗ 3}` to
`X_K` restricts surjectively to every degree-two closed subscheme. `X_K` is again proper of
dimension one with `H⁰ = K`, of genus `g`, with at-worst-nodal singularities, and its dualizing
sheaf is the pullback of `ω_X` ([Stacks, Tag 0E32]), ample since `X_K ⟶ X` is affine; so
`AlgebraicGeometry.surjectsOnDegreeTwo_tensorPower_three_dualizingSheafOverField` applies on
`X_K`. -/
theorem surjectsOnDegreeTwo_pullback_tensorPower_three_dualizingSheafOverField (K : Type u)
    [Field K] [Algebra k K]
    (hdim : topologicalKrullDim X = 1) (hg : 2 ≤ genus (X ↘ Spec (.of k)))
    (hnodal : Stacks.Curves.HasAtWorstNodalSingularities k X)
    (hω : haveI := connectedSpace_of_isIso_globalSections k (X ↘ Spec (.of k))
      letI := isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities k X hdim hnodal
      Scheme.Modules.IsAmple X (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k)))) :
    haveI := connectedSpace_of_isIso_globalSections k (X ↘ Spec (.of k))
    letI := isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities k X hdim hnodal
    SurjectsOnDegreeTwo (pullback.snd (X ↘ Spec (.of k))
        (Spec.map (CommRingCat.ofHom (algebraMap k K))))
      ((Scheme.Modules.pullback (pullback.fst (X ↘ Spec (.of k))
        (Spec.map (CommRingCat.ofHom (algebraMap k K))))).obj
        (Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2
          (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k))) 3)) := by
  have := connectedSpace_of_isIso_globalSections k (X ↘ Spec (.of k))
  let := isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities k X hdim hnodal
  let := Stacks.SheafOfModules.Invertible.tensorPower_isInvertible X.presheaf
    X.ringCatSheaf.2 (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k))) 3
  -- the chosen base change `X_K = X ×_k K`
  let : (pullback (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).Over (Spec (.of K)) := ⟨pullback.snd _ _⟩
  have hP : IsPullback (pullback.fst (X ↘ Spec (.of k))
        (Spec.map (CommRingCat.ofHom (algebraMap k K))))
      (pullback (X ↘ Spec (.of k)) (Spec.map (CommRingCat.ofHom (algebraMap k K))) ↘
        Spec (.of K))
      (X ↘ Spec (.of k)) (Spec.map (CommRingCat.ofHom (algebraMap k K))) :=
    IsPullback.of_hasPullback _ _
  have : IsProper (pullback (X ↘ Spec (.of k)) (Spec.map (CommRingCat.ofHom (algebraMap k K))) ↘
      Spec (.of K)) :=
    MorphismProperty.of_isPullback (P := @IsProper) hP inferInstance
  have : IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫
      (pullback (X ↘ Spec (.of k)) (Spec.map (CommRingCat.ofHom (algebraMap k K))) ↘
        Spec (.of K)).appTop) :=
    isIso_globalSections_baseChange k K _ _ _ hP
  have hdimP : topologicalKrullDim
      (pullback (X ↘ Spec (.of k)) (Spec.map (CommRingCat.ofHom (algebraMap k K))) :
        Scheme.{u}) = 1 :=
    (topologicalKrullDim_baseChange k K _ _ _ hP).trans hdim
  have hgP : 2 ≤ genus (pullback (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) ↘ Spec (.of K)) := by
    rwa [genus_baseChange k K _ _ _ hP]
  have hnodalP : Stacks.Curves.HasAtWorstNodalSingularities K
      (pullback (X ↘ Spec (.of k)) (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :=
    Stacks.Curves.hasAtWorstNodalSingularities_baseChange k K X
      (equidimensional_of_isIso_globalSections_of_dimension_one k (X ↘ Spec (.of k)) hdim) hdim
      hnodal
  have := connectedSpace_of_isIso_globalSections K
    (pullback (X ↘ Spec (.of k)) (Spec.map (CommRingCat.ofHom (algebraMap k K))) ↘ Spec (.of K))
  let hωPinv := isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities K
    (pullback (X ↘ Spec (.of k)) (Spec.map (CommRingCat.ofHom (algebraMap k K)))) hdimP hnodalP
  -- `ω_{X_K} ≅ g'^* ω_X`, [Stacks, Tag 0E32] part (2)
  let e := Stacks.Duality.dualizingSheafOverFieldBaseChangeIso (X ↘ Spec (.of k))
    (pullback.fst (X ↘ Spec (.of k)) (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (pullback (X ↘ Spec (.of k)) (Spec.map (CommRingCat.ofHom (algebraMap k K))) ↘ Spec (.of K))
    hP
  have : IsAffineHom (pullback.fst (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :=
    MorphismProperty.of_isPullback hP.flip inferInstance
  let := Stacks.Modules.isInvertible_pullback
    (pullback.fst (X ↘ Spec (.of k)) (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k)))
  have hωP : Scheme.Modules.IsAmple
      (pullback (X ↘ Spec (.of k)) (Spec.map (CommRingCat.ofHom (algebraMap k K))))
      (Stacks.Duality.dualizingSheafOverField
        (pullback (X ↘ Spec (.of k)) (Spec.map (CommRingCat.ofHom (algebraMap k K))) ↘
          Spec (.of K))) :=
    @Scheme.Modules.isAmple_of_iso _ _ _ inferInstance hωPinv e
      (Scheme.Modules.isAmple_pullback_of_isAffineHom _ _ hω)
  exact surjectsOnDegreeTwo_of_iso
    (Stacks.SheafOfModules.Invertible.tensorPowerCongr
        (pullback (X ↘ Spec (.of k)) (Spec.map (CommRingCat.ofHom (algebraMap k K)))).presheaf
        (pullback (X ↘ Spec (.of k))
          (Spec.map (CommRingCat.ofHom (algebraMap k K)))).ringCatSheaf.2
        _ _ e.symm 3 ≪≫
      (Scheme.Modules.pullbackTensorPowerIso _ _ 3).symm)
    (surjectsOnDegreeTwo_tensorPower_three_dualizingSheafOverField hdimP hgP hnodalP hωP)

/-- **Stacks Project, Tag 0E8X.** Let `X` be a proper scheme of dimension one over a field `k`
with `H⁰(X, 𝒪_X) = k`, of genus `g ≥ 2`, with at-worst-nodal singularities, and assume the
dualizing sheaf `ω_X` is ample. Then `ω_X^{⊗ 3}` is very ample and `H¹(X, ω_X^{⊗ 3}) = 0`.

`ω_X` is invertible since `X` is Gorenstein ([Stacks, Tag 0E37]). `X` has no rational tail, so
`ω_X^{⊗ 3}` is globally generated ([Stacks, Tag 0E3K]); its sections define a morphism to
projective space, which is a closed immersion once it is one after base change to `k̄`
([Stacks, Tag 02L6]). Over `k̄` the base change is again nodal of genus `g` with ample dualizing
sheaf the pullback of `ω_X` ([Stacks, Tag 0E32]), and `H¹(ℐ_Z ω^{⊗ 3}) = 0` for every degree-two
`Z` gives the criterion of [Stacks, Tag 0E8T]. -/
@[stacks 0E8X]
theorem isRelativelyVeryAmple_tensorPower_three_dualizingSheafOverField_and_isZero_cohomology_one
    (hdim : topologicalKrullDim X = 1) (hg : 2 ≤ genus (X ↘ Spec (.of k)))
    (hnodal : Stacks.Curves.HasAtWorstNodalSingularities k X)
    (hω : haveI := connectedSpace_of_isIso_globalSections k (X ↘ Spec (.of k))
      letI := isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities k X hdim hnodal
      Scheme.Modules.IsAmple X (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k)))) :
    haveI := connectedSpace_of_isIso_globalSections k (X ↘ Spec (.of k))
    letI := isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities k X hdim hnodal
    Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple (X ↘ Spec (.of k))
        (Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2
          (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k))) 3) ∧
      IsZero (cohomologyOverField k (X ↘ Spec (.of k))
        (Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2
          (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k))) 3) 1) := by
  have := connectedSpace_of_isIso_globalSections k (X ↘ Spec (.of k))
  let := isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities k X hdim hnodal
  let := Stacks.SheafOfModules.Invertible.tensorPower_isInvertible X.presheaf
    X.ringCatSheaf.2 (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k))) 3
  refine ⟨?_, isZero_cohomology_one_tensorPower_three_dualizingSheafOverField hdim hg hnodal hω⟩
  refine isRelativelyVeryAmple_of_generatesStalks_of_surjectsOnDegreeTwo_baseChange _ _
    (generatesStalks_id_of_isGeneratedByGlobalSections _
      (isGeneratedByGlobalSections_tensorPower_dualizingSheafOverField_of_forall_not_isRationalTail
        hdim hnodal (forall_not_isRationalTail_of_isAmple_dualizingSheafOverField hdim hnodal hω)
        hg 3 (by norm_num))) fun X' g' f' h => ?_
  exact surjectsOnDegreeTwo_pullback_of_isPullback h _
    (surjectsOnDegreeTwo_pullback_tensorPower_three_dualizingSheafOverField (AlgebraicClosure k)
      hdim hg hnodal hω)

end AlgebraicGeometry

end
