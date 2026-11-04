module

public import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.ComponentPositivity
public import StacksFrontier.AlgebraicGeometry.Curves.StableContraction.TricanonicalVeryAmple

/-!
# The tricanonical closed immersion into `ℙ^{5g-6}`

Let `X` be a proper scheme of dimension one over a field `k` with `H⁰(X, 𝒪_X) = k`, of genus
`g ≥ 2`, with at-worst-nodal singularities and ample dualizing sheaf `ω_X`. By [Stacks, Tag 0E8X]
the invertible module `ω_X^{⊗ 3}` is very ample with `H¹(X, ω_X^{⊗ 3}) = 0`. This file makes the
embedding explicit: Riemann–Roch gives `h⁰(X, ω_X^{⊗ 3}) = 3(2g - 2) + 1 - g = 5g - 5`, and a basis
of `H⁰(X, ω_X^{⊗ 3})` defines a closed immersion `X ⟶ ℙ^{5g-6}_k` over `k` pulling `𝒪(1)` back to
`ω_X^{⊗ 3}`.

## Main results

* `AlgebraicGeometry.finrank_cohomologyOverField_zero_tensorPower_three_dualizingSheafOverField`:
  `h⁰(X, ω_X^{⊗ 3}) = 5g - 5`.
* `AlgebraicGeometry.exists_isClosedImmersion_tensorPower_three_dualizingSheafOverField`: the
  closed immersion `X ⟶ ℙ^{5g-6}_k` over `k` with `φ^* 𝒪(1) ≅ ω_X^{⊗ 3}`.

## References

* [Stacks Project, Tag 0E8X](https://stacks.math.columbia.edu/tag/0E8X)
* [Stacks Project, Tag 0BS6](https://stacks.math.columbia.edu/tag/0BS6)
* [Stacks Project, Tag 0E8T](https://stacks.math.columbia.edu/tag/0E8T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Ample (IsInvertibleModule)

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsProper (X ↘ Spec (.of k))] [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]

/-- **`h⁰(X, ω_X^{⊗ 3}) = 5g - 5`.** `H¹` vanishes ([Stacks, Tag 0E8X]) and so do the higher
groups on a curve, so `h⁰` is the Euler characteristic, which is `deg(ω_X^{⊗ 3}) + χ(𝒪_X) =
3(2g - 2) + 1 - g` by the definition of the degree. -/
theorem finrank_cohomologyOverField_zero_tensorPower_three_dualizingSheafOverField
    (hdim : topologicalKrullDim X = 1) (hg : 2 ≤ genus (X ↘ Spec (.of k)))
    (hnodal : Stacks.Curves.HasAtWorstNodalSingularities k X)
    (hω : haveI := connectedSpace_of_isIso_globalSections k (X ↘ Spec (.of k))
      letI := isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities k X hdim hnodal
      Scheme.Modules.IsAmple X (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k)))) :
    haveI := connectedSpace_of_isIso_globalSections k (X ↘ Spec (.of k))
    letI := isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities k X hdim hnodal
    (Module.finrank k (cohomologyOverField k (X ↘ Spec (.of k))
      (Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2
        (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k))) 3) 0) : ℤ) =
      5 * (genus (X ↘ Spec (.of k)) : ℤ) - 5 := by
  have := connectedSpace_of_isIso_globalSections k (X ↘ Spec (.of k))
  let := isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities k X hdim hnodal
  have hdim' : topologicalKrullDim X ≤ 1 := hdim.le
  have hχ := finsum_alternating_finrank_cohomologyOverField_eq_sub_of_isZero k
    (X ↘ Spec (.of k)) (Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2
        (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k))) 3)
    (isZero_cohomologyOverField_two_le k (X ↘ Spec (.of k)) hdim' _)
  have hχO := finsum_alternating_finrank_cohomologyOverField_eq_sub_of_isZero k
    (X ↘ Spec (.of k)) (SheafOfModules.unit X.ringCatSheaf)
    (isZero_cohomologyOverField_two_le k (X ↘ Spec (.of k)) hdim' _)
  have h0O := finrank_cohomologyOverField_unit_zero_eq_one (X ↘ Spec (.of k))
  have h1O := finrank_cohomologyOverField_one_unit_eq_genus k (X ↘ Spec (.of k))
  have hdeg := invertibleCurveDegree_tensorPower_eq_mul_of_topologicalKrullDim_le_one k
    (X ↘ Spec (.of k)) hdim' (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k))) 3
  have hω2 := invertibleCurveDegree_dualizingSheafOverField_of_isInvertible k
    (X ↘ Spec (.of k)) hdim'
  have hz : Module.finrank k (cohomologyOverField k (X ↘ Spec (.of k))
      (Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2
        (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k))) 3) 1) = 0 :=
    have := ModuleCat.subsingleton_of_isZero
      (isZero_cohomology_one_tensorPower_three_dualizingSheafOverField hdim hg hnodal hω)
    Module.finrank_zero_of_subsingleton
  unfold invertibleCurveDegree at hdeg hω2
  rw [hχ, hχO, hz, h0O, h1O] at hdeg
  rw [hχO, h0O, h1O] at hω2
  push_cast at hdeg hω2
  linarith

/-- **The tricanonical closed immersion into `ℙ^{5g-6}`.** A basis of the `5g - 5`-dimensional
space `H⁰(X, ω_X^{⊗ 3})` generates `ω_X^{⊗ 3}` (it is globally generated, [Stacks, Tag 0E3K]) and
so defines a morphism `φ : X ⟶ ℙ^{5g-6}_k` over `k` with `φ^* 𝒪(1) ≅ ω_X^{⊗ 3}`, the homogeneous
coordinates pulling back to the basis. It is a closed immersion by the degree-two criterion of
[Stacks, Tag 0E8T] checked over an algebraic closure, exactly as in the proof of
[Stacks, Tag 0E8X]. -/
theorem exists_isClosedImmersion_tensorPower_three_dualizingSheafOverField
    (hdim : topologicalKrullDim X = 1) (hg : 2 ≤ genus (X ↘ Spec (.of k)))
    (hnodal : Stacks.Curves.HasAtWorstNodalSingularities k X)
    (hω : haveI := connectedSpace_of_isIso_globalSections k (X ↘ Spec (.of k))
      letI := isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities k X hdim hnodal
      Scheme.Modules.IsAmple X (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k)))) :
    haveI := connectedSpace_of_isIso_globalSections k (X ↘ Spec (.of k))
    letI := isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities k X hdim hnodal
    ∃ φ : X ⟶ projectiveSpaceOverRing (5 * genus (X ↘ Spec (.of k)) - 6) (.of k),
      IsClosedImmersion φ ∧
        φ ≫ Stacks.Tag01VT.projectiveSpaceHom (5 * genus (X ↘ Spec (.of k)) - 6) (Spec (.of k)) =
          X ↘ Spec (.of k) ∧
        Nonempty ((Scheme.Modules.pullback φ).obj
            (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf
              (5 * genus (X ↘ Spec (.of k)) - 6) (Spec (.of k))) ≅
          Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2
            (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k))) 3) := by
  classical
  have := connectedSpace_of_isIso_globalSections k (X ↘ Spec (.of k))
  let := isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities k X hdim hnodal
  let := Stacks.SheafOfModules.Invertible.tensorPower_isInvertible X.presheaf
    X.ringCatSheaf.2 (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k))) 3
  set n := 5 * genus (X ↘ Spec (.of k)) - 6 with hn
  set p := X ↘ Spec (.of k)
  set L : X.Modules := Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2
    (Stacks.Duality.dualizingSheafOverField p) 3
  have htail := forall_not_isRationalTail_of_isAmple_dualizingSheafOverField hdim hnodal hω
  have hgen := generatesStalks_id_of_isGeneratedByGlobalSections L
    (isGeneratedByGlobalSections_tensorPower_dualizingSheafOverField_of_forall_not_isRationalTail
      hdim hnodal htail hg 3 (by norm_num))
  -- the dimension of `H⁰(X, ℒ)`
  let : Module k Γ(L, ⊤) := Module.compHom _ (baseRingMap p)
  have : Module.Finite k Γ(L, ⊤) := moduleFinite_sections_of_isProper p L
  have hfin : Module.finrank k Γ(L, ⊤) = n + 1 := by
    have e := (cohomologyOverFieldZeroIsoSections k p L).toLinearEquiv.finrank_eq
    have e' : Module.finrank k
        ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop).hom).obj
          ((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).obj L)) =
        Module.finrank k Γ(L, ⊤) := rfl
    have h5 : (Module.finrank k Γ(L, ⊤) : ℤ) = 5 * (genus p : ℤ) - 5 := by
      rw [← e', ← e]
      exact finrank_cohomologyOverField_zero_tensorPower_three_dualizingSheafOverField
        hdim hg hnodal hω
    omega
  let b : Module.Basis (Fin (n + 1)) k Γ(L, ⊤) := Module.finBasisOfFinrankEq k Γ(L, ⊤) hfin
  have hgenb : Stacks.ProjectiveFromSections.GeneratesStalks (fun i : Fin (n + 1) => b i) := by
    rw [← Stacks.ProjectiveFromSections.generatesStalks_ulift_iff]
    exact generatesStalks_of_span_eq_top p L _
      (fun σ => Submodule.span_mono (by rintro _ ⟨j, rfl⟩; exact ⟨ULift.up j, rfl⟩)
        (b.mem_span σ)) hgen
  obtain ⟨φ, hφ, α, hiso, hα⟩ :=
    Stacks.TwistPullbackPinned.exists_hom_over_and_iso_pullback_twistingSheafAtUniverse
      (fun i : Fin (n + 1) => b i) hgenb p
  have := hiso
  let τ := projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))
  let θ : (Scheme.Modules.pullback φ).obj
      (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n (Spec (.of k))) ≅ L :=
    (Scheme.Modules.pullbackComp φ τ).app
      (Stacks.AmpleProjectiveImmersion.twistingSheafAtUniverse n) ≪≫ asIso α
  have : IsProper (Stacks.Tag01VT.projectiveSpaceHom n (Spec (.of k))) :=
    projectiveSpaceOver_isProper n (Spec (.of k))
  have hci : IsClosedImmersion φ := by
    refine isClosedImmersion_of_pinned_of_span_of_surjectsOnDegreeTwo_baseChange p
      (Stacks.Tag01VT.projectiveSpaceHom n (Spec (.of k))) φ hφ _ L θ
      (fun i : ULift.{u} (Fin (n + 1)) => Stacks.TwistPullbackPinned.pullbackCoordSection
        τ i.down)
      (fun i : ULift.{u} (Fin (n + 1)) => b i.down) (fun i => ?_)
      (fun σ => Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨ULift.up i, rfl⟩)
        (b.mem_span σ))
      (fun X' g' f' h => ?_)
    · rw [← hα i.down, pullbackCoordSection_eq, pullbackCoordSection_eq,
        ← pullbackSectionTop_comp φ τ (Stacks.AmpleProjectiveImmersion.twistingSheafAtUniverse n)
          (Stacks.TwistPullbackPinned.coordGlobalSection n i.down)]
      exact congrArg (fun y => (Scheme.Modules.Hom.app α ⊤) y)
        (SheafOfModules.iso_hom_app_apply_inv ((Scheme.Modules.pullbackComp φ τ).app
          (Stacks.AmpleProjectiveImmersion.twistingSheafAtUniverse n)) (op ⊤) _)
    · exact surjectsOnDegreeTwo_pullback_of_isPullback h _
        (surjectsOnDegreeTwo_pullback_tensorPower_three_dualizingSheafOverField
          (AlgebraicClosure k) hdim hg hnodal hω)
  exact ⟨φ, hci, hφ, ⟨θ⟩⟩

end AlgebraicGeometry

end
