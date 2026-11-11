module

public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.FibreDimensionAssociatedGraded
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.BaseThresholdInitialForms
public import StacksFrontier.AlgebraicGeometry.Blowup.FibreDimensionBound
public import StacksFrontier.AlgebraicGeometry.ProjNoetherian.CoherentFiniteness
public import StacksFrontier.RingTheory.Filtration.AssociatedGradedNoetherian
public import StacksFrontier.Topology.Sheaves.Cohomology.CechToCohomology.AffineCovering
public import StacksCore.Tactic.StacksAttribute

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AssociatedGraded

universe u

namespace Stacks.LocalCohomology.UniformityIII

variable {A : Type u} [CommRing A] (I : Ideal A)

/-- The graded surjection `⨁ Iⁿ → Gr_I(A)` is the quotient onto `Gr_I(A)`. -/
theorem isGrQuotient_reesToGraded : IsGrQuotient I (reesToGraded I) := by
  intro n y hy
  rw [reesToGraded_of_mem I hy, map_eq_zero_iff _ (DirectSum.of_injective n)]
  change Submodule.Quotient.mk _ = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, ring_power_eq I (n + 1)]
  rfl

attribute [local instance] modulesEnoughInjectives in
/-- Some degree satisfies `AssociatedGraded.IsRegularDegree` from it on. -/
theorem exists_forall_isRegularDegree [IsNoetherianRing A] :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → IsRegularDegree I q := by
  obtain ⟨q₀, h⟩ := exists_isBaseThreshold I
  have hg := (isBaseThreshold_iff_isGrThreshold (reesToGraded_surjective I)
    (isGrQuotient_reesToGraded I) q₀).1 h
  refine ⟨q₀, fun q hq => ⟨fun i hi _ => ?_, ?_⟩⟩
  · exact (Stacks.Cohomology.CechAcyclic.isZero_rightDerived_evaluation_iff_isZero_Hgroup
      (projGr I).ringCatSheaf ⊤ i _).2 (hg.1 i q hi hq)
  · exact (bijective_pieceToSections_iff I q).2 (hg.2 q hq)

/-- `d(S)` bounds the dimension of every fibre of `Y = Proj(S) → Spec(S₀)`, for `A` Noetherian;
this is the definition of `AssociatedGraded.dInvariant` read through
`dInvariant_eq_fibreDim`. -/
theorem topologicalKrullDim_fiber_toSpecGradeZero_le [IsNoetherianRing A]
    (y : Spec (.of (grading I 0))) :
    topologicalKrullDim ((toSpecGradeZero I).fiber y) ≤ (fibreDim I : WithBot ℕ∞) := by
  have h1 : (topologicalKrullDim ((toSpecGradeZero I).fiber y)).unbotD 0 ≤ dInvariant I :=
    le_iSup (fun y : Spec (.of (grading I 0)) =>
      (topologicalKrullDim (Scheme.Hom.fiber (toSpecGradeZero I) y)).unbotD 0) y
  rw [dInvariant_eq_fibreDim I] at h1
  cases h : topologicalKrullDim ((toSpecGradeZero I).fiber y) with
  | bot => exact bot_le
  | coe n =>
    rw [h, WithBot.unbotD_coe] at h1
    exact_mod_cast h1

attribute [local instance 2000] HasDerivedCategory.standard in
attribute [local instance 2000]
  HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso in
/-- **`Hⁱ(Y, ℱ) = 0` for `ℱ` quasi-coherent on `Y = Proj(Gr_I(A))` and `i > d(S)`**, for `A`
Noetherian: [Stacks, Tag 02V7] at the stalks of the higher direct images along the proper
morphism `Y → Spec(S₀)`, whose fibres have dimension at most `d(S)`, and the Leray comparison
over the affine base `Spec(S₀)`. -/
theorem isZero_projGr_cohomology_of_fibreDim_lt [IsNoetherianRing A] (F : (projGr I).Modules)
    [F.IsQuasicoherent] {i : ℕ} (hi : fibreDim I < i) :
    IsZero (((Stacks.Cohomology.sectionsFunctor (projGr I) ⊤).rightDerived i).obj F) := by
  have : IsNoetherianRing (gradedRing I) := isNoetherianRing_gradedRing I
  have : IsNoetherianRing (grading I 0) :=
    Stacks.AlgebraicGeometry.ProjNoetherian.isNoetherianRing_gradeZero (grading I)
  have : IsLocallyNoetherian (Spec (.of (grading I 0))) :=
    AlgebraicGeometry.isLocallyNoetherian_Spec.mpr inferInstance
  have : IsProper (toSpecGradeZero I) :=
    Stacks.AlgebraicGeometry.ProjNoetherian.isProper_toSpecZero (grading I)
  have hvan : ∀ q : ℕ, fibreDim I + 1 ≤ q →
      IsZero (((Scheme.Modules.pushforward (toSpecGradeZero I)).rightDerivedPlus
        (q : ℤ)).obj F) := fun q hq =>
    isZero_of_forall_isZero_stalk _ fun s => open Stacks.AlgebraicGeometry in
      FibreDimension.isZero_stalk_rightDerivedPlus_of_fiber_dimension_le_of_isQuasicoherent
        (toSpecGradeZero I) s (fibreDim I) (topologicalKrullDim_fiber_toSpecGradeZero_le I s) F
        (q : ℤ) (by lia)
  exact (Stacks.Cohomology.CechAcyclic.isZero_rightDerived_evaluation_iff_isZero_Hgroup
    (projGr I).ringCatSheaf ⊤ i F).2
    (Stacks.AlgebraicGeometry.LerayAffineBase.isZero_hgroup_of_isZero_rightDerivedPlus
      (toSpecGradeZero I) (fibreDim I + 1) F hvan i (by lia) (by lia))

/-- If the blowup is empty then `d(S) = 0`: every fibre is empty. -/
theorem fibreDim_eq_zero_of_isEmpty (h : IsEmpty (Stacks.Blowup.blowUpSpec I)) :
    fibreDim I = 0 := by
  refine Nat.le_zero.mp (fibreDim_le I fun s => ?_)
  have : IsEmpty ((Stacks.Blowup.toSpec I).fiber s) :=
    ⟨fun x => h.false ((Stacks.Blowup.toSpec I).fiberι s x)⟩
  rw [TopologicalSpace.topologicalKrullDim_eq_iSup_localKrullDim]
  exact iSup_le fun x => isEmptyElim x

/-- **The invariants `d(S)` and `q(S)` of [Stacks, Tag 0GA6].** Let `A` be a Noetherian ring,
`I ⊆ A` an ideal, `p : X → Spec(A)` the blowing up in `I`, and `Y = Proj(S)`,
`S = Gr_I(A) = ⨁ Iⁿ/Iⁿ⁺¹`. Then:

1. `d = d(S)`, the maximal fibre dimension of `Y → Spec(S₀)` (`AssociatedGraded.dInvariant`), is
   the natural number `fibreDim I`, which is the maximum of the dimensions of the fibres of `p`
   (bounded by it, and least such), and is `0` if `X = ∅`;
2. `d ≤ t - 1` if `I` is generated by `t` elements;
3. `Hⁱ(X, ℱ) = 0` for every quasi-coherent `𝒪_X`-module `ℱ` and `i > d`, and likewise
   `Hⁱ(Y, ℱ) = 0` for every quasi-coherent `𝒪_Y`-module `ℱ` and `i > d`;
4. `d = 0` if `I = A`;
5. `q(S)` (`AssociatedGraded.qInvariant`) is the smallest `q₀ ≥ 0` such that for all `q ≥ q₀`
   one has `Hⁱ(Y, 𝒪_Y(q)) = 0` for `1 ≤ i ≤ d` and `H⁰(Y, 𝒪_Y(q)) = I^q/I^{q+1}`; in particular
   such a `q₀` exists;
6. `q(S) = 0` if `I = A`. -/
@[stacks 0GA6 "the integers d = d(Gr_I(A)) and q = q(Gr_I(A)) of the section for a Noetherian \
ring A and an ideal I: d is the maximal fibre dimension of Proj(Gr_I(A)) → Spec(A/I), a natural \
number equal to the maximum of the fibre dimensions of the blowup X → Spec(A) (0 if X is empty), \
at most t - 1 when I has t generators, and above which the cohomology of every quasi-coherent \
module on X and on Y = Proj(Gr_I(A)) vanishes; q is the least q₀ ≥ 0 such that for all q ≥ q₀, \
Hⁱ(Y, 𝒪_Y(q)) = 0 for 1 ≤ i ≤ d and H⁰(Y, 𝒪_Y(q)) = I^q/I^{q+1}, and such a q₀ exists; both are \
0 when I = A"]
theorem dInvariant_qInvariant_spec [IsNoetherianRing A] :
    dInvariant I = (fibreDim I : ℕ∞) ∧
      (∀ s : Spec (CommRingCat.of A),
        topologicalKrullDim ((Stacks.Blowup.toSpec I).fiber s) ≤ (fibreDim I : WithBot ℕ∞)) ∧
      (∀ D : ℕ, (∀ s : Spec (CommRingCat.of A),
        topologicalKrullDim ((Stacks.Blowup.toSpec I).fiber s) ≤ (D : WithBot ℕ∞)) →
          fibreDim I ≤ D) ∧
      (IsEmpty (Stacks.Blowup.blowUpSpec I) → fibreDim I = 0) ∧
      (∀ (t : ℕ) (g : Fin t → A), I = Ideal.span (Set.range g) → fibreDim I ≤ t - 1) ∧
      (∀ (F : (blowupScheme I).Modules) [F.IsQuasicoherent] (i : ℕ), fibreDim I < i →
        Subsingleton (blowupHmod I i F)) ∧
      (∀ (F : (projGr I).Modules) [F.IsQuasicoherent] (i : ℕ), fibreDim I < i →
        IsZero (((Stacks.Cohomology.sectionsFunctor (projGr I) ⊤).rightDerived i).obj F)) ∧
      (I = ⊤ → dInvariant I = 0) ∧
      IsLeast {q₀ : ℕ | ∀ q : ℕ, q₀ ≤ q → IsRegularDegree I q} (qInvariant I) ∧
      (I = ⊤ → qInvariant I = 0) := by
  obtain ⟨q₀, hq₀⟩ := exists_forall_isRegularDegree I
  refine ⟨dInvariant_eq_fibreDim I, topologicalKrullDim_fiber_le_fibreDim I, fun D => fibreDim_le I,
    fibreDim_eq_zero_of_isEmpty I, fun t g hg => fibreDim_le I fun s => ?_,
    fun F _ i hi => subsingleton_blowupHmod_of_fibreDim_lt I F hi,
    fun F _ i hi => isZero_projGr_cohomology_of_fibreDim_lt I F hi,
    dInvariant_eq_zero_of_eq_top I,
    ⟨fun _ hq => isRegularDegree_of_qInvariant_le I ⟨q₀, hq₀⟩ hq, fun _ h => qInvariant_le I h⟩,
    qInvariant_eq_zero_of_eq_top I⟩
  exact Stacks.Blowup.topologicalKrullDim_fiber_toSpec_le_sub_one I g hg s

end Stacks.LocalCohomology.UniformityIII

end
