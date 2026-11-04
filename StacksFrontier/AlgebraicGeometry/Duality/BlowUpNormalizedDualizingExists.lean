module

public import StacksFrontier.AlgebraicGeometry.Duality.ProjectiveSpaceCoefficient.ClosedSubschemeDualizing
public import StacksFrontier.AlgebraicGeometry.Duality.ProjectiveSpaceCoefficient.GqcDualizing
public import StacksFrontier.AlgebraicGeometry.Duality.ClosedImmersionDualizing
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.NormalizedDualizingConstruction
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.ExceptionalCurveSections
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.BlowUpDualizing
public import StacksFrontier.AlgebraicGeometry.Blowup.AffineBlowUpComparison
public import StacksFrontier.AlgebraicGeometry.Blowup.ProjectiveSpaceEmbedding
public import StacksFrontier.AlgebraicGeometry.Blowup.ProjectivePushforwardTruncation
public import StacksFrontier.AlgebraicGeometry.Modules.TildeExactness
public import StacksFrontier.Homology.PseudoCoherentRelative.TildeExact

/-!
# The normalized dualizing module of the blowup of a rational surface singularity

In Situation [Stacks, Tag 0B4W] let `X` be the blowup of `Spec A` in the maximal ideal and `ω_A`
a dualizing module of `A`. The blowup is a closed subscheme of `ℙⁿ_A` over `A`
(`AlgebraicGeometry.BlowUpDualizing.exists_closedImmersion_blowUp_projSpace`), so its twisted
inverse image `f^!(ω_A)` is `i^×((𝒪(-n-1) ⊗ p^*ω~_A)[n])`
(`Stacks.Duality.ProjCoeff.isDualizingComplex_of_closedImmersion_projSpace_of`), a dualizing
complex as soon as `(𝒪(-n-1) ⊗ p^*ω~_A)[n]` is one on `ℙⁿ_A` and `i^×` preserves dualizing
complexes. Remark 0B4R (`dualizingNormalizationOfIsDualizingComplex`) then produces the dualizing
module `ω_X` normalized relative to `ω_A`.

## Main results

* `AlgebraicGeometry.BlowUpDualizing.exists_closedImmersion_blowUp_projSpace`.
* `AlgebraicGeometry.BlowUpDualizing.isDualizingComplex_relativeDualizingComplex_blowUp_of`.
* `AlgebraicGeometry.BlowUpDualizing.exists_dualizingNormalization_blowUp_of`.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry.ProjPolyChart Stacks.Duality.ProjCoeff

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.BlowUpDualizing

/-- **The blowup of a Noetherian local ring in its maximal ideal is a closed subscheme of some
`ℙⁿ_A`, over `Spec A`.** -/
theorem exists_closedImmersion_blowUp_projSpace (A : Type u) [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] :
    ∃ (n : ℕ) (i : blowUp (Stacks.Blowup.residuePoint A).ker ⟶ P A n), IsClosedImmersion i ∧
      i ≫ projToSpecCoeff A n = blowUpToBase (Stacks.Blowup.residuePoint A).ker := by
  classical
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian (IsLocalRing.maximalIdeal A) :
    (IsLocalRing.maximalIdeal A).FG)
  let x : Fin (s.card + 1) → A := Fin.cons 0 (fun i => (s.equivFin.symm i : A))
  have hrange : Set.range x = insert 0 (s : Set A) := by
    ext a
    simp only [Set.mem_range, Set.mem_insert_iff, Finset.mem_coe]
    constructor
    · rintro ⟨i, rfl⟩
      refine Fin.cases (Or.inl rfl) (fun j => Or.inr ?_) i
      simp [x]
    · rintro (rfl | ha)
      · exact ⟨0, rfl⟩
      · exact ⟨Fin.succ (s.equivFin ⟨a, ha⟩), by simp [x]⟩
  have hspan : IsLocalRing.maximalIdeal A = Ideal.span (Set.range x) := by
    rw [hrange, Ideal.span_insert_zero, ← hs]
  have hx : ∀ i, x i ∈ IsLocalRing.maximalIdeal A := fun i => by
    rw [hspan]
    exact Ideal.subset_span ⟨i, rfl⟩
  obtain ⟨e⟩ := Stacks.Blowup.nonempty_over_iso_blowUpToBase A (IsLocalRing.maximalIdeal A)
  rw [← ker_residuePoint_eq_ofIdealTop_map] at e
  refine ⟨s.card, e.inv.left ≫ Stacks.Blowup.blowUpSpecToProjSpace _ x hx hspan,
    inferInstance, ?_⟩
  rw [Category.assoc, ← Stacks.Blowup.projSpaceToSpec_eq_projToSpecCoeff,
    Stacks.Blowup.blowUpSpecToProjSpace_comp_projSpaceToSpec]
  exact Over.w e.inv

variable (S : RationalSingularitySituation.{u})

/-- `M~ ≅ M~[0]`: the derived sheafification of `ω_A[0]` is the base dualizing complex of the
situation. -/
def mqcIsoBaseDualizingComplex (ωA : ModuleCat.{u} S.A) :
    Mqc S.A ωA ≅ (rationalSingularitySituationBlowUp S).baseDualizingComplex ωA :=
  haveI : (tilde.functor (CommRingCat.of S.A)).Additive := ⟨fun {_ _} f g => tilde.map_add f g⟩
  haveI := AlgebraicGeometry.tilde.preservesFiniteLimits (CommRingCat.of S.A)
  haveI := Stacks.AffineTilde.preservesFiniteColimits_tildeFunctor (CommRingCat.of S.A)
  ObjectProperty.isoMk _
    (((tilde.functor (CommRingCat.of S.A)).mapDerivedCategorySingleFunctor 0).app ωA)

/-- **`f^!(ω_A)` is a dualizing complex on the blowup**, given that the right adjoint of `Ri_*`
along a closed immersion preserves dualizing complexes (`hcl`); `(𝒪(-n-1) ⊗ p^*ω~_A)[n]` is a
dualizing complex on `ℙⁿ_A` by `Stacks.Duality.ProjCoeff.isDualizingComplex_Gqc`. -/
theorem isDualizingComplex_relativeDualizingComplex_blowUp_of (ωA : ModuleCat.{u} S.A)
    (hωA : Stacks.Duality.IsDualizingRingModule S.A ωA)
    (hcl : ∀ {Z W : Scheme.{u}} [IsLocallyNoetherian W] [IsLocallyNoetherian Z] (i : Z ⟶ W)
      [IsClosedImmersion i]
      (a : Stacks.Duality.quasiCoherentDerivedCategory W ⥤
        Stacks.Duality.quasiCoherentDerivedCategory Z)
      (_ : Stacks.Duality.LocallySmall.affineHomQuasiCoherentDerivedPushforward i ⊣ a)
      (K : Stacks.Duality.quasiCoherentDerivedCategory W),
      Stacks.Duality.IsDualizingComplex K.obj → Stacks.Duality.IsDualizingComplex (a.obj K).obj) :
    letI : IsLocallyNoetherian (rationalSingularitySituationBlowUp S).X :=
      isLocallyNoetherian_blowUpScheme S.A
    Stacks.Duality.IsDualizingComplex
      ((rationalSingularitySituationBlowUp S).relativeDualizingComplex ωA).obj := by
  let : IsLocallyNoetherian (rationalSingularitySituationBlowUp S).X :=
    isLocallyNoetherian_blowUpScheme S.A
  obtain ⟨n, i, _, hfac⟩ := exists_closedImmersion_blowUp_projSpace S.A
  let S' := rationalSingularitySituationBlowUp S
  have : IsLocallyNoetherian (blowUp (Stacks.Blowup.residuePoint S.A).ker) :=
    isLocallyNoetherian_blowUpScheme S.A
  have hqc := Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs S'.f
  have h := isDualizingComplex_of_closedImmersion_projSpace_of n ωA
    (isDualizingComplex_Gqc S.A n ωA hωA)
    (X := blowUp (Stacks.Blowup.residuePoint S.A).ker) S'.f i
    hfac (fun a adj K hK => hcl i a adj K hK) hqc
    (Stacks.Duality.twistedInverseImage S'.f hqc)
    (Stacks.Duality.twistedInverseImageAdjunction S'.f hqc)
  exact Stacks.Duality.isDualizingComplex_of_iso ((ObjectProperty.ι _).mapIso
    ((Stacks.Duality.twistedInverseImage S'.f hqc).mapIso
      (mqcIsoBaseDualizingComplex S ωA))) h

/-- **The dualizing module of the blowup normalized relative to `ω_A` exists**, given the input
`hcl` of `isDualizingComplex_relativeDualizingComplex_blowUp_of`. -/
theorem exists_dualizingNormalization_blowUp_of (ωA : ModuleCat.{u} S.A)
    (hωA : Stacks.Duality.IsDualizingRingModule S.A ωA)
    (hcl : ∀ {Z W : Scheme.{u}} [IsLocallyNoetherian W] [IsLocallyNoetherian Z] (i : Z ⟶ W)
      [IsClosedImmersion i]
      (a : Stacks.Duality.quasiCoherentDerivedCategory W ⥤
        Stacks.Duality.quasiCoherentDerivedCategory Z)
      (_ : Stacks.Duality.LocallySmall.affineHomQuasiCoherentDerivedPushforward i ⊣ a)
      (K : Stacks.Duality.quasiCoherentDerivedCategory W),
      Stacks.Duality.IsDualizingComplex K.obj → Stacks.Duality.IsDualizingComplex (a.obj K).obj) :
    letI : IsLocallyNoetherian (rationalSingularitySituationBlowUp S).X :=
      isLocallyNoetherian_blowUpScheme S.A
    ∃ ωX : (blowUpScheme S.A).Modules,
      Nonempty ((rationalSingularitySituationBlowUp S).DualizingNormalization ωA ωX) := by
  let : IsLocallyNoetherian (rationalSingularitySituationBlowUp S).X :=
    isLocallyNoetherian_blowUpScheme S.A
  exact ⟨_, ⟨(rationalSingularitySituationBlowUp S).dualizingNormalizationOfIsDualizingComplex
    hωA (isDualizingComplex_relativeDualizingComplex_blowUp_of S ωA hωA hcl)⟩⟩

/-- **The dualizing module of the blowup normalized relative to `ω_A` exists.** In Situation
[Stacks, Tag 0B4W], for `ω_A` a dualizing module of `A`, the twisted inverse image `f^!(ω_A)`
along the blowup `f` of the maximal ideal is a coherent module `ω_X` in degree zero, and `ω_X` is
a dualizing module of the blowup ([Stacks, Remark 0B4R]). -/
theorem exists_dualizingNormalization_blowUp (ωA : ModuleCat.{u} S.A)
    (hωA : Stacks.Duality.IsDualizingRingModule S.A ωA) :
    letI : IsLocallyNoetherian (rationalSingularitySituationBlowUp S).X :=
      isLocallyNoetherian_blowUpScheme S.A
    ∃ ωX : (blowUpScheme S.A).Modules,
      Nonempty ((rationalSingularitySituationBlowUp S).DualizingNormalization ωA ωX) :=
  exists_dualizingNormalization_blowUp_of S ωA hωA fun i _ a adj K hK =>
    Stacks.Duality.LocallySmall.isDualizingComplex_of_closedImmersion i a adj K hK

end AlgebraicGeometry.BlowUpDualizing
