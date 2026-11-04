module

public import StacksFrontier.AlgebraicGeometry.Duality.ClosedImmersionSheafHomRestriction
public import StacksFrontier.AlgebraicGeometry.Duality.ClosedImmersionUpperShriekDualizing
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.NormalizedDualizingConstruction
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.ExceptionalCurveSections
public import StacksFrontier.AlgebraicGeometry.Blowup.AffineBlowUpProjective
public import StacksFrontier.AlgebraicGeometry.Duality.ProjectiveSpace.DualizingTwistChart
public import StacksFrontier.AlgebraicGeometry.Duality.ProjectiveSpace.TwistedInverseImageStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.PullbackComparisonUnconditional
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.Flat
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentCompactDualizable
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.FlatPullbackTensorSingle
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.TwistByInvertible
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceSectionMultiplication
public import StacksFrontier.AlgebraicGeometry.Modules.CoherentPullbackPushforward

/-!
# `f^!(ω_A)` is dualizing when the modification factors through a closed immersion

In Situation [Stacks, Tag 0B4W], let `ω_A` be a dualizing module of `A` and suppose the
modification `f : X ⟶ Spec(A)` factors as a closed immersion `i : X ⟶ P` followed by a
quasi-compact quasi-separated `p : P ⟶ Spec(A)` with `P` locally Noetherian and quasi-compact.
If `p^!(ω_A)` is a bounded-below dualizing complex on `P`, then so is `f^!(ω_A)` on `X`: the
twisted inverse images compose, `f^! ≅ i^! ∘ p^!`, and `i^!` preserves dualizing complexes
(`Stacks.Duality.ClosedImmersionRestriction.isDualizingComplex_rightAdjoint_of_isClosedImmersion`).

For `P = ℙⁿ_A` this is the route of the source: a blowup of `Spec(A)` is a closed subscheme of a
projective space over `A`, and `p^!(ω_A) = p^*ω_A(-n-1)[n]` by [Stacks, Tag 0A9W] and
[Stacks, Tag 0A9U].

## Main results

All names are in the namespace `AlgebraicGeometry.RationalSingularitySituation`.

* `isDualizingComplex_relativeDualizingComplex_blowUp`: for every Situation 0B4W and dualizing
  module `ω_A`, `f^!(ω_A)` is a dualizing complex on the blowup of `Spec(A)` in the maximal ideal.
* `dualizingNormalizationBlowUp`: the dualizing module of the blowup normalized relative to `ω_A`
  ([Stacks, Remark 0B4R]).
* `isDualizingComplex_relativeDualizingComplex_of_comp` and
  `isDualizingComplex_relativeDualizingComplex_of_isProjectiveMorphism`: the reduction of
  `f^!(ω_A)` dualizing to `p^!(ω_A)` dualizing, for `f = i ≫ p` with `i` a closed immersion.
* `isProjectiveMorphism_f_rationalSingularitySituationBlowUp`: the blowup of `Spec(A)` in the
  maximal ideal is H-projective.
* `isDualizingComplex_twistedInverseImage_projectiveSpaceOver_of_isos`: `p^!(ω_A)` is dualizing
  on `ℙ^{m+1}_A` from the formulas of [Stacks, Tag 0A9U] and [Stacks, Tag 0A9W].
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory Stacks.Duality.ClosedImmersionRestriction

universe u

namespace AlgebraicGeometry.RationalSingularitySituation

variable (S : RationalSingularitySituation.{u}) (ωA : ModuleCat.{u} S.A)

/-- **`f^!(ω_A)` is dualizing when `f` factors through a closed immersion into a scheme on which
the twisted inverse image of `ω_A` is a bounded-below dualizing complex.** -/
theorem isDualizingComplex_relativeDualizingComplex_of_comp {P : Scheme.{u}} (i : S.X ⟶ P)
    [IsClosedImmersion i] (p : P ⟶ S.base) [QuasiCompact p] [QuasiSeparated p] [CompactSpace P]
    [IsLocallyNoetherian P] (hip : i ≫ p = S.f)
    (hb : letI := isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward p
      DerivedCategoryB.IsBoundedBelow
        ((Stacks.Duality.twistedInverseImage p
          (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs p)).obj
            (S.baseDualizingComplex ωA)).obj)
    (hK : letI := isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward p
      Stacks.Duality.IsDualizingComplex
        ((Stacks.Duality.twistedInverseImage p
          (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs p)).obj
            (S.baseDualizingComplex ωA)).obj) :
    Stacks.Duality.IsDualizingComplex (S.relativeDualizingComplex ωA).obj := by
  let := isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward (i ≫ p)
  have h := isDualizingComplex_twistedInverseImage_comp_of_isClosedImmersion i p
    (S.baseDualizingComplex ωA) hb hK
  exact (isDualizingComplex_twistedInverseImage_congr hip
    _ _ (S.baseDualizingComplex ωA)).1 h

/-- If `f` factors through a closed immersion into `ℙⁿ_A` and `p^!(ω_A)` is dualizing there, then
`f^!(ω_A)` is dualizing. -/
private theorem isDualizing_of_closedImmersion_projective
    (n : ℕ) (i : S.X ⟶ projectiveSpaceOver n S.base) [IsClosedImmersion i]
    (hip : i ≫ (projectiveSpaceOver n S.base ↘ S.base) = S.f)
    (hP :
      haveI : IsLocallyNoetherian (projectiveSpaceOver n S.base) :=
        LocallyOfFiniteType.isLocallyNoetherian (projectiveSpaceOver n S.base ↘ S.base)
      letI := isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward
        (projectiveSpaceOver n S.base ↘ S.base)
      Stacks.Duality.IsDualizingComplex
        ((Stacks.Duality.twistedInverseImage (projectiveSpaceOver n S.base ↘ S.base)
          (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj
            (S.baseDualizingComplex ωA)).obj) :
    Stacks.Duality.IsDualizingComplex (S.relativeDualizingComplex ωA).obj := by
  have : IsLocallyNoetherian (projectiveSpaceOver n S.base) :=
    LocallyOfFiniteType.isLocallyNoetherian (projectiveSpaceOver n S.base ↘ S.base)
  have : CompactSpace (projectiveSpaceOver n S.base) :=
    QuasiCompact.compactSpace_of_compactSpace (projectiveSpaceOver n S.base ↘ S.base)
  exact S.isDualizingComplex_relativeDualizingComplex_of_comp ωA i _ hip
    (Stacks.Duality.isBoundedBelow_of_isDualizingComplex _ hP) hP

/-- **The blowup of `Spec(A)` in its maximal ideal is H-projective**: it is a closed subscheme of
a projective space over `A`, over `A`
(`Stacks.Blowup.isProjectiveMorphism_blowUpToBase_ofIdealTop`, the maximal ideal being finitely
generated). -/
theorem isProjectiveMorphism_f_rationalSingularitySituationBlowUp :
    IsProjectiveMorphism (rationalSingularitySituationBlowUp S).f := by
  have key := Stacks.Blowup.isProjectiveMorphism_blowUpToBase_ofIdealTop
    (IsLocalRing.maximalIdeal S.A) (IsNoetherian.noetherian _)
  rw [← AlgebraicGeometry.ker_residuePoint_eq_ofIdealTop_map] at key
  exact key

/-- **`f^!(ω_A)` is dualizing for an H-projective modification**, given that on every projective
space `ℙⁿ_A` the twisted inverse image of `ω_A` along the structure morphism is a dualizing
complex. Boundedness below of the latter is automatic, `ℙⁿ_A` being quasi-compact
(`Stacks.Duality.isBoundedBelow_of_isDualizingComplex`). -/
theorem isDualizingComplex_relativeDualizingComplex_of_isProjectiveMorphism
    (hf : IsProjectiveMorphism S.f)
    (hP : ∀ n : ℕ,
      haveI : IsLocallyNoetherian (projectiveSpaceOver n S.base) :=
        LocallyOfFiniteType.isLocallyNoetherian (projectiveSpaceOver n S.base ↘ S.base)
      letI := isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward
        (projectiveSpaceOver n S.base ↘ S.base)
      Stacks.Duality.IsDualizingComplex
        ((Stacks.Duality.twistedInverseImage (projectiveSpaceOver n S.base ↘ S.base)
          (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj
            (S.baseDualizingComplex ωA)).obj) :
    Stacks.Duality.IsDualizingComplex (S.relativeDualizingComplex ωA).obj := by
  obtain ⟨n, i, hi, hip⟩ := hf
  have := hi
  exact S.isDualizing_of_closedImmersion_projective ωA n i
    hip (hP n)

/-! ### The twisted inverse image of `ω_A` on projective space -/

section ProjectiveSpace

open Stacks.AlgebraicGeometry.ProjTwistTensorPow (twistOver)
open CategoryTheory.Limits

variable {A : CommRingCat.{u}} [IsNoetherianRing A] (m : ℕ)

/-- [Stacks, Tag 0A9E] for `ℙ^{m+1}_A ⟶ Spec A`, as a local instance. -/
local instance :
    (Stacks.Duality.quasiCoherentDerivedPushforward (projectiveSpaceOver (m + 1) (Spec A) ↘ Spec A)
      (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs _)).IsLeftAdjoint :=
  isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward _

/-- `ℙ^{m+1}_A` is locally Noetherian, being of finite type over `A`. -/
local instance : IsLocallyNoetherian (projectiveSpaceOver (m + 1) (Spec A)) :=
  LocallyOfFiniteType.isLocallyNoetherian (projectiveSpaceOver (m + 1) (Spec A) ↘ Spec A)

/-- **`p^!(ω_A)` is dualizing on `ℙ^{m+1}_A`, from the formula `p^!(K) ≅ Lp^*K ⊗ᴸ p^!(𝒪)` and the
computation `p^!(𝒪) ≅ 𝒪(-m-2)[m+1]`.** These are [Stacks, Tag 0A9U] and [Stacks, Tag 0A9W] for
`p : ℙ^{m+1}_A ⟶ Spec A`, entering as the isomorphisms `e₁` and `e₂`. Given them,
`p^!(ω̃_A[0]) ≅ (p^*ω̃_A ⊗ 𝒪(-m-2))[m+1]`
(`Stacks.Duality.derivedPullbackSingleTensorSingleIso`, `𝒪(-m-2)` being invertible hence flat),
which is dualizing by
`Stacks.Duality.ProjectiveSpace.isDualizingComplex_singleFunctor_pullback_tensor_twistOver`. -/
theorem isDualizingComplex_twistedInverseImage_projectiveSpaceOver_of_isos
    (ωA : ModuleCat.{u} A) (hωA : Stacks.Duality.IsDualizingRingModule A ωA)
    (K : Stacks.Duality.quasiCoherentDerivedCategory (Spec A))
    (hK : K.obj = (DerivedCategory.singleFunctor _ 0).obj ((tilde.functor A).obj ωA))
    (E₀ : Stacks.Duality.quasiCoherentDerivedCategory (projectiveSpaceOver (m + 1) (Spec A)))
    (hE₀ : E₀.obj = (shiftFunctor _ ((m + 1 : ℕ) : ℤ)).obj ((DerivedCategory.singleFunctor _ 0).obj
      (twistOver (m + 1) (Spec A) (-((m + 1 : ℕ) : ℤ) - 1))))
    (e₁ : (Stacks.Duality.twistedInverseImage (projectiveSpaceOver (m + 1) (Spec A) ↘ Spec A)
          (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj K ≅
        ((Stacks.Duality.quasiCoherentDerivedTensor _).obj
          ((Stacks.Duality.quasiCoherentDerivedPullback'
            (projectiveSpaceOver (m + 1) (Spec A) ↘ Spec A)).obj K)).obj
          ((Stacks.Duality.twistedInverseImage (projectiveSpaceOver (m + 1) (Spec A) ↘ Spec A)
            (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj
              (Stacks.Duality.DerivedPushforward.derivedStructureSheaf (Spec A))))
    (e₂ : (Stacks.Duality.twistedInverseImage (projectiveSpaceOver (m + 1) (Spec A) ↘ Spec A)
          (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj
            (Stacks.Duality.DerivedPushforward.derivedStructureSheaf (Spec A)) ≅ E₀) :
    Stacks.Duality.IsDualizingComplex
      ((Stacks.Duality.twistedInverseImage (projectiveSpaceOver (m + 1) (Spec A) ↘ Spec A)
        (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj K).obj := by
  set p := projectiveSpaceOver (m + 1) (Spec A) ↘ Spec A
  set L := twistOver (m + 1) (Spec A) (-((m + 1 : ℕ) : ℤ) - 1)
  have : PreservesFiniteLimits (Scheme.Modules.pullback p) :=
    AlgebraicGeometry.preservesFiniteLimits_modulesPullback_of_flat p
  have hL := Stacks.Chow.isFlat_of_isInvertible L
  have eS : E₀.obj ≅ (DerivedCategory.singleFunctor _ (-((m + 1 : ℕ) : ℤ))).obj L :=
    eqToIso hE₀ ≪≫
      ((DerivedCategory.singleFunctors _).shiftIso ((m + 1 : ℕ) : ℤ) (-((m + 1 : ℕ) : ℤ)) 0
        (by omega)).app L
  have e : ((Stacks.Duality.twistedInverseImage p
      (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj K).obj ≅
        (DerivedCategory.singleFunctor _ (-((m + 1 : ℕ) : ℤ))).obj
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            (projectiveSpaceOver (m + 1) (Spec A)).toRingedSpace.sheaf).obj
              ((Scheme.Modules.pullback p).obj ((tilde.functor A).obj ωA))).obj L) :=
    (ObjectProperty.ι _).mapIso e₁ ≪≫
      (ObjectProperty.ι _).mapIso
        (((Stacks.Duality.quasiCoherentDerivedTensor _).obj
          ((Stacks.Duality.quasiCoherentDerivedPullback' p).obj K)).mapIso e₂) ≪≫
      ((Stacks.Duality.derivedTensor _).mapIso
        ((Stacks.Duality.derivedPullback p).mapIso (eqToIso hK))).app E₀.obj ≪≫
      ((Stacks.Duality.derivedTensor _).obj _).mapIso eS ≪≫
      Stacks.Duality.derivedPullbackSingleTensorSingleIso p _ L hL _
  exact Stacks.Duality.isDualizingComplex_of_iso e.symm
    (Stacks.Duality.ProjectiveSpace.isDualizingComplex_singleFunctor_pullback_tensor_twistOver
      (m + 1) ωA hωA _ _)

end ProjectiveSpace

/-- **`f^!(ω_A)` is dualizing for the blowup of `Spec(A)` in the maximal ideal**, given that on
every projective space `ℙ^{m+1}_A` of positive dimension the twisted inverse image of `ω_A` is a
dualizing complex. The blowup is a closed subscheme of such a projective space over `A`
(`Stacks.Blowup.exists_isClosedImmersion_projectiveSpaceOver_succ_blowUpToBase`). -/
theorem isDualizingComplex_relativeDualizingComplex_rationalSingularitySituationBlowUp
    (hP : ∀ m : ℕ,
      haveI : IsLocallyNoetherian (projectiveSpaceOver (m + 1) S.base) :=
        LocallyOfFiniteType.isLocallyNoetherian (projectiveSpaceOver (m + 1) S.base ↘ S.base)
      letI := isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward
        (projectiveSpaceOver (m + 1) S.base ↘ S.base)
      Stacks.Duality.IsDualizingComplex
        ((Stacks.Duality.twistedInverseImage (projectiveSpaceOver (m + 1) S.base ↘ S.base)
          (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj
            (S.baseDualizingComplex ωA)).obj) :
    Stacks.Duality.IsDualizingComplex
      ((rationalSingularitySituationBlowUp S).relativeDualizingComplex ωA).obj := by
  have key : ∃ (m : ℕ) (i : blowUp (Stacks.Blowup.residuePoint S.A).ker ⟶
      projectiveSpaceOver (m + 1) S.base), IsClosedImmersion i ∧
        i ≫ (projectiveSpaceOver (m + 1) S.base ↘ S.base) =
          blowUpToBase (Stacks.Blowup.residuePoint S.A).ker := by
    rw [AlgebraicGeometry.ker_residuePoint_eq_ofIdealTop_map]
    exact Stacks.Blowup.exists_isClosedImmersion_projectiveSpaceOver_succ_blowUpToBase
      (IsLocalRing.maximalIdeal S.A) (IsNoetherian.noetherian _)
  obtain ⟨m, i, hi, hip⟩ := key
  let i' : (rationalSingularitySituationBlowUp S).X ⟶
    projectiveSpaceOver (m + 1) (rationalSingularitySituationBlowUp S).base := i
  have : IsClosedImmersion i' := hi
  exact (rationalSingularitySituationBlowUp S).isDualizing_of_closedImmersion_projective ωA
    (m + 1) i' hip (hP m)

open Stacks.AlgebraicGeometry.ProjTwistTensorPow (twistOver) in
/-- **E1 in the shape `0BBV` consumes, over the two projective-space inputs.** For every
Situation 0B4W and every dualizing module `ω_A`, `f^!(ω_A)` is a dualizing complex on the blowup
of `Spec(A)` in the maximal ideal, given, on every `ℙ^{m+1}_A` (`A` Noetherian), the formula
`p^!(K) ≅ Lp^*K ⊗ᴸ p^!(𝒪)` of [Stacks, Tag 0A9U] (`h0A9U`) and `p^!(𝒪) ≅ 𝒪(-m-2)[m+1]` of
[Stacks, Tag 0A9W] (`h0A9W`). -/
theorem isDualizingComplex_relativeDualizingComplex_blowUp_of_projectiveSpace
    (h0A9U : ∀ (A : CommRingCat.{u}) [IsNoetherianRing A] (m : ℕ)
      (K : Stacks.Duality.quasiCoherentDerivedCategory (Spec A)),
      letI := isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward
        (projectiveSpaceOver (m + 1) (Spec A) ↘ Spec A)
      Nonempty ((Stacks.Duality.twistedInverseImage (projectiveSpaceOver (m + 1) (Spec A) ↘ Spec A)
          (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj K ≅
        ((Stacks.Duality.quasiCoherentDerivedTensor _).obj
          ((Stacks.Duality.quasiCoherentDerivedPullback'
            (projectiveSpaceOver (m + 1) (Spec A) ↘ Spec A)).obj K)).obj
          ((Stacks.Duality.twistedInverseImage (projectiveSpaceOver (m + 1) (Spec A) ↘ Spec A)
            (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj
              (Stacks.Duality.DerivedPushforward.derivedStructureSheaf (Spec A)))))
    (h0A9W : ∀ (A : CommRingCat.{u}) [IsNoetherianRing A] (m : ℕ),
      letI := isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward
        (projectiveSpaceOver (m + 1) (Spec A) ↘ Spec A)
      ∃ E₀ : Stacks.Duality.quasiCoherentDerivedCategory (projectiveSpaceOver (m + 1) (Spec A)),
        E₀.obj = (shiftFunctor _ ((m + 1 : ℕ) : ℤ)).obj ((DerivedCategory.singleFunctor _ 0).obj
          (twistOver (m + 1) (Spec A) (-((m + 1 : ℕ) : ℤ) - 1))) ∧
        Nonempty ((Stacks.Duality.twistedInverseImage
          (projectiveSpaceOver (m + 1) (Spec A) ↘ Spec A)
          (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj
            (Stacks.Duality.DerivedPushforward.derivedStructureSheaf (Spec A)) ≅ E₀))
    (S : RationalSingularitySituation.{u}) (ωA : ModuleCat.{u} S.A)
    (hωA : Stacks.Duality.IsDualizingRingModule S.A ωA) :
    Stacks.Duality.IsDualizingComplex
      ((rationalSingularitySituationBlowUp S).relativeDualizingComplex ωA).obj := by
  refine S.isDualizingComplex_relativeDualizingComplex_rationalSingularitySituationBlowUp ωA
    fun m => ?_
  obtain ⟨e₁⟩ := h0A9U (.of S.A) m (S.baseDualizingComplex ωA)
  obtain ⟨E₀, hE₀, ⟨e₂⟩⟩ := h0A9W (.of S.A) m
  exact isDualizingComplex_twistedInverseImage_projectiveSpaceOver_of_isos m ωA hωA
    (S.baseDualizingComplex ωA) rfl E₀ hE₀ e₁ e₂

open Stacks.AlgebraicGeometry.ProjTwistTensorPow (twistOver) in
/-- **[Stacks, Tag 0A9W] in the shape of the second input of
`isDualizingComplex_relativeDualizingComplex_blowUp_of_projectiveSpace`**:
`p^!(𝒪) ≅ 𝒪(-m-2)[m+1]` on `ℙ^{m+1}_A`, from
`Stacks.Duality.ProjectiveSpace.nonempty_twistedInverseImage_derivedStructureSheaf_iso`. -/
theorem exists_twistedInverseImage_derivedStructureSheaf_iso_shift (A : CommRingCat.{u})
    (m : ℕ) :
    letI := isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward
      (projectiveSpaceOver (m + 1) (Spec A) ↘ Spec A)
    ∃ E₀ : Stacks.Duality.quasiCoherentDerivedCategory (projectiveSpaceOver (m + 1) (Spec A)),
      E₀.obj = (shiftFunctor _ ((m + 1 : ℕ) : ℤ)).obj ((DerivedCategory.singleFunctor _ 0).obj
        (twistOver (m + 1) (Spec A) (-((m + 1 : ℕ) : ℤ) - 1))) ∧
      Nonempty ((Stacks.Duality.twistedInverseImage
        (projectiveSpaceOver (m + 1) (Spec A) ↘ Spec A)
        (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj
          (Stacks.Duality.DerivedPushforward.derivedStructureSheaf (Spec A)) ≅ E₀) :=
  ⟨Stacks.Duality.ProjectiveSpace.dualizingTwist (m + 1) (Spec A), rfl,
    Stacks.Duality.ProjectiveSpace.nonempty_twistedInverseImage_derivedStructureSheaf_iso
      (m + 1) (Spec A)⟩

/-- **[Stacks, Tag 0A9U] in the shape of the first input of
`isDualizingComplex_relativeDualizingComplex_blowUp_of_projectiveSpace`**, given that compact
objects of `D_QCoh(𝒪_{Spec A})` are dualizable: `p : ℙ^{m+1}_A ⟶ Spec A` is a perfect proper
morphism of Noetherian schemes, so the comparison `Lp^*K ⊗ᴸ p^!(𝒪) ⟶ p^!(K)` of
[Stacks, Tag 0A9S] is an isomorphism
(`Stacks.Duality.isIso_compareWithPullback_of_perfect_of_isProper_of_hasRightDual`). -/
theorem nonempty_twistedInverseImage_iso_tensor_of_hasRightDual (A : CommRingCat.{u})
    [IsNoetherianRing A] (m : ℕ)
    (hdual : ∀ K : Stacks.Duality.quasiCoherentDerivedCategory (Spec A),
      IsCompactObject.{u} K →
        Nonempty (@HasRightDual _ _ (Stacks.Duality.quasiCoherentDerivedMonoidal (Spec A)) K))
    (K : Stacks.Duality.quasiCoherentDerivedCategory (Spec A)) :
    letI := isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward
      (projectiveSpaceOver (m + 1) (Spec A) ↘ Spec A)
    Nonempty ((Stacks.Duality.twistedInverseImage (projectiveSpaceOver (m + 1) (Spec A) ↘ Spec A)
        (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj K ≅
      ((Stacks.Duality.quasiCoherentDerivedTensor _).obj
        ((Stacks.Duality.quasiCoherentDerivedPullback'
          (projectiveSpaceOver (m + 1) (Spec A) ↘ Spec A)).obj K)).obj
        ((Stacks.Duality.twistedInverseImage (projectiveSpaceOver (m + 1) (Spec A) ↘ Spec A)
          (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj
            (Stacks.Duality.DerivedPushforward.derivedStructureSheaf (Spec A)))) := by
  let := isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward
    (projectiveSpaceOver (m + 1) (Spec A) ↘ Spec A)
  set p := projectiveSpaceOver (m + 1) (Spec A) ↘ Spec A
  have : IsProper p := isProper_projectiveSpaceOver _ _
  have : IsLocallyNoetherian (projectiveSpaceOver (m + 1) (Spec A)) :=
    LocallyOfFiniteType.isLocallyNoetherian p
  have : CompactSpace (projectiveSpaceOver (m + 1) (Spec A)) :=
    QuasiCompact.compactSpace_of_compactSpace p
  have : IsNoetherian (projectiveSpaceOver (m + 1) (Spec A)) := ⟨⟩
  have := fun E K => Stacks.Duality.isIso_projectionFormulaMap_pullbackCotensorator_of_hasRightDual
    p (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs p) hdual E K
  have := Stacks.Duality.isIso_compareWithPullback_of_perfect_of_isProper_of_hasRightDual p hdual
    (Stacks.Duality.twistedInverseImageAdjunction p _) K
  exact ⟨(asIso (Stacks.Duality.compareWithPullback p _ (Stacks.Duality.pullbackCotensorator p)
    (Stacks.Duality.twistedInverseImageAdjunction p _) Stacks.Duality.quasiCoherentRightUnitor
      K)).symm⟩

/-- **E1 in the shape `0BBV` consumes, over the dualizability of compact objects of
`D_QCoh(𝒪_{Spec A})`** for Noetherian `A`, which is the last input of the unconditional
[Stacks, Tag 0A9U]. -/
theorem isDualizingComplex_relativeDualizingComplex_blowUp_of_hasRightDual
    (hdual : ∀ (A : CommRingCat.{u}) [IsNoetherianRing A]
      (K : Stacks.Duality.quasiCoherentDerivedCategory (Spec A)), IsCompactObject.{u} K →
        Nonempty (@HasRightDual _ _ (Stacks.Duality.quasiCoherentDerivedMonoidal (Spec A)) K))
    (S : RationalSingularitySituation.{u}) (ωA : ModuleCat.{u} S.A)
    (hωA : Stacks.Duality.IsDualizingRingModule S.A ωA) :
    Stacks.Duality.IsDualizingComplex
      ((rationalSingularitySituationBlowUp S).relativeDualizingComplex ωA).obj :=
  isDualizingComplex_relativeDualizingComplex_blowUp_of_projectiveSpace
    (fun A _ m K => nonempty_twistedInverseImage_iso_tensor_of_hasRightDual A m (hdual A) K)
    (fun A _ m => exists_twistedInverseImage_derivedStructureSheaf_iso_shift A m) S ωA hωA

/-- **E1: `f^!(ω_A)` is a dualizing complex on the blowup of `Spec(A)` in the maximal ideal**, for
every Situation [Stacks, Tag 0B4W] and every dualizing module `ω_A` of `A`. This is
[Stacks, Tag 0AA3] for the blowup `f : X ⟶ Spec(A)`, obtained by the source's projective route:
`X ⊆ ℙ^{m+1}_A` (`isProjectiveMorphism_f_rationalSingularitySituationBlowUp` and its
positive-dimensional form), `f^! = i^! ∘ p^!`, `p^!(ω_A) = p^*ω_A(-m-2)[m+1]` by
[Stacks, Tag 0A9U] and [Stacks, Tag 0A9W], which is dualizing by the chart computation and
[Stacks, Tag 0A7J], and `i^!` preserves dualizing complexes. -/
theorem isDualizingComplex_relativeDualizingComplex_blowUp
    (S : RationalSingularitySituation.{u}) (ωA : ModuleCat.{u} S.A)
    (hωA : Stacks.Duality.IsDualizingRingModule S.A ωA) :
    Stacks.Duality.IsDualizingComplex
      ((rationalSingularitySituationBlowUp S).relativeDualizingComplex ωA).obj :=
  isDualizingComplex_relativeDualizingComplex_blowUp_of_hasRightDual
    (fun A _ K hK => Stacks.Duality.nonempty_hasRightDual_of_isCompactObject (Spec A) K hK)
    S ωA hωA

/-- **The dualizing module of the blowup normalized relative to `ω_A`** ([Stacks, Remark 0B4R]),
unconditionally: `H⁰(f^!(ω_A))` together with its normalization `f^!(ω_A) ≅ H⁰(f^!(ω_A))[0]`. -/
def dualizingNormalizationBlowUp (S : RationalSingularitySituation.{u}) {ωA : ModuleCat.{u} S.A}
    (hωA : Stacks.Duality.IsDualizingRingModule S.A ωA) :
    (rationalSingularitySituationBlowUp S).DualizingNormalization ωA
      ((rationalSingularitySituationBlowUp S).normalizedDualizingSheaf ωA) :=
  (rationalSingularitySituationBlowUp S).dualizingNormalizationOfIsDualizingComplex hωA
    (isDualizingComplex_relativeDualizingComplex_blowUp S ωA hωA)

end AlgebraicGeometry.RationalSingularitySituation

end
