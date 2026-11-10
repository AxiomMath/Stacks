module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Lipman.DominatingStageLocalRings
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.CompleteLocalInduction
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.Reduction
public import StacksFrontier.FieldTheory.Separable.NoIntermediateField
public import StacksFrontier.RingTheory.IntegrallyClosed.Stability
public import StacksFrontier.RingTheory.Nagata.CompleteLocalRing

/-!
# The base case of the induction of Tag 0BGN

Let `R` be a two-dimensional regular complete local ring and `A` a Noetherian complete local
normal domain, finite over `R`, such that the extension of fraction fields has no intermediate
field other than its two ends. The source's proof of [Stacks, Tag 0BGN] resolves `Spec A` as
follows. The extension is separable, or purely inseparable of prime degree `p`; `R` defines a
rational singularity ([Stacks, Tag 0B4Q]), so reduction to rational singularities is possible
for `R` and therefore for `A` ([Stacks, Tags 0AXL and 0B4U]). By [Stacks, Tag 0B4P] a sequence
of normalized blowups `X ⟶ Spec A` has rational singularities at all its closed points; these
are finitely many and are resolved by
`AlgebraicGeometry.hasResolutionByNormalizedBlowUps_of_definesRationalSingularity`, and the
local resolutions assemble.

## Main results

* `AlgebraicGeometry.exists_isResolution_of_forall_eq_bot_or_eq_top`: the step `stepB` of
  `Stacks.ResolutionOfSurfaces.exists_isResolution_of_steps`.

## Implementation notes

The tags consumed are arguments, stated as they are stated elsewhere: besides those of
`StacksFrontier/AlgebraicGeometry/ResolutionOfSurfaces/Lipman/DominatingStageLocalRings.lean`,
`hseparable` is [Stacks, Tag 0AXL], `hinseparable` is [Stacks, Tag 0B4U] and `hreduction` is
[Stacks, Tag 0B4P].

## References

* [Stacks Project, Tag 0BGN](https://stacks.math.columbia.edu/tag/0BGN)
* [Stacks Project, Tag 0AXL](https://stacks.math.columbia.edu/tag/0AXL)
* [Stacks Project, Tag 0B4U](https://stacks.math.columbia.edu/tag/0B4U)
* [Stacks Project, Tag 0B4P](https://stacks.math.columbia.edu/tag/0B4P)
-/

@[expose] public section

open CategoryTheory IsLocalRing

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry

/-- **The base case of the induction of [Stacks, Tag 0BGN].** A Noetherian complete local normal
domain `A`, finite over a two-dimensional regular complete local ring `R` with no intermediate
field between the fraction fields, has a resolution of singularities. -/
theorem exists_isResolution_of_forall_eq_bot_or_eq_top
    (hregular : ∀ (A : Type u) [CommRing A] [IsRegularLocalRing A] [IsNagataRing A],
      ringKrullDim A = 2 → (letI := IsRegularLocalRing.isDomain A; DefinesRationalSingularity A))
    (hgorenstein : ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNormalDomain A]
      (hN : IsNagataRing A), ringKrullDim A = 2 → DefinesRationalSingularity A →
      (letI := hN.1; ∃ K : DerivedCategory (ModuleCat.{u} A), Dualizing.IsDualizingComplex K) →
      ∃ (Y : Scheme.{u}) (f : Y ⟶ Spec (.of A)),
        Stacks.ResolutionOfSurfaces.NormalizedPointBlowupChain (Spec (.of A))
          {IsLocalRing.closedPoint A} Y f ∧
        ∀ y : Y, ∃ _ : IsNoetherianRing (Y.presheaf.stalk y),
          Dualizing.IsGorensteinLocalRing (Y.presheaf.stalk y))
    (hdoublePoint : ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNormalDomain A]
      (hN : IsNagataRing A), ringKrullDim A = 2 → DefinesRationalSingularity A →
      IsNormalRing (AdicCompletion (maximalIdeal A) A) →
      (letI := hN.1; Dualizing.IsGorensteinLocalRing A) →
      ∃ (Y : Scheme.{u}) (f : Y ⟶ Spec (.of A)),
        Stacks.ResolutionOfSurfaces.NormalizedPointBlowupChain (Spec (.of A))
          {IsLocalRing.closedPoint A} Y f ∧ IsRegular Y)
    (hrationalExt : ∀ (A B : Type u) [CommRing A] [IsLocalRing A] [IsNormalDomain A]
      [CommRing B] [IsLocalRing B] [IsNormalDomain B] [Algebra A B]
      [IsLocalHom (algebraMap A B)] (K : Type u) [Field K] [Algebra A K] [Algebra B K]
      [IsScalarTower A B K] [IsFractionRing A K] [IsFractionRing B K], IsNagataRing A →
      ringKrullDim A = 2 → ringKrullDim B = 2 → Algebra.EssFiniteType A B →
      DefinesRationalSingularity A → DefinesRationalSingularity B)
    (hseparable : ∀ (A B : Type u) [CommRing A] [IsLocalRing A] [IsNormalDomain A]
      [CommRing B] [IsLocalRing B] [IsNormalDomain B] [Algebra A B] [Module.Finite A B]
      [FaithfulSMul A B] [IsLocalHom (algebraMap A B)], IsNagataRing A → IsNagataRing B →
      ringKrullDim A = 2 → ringKrullDim B = 2 →
      (letI := FractionRing.liftAlgebra A (FractionRing B);
        Algebra.IsSeparable (FractionRing A) (FractionRing B)) →
      IsReductionToRationalSingularitiesPossible A → IsReductionToRationalSingularitiesPossible B)
    (hinseparable : ∀ (p : ℕ) [Fact p.Prime] (R A : Type u) [CommRing R] [IsRegularLocalRing R]
      [IsAdicComplete (maximalIdeal R) R] [CharP R p] [CommRing A] [IsNoetherianRing A]
      [IsLocalRing A] [IsNormalDomain A] [IsAdicComplete (maximalIdeal A) A] [Algebra R A]
      [Module.Finite R A] [FaithfulSMul R A], ringKrullDim R = 2 →
      (letI := IsRegularLocalRing.isDomain R; letI := FractionRing.liftAlgebra R (FractionRing A);
       Module.finrank (FractionRing R) (FractionRing A) = p ∧
        ¬ Algebra.IsSeparable (FractionRing R) (FractionRing A)) →
      IsReductionToRationalSingularitiesPossible A)
    (hreduction : ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNormalDomain A],
      IsNagataRing A → ringKrullDim A = 2 → IsReductionToRationalSingularitiesPossible A →
      ∃ (X : Scheme.{u}) (f : X ⟶ Spec (.of A)),
        Stacks.ResolutionOfSurfaces.NormalizedPointBlowupChain (Spec (.of A))
          {IsLocalRing.closedPoint A} X f ∧
        ∀ x : X, IsClosed ({x} : Set X) → ∃ _ : IsDomain (X.presheaf.stalk x),
          DefinesRationalSingularity (X.presheaf.stalk x))
    (R A : Type u) [CommRing R] [IsRegularLocalRing R] [IsDomain R]
    [IsAdicComplete (maximalIdeal R) R] [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsNormalDomain A] [IsAdicComplete (maximalIdeal A) A] [Algebra R A] [Module.Finite R A]
    [FaithfulSMul R A] (hR : ringKrullDim R = 2)
    (hmin : letI := FractionRing.liftAlgebra R (FractionRing A);
      ∀ M : IntermediateField (FractionRing R) (FractionRing A), M = ⊥ ∨ M = ⊤) :
    ∃ (X : Scheme.{u}) (f : X ⟶ Spec (.of A)), IsResolution f := by
  let := FractionRing.liftAlgebra R (FractionRing A)
  have : IsIntegrallyClosed R := isIntegrallyClosed_of_isRegularLocalRing R
  have : IsNormalDomain R := ⟨inferInstance, inferInstance⟩
  have : FiniteDimensional (FractionRing R) (FractionRing A) :=
    Stacks.ResolutionOfSurfaces.finiteDimensional_fractionRing R A
  have hRN : IsNagataRing R := IsNagataRing.of_isPrecomplete_maximalIdeal
  have hAN : IsNagataRing A := IsNagataRing.of_isPrecomplete_maximalIdeal
  have hdimA : ringKrullDim A = 2 := (Algebra.IsIntegral.ringKrullDim_eq R A).symm.trans hR
  -- reduction to rational singularities is possible for `A`
  have hAred : IsReductionToRationalSingularitiesPossible A := by
    rcases IntermediateField.isSeparable_or_finrank_eq_ringChar_of_forall_eq_bot_or_eq_top hmin with
      hsep | ⟨hp, hpi, hdeg⟩
    · exact hseparable R A hRN hAN hR hdimA hsep
        (isReductionToRationalSingularitiesPossible_of_definesRationalSingularity R (hregular R hR))
    · have : Fact (ringChar (FractionRing R)).Prime := ⟨hp⟩
      have : CharP (FractionRing R) (ringChar (FractionRing R)) := ringChar.charP _
      have : CharP R (ringChar (FractionRing R)) :=
        ((algebraMap R (FractionRing R)).charP_iff (IsFractionRing.injective R _) _).mpr
          inferInstance
      refine hinseparable (ringChar (FractionRing R)) R A hR ⟨hdeg, fun hsep => ?_⟩
      let e : FractionRing R ≃ₐ[FractionRing R] FractionRing A :=
        AlgEquiv.ofBijective (Algebra.ofId _ _)
          ⟨(algebraMap (FractionRing R) (FractionRing A)).injective,
            IsPurelyInseparable.surjective_algebraMap_of_isSeparable _ _⟩
      have h1 : Module.finrank (FractionRing R) (FractionRing A) = 1 := by
        rw [← e.toLinearEquiv.finrank_eq, Module.finrank_self]
      exact hp.one_lt.ne' (hdeg ▸ h1)
  -- normalized blowups with rational singularities at the closed points
  obtain ⟨X, f, hchain, hrat⟩ := hreduction A hAN hdimA hAred
  obtain ⟨hfmod, hXnormal, hXnoeth, hXdim⟩ := isModification_of_normalizedBlowUpSeq A hAN hdimA
    (normalizedBlowUpSeq_of_normalizedPointBlowupChain (hchain.mono (Set.subset_univ _)))
  have := hXnormal
  have := hXnoeth
  have : IsProper f := hfmod.isProper
  have hAexc : IsExcellent A := (isExcellent_of_standard_classes_and_finiteType.{u, u}).2.1 A
  have hsing := finite_singularLocus_of_locallyOfFiniteType_of_isExcellent hAexc f hXdim.le
  refine exists_isResolution_of_isModification_of_singularLocus A f hfmod hdimA hsing
    fun x hx => ?_
  let O := X.presheaf.stalk x
  have : IsNormalDomain O := ⟨IsNormal.stalk_isDomain _, IsNormal.stalk_normal _⟩
  obtain ⟨_, L, hL⟩ := exists_isDualizingComplex_stalk_of_locallyOfFiniteType A
    (Dualizing.exists_isDualizingComplex_of_isPrecomplete_maximalIdeal A) f x
  obtain ⟨_, hOrat⟩ := hrat x (isClosed_singleton_of_mem_singularLocus X hXdim.le x hx)
  exact hasResolutionByNormalizedBlowUps_of_definesRationalSingularity hgorenstein hdoublePoint
    hrationalExt O (isExcellent_stalk_of_locallyOfFiniteType hAexc f x) ⟨L, hL⟩
    (ringKrullDim_stalk_eq_two_of_mem_singularLocus X hXdim.le x hx) hOrat

end AlgebraicGeometry

end
