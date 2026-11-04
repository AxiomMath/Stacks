module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.FiniteCoproductPresentingRing
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineCompletionTypes
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineCoproduct
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionSubspaceLocalTypes
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountablePresentation
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Types
import all StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionSubspaceLocalTypes

/-!
# The types of an affine formal algebraic space pass to a finite disjoint union

Let `S` be a scheme contained in a big fppf site `B`. Each of the five types of affine formal
algebraic space listed in Stacks 0AKX — countably indexed, countably indexed and classical,
weakly adic, adic\* and Noetherian — is inherited by a coproduct of finitely many affine formal
algebraic spaces of that type. This is the step of Stacks 0AKX which the source states without
proof, the hypothesis `hPsigma` of
`AlgebraicGeometry.FormalSpace.hasAffineEtaleChartProperty_iff_hasAffineEtaleAtlasWithProperty`.

For the four types of Stacks 0AID the argument is algebraic. The coproduct is presented by the
product of the presenting rings of the summands,
`AlgebraicGeometry.FormalSpace.isPresentingRing_pi_sigma`, so it is McQuillan — condition (1) of
Stacks 0AIC implies condition (5), hence (4) — and each of the four conditions on the presenting
ring is inherited by a finite product of topological rings, which is the content of
`StacksFrontier.Topology.Algebra.AdicTopology.FiniteProduct`.

Countable indexing is not a condition on a presenting ring, and the argument for it is
different: by Stacks 0AII it suffices to present the coproduct over *some* countable nonempty
directed index, and the product of the index preorders of sequential presentations of the
summands is such an index.

## Main results

* `AlgebraicGeometry.FormalSpace.isCountablyIndexed_sigma'`,
  `AlgebraicGeometry.FormalSpace.isClassical_sigma`,
  `AlgebraicGeometry.FormalSpace.isWeaklyAdic_sigma'`,
  `AlgebraicGeometry.FormalSpace.isAdicStar_sigma'` and
  `AlgebraicGeometry.FormalSpace.isNoetherian_sigma'`: **the five types pass to a finite
  coproduct.**

## Implementation notes

The index of a coproduct in Definition 0AIM lives in `Type (u + 1)` and a presenting ring in
`Type u`, so the statements are proved first for an index of the form `ULift.{u + 1} κ` with
`κ : Type u` and then transported along an equivalence of the index, the five types all being
invariant under isomorphism of the sheaf.

None of the five statements asks that the summands be affine formal algebraic spaces, as
Stacks 0AKX does: each of the five types of Stacks 0AID contains condition (4) of Stacks 0AIC,
which contains affineness, and countable indexing needs no affineness at all.

## References

* [Stacks Project, Tag 0AIC](https://stacks.math.columbia.edu/tag/0AIC)
* [Stacks Project, Tag 0AID](https://stacks.math.columbia.edu/tag/0AID)
* [Stacks Project, Tag 0AII](https://stacks.math.columbia.edu/tag/0AII)
* [Stacks Project, Tag 0AIJ](https://stacks.math.columbia.edu/tag/0AIJ)
* [Stacks Project, Tag 0AKX](https://stacks.math.columbia.edu/tag/0AKX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

attribute [local instance] sheaf_hasColimits

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### A small index -/

section SmallIndex

variable {κ : Type u} [Finite κ] (Z : ULift.{u + 1} κ → FppfSheaf B S hS)

/-- **A finite coproduct of countably indexed affine formal algebraic spaces is countably
indexed.** The product of finitely many copies of `ℕ` is a countable nonempty directed
preorder, the product diagram over it presents the coproduct, and Stacks 0AII replaces that
index by `ℕ`. -/
theorem isCountablyIndexed_sigma_ulift (hZ : ∀ i, IsCountablyIndexed B S hS (Z i)) :
    IsCountablyIndexed B S hS (∐ Z) := by
  classical
  choose D hD he using hZ
  let Idx : ULift.{u + 1} κ → Type (u + 1) := fun _ ↦ ULift.{u + 1} ℕ
  let D' : ∀ i, Idx i ⥤ BigAffineFppf B S hS := fun i ↦
    (uliftOrderIso ℕ).equivalence.functor ⋙ D i
  have hcol : (∐ Z) ≅ colimit (sigmaStage B S hS Idx D' ⋙ affineStageSheafFunctor B S hS) :=
    sigmaColimitIso B S hS Idx D' Z fun i ↦
      stageColimitIsoOfOrderIso B S hS (uliftOrderIso ℕ) (D i) (Z i) (he i).some
  have : Countable (StageIndex Idx) :=
    Countable.of_equiv (∀ i, Idx i) (stageIndexOrderIso Idx).toEquiv
  exact (isCountablyIndexed_iff_exists_countable_presentation B S hS (∐ Z)).mpr
    ⟨StageIndex Idx, inferInstance, inferInstance, inferInstance, inferInstance,
      sigmaStage B S hS Idx D',
      fun _ _ f ↦ isThickening_sigmaStage_map B S hS Idx D' (fun i _ _ f ↦ hD i _) f, ⟨hcol⟩⟩

variable (A : κ → Type u) [∀ c, CommRing (A c)] [∀ c, TopologicalSpace (A c)]
  [∀ c, IsTopologicalRing (A c)] [∀ c, IsLinearTopology (A c) (A c)]

/-- **A finite coproduct of affine formal algebraic spaces presented by the rings `A c` is
McQuillan and is presented by `∀ c, A c`.** The presentation is
`AlgebraicGeometry.FormalSpace.isPresentingRing_pi_sigma`, and McQuillan-ness is the implication
(1) ⟹ (5) ⟹ (4) of Stacks 0AIC applied to it. -/
theorem hasSomeSurjectivePresentation_and_isPresentingRing_pi_sigma
    (hZaff : ∀ i, IsAffineFormalAlgebraicSpace B S hS (Z i))
    (h : ∀ i, IsPresentingRing B S hS (A i.down) (Z i)) :
    letI : IsLinearTopology (∀ c, A c) (∀ c, A c) := TopologicalRing.pi_isLinearTopology
    HasSomeSurjectivePresentation B S hS (∐ Z) ∧
      IsPresentingRing B S hS (∀ c, A c) (∐ Z) := by
  let : IsLinearTopology (∀ c, A c) (∀ c, A c) := TopologicalRing.pi_isLinearTopology
  have hpr : IsPresentingRing B S hS (∀ c, A c) (∐ Z) :=
    isPresentingRing_pi_sigma B S hS A Z h
  exact ⟨(hasAllSurjectivePresentations_of_weakIdealColimitPresentation B S hS (∀ c, A c)
      hpr.1 (isAffineFormalAlgebraicSpace_sigma B S hS Z hZaff).1
      hpr.2.some).hasSomeSurjectivePresentation, hpr⟩

end SmallIndex

section SmallIndexTypes

variable {κ : Type u} [Finite κ] (Z : ULift.{u + 1} κ → FppfSheaf B S hS)

/-- A finite coproduct of McQuillan affine formal algebraic spaces, each presented by a ring with
a property `P` that passes to finite products, is McQuillan and presented by a ring with `P`. -/
private theorem hasSomeSurjectivePresentation_and_exists_presentingRing_sigma_ulift
    (P : ∀ (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
      [IsLinearTopology A A], Prop)
    (hP : ∀ (A : κ → Type u) [∀ c, CommRing (A c)] [∀ c, TopologicalSpace (A c)]
      [∀ c, IsTopologicalRing (A c)] [∀ c, IsLinearTopology (A c) (A c)],
      letI : IsLinearTopology (∀ c, A c) (∀ c, A c) := TopologicalRing.pi_isLinearTopology
      (∀ c, P (A c)) → P (∀ c, A c))
    (hZ : ∀ i, HasSomeSurjectivePresentation B S hS (Z i) ∧
      ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
        (_ : IsLinearTopology A A), IsPresentingRing B S hS A (Z i) ∧ P A) :
    HasSomeSurjectivePresentation B S hS (∐ Z) ∧
      ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
        (_ : IsLinearTopology A A), IsPresentingRing B S hS A (∐ Z) ∧ P A := by
  classical
  choose _ A instCR instTS instTR instLT hpr hcond using fun c : κ ↦ hZ (ULift.up c)
  let : ∀ c, CommRing (A c) := instCR
  let : ∀ c, TopologicalSpace (A c) := instTS
  let : ∀ c, IsTopologicalRing (A c) := instTR
  let : ∀ c, IsLinearTopology (A c) (A c) := instLT
  let : IsLinearTopology (∀ c, A c) (∀ c, A c) := TopologicalRing.pi_isLinearTopology
  obtain ⟨hmc, hprs⟩ := hasSomeSurjectivePresentation_and_isPresentingRing_pi_sigma
    B S hS Z A (fun i ↦ (hZ i).1.1) fun i ↦ hpr i.down
  exact ⟨hmc, (∀ c, A c), inferInstance, inferInstance, inferInstance, inferInstance, hprs,
    hP A hcond⟩

/-- A finite coproduct of classical affine formal algebraic spaces is classical: the product of
admissible topological rings is admissible. -/
theorem isClassical_sigma_ulift (hZ : ∀ i, IsClassical B S hS (Z i)) :
    IsClassical B S hS (∐ Z) :=
  hasSomeSurjectivePresentation_and_exists_presentingRing_sigma_ulift B S hS Z
    (fun A _ _ _ _ ↦ TopologicalRing.IsAdmissible A)
    (fun _ _ _ _ _ h ↦ TopologicalRing.isAdmissible_pi' h) hZ

/-- A finite coproduct of weakly adic affine formal algebraic spaces is weakly adic: the product
of weakly adic topological rings is weakly adic. -/
theorem isWeaklyAdic_sigma_ulift (hZ : ∀ i, IsWeaklyAdic B S hS (Z i)) :
    IsWeaklyAdic B S hS (∐ Z) :=
  hasSomeSurjectivePresentation_and_exists_presentingRing_sigma_ulift B S hS Z
    (fun A _ _ _ _ ↦ TopologicalRing.IsWeaklyAdic A)
    (fun _ _ _ _ _ h ↦ TopologicalRing.isWeaklyAdic_pi' h) hZ

/-- A finite coproduct of adic\* affine formal algebraic spaces is adic\*: the product of adic
topological rings is adic, and the product of finitely generated ideals of definition is a
finitely generated ideal of definition. -/
theorem isAdicStar_sigma_ulift (hZ : ∀ i, IsAdicStar B S hS (Z i)) :
    IsAdicStar B S hS (∐ Z) :=
  hasSomeSurjectivePresentation_and_exists_presentingRing_sigma_ulift B S hS Z
    (fun A _ _ _ _ ↦ TopologicalRing.IsAdic A ∧
      ∃ I : Ideal A, TopologicalRing.IsIdealOfDefinition I ∧ I.FG)
    (fun A _ _ _ _ h ↦ ⟨Rig.isAdic_pi A fun c ↦ (h c).1,
      TopologicalRing.exists_fg_isIdealOfDefinition_pi fun c ↦ (h c).2⟩) hZ

/-- A finite coproduct of Noetherian affine formal algebraic spaces is Noetherian: the product
of finitely many Noetherian adic topological rings is Noetherian and adic. -/
theorem isNoetherian_sigma_ulift (hZ : ∀ i, IsNoetherian B S hS (Z i)) :
    IsNoetherian B S hS (∐ Z) :=
  hasSomeSurjectivePresentation_and_exists_presentingRing_sigma_ulift B S hS Z
    (fun A _ _ _ _ ↦ IsNoetherianRing A ∧ TopologicalRing.IsAdic A)
    (fun A _ _ _ _ h ↦
      have := fun c ↦ (h c).1
      ⟨inferInstance, Rig.isAdic_pi A fun c ↦ (h c).2⟩) hZ

end SmallIndexTypes

/-! ### An arbitrary finite index -/

section GeneralIndex

variable {K : Type (u + 1)} [Finite K] (Z : K → FppfSheaf B S hS)

/-- The index of a finite coproduct, reindexed by the universe lift of a small type. -/
private theorem exists_ulift_reindex :
    ∃ (κ : Type u) (_ : Finite κ) (e : ULift.{u + 1} κ ≃ K),
      Nonempty ((∐ fun i ↦ Z (e i)) ≅ (∐ Z)) := by
  obtain ⟨n, ⟨eFin⟩⟩ := Finite.exists_equiv_fin K
  exact ⟨ULift.{u} (Fin n), inferInstance, (Equiv.ulift.trans Equiv.ulift).trans eFin.symm,
    ⟨Sigma.whiskerEquiv _ fun _ ↦ Iso.refl _⟩⟩

/-- **A finite coproduct of countably indexed affine formal algebraic spaces is countably
indexed** (Stacks 0AIJ). -/
theorem isCountablyIndexed_sigma' (hZ : ∀ k, IsCountablyIndexed B S hS (Z k)) :
    IsCountablyIndexed B S hS (∐ Z) := by
  obtain ⟨κ, _, e, ⟨eiso⟩⟩ := exists_ulift_reindex B S hS Z
  obtain ⟨D, hD, ⟨k⟩⟩ := isCountablyIndexed_sigma_ulift B S hS (fun i ↦ Z (e i)) fun i ↦ hZ _
  exact ⟨D, hD, ⟨eiso.symm ≪≫ k⟩⟩

/-- **A finite coproduct of classical affine formal algebraic spaces is classical**
(Stacks 0AID). -/
theorem isClassical_sigma (hZ : ∀ k, IsClassical B S hS (Z k)) :
    IsClassical B S hS (∐ Z) := by
  obtain ⟨κ, _, e, ⟨eiso⟩⟩ := exists_ulift_reindex B S hS Z
  exact isClassical_of_iso B S hS eiso
    (isClassical_sigma_ulift B S hS (fun i ↦ Z (e i)) fun i ↦ hZ _)

/-- **A finite coproduct of Noetherian affine formal algebraic spaces is Noetherian**
(Stacks 0AID). -/
theorem isNoetherian_sigma' (hZ : ∀ k, IsNoetherian B S hS (Z k)) :
    IsNoetherian B S hS (∐ Z) := by
  obtain ⟨κ, _, e, ⟨eiso⟩⟩ := exists_ulift_reindex B S hS Z
  exact isNoetherian_of_iso B S hS eiso
    (isNoetherian_sigma_ulift B S hS (fun i ↦ Z (e i)) fun i ↦ hZ _)

/-- **A finite coproduct of adic\* affine formal algebraic spaces is adic\*** (Stacks 0AID). -/
theorem isAdicStar_sigma' (hZ : ∀ k, IsAdicStar B S hS (Z k)) :
    IsAdicStar B S hS (∐ Z) := by
  obtain ⟨κ, _, e, ⟨eiso⟩⟩ := exists_ulift_reindex B S hS Z
  exact isAdicStar_of_iso B S hS eiso
    (isAdicStar_sigma_ulift B S hS (fun i ↦ Z (e i)) fun i ↦ hZ _)

/-- **A finite coproduct of weakly adic affine formal algebraic spaces is weakly adic**
(Stacks 0AID). -/
theorem isWeaklyAdic_sigma' (hZ : ∀ k, IsWeaklyAdic B S hS (Z k)) :
    IsWeaklyAdic B S hS (∐ Z) := by
  obtain ⟨κ, _, e, ⟨eiso⟩⟩ := exists_ulift_reindex B S hS Z
  exact isWeaklyAdic_of_iso B S hS eiso.symm
    (isWeaklyAdic_sigma_ulift B S hS (fun i ↦ Z (e i)) fun i ↦ hZ _)

end GeneralIndex

end AlgebraicGeometry.FormalSpace

end
