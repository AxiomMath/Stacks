module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AdicQuotientSystemOfCompleteLocal
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionSubspaceLocalTypes
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSpectrumClassical
public import StacksFrontier.AlgebraicGeometry.FormalSpace.PresentationQuotientSystem
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableOverMcQuillan
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SharpnessOfRepresentability
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SurjectivePresentationRing
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautFromRepresentable
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.ContainingSet
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineCompletionTypes
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautOfRepresentable
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SharpnessOfRepresentabilityFirstSense

/-!
# The two counterexamples of Stacks 0AN7

**Stacks 0AN7** records that Stacks 0AN5, 0AKP and 0AKQ are sharp in two senses, each witnessed
by an example. This file states both examples as concrete existence statements with no
hypothesis at all.

1. For weakly admissible topological rings `A`, `B` and a continuous `φ : A → B`, the morphism
   `Spf (φ) : Spf B ⟶ Spf A` need not be representable. The example is `A = k` a field with the
   discrete topology and `B = k⟦t⟧` with the `t`-adic topology. For every such field we build a
   big fppf site, the base `S = Spec k`, the formal spectra `Spf k` and `Spf k⟦t⟧` over it (both
   affine formal algebraic spaces), and the formal spectrum of the inclusion of constants, and we
   show that it is neither representable (by schemes, i.e. by objects of the site) nor
   representable by algebraic spaces.
2. If `f : Y ⟶ X` is a representable morphism of affine formal algebraic spaces and
   `X = Spf (A)` is McQuillan, `Y` need not be McQuillan. The example is the one of Examples,
   Section 0ANY, which is Stacks 0CBE in this library; here its target is moreover identified
   with the formal spectrum of a weakly admissible topological ring.

## Main results

* `FormalSpace.not_isRepresentableByAlgebraicSpaces_formalSpectrumMap_constants'`:
  **Stacks 0AN7**, first sense, on condition (1) of Stacks 0AN5 and with no hypothesis whatever:
  the formal spectrum of the inclusion of constants `k → k⟦t⟧` is not representable by algebraic
  spaces, over any base and any quotient systems presenting the two formal spectra.
* `AlgebraicGeometry.FormalSpace.not_relativelyRepresentable_formalSpectrumMap_constants`:
  **Stacks 0AN7**, first sense, on condition (2) of Stacks 0AN5 and with no hypothesis
  whatever: the same morphism is not representable.
* `AlgebraicGeometry.FormalSpace.exists_formalSpectrumMap_constants_not_representable`:
  **Stacks 0AN7 (1)**.
* `AlgebraicGeometry.FormalSpace.exists_representable_formalSpectrum_not_mcQuillan`:
  **Stacks 0AN7 (2)**.

## Implementation notes

For (1) the quotient systems presenting `Spf k` and `Spf k⟦t⟧` over `Spec k` are the canonical
ones of `AlgebraicGeometry.FormalSpace.quotientSystemOfSpec`, with structure morphisms the
identity of `Spec k` and `Spec` of the inclusion of constants; the site is chosen to contain
`Spec k`, `Spec k⟦t⟧` and the two coproducts of quotient spectra that make the formal spectra
affine formal algebraic spaces. Non-representability is
`AlgebraicGeometry.FormalSpace.not_relativelyRepresentable_formalSpectrumMap_constants` and
`AlgebraicGeometry.FormalSpace.not_isRepresentableByAlgebraicSpaces_formalSpectrumMap_constants'`,
which rest on the non-tautness of the inclusion of constants and on the implications
(2) ⟹ (3) and (1) ⟹ (3) of Stacks 0AN5.

For (2), "McQuillan" is condition (4) of Stacks 0AIC,
`AlgebraicGeometry.FormalSpace.HasSomeSurjectivePresentation`. The target of the example of
Stacks 0CBE is McQuillan, so by condition (1) of Stacks 0AIC it is presented by a weakly
admissible topological ring `A`, hence isomorphic to `Spf A`; composing with that isomorphism
puts the morphism literally over `Spf A`.

## References

* [Stacks Project, Tag 0AN7](https://stacks.math.columbia.edu/tag/0AN7)
* [Stacks Project, Tag 0AN5](https://stacks.math.columbia.edu/tag/0AN5)
* [Stacks Project, Tag 0ANY](https://stacks.math.columbia.edu/tag/0ANY)
* [Stacks Project, Tag 0CBE](https://stacks.math.columbia.edu/tag/0CBE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

section ReadingsOfZeroAN5

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0AN7**, its first sense, read on condition (2) of **Stacks 0AN5** and with no
hypothesis whatever. Let `k` be a field with the discrete topology, let `k⟦t⟧` carry the
`t`-adic topology and let `Spf (φ) : Spf k⟦t⟧ ⟶ Spf k` be the formal spectrum of the inclusion
of constants. Then `Spf (φ)` is not representable: some base change of it along a point of
`Spf k` coming from an object of the site is not again such an object.

The implication (2) ⟹ (3) of Stacks 0AN5,
`AlgebraicGeometry.FormalSpace.isTaut_of_relativelyRepresentable_formalSpectrumMap`, carries no
side condition at all — only the base changes along the quotient stages are used, and condition
(2) supplies those directly — so the non-tautness of the example rules out condition (2)
outright. Ruling out the weaker condition (1), representability by algebraic spaces, needs the
step from (1) to (2), which is Stacks 0AKN; that is
`AlgebraicGeometry.FormalSpace.not_isRepresentableByAlgebraicSpaces_formalSpectrumMap_constants'`,
and it is unconditional too, the library's Stacks 0AKN consuming of a formal spectrum only its
presentation by affine thickenings. -/
@[stacks 0AN7 "first sense, the non-representability itself in the reading of condition (2) of
  Stacks 0AN5 — representable, i.e. every base change along a point of `Spf k` out of an object
  of the site is again such an object — and with no hypothesis whatever: the implication
  (2) ⟹ (3) of Stacks 0AN5,
  `AlgebraicGeometry.FormalSpace.isTaut_of_relativelyRepresentable_formalSpectrumMap`, carries
  no side condition, so the non-tautness of the example
  (`TopologicalRing.not_isTaut_constantsToTAdicPowerSeries`) rules condition (2) out directly.
  The reading on condition (1), representability by algebraic spaces, is
  `AlgebraicGeometry.FormalSpace.not_isRepresentableByAlgebraicSpaces_formalSpectrumMap_constants'`,
  which is unconditional as well. The concrete instance and the second sense of the remark are
  `AlgebraicGeometry.FormalSpace.exists_formalSpectrumMap_constants_not_representable` and
  `AlgebraicGeometry.FormalSpace.exists_representable_formalSpectrum_not_mcQuillan`"]
theorem not_relativelyRepresentable_formalSpectrumMap_constants
    (k : Type u) [Field k] [TopologicalSpace k] [DiscreteTopology k]
    (D : QuotientSystem B S hS k)
    (E : QuotientSystem B S hS (TopologicalRing.TAdicPowerSeries k))
    (f : ContinuousHom D E)
    (hf : f.toRingHom = TopologicalRing.constantsToTAdicPowerSeries k) :
    ¬ (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).relativelyRepresentable
      (formalSpectrumMap (TopologicalRing.isWeaklyAdmissible_discreteTopology k) f) := by
  intro hrep
  refine TopologicalRing.not_isTaut_constantsToTAdicPowerSeries k (hf ▸ ?_)
  exact isTaut_of_relativelyRepresentable_formalSpectrumMap B S hS
    (TopologicalRing.isWeaklyAdmissible_discreteTopology k)
    (TopologicalRing.isWeaklyAdmissible_tAdicPowerSeries k) D E f hrep

end ReadingsOfZeroAN5

/-- **Stacks 0AN7 (1).** Let `k` be a field with the discrete topology and let `k⟦t⟧` carry the
`t`-adic topology; both are weakly admissible and the inclusion of constants `φ : k → k⟦t⟧` is
continuous. Then, over the base `S = Spec k` of a suitable big fppf site, the formal spectra
`Spf k` and `Spf k⟦t⟧` are affine formal algebraic spaces and
`Spf (φ) : Spf k⟦t⟧ ⟶ Spf k` is neither representable nor representable by algebraic spaces. -/
@[stacks 0AN7 "(1): for `A = k` a field with the discrete topology and `B = k⟦t⟧` with the
  `t`-adic topology, `Spf (φ) : Spf(k⟦t⟧) → Spf(k)` of the inclusion of constants is a morphism
  of affine formal algebraic spaces which is not representable, and not even representable by
  algebraic spaces"]
theorem exists_formalSpectrumMap_constants_not_representable
    (k : Type u) [Field k] [TopologicalSpace k] [DiscreteTopology k] :
    ∃ (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
      (D : QuotientSystem B S hS k)
      (E : QuotientSystem B S hS (TopologicalRing.TAdicPowerSeries k))
      (f : ContinuousHom D E),
      f.toRingHom = TopologicalRing.constantsToTAdicPowerSeries k ∧
      IsAffineFormalAlgebraicSpace B S hS (formalSpectrum D) ∧
      IsAffineFormalAlgebraicSpace B S hS (formalSpectrum E) ∧
      ¬ (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).relativelyRepresentable
        (formalSpectrumMap (TopologicalRing.isWeaklyAdmissible_discreteTopology k) f) ∧
      ¬ Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
        (formalSpectrumMap (TopologicalRing.isWeaklyAdmissible_discreteTopology k) f).hom := by
  classical
  let T := TopologicalRing.TAdicPowerSeries k
  let φ := TopologicalRing.constantsToTAdicPowerSeries k
  let S₀ : Set Scheme.{u} := {Spec (.of k), Spec (.of T),
    ∐ (fun J : { I : Ideal k // TopologicalRing.IsWeakIdealOfDefinition I } ↦
      Spec (.of (k ⧸ J.1))),
    ∐ (fun J : { I : Ideal T // TopologicalRing.IsWeakIdealOfDefinition I } ↦
      Spec (.of (T ⧸ J.1)))}
  obtain ⟨B, hB⟩ := BigFppfSite.exists_containing S₀
  have hk : B.Contains (Spec (.of k)) := hB _ (Set.mem_insert _ _)
  have hT : B.Contains (Spec (.of T)) := hB _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  let D : QuotientSystem B (Spec (.of k)) hk k := quotientSystemOfSpec hk (𝟙 _)
  let E : QuotientSystem B (Spec (.of k)) hk T :=
    quotientSystemOfSpec hT (Spec.map (CommRingCat.ofHom φ))
  let f : ContinuousHom D E :=
    { toRingHom := φ
      continuous := TopologicalRing.continuous_constantsToTAdicPowerSeries k
      overS := fun J K h => by
        show Spec.map _ ≫ (Spec.map _ ≫ 𝟙 _) = Spec.map _ ≫ Spec.map _
        rw [Category.comp_id, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
          ← CommRingCat.ofHom_comp, Ideal.quotientMap_comp_mk] }
  refine ⟨B, Spec (.of k), hk, D, E, f, rfl, ?_, ?_, ?_, ?_⟩
  · exact isAffineFormalAlgebraicSpace_formalSpectrum
      (TopologicalRing.isWeaklyAdmissible_discreteTopology k) D
      (hB _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))))
  · exact isAffineFormalAlgebraicSpace_formalSpectrum
      (TopologicalRing.isWeaklyAdmissible_tAdicPowerSeries k) E
      (hB _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))))
  · exact not_relativelyRepresentable_formalSpectrumMap_constants B _ hk k D E f rfl
  · exact not_isRepresentableByAlgebraicSpaces_formalSpectrumMap_constants' B _ hk k D E f rfl

/-- **Stacks 0AN7 (2).** There are a weakly admissible topological ring `A` over a base `S` and a
representable morphism `f : Y ⟶ Spf A` of affine formal algebraic spaces such that the target
`Spf A` is McQuillan but the source `Y` is not. This is the example of Examples, Section 0ANY,
i.e. Stacks 0CBE, with its McQuillan target identified with a formal spectrum. The source is not
McQuillan in the sense of condition (4) of Stacks 0AIC, and not in the sense of condition (1)
either: it is isomorphic to the formal spectrum of no weakly admissible topological ring. -/
@[stacks 0AN7 "(2): a representable morphism `f : Y → X` of affine formal algebraic spaces with
  `X = Spf(A)` McQuillan and `Y` not McQuillan, the example of Examples, Section 0ANY"]
theorem exists_representable_formalSpectrum_not_mcQuillan :
    ∃ (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
      (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
      (_ : IsLinearTopology A A) (D : QuotientSystem B S hS A) (Y : FppfSheaf B S hS)
      (f : Y ⟶ formalSpectrum D),
      TopologicalRing.IsWeaklyAdmissible A ∧
      IsAffineFormalAlgebraicSpace B S hS Y ∧
      IsAffineFormalAlgebraicSpace B S hS (formalSpectrum D) ∧
      HasSomeSurjectivePresentation B S hS (formalSpectrum D) ∧
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).relativelyRepresentable f ∧
      ¬ HasSomeSurjectivePresentation B S hS Y ∧
      ¬ ∃ (A' : Type u) (_ : CommRing A') (_ : TopologicalSpace A') (_ : IsTopologicalRing A')
        (_ : IsLinearTopology A' A') (D' : QuotientSystem B S hS A'),
        TopologicalRing.IsWeaklyAdmissible A' ∧ Nonempty (Y ≅ formalSpectrum D') := by
  obtain ⟨B, S, hS, Y, X, f, hY, hX, hrep, -, hXm, hYn⟩ :=
    exists_representable_hasSomeSurjectivePresentation_not.{u}
  obtain ⟨A, _, _, _, _, hpr⟩ :=
    exists_isPresentingRing_of_hasSomeSurjectivePresentation B S hS hXm
  obtain ⟨D, ⟨e⟩⟩ := exists_quotientSystem_iso_formalSpectrum_of_isPresentingRing hpr
  refine ⟨B, S, hS, A, _, _, _, _, D, Y, f ≫ e.hom, hpr.1, hY,
    isAffineFormalAlgebraicSpace_of_iso B S hS e hX,
    hasSomeSurjectivePresentation_of_iso B S hS e hXm,
    MorphismProperty.RespectsIso.postcomp _ e.hom f hrep, hYn, ?_⟩
  rintro ⟨A', _, _, _, _, D', hA', ⟨e'⟩⟩
  exact hYn ((hasSomeSurjectivePresentation_iff_exists_isPresentingRing B S hS hY.1).2
    ⟨A', _, _, _, _, isPresentingRing_of_iso B S hS A' e'.symm
      (isPresentingRing_formalSpectrum hA' D')⟩)

end AlgebraicGeometry.FormalSpace

end
