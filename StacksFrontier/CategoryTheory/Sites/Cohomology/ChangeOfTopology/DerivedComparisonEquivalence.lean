module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.HigherDirectImageVanishing
import StacksCore.Tactic.StacksAttribute

/-!
# The comparison of bounded below derived categories for a change of topology

In the situation of Stacks 0EZ3 this file proves **Stacks 0EZG**: for every object `X` the class
`𝒜_X ⊂ Ab(C_τ/X)` of Stacks 0EZ9 is a weak Serre subcategory, and the derived change-of-topology
direct image `Rε_{X,*} : D⁺_{𝒜_X}(C_τ/X) ⟶ D⁺_{𝒜'_X}(C_{τ'}/X)` is an equivalence with
quasi-inverse `ε_X^{-1}`.

## Main results

* `Stacks.ComparingTopologies.CohomologyComparison.fineWeakSerre_isWeakSerreClass`: the first
  assertion.
* `Stacks.ComparingTopologies.boundedBelowComparisonEquivalence`, with
  `boundedBelowComparisonEquivalence_functor` and `boundedBelowComparisonEquivalence_inverse`:
  the second assertion.

## The argument

Membership in `𝒜_X` is detected by `ε_{X,*}` (`fineWeakSerre_iff_weakSerre_pushforward`), and
every sheaf of `𝒜_X` is right acyclic for `ε_{X,*}` because `(V_n)` holds for every `n`
(`CohomologyComparison.vanishingCondition_all`, Stacks 0EZF), so the closure properties of `𝒜_X`
are transported from those of `𝒜'_X`; Stacks 015D handles cokernels and extensions. The
equivalence is the derived adjunction `ε_X^{-1} ⊣ Rε_{X,*}` restricted to the two subcategories:
its counit is invertible because `ε_{X,*}` is fully faithful, and its unit by Stacks 0EZF (1).

## References

* [Stacks Project, Tag 0EZG](https://stacks.math.columbia.edu/tag/0EZG)
* [Stacks Project, Tag 0EZF](https://stacks.math.columbia.edu/tag/0EZF)
* [Stacks Project, Tag 0754](https://stacks.math.columbia.edu/tag/0754)
* [Stacks Project, Tag 0D7U](https://stacks.math.columbia.edu/tag/0D7U)
-/

@[expose] public noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace Stacks.ComparingTopologies

open Stacks.Cohomology.Localization

variable {C : Type u} [Category.{v} C]

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000]
  HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

namespace CohomologyComparison

/-- **First assertion of Stacks 0EZG.** In the comparison situation of Stacks 0EZ3, for any
object `X` of `C` the class `𝒜_X ⊂ Ab(C_τ/X)` of Stacks 0EZ9 is a weak Serre subcategory. -/
@[stacks 0EZG "first assertion: `𝒜_X` is a weak Serre subcategory of `Ab(C_τ/X)`"]
theorem fineWeakSerre_isWeakSerreClass (S : CohomologyComparison C) (X : C) :
    (S.fineWeakSerre X).IsWeakSerreClass := by
  classical
  let P := S.fineWeakSerre X
  let Q := S.weakSerre X
  let R := abelianComparisonPushforward S.fineCoverage S.coarseCoverage S.coarse_le_fine X
  have hmem := fineWeakSerre_iff_weakSerre_pushforward S X
  have hacyc : ∀ F, P F → R.rightAcyclic F := fun F hF ↦
    abelianComparisonPushforward_rightAcyclic_of_fineWeakSerre S S.vanishingCondition_all X F hF
  have : P.ContainsZero :=
    ⟨_, isZero_zero _, (hmem 0).2 (Q.prop_of_isZero (R.map_isZero (isZero_zero _)))⟩
  have : P.IsClosedUnderIsomorphisms :=
    ⟨fun e hA ↦ (hmem _).2 (Q.prop_of_iso (R.mapIso e) ((hmem _).1 hA))⟩
  have : P.IsClosedUnderKernels := by
    constructor
    intro K ⟨f, k, hk, hAB⟩
    have hK : Q (R.obj (kernel f)) :=
      Q.prop_of_iso (PreservesKernel.iso R f).symm
        (Q.prop_kernel (R.map f) ((hmem _).1 hAB.1) ((hmem _).1 hAB.2))
    let eK : kernel f ≅ k.pt :=
      IsLimit.conePointUniqueUpToIso (limit.isLimit (parallelPair f 0)) hk
    exact (hmem k.pt).2 (Q.prop_of_iso (R.mapIso eK) hK)
  have : P.IsClosedUnderCokernels := by
    constructor
    intro K ⟨f, c, hc, hAB⟩
    have hkerP : P (kernel f) := P.prop_kernel f hAB.1 hAB.2
    have hcok : ∀ T : ShortComplex _, (T.map R).ShortExact → Q (R.obj T.X₁) →
        Q (R.obj T.X₂) → Q (R.obj T.X₃) := fun T hT h₁ h₂ ↦
      Q.prop_of_iso ((hT.gIsCokernel).coconePointUniqueUpToIso
        (cokernelIsCokernel (R.map T.f))).symm (Q.prop_cokernel (R.map T.f) h₁ h₂)
    obtain ⟨hImageAcyc, hS₁map⟩ :=
      (R.rightAcyclic_and_shortExact_map_of_shortExact _ (kernelCoimageShortExact f)).2.1
        (hacyc _ hkerP) (hacyc _ hAB.1)
    obtain ⟨_, hS₂map⟩ :=
      (R.rightAcyclic_and_shortExact_map_of_shortExact _ (coimageCokernelShortExact f)).2.1
        hImageAcyc (hacyc _ hAB.2)
    have hCokerQ := hcok _ hS₂map (hcok _ hS₁map ((hmem _).1 hkerP) ((hmem _).1 hAB.1))
      ((hmem _).1 hAB.2)
    exact P.prop_of_iso (hc.coconePointUniqueUpToIso (cokernelIsCokernel f)).symm
      ((hmem (cokernel f)).2 hCokerQ)
  have : P.IsClosedUnderExtensions := by
    constructor
    intro S₀ hS₀ hA hC
    obtain ⟨_, hMap⟩ :=
      (R.rightAcyclic_and_shortExact_map_of_shortExact S₀ hS₀).1 (hacyc _ hA) (hacyc _ hC)
    exact (hmem _).2 (Q.prop_X₂_of_shortExact hMap ((hmem _).1 hA) ((hmem _).1 hC))
  exact {}

end CohomologyComparison

/-- `Rε_{X,*} : D⁺_{𝒜_X}(C_τ/X) ⥤ D⁺_{𝒜'_X}(C_{τ'}/X)`, the restriction of the derived
change-of-topology direct image. -/
abbrev derivedComparisonPushforwardLift (S : CohomologyComparison C) (X : C) :
    (derivedFineWeakSerre S X).FullSubcategory ⥤ (derivedWeakSerre S X).FullSubcategory :=
  (derivedWeakSerre S X).lift ((derivedFineWeakSerre S X).ι ⋙
      (abelianComparisonPushforward S.fineCoverage S.coarseCoverage
        S.coarse_le_fine X).rightDerivedFunctorPlus)
    fun K ↦ derivedWeakSerre_rightDerivedFunctorPlus_obj S X
      (fun F hF ↦ CohomologyComparison.abelianComparisonPushforward_rightAcyclic_of_fineWeakSerre
        S S.vanishingCondition_all X F hF) K.obj K.property

/-- The adjunction `ε_X^{-1} ⊣ Rε_{X,*}` restricted to the two bounded below subcategories. -/
def derivedComparisonAdjunctionLift (S : CohomologyComparison C) (X : C) :
    derivedComparisonPullbackLift S X ⊣ derivedComparisonPushforwardLift S X :=
  (derivedComparisonAdjunction S X).restrictFullyFaithful
    (derivedWeakSerre S X).fullyFaithfulι (derivedFineWeakSerre S X).fullyFaithfulι
    (Iso.refl _) (Iso.refl _)

/-- **Second assertion of Stacks 0EZG.** In the comparison situation of Stacks 0EZ3, for any
object `X` of `C` the derived change-of-topology direct image

`Rε_{X,*} : D⁺_{𝒜_X}(C_τ/X) ⟶ D⁺_{𝒜'_X}(C_{τ'}/X)`

is an equivalence of categories, with quasi-inverse `ε_X^{-1}`. -/
@[stacks 0EZG "second assertion: `Rε_{X,*} : D⁺_{𝒜_X}(C_τ/X) ⟶ D⁺_{𝒜'_X}(C_{τ'}/X)` is an \
equivalence"]
def boundedBelowComparisonEquivalence (S : CohomologyComparison C) (X : C) :
    (derivedFineWeakSerre S X).FullSubcategory ≌
      (derivedWeakSerre S X).FullSubcategory :=
  haveI hu : ∀ K : (derivedWeakSerre S X).FullSubcategory,
      IsIso ((derivedComparisonAdjunctionLift S X).unit.app K) := fun K ↦ by
    have h : IsIso ((derivedWeakSerre S X).ι.map
        ((derivedComparisonAdjunctionLift S X).unit.app K)) := by
      dsimp only [derivedComparisonAdjunctionLift]
      rw [Adjunction.map_restrictFullyFaithful_unit_app]
      simpa using isIso_derivedComparisonAdjunction_unit_app S S.vanishingCondition_all X K.obj
        K.property
    exact isIso_of_reflects_iso _ (derivedWeakSerre S X).ι
  haveI hc : ∀ K : (derivedFineWeakSerre S X).FullSubcategory,
      IsIso ((derivedComparisonAdjunctionLift S X).counit.app K) := fun K ↦ by
    have h : IsIso ((derivedFineWeakSerre S X).ι.map
        ((derivedComparisonAdjunctionLift S X).counit.app K)) := by
      dsimp only [derivedComparisonAdjunctionLift]
      rw [Adjunction.map_restrictFullyFaithful_counit_app]
      simpa using isIso_derivedComparisonAdjunction_counit_app S X K.obj
    exact isIso_of_reflects_iso _ (derivedFineWeakSerre S X).ι
  (derivedComparisonAdjunctionLift S X).toEquivalence.symm

/-- **Stacks 0EZG**, the identification of the functor of the equivalence with the restriction
of the derived change-of-topology direct image `Rε_{X,*}`. -/
@[stacks 0EZG "the second assertion: the functor of the equivalence is `Rε_{X,*}`"]
theorem boundedBelowComparisonEquivalence_functor (S : CohomologyComparison C) (X : C) :
    (boundedBelowComparisonEquivalence S X).functor =
      derivedComparisonPushforwardLift S X :=
  rfl

/-- **Stacks 0EZG**, the identification of the quasi-inverse of the equivalence with the
restriction of the change-of-topology inverse image `ε_X^{-1}`. -/
@[stacks 0EZG "the second assertion: the quasi-inverse of the equivalence is `ε_X^{-1}`"]
theorem boundedBelowComparisonEquivalence_inverse (S : CohomologyComparison C) (X : C) :
    (boundedBelowComparisonEquivalence S X).inverse =
      derivedComparisonPullbackLift S X :=
  rfl

end Stacks.ComparingTopologies

end
