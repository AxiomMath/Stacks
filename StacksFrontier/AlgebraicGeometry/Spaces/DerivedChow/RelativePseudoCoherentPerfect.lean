module

public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedChow.RelativePseudoCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.BoundedAboveCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.GlobalSectionsRepresentedAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectCompactQcqs
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PseudoCoherentSectionsTensor
import StacksCore.Tactic.StacksAttribute

/-!
# Pseudo-coherence relative to the base from derived sections against perfect objects

Let `X` be an algebraic space separated and of finite presentation over a ring `A` and `K` an
object of `D_QCoh(𝒪_X)` such that `RΓ(X, E ⊗^𝐋 K)` is pseudo-coherent over `A` for every perfect
`E`. Then `K` is pseudo-coherent relative to `A`, following the proof of Stacks 0GFJ: testing
against the dual of a perfect generator shows that `K` is bounded above (Stacks 0GFH), so the
hypothesis extends to pseudo-coherent `E` (Stacks 0CWH), and Stacks 0CTT applies.

## Main results

* `isRelativelyPseudoCoherent_of_isPseudoCoherent_derivedSections_tensor_perfect`: if `X` is
  separated and of finite presentation over `A` and `RΓ(X, E ⊗^𝐋 K)` is pseudo-coherent over `A`
  for every perfect `E`, then `K` is pseudo-coherent relative to `A`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading)
open AlgebraicGeometry.Space.DerivedChow

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits
attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective
  SmallEtale.instHasSheafifyOver SmallEtale.instWEqualsLocallyBijectiveOver

variable (B : BigFppfSite.{u}) {A : Type u} [CommRing A] (hA : B.Contains (Spec (CommRingCat.of A)))

/-- Let `X` be an algebraic space separated and of finite presentation over `A` and
`K ∈ D_QCoh(𝒪_X)` with `RΓ(X, E ⊗^𝐋 K)` pseudo-coherent over `A` for every perfect `E`. Then `K`
is pseudo-coherent relative to `A`. -/
@[stacks 0GFJ]
theorem isRelativelyPseudoCoherent_of_isPseudoCoherent_derivedSections_tensor_perfect
    {X : AlgebraicSpaces B (Spec (CommRingCat.of A)) hA}
    (hsep : IsSeparated B _ hA (toBase B _ hA X).hom)
    (hfp : IsFinitePresentation B _ hA (toBase B _ hA X).hom)
    (K : DerivedCategory (Modules.{u, u} B _ hA X.1 X.2)) (hK : QcohDerived B _ hA X K)
    (h : ∀ E : DerivedCategory (Modules.{u, u} B _ hA X.1 X.2),
      (smallEtaleRingedSite B _ hA X.1 X.2).IsPerfect E →
        StacksDraft.PseudoCoherence.IsPseudoCoherent
          ((representedAffineDerivedSections B _ hA (baseSiteObj B _ hA)).obj
            ((derivedModulePushforward B _ hA (toBase B _ hA X)).obj
              (((smallEtaleDerivedTensor B _ hA X).obj E).obj K)))) :
    IsRelativelyPseudoCoherent B _ hA X.1 X.2 (toBase B _ hA X).hom
      (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B _ hA hfp.1) ⟨K, hK⟩ := by
  obtain ⟨hYqc, hYqs⟩ := isQuasiCompactSpace_and_isAbsolutelyQuasiSeparated_yoneda_of_isAffine
    (B := B) (S := Spec (CommRingCat.of A)) (hS := hA) (U := baseSiteObj B _ hA)
  obtain ⟨hqc, hqs⟩ := qcqs_of_isFinitePresentation B _ hA B.contains_terminal X.2
    (isAlgebraicSpace_yoneda B _ hA _) hYqc hYqs hfp
  obtain ⟨G, hG, hgen⟩ := exists_isPerfect_generator X hqc hqs
  obtain ⟨a, ha⟩ := (h _ (isPerfect_smallEtaleDerivedDual B _ hA X G hG)).exists_isLE
  have hout := (tfae_isLE_of_isPerfect_generator X hqc hqs G hG (fun E hE => (hgen E).2 hE)
    ⟨K, hK⟩).out 5 1
  obtain ⟨b, hb⟩ := hout.1 ⟨a + 1, fun i hi =>
      (isZero_homology_derivedModuleGlobalSectionsSmallEtale_iff_derivedModulePushforward
        (toBase B _ hA X) _ i).2 fun g =>
          eq_zero_of_isLE_representedAffineDerivedSections (baseSiteObj B _ hA) _ ha
            (by omega) g⟩
  exact isRelativelyPseudoCoherent_of_isPseudoCoherent_derivedSections_tensor B hA hsep hfp
    K hK (isPseudoCoherent_representedAffineDerivedSections_tensor (toBase B _ hA X) hqc hqs K hK
      ⟨b, hb⟩ h)

end AlgebraicGeometry.Space

end
