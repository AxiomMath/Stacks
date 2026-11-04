module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.AffineAdicTowerPseudoCoherent
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.CohomologyAffineAdicComparison
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorAmplitudeRestriction
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectDerivedSections
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.QuasicoherentCohomology
public import StacksFrontier.RingTheory.Module.AdicSystem.PseudoCoherentHomology

/-!
# Cohomology of the derived completion over an affine open

Let `X` be a locally Noetherian scheme, `ℐ ⊂ 𝒪_X` a quasi-coherent sheaf of ideals, `K` a
pseudo-coherent object of `D(𝒪_X)` and `U ⊂ X` an affine open, and write `A = Γ(X, U)`,
`I = ℐ(U)`. We prove

`H^q(U, K^∧) ≅ lim_n H^q(RΓ(U, K) ⊗^𝐋_A A/Iⁿ⁺¹)`,

and that the tower `n ↦ H^q(RΓ(U, K) ⊗^𝐋_A A/Iⁿ⁺¹)` is Mittag-Leffler.

The tower on the right is the derived reduction tower of the complex of `A`-modules `RΓ(U, K)`,
formed by `NoetherianAdicCompletion.idealPowerQuotientSystem` over the Noetherian ring `A`; it is
not the sheaf-level tower `AlgebraicGeometry.RingedSite.adicReductionTower` evaluated at `U`.

## Main results

All in the namespace `Stacks.Algebraization`.

* `isPseudoCoherent_derivedSections_of_isPseudoCoherent`: for `K` pseudo-coherent and `U` affine,
  `RΓ(U, K)` is a pseudo-coherent complex of `A`-modules.
* `isMittagLefflerCategorical_derivedReduction_derivedSections_of_isAffineOpen`: the tower
  `n ↦ H^q(RΓ(U, K) ⊗^𝐋_A A/Iⁿ⁺¹)` is Mittag-Leffler.
* `nonempty_iso_homology_derivedSections_derivedCompletion_limit_derivedReduction`:
  `H^q(U, K^∧) ≅ lim_n H^q(RΓ(U, K) ⊗^𝐋_A A/Iⁿ⁺¹)`.

## Implementation notes

The two spellings of derived sections, `AlgebraicGeometry.derivedSectionsUnbounded X U` and
`Stacks.Cohomology.HypercohomologyEdge.derivedSections (structureSheafRing X.toRingedSpace) U`,
are the same term: both are the total right derived functor of `SheafOfModules.evaluation` along
the quasi-isomorphisms.

## References

* [Stacks Project, Tag 0A0K](https://stacks.math.columbia.edu/tag/0A0K)
* [Stacks Project, Tag 0CQI](https://stacks.math.columbia.edu/tag/0CQI)
* [Stacks Project, Tag 0EGV](https://stacks.math.columbia.edu/tag/0EGV)
* [Stacks Project, Tag 08E5](https://stacks.math.columbia.edu/tag/08E5)
* [Stacks Project, Tag 08E7](https://stacks.math.columbia.edu/tag/08E7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.SheafOfModules (opensRingedSite)
open Stacks.Cohomology.HypercohomologyEdge (derivedSections)
open Stacks.PseudoCoherent.AdicCompletion
  (pseudoCoherent_mittagLeffler_and_adicCompletion_iso_limit_derivedReduction)

universe u

namespace Stacks.Algebraization

attribute [local instance 100000] HasDerivedCategory.standard

variable {X : Scheme.{u}} [IsLocallyNoetherian X] (𝓘 : X.IdealSheafData)
  (K : DerivedCategory X.Modules) (U : X.affineOpens)

omit [IsLocallyNoetherian X] in
/-- For `K` a pseudo-coherent object of `D(𝒪_X)` and `U` an affine open, the derived sections
`RΓ(U, K)` form a pseudo-coherent object of `D(Γ(X, U))`. -/
public theorem isPseudoCoherent_derivedSections_of_isPseudoCoherent
    (hK : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) K) :
    StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((derivedSections (structureSheafRing X.toRingedSpace) U.1).obj K) :=
  (isPseudoCoherent_derivedRestrictModules_iff_derivedSections K
      (isQuasicoherentDerived_of_isPseudoCoherent X K hK) U.2).1
    (AlgebraicGeometry.RingedSpace.isPseudoCoherent_derivedRestrictModules K hK U.1)

/-- For `X` locally Noetherian, `ℐ` a quasi-coherent sheaf of ideals, `K` a pseudo-coherent
object of `D(𝒪_X)` and `U` an affine open, with `A = Γ(X, U)` and `I = ℐ(U)`, the tower
`n ↦ H^q(RΓ(U, K) ⊗^𝐋_A A/Iⁿ⁺¹)` of `A`-modules is Mittag-Leffler in every degree `q`. -/
public theorem isMittagLefflerCategorical_derivedReduction_derivedSections_of_isAffineOpen
    (hK : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) K) (q : ℤ)
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct Γ(X, U.1)) :
    IsMittagLefflerCategorical
      ((NoetherianAdicCompletion.idealPowerQuotientSystem (𝓘.ideal U) ⋙
          T.tensor.obj ((derivedSections (structureSheafRing X.toRingedSpace) U.1).obj K)) ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U.1)) q) := by
  have : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  exact isMittagLefflerCategorical_of_isMittagLeffler_forget _
    (pseudoCoherent_mittagLeffler_and_adicCompletion_iso_limit_derivedReduction
      Γ(X, U.1) (𝓘.ideal U)
      ((derivedSections (structureSheafRing X.toRingedSpace) U.1).obj K) T
      (isPseudoCoherent_derivedSections_of_isPseudoCoherent K U hK) q).1

/-- For `X` locally Noetherian, `ℐ` a quasi-coherent sheaf of ideals, `K` a pseudo-coherent
object of `D(𝒪_X)` and `U` an affine open, with `A = Γ(X, U)` and `I = ℐ(U)`, there is an
isomorphism of `A`-modules `H^q(U, K^∧) ≅ lim_n H^q(RΓ(U, K) ⊗^𝐋_A A/Iⁿ⁺¹)`, where `K^∧` is the
derived `ℐ`-adic completion of `K`. -/
public theorem nonempty_iso_homology_derivedSections_derivedCompletion_limit_derivedReduction
    (hK : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) K) (q : ℤ)
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct Γ(X, U.1)) :
    Nonempty ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U.1)) q).obj
        ((derivedSections (structureSheafRing X.toRingedSpace) U.1).obj
          ((AlgebraicGeometry.RingedSite.derivedCompletion (opensRingedSite X.sheaf)
            (idealSheafSiteSubmodule 𝓘)).obj K)) ≅
      limit ((NoetherianAdicCompletion.idealPowerQuotientSystem (𝓘.ideal U) ⋙
          T.tensor.obj ((derivedSections (structureSheafRing X.toRingedSpace) U.1).obj K)) ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U.1)) q)) := by
  have : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  obtain ⟨e⟩ := (pseudoCoherent_mittagLeffler_and_adicCompletion_iso_limit_derivedReduction
    Γ(X, U.1) (𝓘.ideal U)
    ((derivedSections (structureSheafRing X.toRingedSpace) U.1).obj K) T
    (isPseudoCoherent_derivedSections_of_isPseudoCoherent K U hK) q).2
  obtain ⟨c, -, hbij, -⟩ :=
    existsUnique_bijective_adicComparison_homology_derivedSections 𝓘 K U hK q
  exact ⟨(LinearEquiv.ofBijective c hbij).symm.toModuleIso ≪≫ e⟩

end Stacks.Algebraization

end
