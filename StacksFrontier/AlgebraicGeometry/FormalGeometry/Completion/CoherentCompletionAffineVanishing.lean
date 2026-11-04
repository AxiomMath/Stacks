module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.AdicQuotientDerivedLimit
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.AdicQuotientSliceTowerKoszul
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjectiveLocalization
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.SingleObject
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.ConnectiveHypercohomology
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsOverAnOpen
public import StacksCore.Tactic.StacksAttribute

/-!
# Part (5) of Tag 0A0K on the derived completion: `H^p(U, ℱ^∧) = 0` for `p ≠ 0`

Let `X` be a locally Noetherian scheme, `𝓘 ⊂ 𝒪_X` an arbitrary quasi-coherent sheaf of ideals and
`ℱ` a coherent `𝒪_X`-module. This file proves part (5) of [Stacks, Tag 0A0K] for the derived
completion `ℱ^∧` of `ℱ` along `𝓘` itself, an object of `D(𝒪_X)`: for every affine open `U ⊂ X`
the hypercohomology `H^p(U, ℱ^∧)` vanishes for every integer `p ≠ 0`, positive or negative.

## Main results

* `Stacks.Algebraization.isZero_homology_derivedSections_derivedCompletion_of_isAffineOpen` —
  part (5) of [Stacks, Tag 0A0K], on `ℱ^∧`.

## Implementation notes

The cohomology `H^p(U, -)` of an object of `D(𝒪_X)` is the degree-`p` cohomology of the unbounded
derived sections `Stacks.Cohomology.HypercohomologyEdge.derivedSections` over `U`, the model in
which part (2) of the tag is stated too.

The proof follows the source. Part (3) identifies `ℱ^∧` with `(lim ℱ/𝓘ⁿℱ)[0]` through the
canonical comparison `Stacks.Algebraization.comparisonDerivedCompletionLimitAdicQuotient`, whose
invertibility is `Stacks.Algebraization.isIso_comparisonDerivedCompletionLimitAdicQuotient`. On
`(lim ℱ/𝓘ⁿℱ)[0]` the negative degrees vanish by left t-exactness of `RΓ(U, -)`
(`Stacks.Cohomology.Connective.isZero_homology_derivedSections_of_isZero_negative`), and the
positive degrees are the classical right derived functors of `Γ(U, -)` at `lim ℱ/𝓘ⁿℱ`
(`Stacks.DerivedFunctor.isZero_homologyTotalRightDerived_single_of_rightDerived_isZero`), which
vanish on an affine open by
`Stacks.Algebraization.isZero_cohomology_limit_powerQuotients_of_isAffineOpen` — that is, by
[Stacks, Tag 0A0J] for the adic quotient tower, as in the source.

## References

* [Stacks Project, Tag 0A0K](https://stacks.math.columbia.edu/tag/0A0K)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction Stacks.Cohomology.HypercohomologyEdge
open Stacks.SheafOfModules (opensRingedSite)

universe u

namespace Stacks.Algebraization

attribute [local instance 100000] HasDerivedCategory.standard
attribute [local instance] Stacks.Cohomology.HypercohomologyEdge.evaluation_additive

/-- **A module whose underlying abelian group is zero is zero.** The forgetful functor from
modules to abelian groups is faithful, so it reflects the vanishing of the identity. -/
theorem isZero_of_isZero_forget₂_addCommGrp {R : Type u} [Ring R] {M : ModuleCat.{u} R}
    (h : IsZero ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).obj M)) : IsZero M := by
  refine (IsZero.iff_id_eq_zero M).2
    ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map_injective ?_)
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
  exact h.eq_of_src _ _

/-- **Part (5) of [Stacks, Tag 0A0K]: `H^p(U, ℱ^∧) = 0` for `p ≠ 0` and `U ⊂ X` affine open.** Let
`X` be a locally Noetherian scheme — not assumed quasi-compact — let `𝓘 ⊂ 𝒪_X` be an arbitrary
quasi-coherent sheaf of ideals and let `ℱ` be a coherent `𝒪_X`-module. Then for every affine open
`U ⊂ X` and every integer `p ≠ 0` the degree-`p` hypercohomology over `U` of the derived
completion `ℱ^∧` of `ℱ` along `𝓘`, an object of `D(𝒪_X)`, vanishes.

Part (3) (`Stacks.Algebraization.isIso_comparisonDerivedCompletionLimitAdicQuotient`) identifies
`ℱ^∧` with `(lim ℱ/𝓘ⁿℱ)[0]`; below degree zero the vanishing is left t-exactness of `RΓ(U, -)`,
and above it is the vanishing of the higher cohomology of `lim ℱ/𝓘ⁿℱ` over an affine open,
`Stacks.Algebraization.isZero_cohomology_limit_powerQuotients_of_isAffineOpen`. -/
@[stacks 0A0K "part (5), `H^p(U, ℱ^∧) = 0` for `p ≠ 0` and `U ⊂ X` affine open, on the derived \
completion itself: for a coherent module `ℱ` on a locally Noetherian scheme `X`, which is not \
required to be quasi-compact, and an arbitrary quasi-coherent sheaf of ideals `𝓘`, the degree-`p` \
hypercohomology over an affine open `U` of the derived completion `ℱ^∧` of `ℱ` along `𝓘`, an \
object of `D(𝒪_X)`, vanishes for every integer `p ≠ 0`, negative degrees included. The proof \
reads `ℱ^∧` as `lim ℱ/𝓘ⁿℱ` in degree zero by part (3) and applies the vanishing on that limit"]
theorem isZero_homology_derivedSections_derivedCompletion_of_isAffineOpen
    {X : Scheme.{u}} [IsLocallyNoetherian X] (I : X.IdealSheafData) (ℱ : X.Modules)
    [ℱ.IsCoherent] (U : X.affineOpens) (p : ℤ) (hp : p ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U.1)) p).obj
      ((derivedSections (structureSheafRing X.toRingedSpace) U.1).obj
        ((AlgebraicGeometry.RingedSite.derivedCompletion (opensRingedSite X.sheaf)
            (idealSheafSiteSubmodule I)).obj
          ((DerivedCategory.singleFunctor X.Modules 0).obj ℱ)))) := by
  let O := structureSheafRing X.toRingedSpace
  let L : SheafOfModules.{u} O := (show X.Modules from limit (adicQuotientSystem I ℱ))
  have key : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U.1)) p).obj
      ((derivedSections O U.1).obj
        ((DerivedCategory.singleFunctor (SheafOfModules.{u} O) 0).obj L))) := by
    obtain h | h := hp.lt_or_gt
    · exact Stacks.Cohomology.Connective.isZero_homology_derivedSections_of_isZero_negative
        X.toRingedSpace ((DerivedCategory.singleFunctor (SheafOfModules.{u} O) 0).obj L)
        (fun i hi => DerivedCategory.isZero_of_isGE _ 0 i hi) U.1 p h
    · refine Stacks.DerivedFunctor.isZero_homologyTotalRightDerived_single_of_rightDerived_isZero
        (_root_.SheafOfModules.evaluation O (op U.1)) (derivedSections O U.1)
        ((homotopySections O U.1).totalRightDerivedUnit DerivedCategory.Qh
          (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ)))
        Stacks.Cohomology.Localization.enoughKInjectives L (fun n hn => ?_) 0 p h
      exact isZero_of_isZero_forget₂_addCommGrp (IsZero.of_iso
        (isZero_cohomology_limit_powerQuotients_of_isAffineOpen I ℱ U n hn)
        ((Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso O U.1 n).app L))
  exact IsZero.of_iso key
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U.1)) p).mapIso
      ((derivedSections O U.1).mapIso
        (@asIso _ _ _ _ (comparisonDerivedCompletionLimitAdicQuotient I ℱ)
          (isIso_comparisonDerivedCompletionLimitAdicQuotient I ℱ))))

end Stacks.Algebraization

end
