module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinCupProduct
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.SingleObjectNaturality

/-!
# The comparison `cohomologyDerivedSingleIso` is natural

`Stacks.DeRham.CohomologicalGysin.cohomologyDerivedSingleIso` identifies the degree-`m`
cohomology of the derived global sections of a sheaf of modules placed in degree `a` with the
cohomology group `H^{m - a}(X, -)`. It is built object by object, from the chosen injective
resolution, by `Stacks.DerivedFunctor.homologyTotalRightDerivedSingleShiftIso`; that construction
is the component of the natural isomorphism
`Stacks.DerivedFunctor.singleShiftCompDerivedCompHomologyIsoRightDerived`
(`Stacks.DerivedFunctor.homologyTotalRightDerivedSingleShiftIso_eq`), so the comparison is natural
in the sheaf. In particular the hypothesis
`Stacks.DeRham.GysinProjection.ComparisonIsNatural` holds on every ringed space.

## Main results

* `Stacks.DeRham.CohomologicalGysin.cohomologyDerivedSingleIso_hom_naturality`: the comparison is
  natural.
* `Stacks.DeRham.GysinProjection.comparisonIsNatural`: the comparison-read map on cohomology
  induced by a morphism of sheaves is the canonical one.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Stacks.Cohomology.SupportedComplexes

namespace Stacks.DeRham.CohomologicalGysin

universe u

open DerivedCategory

section StandardModel

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.Topology.RingedSpaceSheafifyOpens.opensHasSheafifyAddCommGrpCat
  Stacks.Topology.RingedSpaceSheafifyOpens.opensWEqualsLocallyBijectiveAddCommGrpCat
attribute [local instance] Stacks.DeRham.CohomologicalGysin.moduleSheavesHasDerivedCategory

/-- **`cohomologyDerivedSingleIso` is natural in the sheaf of modules.** -/
theorem cohomologyDerivedSingleIso_hom_naturality (X : RingedSpace.{u, u})
    {A A' : _root_.SheafOfModules.{u} (structureSheafRing X)} (ψ : A ⟶ A') (a m : ℤ) (n : ℕ)
    (hn : m - a = n) :
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u} m).map
        ((derivedGlobalSections X).map ((singleFunctor _ a).map ψ)) ≫
      (cohomologyDerivedSingleIso X A' a m n hn).hom =
    (cohomologyDerivedSingleIso X A a m n hn).hom ≫
      (Hfunctor (structureSheafRing X) ⊤ n).map ψ := by
  unfold cohomologyDerivedSingleIso
  rw [Stacks.DerivedFunctor.homologyTotalRightDerivedSingleShiftIso_eq,
    Stacks.DerivedFunctor.homologyTotalRightDerivedSingleShiftIso_eq]
  exact (Stacks.DerivedFunctor.singleShiftCompDerivedCompHomologyIsoRightDerived _ _
    (derivedGlobalSectionsUnit X) (exists_isKInjective_quasiIso_moduleSheaves X)
    a m n hn).hom.naturality ψ

end StandardModel

end Stacks.DeRham.CohomologicalGysin

namespace Stacks.DeRham.GysinProjection

universe u

open Stacks.DeRham.CohomologicalGysin DerivedCategory

section StandardModel

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.Topology.RingedSpaceSheafifyOpens.opensHasSheafifyAddCommGrpCat
  Stacks.Topology.RingedSpaceSheafifyOpens.opensWEqualsLocallyBijectiveAddCommGrpCat
attribute [local instance] Stacks.DeRham.CohomologicalGysin.moduleSheavesHasDerivedCategory

/-- **The comparison-read map on cohomology induced by a morphism of sheaves is the canonical
one**, on every ringed space and at every placement degree: the hypothesis
`ComparisonIsNatural` holds. -/
theorem comparisonIsNatural (X : RingedSpace.{u, u}) (c : ℕ) : ComparisonIsNatural X c := by
  intro q A A' ψ
  rw [cohomologyMapOfModuleHom, Iso.inv_comp_eq,
    cohomologyDerivedSingleIso_hom_naturality]

end StandardModel

end Stacks.DeRham.GysinProjection
