module

public import StacksFrontier.AlgebraicGeometry.Modules.DerivedMonoidal
public import StacksFrontier.CategoryTheory.Monoidal.ReseatFunctor
public import StacksFrontier.CategoryTheory.Monoidal.ReseatFunctorBraided
public import StacksFrontier.CategoryTheory.Monoidal.Rigid
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedCategoryModelComparison
public import StacksFrontier.Homology.DerivedCategory.ModelComparisonTransport
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorInternalHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafTensorAdditiveOnOpens

/-!
# Left duals in `D(𝒪_X)` at the standard and the locally small model

For a scheme `X` the comparison `D_std(𝒪_X) ⥤ D_ls(𝒪_X)` of the standard and the locally small
model of the derived category is monoidal, from the monoidal structure
`Stacks.SheafOfModules.derivedMonoidalStructure` of Stacks 0FPT at the standard model to
`AlgebraicGeometry.Scheme.Modules.canonicalDerivedMonoidal` at the locally small one. In
particular it carries left duals to left duals.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.derivedMonoidalModelComparison`
* `AlgebraicGeometry.Scheme.Modules.exactPairingOfStandard`
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory

universe u

namespace AlgebraicGeometry.Scheme.Modules

attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive

variable (X : Scheme.{u})

attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor

/-- The monoidal structure of Stacks 0FPT on `D(𝒪_X)` at the standard model, with the derived
tensor product as tensor product: `Stacks.SheafOfModules.derivedMonoidalStructure` at `X`. -/
abbrev standardDerivedMonoidal :
    MonoidalCategory (@DerivedCategory X.Modules _ _ (HasDerivedCategory.standard _)) :=
  @Stacks.SheafOfModules.derivedMonoidalStructure _ X.sheaf _ _ _ _ _

/-- **The comparison of the standard and the locally small model of `D(𝒪_X)` is monoidal**, from
the monoidal structure of Stacks 0FPT at the standard model, with the derived tensor product as
tensor product, to `AlgebraicGeometry.Scheme.Modules.canonicalDerivedMonoidal`. -/
@[instance_reducible]
def derivedMonoidalModelComparison :
    letI := standardDerivedMonoidal X
    letI := canonicalDerivedMonoidal X
    (StacksDraft.DerivedModel.schemeModulesComparison X).functor.Monoidal :=
  @reseatFunctorMonoidal _ _
    (@Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal _ _ _ X.sheaf _ _
      (HasDerivedCategory.standard _)) _ _ _ _
    (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal X.sheaf) _ _
    (StacksDraft.DerivedModel.schemeModulesComparison X).functor
    (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidalModelComparison X.sheaf
      (HasDerivedCategory.standard _) inferInstance
      (StacksDraft.DerivedModel.schemeModulesComparison X).functor
      (StacksDraft.DerivedModel.shrinkComparisonQhIso X.Modules).symm)
    (@Stacks.SheafOfModules.derivedTensorMonoidalIso _ X.sheaf _ _ _ _ _)
    (@Stacks.SheafOfModules.DerivedMonoidal.canonicalUnitIso _ _ _ X.sheaf _ _
      (HasDerivedCategory.standard _))
    (Stacks.SheafOfModules.DerivedMonoidal.monoidalTensorCanonicalIso X.sheaf)
    (Stacks.SheafOfModules.DerivedMonoidal.canonicalUnitIso X.sheaf)

/-- **A left dual at the standard model is a left dual at the locally small model.** If `N` is a
left dual of `K` in `D(𝒪_X)` for the monoidal structure of Stacks 0FPT at the standard model, then
it is one for `AlgebraicGeometry.Scheme.Modules.canonicalDerivedMonoidal` at the locally small
model; both models have the same objects. -/
@[instance_reducible]
def exactPairingOfStandard (K N : @DerivedCategory X.Modules _ _ (HasDerivedCategory.standard _))
    (h : letI := standardDerivedMonoidal X; ExactPairing K N) :
    letI := canonicalDerivedMonoidal X
    ExactPairing ((StacksDraft.DerivedModel.schemeModulesComparison X).functor.obj K)
      ((StacksDraft.DerivedModel.schemeModulesComparison X).functor.obj N) :=
  letI := standardDerivedMonoidal X
  letI := canonicalDerivedMonoidal X
  letI := derivedMonoidalModelComparison X
  ExactPairing.map _ K N

end AlgebraicGeometry.Scheme.Modules

end
