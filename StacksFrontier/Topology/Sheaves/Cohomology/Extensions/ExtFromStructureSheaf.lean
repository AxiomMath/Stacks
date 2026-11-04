module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.ExtFromUnit
public import StacksFrontier.Topology.Sheaves.Cohomology.Extensions.FirstCohomologyAndExtensions

/-!
# Morphisms out of the structure sheaf compute the cohomology of a ringed space

Let `(X, O_X)` be a ringed space and `F` a sheaf of `O_X`-modules. For every `n` the extension
group `Ext^n_{Mod(O_X)}(O_X, F)` is the sheaf cohomology `H^n(X, F)`. Since `Ext^n(A, B)` is by
definition the group of morphisms `A[0] ⟶ B[0]⟦n⟧` in the derived category of `O_X`-modules,
this says that

$$ \operatorname{Hom}_{D(\mathcal O_X)}(\mathcal O_X, \mathcal F[n]) = H^n(X, \mathcal F) . $$

Two presentations of `H^n(X, F)` are covered: the abelian-group-valued one
`Stacks.Cohomology.SpaceModules.Hgroup R ⊤ n F` of [Stacks, Tag 01E3], which derives sections
over the top open after forgetting the module structure, and the module-valued one
`((SheafOfModules.evaluation R (op ⊤)).rightDerived n).obj F` over the ring `Γ(X, O_X)`, which
is the presentation `AlgebraicGeometry.cohomologyOverField` is built from.

## Main results

* `Stacks.Cohomology.SpaceModules.extEquivCohomology`: `Ext^n(O_X, F) ≃+ H^n(X, F)`.
* `Stacks.Cohomology.SpaceModules.extEquivModuleCohomology`: the same with the module-valued
  presentation of cohomology.
* `Stacks.Cohomology.SpaceModules.derivedHomEquivCohomology` and
  `Stacks.Cohomology.SpaceModules.derivedHomEquivModuleCohomology`: both written with the
  morphism group `Hom_{D(Mod(O_X))}(O_X[0], F[0]⟦n⟧)` of the derived category in place of
  `Ext^n(O_X, F)`.

## Implementation notes

Nothing is proved here beyond assembling three existing comparisons:
`Stacks.Cohomology.SiteModules.extEquivCohomology` on the site of opens, the identification
`Stacks.Cohomology.SpaceModules.cohomologyIsoSiteCohomology` of `H^n(X, -)` with the cohomology
of that site, and `Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso` for the
passage between the module-valued and the abelian-group-valued presentations. The degree-one
case of the first statement is [Stacks, Tag 0B3A],
`Stacks.Cohomology.SpaceModules.extOneEquivFirstCohomology`.

No `@[stacks]` attribute is placed; see the implementation notes of
`StacksFrontier/CategoryTheory/Sites/Cohomology/Modules/ExtFromUnit.lean`.

## References

* [Stacks Project, Tag 0B3A](https://stacks.math.columbia.edu/tag/0B3A)
* [Stacks Project, Tag 01E3](https://stacks.math.columbia.edu/tag/01E3)
* [Stacks Project, Tag 01F1](https://stacks.math.columbia.edu/tag/01F1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace

universe u

namespace Stacks.Cohomology.SpaceModules

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] HasExt.standard

variable {X : Type u} [TopologicalSpace X]
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

/-- **Extensions of the structure sheaf of a ringed space are its cohomology, in every
degree.** For a ringed space `(X, O_X)` and a sheaf of `O_X`-modules `F`, the extension group
`Ext^n(O_X, F)` is canonically `H^n(X, F)`.

In degree one this is [Stacks, Tag 0B3A], `extOneEquivFirstCohomology`. -/
def extEquivCohomology (M : SheafOfModules.{u} R) (n : ℕ) :
    Abelian.Ext (SheafOfModules.unit R) M n ≃+ Hgroup R ⊤ n M :=
  (SiteModules.extEquivCohomology R M n).trans
    (Iso.addCommGroupIsoToAddEquiv ((cohomologyIsoSiteCohomology R n).app M))

/-- In degree one the all-degree comparison is the map of [Stacks, Tag 0B3A]. -/
theorem extEquivCohomology_one (M : SheafOfModules.{u} R) :
    extEquivCohomology R M 1 = extOneEquivFirstCohomology R M := rfl

/-- **Extensions of the structure sheaf are cohomology, in the module-valued presentation.**
The extension group `Ext^n(O_X, F)` is the underlying additive group of the `Γ(X, O_X)`-module
`H^n(X, F)` obtained by deriving module-valued sections over the top open.

This is `extEquivCohomology` composed with
`Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso`, the comparison of the two
presentations of cohomology ([Stacks, Tag 01F1]). -/
def extEquivModuleCohomology (M : SheafOfModules.{u} R) (n : ℕ) :
    Abelian.Ext (SheafOfModules.unit R) M n ≃+
      ((SheafOfModules.evaluation R (op (⊤ : Opens X))).rightDerived n).obj M :=
  (extEquivCohomology R M n).trans
    (Iso.addCommGroupIsoToAddEquiv
      ((ModuleComparison.rightDerivedEvaluationForgetIso R ⊤ n).app M)).symm

/-- **Morphisms out of the structure sheaf in the derived category compute sheaf cohomology.**
The group of morphisms `O_X[0] ⟶ F[0]⟦n⟧` in the derived category of `O_X`-modules is
canonically `H^n(X, F)`. -/
def derivedHomEquivCohomology (M : SheafOfModules.{u} R) (n : ℕ) :
    Abelian.zExt (SheafOfModules.unit R) M (n : ℤ) ≃+ Hgroup R ⊤ n M :=
  Ext.homAddEquiv.symm.trans (extEquivCohomology R M n)

/-- **Morphisms out of the structure sheaf in the derived category compute sheaf cohomology**,
in the module-valued presentation: the group of morphisms `O_X[0] ⟶ F[0]⟦n⟧` in the derived
category of `O_X`-modules is the underlying additive group of the `Γ(X, O_X)`-module
`H^n(X, F)` obtained by deriving module-valued sections over the top open. -/
def derivedHomEquivModuleCohomology (M : SheafOfModules.{u} R) (n : ℕ) :
    Abelian.zExt (SheafOfModules.unit R) M (n : ℤ) ≃+
      ((SheafOfModules.evaluation R (op (⊤ : Opens X))).rightDerived n).obj M :=
  Ext.homAddEquiv.symm.trans (extEquivModuleCohomology R M n)

end Stacks.Cohomology.SpaceModules

end
