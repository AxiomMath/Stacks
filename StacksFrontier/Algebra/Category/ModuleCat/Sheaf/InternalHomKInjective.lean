module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Abelian
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoextendScalarsKInjective
public import StacksFrontier.Topology.Sheaves.Functors.Module.HomSheaf
public import StacksCore.Tactic.StacksAttribute

/-!
# K-injectivity of the internal Hom for sheaves of modules

For a morphism `φ : O ⟶ O'` of sheaves of rings on a site, the internal Hom
`SheafHom_O(O', -)` from the target ring sheaf sends K-injective complexes of `O`-modules to
K-injective complexes of `O'`-modules.

The internal Hom functor is `RingedSpaceModuleAdjunction.homSheaf φ`, and the input to the
K-injectivity criterion is its adjunction
`RingedSpaceModuleAdjunction.restrictScalarsHomAdjunction φ` with restriction of scalars.

## Main results

* `Stacks.Sheaves.KInjectiveInternalHom.isKInjective_homSheaf`: the internal Hom from the target
  ring sheaf preserves
  K-injectivity.

## Implementation notes

The criterion applied is `CochainComplex.isKInjective_mapHomologicalComplex_of_exact`: a right
adjoint whose left adjoint is exact preserves K-injectivity.  The left adjoint here is
restriction of scalars along `φ`, which is exact by
`Stacks.SheafOfModules.CoextendScalars.preservesFiniteLimits_restrictScalars` and
`Stacks.SheafOfModules.CoextendScalars.preservesFiniteColimits_restrictScalars`.

The additive structure on the internal Hom functor needed to apply it degreewise to cochain
complexes is the one its adjunction supplies, which is why it appears as a `letI` in the
statement rather than as an instance.

## References

* [Stacks Project, Tag 093Z](https://stacks.math.columbia.edu/tag/093Z)
-/

@[expose] public section

open CategoryTheory

universe u

namespace Stacks.Sheaves.KInjectiveInternalHom

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify J AddCommGrpCat.{u}]
  {O O' : Sheaf J RingCat.{u}}

/-- **Stacks Project, Tag 093Z.** Internal Hom from `O'` takes K-injective complexes of
`O`-modules to K-injective complexes of `O'`-modules. -/
@[stacks 093Z]
theorem isKInjective_homSheaf (φ : O ⟶ O')
    (I : CochainComplex (SheafOfModules.{u} O) ℤ) [I.IsKInjective] :
    letI := (RingedSpaceModuleAdjunction.restrictScalarsHomAdjunction φ).right_adjoint_additive
    CochainComplex.IsKInjective
      (((RingedSpaceModuleAdjunction.homSheaf φ).mapHomologicalComplex (.up ℤ)).obj I) :=
  let : (RingedSpaceModuleAdjunction.homSheaf φ).Additive :=
    (RingedSpaceModuleAdjunction.restrictScalarsHomAdjunction φ).right_adjoint_additive
  CochainComplex.isKInjective_mapHomologicalComplex_of_exact _ _
    (RingedSpaceModuleAdjunction.restrictScalarsHomAdjunction φ) I

end Stacks.Sheaves.KInjectiveInternalHom

end
