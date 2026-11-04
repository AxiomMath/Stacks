module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactFunctorBoundedBelow
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyZero

/-!
# Derived extension by zero is left adjoint to derived restriction

Let `j : U ⟶ X` be an étale morphism of schemes and let `Λ` be a ring. Extension by zero
`j_!` is left adjoint to restriction `j^{-1}` on sheaves of `Λ`-modules for the small étale
topologies, and `j_!` is exact. So the adjunction descends to the bounded below derived
categories,

`Rj_! ⊣ Rj^{-1} : D⁺(U_étale, Λ) ⟶ D⁺(X_étale, Λ)`.

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleDerivedRestriction`: `Rj^{-1}`, the right derived functor
  of restriction on bounded below derived categories.
* `Stacks.EtaleCohomology.etaleModuleDerivedExtensionByZeroAdj`: the adjunction
  `Rj_! ⊣ Rj^{-1}`.

## Implementation notes

*What this is for.* Several statements in this development carry the adjunction as an
explicit hypothesis, written `adjImmersion`, because it was not constructed anywhere: the
clause (1) of [Stacks, Tag 0G29] at
`Stacks.EtaleCohomology.DerivedUpperShriek.preservesColimit_derivedLowerShriek_of_isGE`, and
the factorisation of the derived upper shriek at
`Stacks.EtaleCohomology.derivedLowerShriekAdjunctionOfFactors`. This module supplies it, so
those hypotheses can be discharged at the small étale site with module coefficients.

*The adjunction is not [Stacks, Tag 08FJ] over again.* Tag 08FJ is the same statement for the
localization morphism of a ringed site, and it is proved, for the unbounded derived category of
`SheafOfModules`, at
`Stacks.Cohomology.Localization.derivedExtensionByZeroRestrictionAdjunction`. That is a
different category and a different derived category from the one here, and it is built by a
different route — `CategoryTheory.Adjunction.localization`, which needs *both* functors exact
because it identifies each derived functor with the localization of the degreewise one. On
`D⁺` the right derived functor is not literally the localization of the degreewise one, so the
route here is `CategoryTheory.Adjunction.rightDerivedFunctorPlus`, which needs only `j_!` to
preserve homology. No tag attribute is claimed: this is the Lean-side substrate for the étale
spelling.

*Exactness of `j_!` for module coefficients* is [Stacks, Tag 03S5], available as the instances
`Stacks.EtaleCohomology.etaleModuleExtensionByZero_preservesFiniteLimits` and
`..._preservesFiniteColimits`. Preserving homology follows, and is the weaker property the
construction actually uses.

## References

* [Stacks Project, Tag 03S5](https://stacks.math.columbia.edu/tag/03S5)
* [Stacks Project, Tag 08FJ](https://stacks.math.columbia.edu/tag/08FJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

universe u r

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [Ring Λ]

/-- Extension by zero of sheaves of `Λ`-modules along an étale morphism preserves homology,
being exact: [Stacks, Tag 03S5]. -/
instance etaleModuleExtensionByZero_preservesHomology {U X : Scheme.{u}} (j : U ⟶ X)
    [Etale j] : (etaleModuleExtensionByZero.{u, r} Λ j).PreservesHomology :=
  Functor.preservesHomologyOfExact _

/-- The bounded below derived restriction `Rj^{-1}` of sheaves of modules along an étale
morphism. Restriction is exact, so this is restriction applied degreewise. -/
abbrev etaleModuleDerivedRestriction {U X : Scheme.{u}} (j : U ⟶ X) [Etale j] :
    DerivedCategory.Plus (EtaleModules.{u, r} Λ X) ⥤
      DerivedCategory.Plus (EtaleModules.{u, r} Λ U) :=
  (etaleModuleRestriction.{u, r} Λ j).rightDerivedFunctorPlus

/-- **Derived extension by zero is left adjoint to derived restriction**: `Rj_! ⊣ Rj^{-1}` on
the bounded below derived categories of sheaves of `Λ`-modules for the small étale topologies
of an étale morphism `j : U ⟶ X`.

The underived adjunction is `Stacks.EtaleCohomology.etaleModuleExtensionByZeroAdj`, and `j_!`
is exact by [Stacks, Tag 03S5], which is what lets it descend. -/
def etaleModuleDerivedExtensionByZeroAdj {U X : Scheme.{u}} (j : U ⟶ X) [Etale j] :
    etaleModuleDerivedExtensionByZero.{u, r} Λ j ⊣ etaleModuleDerivedRestriction.{u, r} Λ j :=
  (etaleModuleExtensionByZeroAdj.{u, r} Λ j).rightDerivedFunctorPlus

end Stacks.EtaleCohomology

end
