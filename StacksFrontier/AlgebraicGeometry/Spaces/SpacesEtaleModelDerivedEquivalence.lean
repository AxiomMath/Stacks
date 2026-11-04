module

public import StacksFrontier.AlgebraicGeometry.Spaces.BaseRingTensorModuleQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleModelModules
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.GlueingForHomsOverACover

/-!
# The derived category of the spaces-étale model is the derived category of `𝒪_X`-modules

The equivalence `AlgebraicGeometry.Space.spacesEtaleModelModulesEquiv` between sheaves of modules
on the model of the ringed spaces-étale site of an algebraic space `X` and the `𝒪_X`-modules is an
equivalence of abelian categories, so both of its halves are exact and it induces an equivalence
of unbounded derived categories.  This is what transports statements about `D(𝒪_X)` — for
instance about morphisms out of a perfect generator — to the spaces-étale model, where the
morphism `X ⟶ (pt, R)` and its derived pullback and pushforward live.

## Main definitions

* `AlgebraicGeometry.Space.spacesEtaleModelDerivedEquiv`: the equivalence
  `D((X_{spaces,étale})_model, 𝒪_X) ≌ D(𝒪_X)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- **The derived equivalence of the spaces-étale model with `𝒪_X`-modules**, induced by the
exact equivalence `AlgebraicGeometry.Space.spacesEtaleModelModulesEquiv`. -/
def spacesEtaleModelDerivedEquiv :
    DerivedCategory (spacesEtaleModelRingedTopos B S hS X).Modules ≌
      DerivedCategory (Modules.{u, u} B S hS X.1 X.2) :=
  let e := spacesEtaleModelModulesEquiv B S hS X
  haveI : PreservesFiniteLimits e.functor := @PreservesLimitsOfSize.preservesFiniteLimits.{0, 0}
    _ _ _ _ _ e.symm.toAdjunction.rightAdjoint_preservesLimits
  haveI : PreservesFiniteColimits e.functor :=
    @PreservesColimitsOfSize.preservesFiniteColimits.{0, 0} _ _ _ _ _
      e.toAdjunction.leftAdjoint_preservesColimits
  haveI : PreservesFiniteLimits e.inverse := @PreservesLimitsOfSize.preservesFiniteLimits.{0, 0}
    _ _ _ _ _ e.toAdjunction.rightAdjoint_preservesLimits
  haveI : PreservesFiniteColimits e.inverse :=
    @PreservesColimitsOfSize.preservesFiniteColimits.{0, 0} _ _ _ _ _
      e.symm.toAdjunction.leftAdjoint_preservesColimits
  haveI : PreservesBinaryBiproducts e.functor :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  haveI : e.functor.Additive := Functor.additive_of_preservesBinaryBiproducts _
  Stacks.DerivedGlueing.mapDerivedCategoryEquivalence e.functor e.inverse e.unitIso e.counitIso

end AlgebraicGeometry.Space

end
