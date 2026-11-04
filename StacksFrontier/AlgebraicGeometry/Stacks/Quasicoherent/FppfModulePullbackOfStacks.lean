module

public import StacksFrontier.AlgebraicGeometry.Stacks.ModuleSheafHigherDirectImage
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.DerivedPushforwardQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.QuasicoherentPullbackExactness

/-!
# Inverse image of fppf modules along a 1-morphism of algebraic stacks, at universe `u + 1`

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks. The direct image
`f_* : Mod(𝒪_𝒳) ⥤ Mod(𝒪_𝒴)` of fppf modules, whose total right derived functor is the `Rf_*` of
**Stacks 07BC**, lives at module universe `u + 1`
(`AlgebraicGeometry.Stack.fppfModuleSheafPushforwardOfStacks`). This file records its left
adjoint, the inverse image `f^* = f^{-1}` of **Stacks 06WE** at the same module universe, together
with the adjunction and the exactness of `f^*`: left exact because limits are computed on
sections, right exact because it is a left adjoint.

These are the data of **Stacks 07BE** on the side of modules: the exact functor `f^*` induces
`f^* : D(𝒪_𝒴) ⥤ D(𝒪_𝒳)`, and the adjunction `f^* ⊣ f_*` induces the adjunction of **Stacks 07A6**
used in the proof of the adjointness of `Lf^*_QCoh` and `Rf_{QCoh,*}`.

## Main definitions

* `AlgebraicGeometry.Stack.fppfModulePullbackOfStacks`: `f^*` at module universe `u + 1`.
* `AlgebraicGeometry.Stack.fppfModuleAdjunctionOfStacks`: `f^* ⊣ f_*`.

## References

* [Stacks Project, Tag 06WE](https://stacks.math.columbia.edu/tag/06WE)
* [Stacks Project, Tag 07BE](https://stacks.math.columbia.edu/tag/07BE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Stack

attribute [local instance] hasSheafify_fppfAssociatedTopology_succ
  wEqualsLocallyBijective_fppfAssociatedTopology_succ

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)

/-- **The inverse image `f^* : Mod(𝒪_𝒴) ⥤ Mod(𝒪_𝒳)` of fppf modules along a 1-morphism of
algebraic stacks, at module universe `u + 1`**: `AlgebraicGeometry.Stack.modulePullback`
(**Stacks 06WE**) along the structure functor of `f`, at the base fppf topology, which is the
topology `AlgebraicGeometry.Stack.fppfModuleSheafPushforwardOfStacks` is taken at. -/
abbrev fppfModulePullbackOfStacks :
    fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒴 ⥤ fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒳 :=
  modulePullback.{u, u + 1, u, u + 1, u + 1, u} B S hS 𝒳.val.val.p 𝒴.val.val.p
    𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
    (CatFiberedInGroupoids.homFunctor f.hom) (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
    (B.baseTopology .fppf) (B.baseTopology_le_topology .fppf)

/-- **Stacks 06WE, the adjunction `f^* ⊣ f_*`** on fppf modules of algebraic stacks at module
universe `u + 1`. -/
def fppfModuleAdjunctionOfStacks :
    fppfModulePullbackOfStacks B S hS f ⊣ fppfModuleSheafPushforwardOfStacks B S hS f :=
  moduleSheafAdjunction.{u, u + 1, u, u, u + 1, u} B S hS 𝒳.val.val.p 𝒴.val.val.p
    𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
    (CatFiberedInGroupoids.homFunctor f.hom) (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
    (B.baseTopology .fppf) (B.baseTopology_le_topology .fppf)

/-- The inverse image is additive. -/
instance additive_fppfModulePullbackOfStacks : (fppfModulePullbackOfStacks B S hS f).Additive :=
  additive_modulePullback.{u, u + 1, u, u + 1, u} B S hS _ _ _ _ _ _ _ _

/-- The inverse image is left exact: limits of sheaves of modules are computed on sections. -/
instance preservesFiniteLimits_fppfModulePullbackOfStacks :
    PreservesFiniteLimits (fppfModulePullbackOfStacks B S hS f) :=
  preservesFiniteLimits_modulePullback.{u, u + 1, u, u + 1, u + 1, u} B S hS _ _ _ _ _ _ _ _

/-- The inverse image is right exact, being a left adjoint. -/
instance preservesFiniteColimits_fppfModulePullbackOfStacks :
    PreservesFiniteColimits (fppfModulePullbackOfStacks B S hS f) :=
  preservesFiniteColimits_modulePullback.{u, u + 1, u, u, u + 1, u} B S hS _ _ _ _ _ _ _ _

end AlgebraicGeometry.Stack
