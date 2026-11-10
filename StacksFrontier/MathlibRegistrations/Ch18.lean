module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafify
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
public import StacksCore.Tactic.StacksAttribute
import StacksCore.Tactic.StacksAttribute

/-!
# Mathlib declarations for Stacks Project Chapter 18, Modules on Sites

Results of Chapter 18 that Mathlib states, registered against their Stacks tags. Where a tag has
several parts, each registration names its part.

* Tag 03A7: the free presheaf of modules on a presheaf of sets (`PresheafOfModules.freeObj`).
* Tag 03CO: limits and colimits of sheaves (`CategoryTheory.Sheaf`).
* Tags 03CT, 03CW: presheaves and sheaves of modules (`PresheafOfModules`, `SheafOfModules`).
* Tags 03CY, 03EI: sheafification of presheaves of modules (`PresheafOfModules.sheafify`,
  `PresheafOfModules.sheafification`).
This file records Stacks Project tags from Chapter 18 (Modules on Sites) whose statements are
already available in Mathlib, by attaching each tag to the Mathlib declarations that state it.
When a tag is covered by several declarations, each registration names the part it covers.
A derivation of sheaves of rings into a sheaf of modules is a
`PresheafOfModulesOfCommRing.Derivation'` of
the underlying presheaves: morphisms of sheaves are morphisms of the underlying presheaves, and
additivity, the Leibniz rule and the vanishing on the image of `O₁` are conditions on sections.
Tag 04EP (exactness of stalk functors at a point of a site) is not registered: Mathlib's points
of a site, `GrothendieckTopology.Point`, are defined differently from Stacks points (Tag 00Y3), and
the equivalence of the two notions is not stated in Mathlib.
* 04BK: `φ`-derivations of a sheaf of rings into a module.
* [Stacks: Modules on Sites](https://stacks.math.columbia.edu/tag/03A4)
-/

add_to_stacks 03A7 "for the constant presheaf of rings ℤ this is the free abelian presheaf \
  U ↦ ℤ[G(U)], and Z_X is its value at the presheaf yoneda X" PresheafOfModules.freeObj

add_to_stacks 03CO "(1) limits exist" CategoryTheory.Sheaf.hasLimitsOfSize
add_to_stacks 03CO "(1) colimits exist" CategoryTheory.Sheaf.instHasColimitsOfSize
add_to_stacks 03CO "(2) and (3): limits, finite direct sums among them, are those of presheaves"
  CategoryTheory.Sheaf.createsLimits
add_to_stacks 03CO "(4) a colimit is the sheafification of the presheaf colimit"
  CategoryTheory.Sheaf.isColimitSheafifyCocone
add_to_stacks 03CO "(5) filtered colimits are exact" CategoryTheory.Sheaf.ab5ofSize

add_to_stacks 03CT "(1) presheaf of O-modules" PresheafOfModules
add_to_stacks 03CT "(2) and (3) morphisms of presheaves of O-modules" PresheafOfModules.Hom
add_to_stacks 03CT "(4) the category PMod(O)" PresheafOfModules.instCategory

add_to_stacks 03CW "(1) sheaf of O-modules" SheafOfModules
add_to_stacks 03CW "(2) and (3) morphisms of sheaves of O-modules" SheafOfModules.Hom
add_to_stacks 03CW "(4) the category Mod(O)" SheafOfModules.instCategory

add_to_stacks 03CY "existence: the sheafification of the underlying abelian presheaf is a sheaf of \
  O^#-modules" PresheafOfModules.sheafify
add_to_stacks 03CY "uniqueness of the O^#-module structure compatible with the square"
  PresheafOfModules.Sheafify.instUniqueSMulCandidate
add_to_stacks 03CY "the commutative square F ⟶ F^#" PresheafOfModules.toSheafify
add_to_stacks 03CY "in addition: maps to sheaves of O^#-modules factor uniquely through F^#"
  PresheafOfModules.sheafifyHomEquiv

add_to_stacks 03EI "left exact: sheafification preserves finite limits"
  PresheafOfModules.instPreservesFiniteLimitsSheafOfModulesSheafification
add_to_stacks 03EI "right exact: sheafification is a left adjoint, so it preserves colimits"
  PresheafOfModules.instIsLeftAdjointSheafOfModulesSheafification

@[expose] public section
open CategoryTheory
add_to_stacks 04BK "for the underlying presheaves of rings and of modules"
  PresheafOfModulesOfCommRing.Derivation'
