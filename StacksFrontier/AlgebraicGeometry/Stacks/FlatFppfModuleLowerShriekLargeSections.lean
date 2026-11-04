module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LowerShriekUnitOfFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfDerivedModuleLowerShriek
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatFppfCoherator

/-!
# The lower shriek of modules for the flat-fppf site, at module universe `u + 1`

Let `𝒳` be an algebraic stack and `g : Sh(𝒳_{flat,fppf}) ⟶ Sh(𝒳_{fppf})` the morphism of ringed
topoi of **Stacks 0788** (2). At module universe `u + 1` — sections one universe above the
structure sheaf of **Stacks 06TV**, the universe of the derived direct image of **Stacks 07BC** —
`g^* = g^{-1}` is `AlgebraicGeometry.Stack.FlatFppf.moduleInverseImage`. This file gives its left
adjoint `g_!` (**Stacks 0789** (2)), the concrete lower shriek of **Stacks 0797**, and proves
`g^* g_! = id`, the invertibility of the unit.

## Main definitions

* `AlgebraicGeometry.Stack.FlatFppf.moduleLowerShriekSucc`: `g_!`.
* `AlgebraicGeometry.Stack.FlatFppf.moduleLowerShriekSuccAdjunction`: `g_! ⊣ g^*`.

## Main results

* `AlgebraicGeometry.Stack.FlatFppf.isIso_moduleLowerShriekSuccAdjunction_unit`: `g^* g_! = id`.

## References

* [Stacks Project, Tag 0789](https://stacks.math.columbia.edu/tag/0789)
* [Stacks Project, Tag 0797](https://stacks.math.columbia.edu/tag/0797)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Stack.FlatFppf

attribute [local instance] hasSheafify_fppfAssociatedTopology_succ
  wEqualsLocallyBijective_fppfAssociatedTopology_succ
  isContinuous_inclusion_topology isCocontinuous_inclusion_topology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- **The lower shriek `g_!` of Stacks 0789 (2) on sheaves of modules at module universe
`u + 1`**: the concrete left adjoint of `g^*` of **Stacks 0797**, push forward as presheaves of
modules and sheafify. -/
abbrev moduleLowerShriekSucc :
    SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒳) ⥤
      SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳) :=
  Stacks.SheafOfModules.lowerShriek.{u + 1} (topology B S hS 𝒳)
    (associatedTopology B S hS 𝒳.val.val.p B.topology) (objectProperty B S hS 𝒳).ι
    (ambientRingStructureSheaf B S hS 𝒳)

/-- The adjunction `g_! ⊣ g^*` of Stacks 0789 (2) on sheaves of modules at module universe
`u + 1`. -/
abbrev moduleLowerShriekSuccAdjunction :
    moduleLowerShriekSucc B S hS 𝒳 ⊣ moduleInverseImage B S hS 𝒳 :=
  Stacks.SheafOfModules.lowerShriekAdjunction.{u + 1} (topology B S hS 𝒳)
    (associatedTopology B S hS 𝒳.val.val.p B.topology) (objectProperty B S hS 𝒳).ι
    (ambientRingStructureSheaf B S hS 𝒳)

/-- **`g^* g_! = id` (Stacks 0789 (2)) at module universe `u + 1`**: the unit of `g_! ⊣ g^*` is
invertible, the inclusion of the flat objects being fully faithful. -/
instance isIso_moduleLowerShriekSuccAdjunction_unit :
    IsIso (moduleLowerShriekSuccAdjunction B S hS 𝒳).unit :=
  haveI := hasPointwiseRightKanExtension_inclusion_ringCat B S hS 𝒳
  haveI := hasPointwiseRightKanExtension_inclusion_addCommGrpCat_largeSections B S hS 𝒳
  Stacks.SheafOfModules.isIso_lowerShriekAdjunction_unit_of_full.{u + 1} (topology B S hS 𝒳)
    (associatedTopology B S hS 𝒳.val.val.p B.topology) (objectProperty B S hS 𝒳).ι
    (ambientRingStructureSheaf B S hS 𝒳)

end AlgebraicGeometry.Stack.FlatFppf
