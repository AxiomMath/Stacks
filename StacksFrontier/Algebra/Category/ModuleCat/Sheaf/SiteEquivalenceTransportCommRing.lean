module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteEquivalenceTransport

/-!
# Transporting a sheaf of commutative rings along an equivalence of sites

`Stacks.SheafOfModules.reindexRing` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/SiteEquivalenceTransport.lean` transports a sheaf
of rings along an equivalence of sites `e : C' ≌ C`, with the two sites at independent object and
morphism universes. This file adds the same construction for a sheaf of *commutative* rings.

## Main definitions

* `Stacks.SheafOfModules.reindexCommRingGeneral`: the sheaf of commutative rings transported
  along `e`, i.e. its direct image under `e.functor`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.SheafOfModules

universe w u₁ v₁ u₂ v₂

variable {C : Type u₁} [Category.{v₁} C] {C' : Type u₂} [Category.{v₂} C']
  {J : GrothendieckTopology C}

/-- The sheaf of *commutative* rings transported along an equivalence of sites `e : C' ≌ C`,
that is, the direct image of `𝒪` under `e.functor`, **at independent object and morphism
universes for the two sites**.

This is `Stacks.SheafOfModules.reindexRing` with commutativity not yet forgotten; forgetting it
commutes with the direct image on the nose, so the sheaf of rings underlying this one *is*
`reindexRing J' e` of the sheaf of rings underlying `𝒪`.

`Stacks.SheafOfModules.reindexCommRing` of
`StacksFrontier/AlgebraicGeometry/Topologies/SiteEquivalenceTensor.lean` is the same construction
read where the two sites share their universes; this one is what the derived-level transport of
`StacksFrontier/CategoryTheory/Sites/Cohomology/KFlat/SiteEquivalenceDerivedTensorTransport.lean`
is stated at, the comparison of the small étale site of a scheme with its `Type u` model being a
consumer that genuinely needs the universes apart. -/
abbrev reindexCommRingGeneral (J' : GrothendieckTopology C') (e : C' ≌ C)
    [e.functor.IsContinuous J' J] (O : Sheaf J CommRingCat.{w}) : Sheaf J' CommRingCat.{w} :=
  (e.functor.sheafPushforwardContinuous CommRingCat.{w} J' J).obj O

end Stacks.SheafOfModules

end
