module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.AugmentationDerivedBaseChange
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.SimplicialModuleFibrewise
public import StacksFrontier.CategoryTheory.Sites.Modules.DifferentialsRestriction
import StacksCore.Tactic.StacksAttribute

/-!
# The two spellings of restriction to the fibre over a simplicial degree agree

Let `(C, J)` be a small site, let `O` be a sheaf of commutative rings on it and let `Δ × C` carry
the topology inherited along the projection `π`.  Restriction of sheaves of modules to the fibre
`{n} × C` is written twice in this development:

* `Stacks.SimplicialModules.fibreRestrictionMod`, the level `n` of
  `Stacks.SimplicialModules.fibrewiseMod`, which reads a sheaf of `π^{-1}O`-modules as a
  **simplicial** sheaf of `O`-modules and therefore carries structure maps in `n`
  (`Stacks.SimplicialModules.fibrewiseModMap`); and
* `Stacks.Sheaves.Differentials.restrictedModules` at the fibre inclusion `i_n`, stated for one
  fixed continuous and cocontinuous functor of sites, which is the spelling the sheaf of
  differentials and the tensor product are restricted in
  (`Stacks.Sheaves.Differentials.restrictedDifferentialsOfSiteIso` and
  `restrictedSheafTensorRightIso`).

This file proves that **at the sheaf of rings `π^{-1}O` the two are the same functor, on the
nose**, together with the identification of the rings they are taken over.

## Why this is wanted

The two spellings had no bridge, and that is what kept the fibrewise identifications of
`StacksFrontier/Cotangent/SheavesOfRings/FibreDifferentials.lean` and
`StacksFrontier/Cotangent/SheavesOfRings/FibreDifferentialsDegree.lean` from assembling into a
simplicial sheaf of `ℬ`-modules: `restrictedModules` is stated for a fixed functor of sites and
has no functoriality lemma in that functor, while `fibrewiseMod` has exactly that functoriality
and nothing else.  With the bridge below, a sheaf of `π^{-1}O`-modules on `Δ × C` has its fibres
assembled for free, and what remains owed for the first-term identification `e₁` of [Stacks, Tag
09DH] is one statement, named in the implementation notes.

## Main results

* `Stacks.SimplicialModules.restrictedCommRing_fibreInclusion_projectionCommRing`:
  **`i_n^{-1}(π^{-1}O) = O`.**
* `Stacks.SimplicialModules.restrictedModules_fibreInclusion_eq_fibreRestrictionMod`:
  **`restrictedModules J i_n = fibreRestrictionMod C J O n` at `π^{-1}O`.**

## Implementation notes

Both are `rfl`: the fibre inclusion followed by the projection is the identity functor
(`Stacks.SimplicialModules.fibreInclusion_comp_projection`), so the two restrictions of sections
compose to no restriction at all, and both functors are Mathlib's `SheafOfModules.pushforward`
along `i_n` for the identity morphism of sheaves of rings
(`Stacks.SimplicialModules.fibreRingMap`).  Nothing is constructed here; what the file adds is
that the equality is *recorded*, so that `Stacks.SimplicialModules.fibrewiseModMap` may be
quoted as the structure map of a family of `restrictedModules`.

**What is still owed, exactly.**  The bridge supplies the simplicial structure of the *objects*;
it does not make the fibrewise *comparisons* natural in `n`.  For the differentials factor that
is no longer the way in: the base-changed simplicial module of [Stacks, Tag 08SS] is specified by
a universal property, and
`StacksFrontier/Cotangent/SheavesOfRings/SimplicialDerivationFibres.lean` reduces the naturality in
`n` that property asks for to the `d_map` of a derivation on `Δ × C`, so no comparison has to be
made natural there.  What remains needing naturality in `n` is the *tensor* factor, and the rest
of this paragraph describes the obstruction, for both comparisons, independently of that
reduction.  Those comparisons —
`Stacks.Sheaves.Differentials.restrictedSheafTensorRightIso` and
`restrictedDifferentialsOfSiteIso` — are both built from
`Stacks.SheafOfModules.PushforwardSheafification.pushforwardSheafifyIso`, sheafification
commuting with restriction of sections along a continuous and cocontinuous functor of sites, and
that isomorphism is made natural only in the *presheaf*
(`Stacks.SheafOfModules.PushforwardSheafification.pushforwardSheafifyHom_naturality`,
`pushforwardSheafifyNatIso`), not in the functor `G`.  Naturality in `G` is what the assembly of
the degrees needs, and it is not in this tree.  It is a definite statement and not an open
problem: `pushforwardSheafifyHom` is pinned down as an adjoint transpose of the pushed-forward
sheafification unit
(`Stacks.SheafOfModules.PushforwardSheafification.pushforwardSheafifyHom_eq`), so its naturality
in `G` is the compatibility of
`Stacks.SheafOfModules.PushforwardSheafification.pushforwardUnit` with
`CategoryTheory.Functor.sheafPushforwardContinuousNatTrans`, transposed — the same argument as
`pushforwardSheafifyHom_naturality` with the action of `presheafPushforwardFunctor` on a
natural transformation of functors of sites in place of its action on a morphism of presheaves.
The one complication is that `G` and `G'` give *different* restricted sheaves of rings, so the
statement carries a restriction of scalars between them, which is the correction
`Stacks.SimplicialModules.fibrewiseModMap` already applies in the shape
`Stacks.SimplicialModules.fibreRingMap_comp`.

## References

* [Stacks Project, Tag 09D0](https://stacks.math.columbia.edu/tag/09D0), where the projection and
  the fibres are introduced.
* [Stacks Project, Tag 09D1](https://stacks.math.columbia.edu/tag/09D1), a simplicial module as a
  sheaf of modules on `Δ × C`.
* [Stacks Project, Tag 09DH](https://stacks.math.columbia.edu/tag/09DH), the Atiyah triangle,
  whose first-term identification is what wants the fibres assembled.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open Stacks.Sheaves.Differentials (restrictedCommRing restrictedModules)

attribute [local instance_reducible] CategoryTheory.sheafCompose

universe u

namespace Stacks.SimplicialModules

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  [Stacks.Sites.PreservesCoveringPullbacks (projectionTopology C J) (projection C)]
  [(projection C).IsCocontinuous (projectionTopology C J) J]
  (O : Sheaf J CommRingCat.{u}) (n : SimplexCategory)

omit [Stacks.Sites.PreservesCoveringPullbacks (projectionTopology C J) (projection C)]
  [(projection C).IsCocontinuous (projectionTopology C J) J] in
/-- **`i_n^{-1}(π^{-1}O) = O`.**  Restricting a sheaf of commutative rings along the projection
`π : Δ × C ⥤ C` and then along the fibre inclusion `i_n : C ⥤ Δ × C` returns it, because
`i_n ⋙ π` is the identity functor. -/
theorem restrictedCommRing_fibreInclusion_projectionCommRing :
    restrictedCommRing J (fibreInclusion C n) (projectionCommRing J O) = O := rfl

omit [Stacks.Sites.PreservesCoveringPullbacks (projectionTopology C J) (projection C)]
  [(projection C).IsCocontinuous (projectionTopology C J) J] in
/-- **The two spellings of restriction to the fibre over `n` are the same functor.**  At the
sheaf of rings `π^{-1}O`, `Stacks.Sheaves.Differentials.restrictedModules` along the fibre
inclusion is the level `n` of `Stacks.SimplicialModules.fibrewiseMod`.

This is what lets `Stacks.SimplicialModules.fibrewiseModMap` be quoted as the structure map in
`n` of a family of restrictions written in the `restrictedModules` spelling, which is the
spelling the sheaf of differentials and the tensor product are restricted in. -/
theorem restrictedModules_fibreInclusion_eq_fibreRestrictionMod :
    restrictedModules J (fibreInclusion C n) (O₂ := projectionCommRing J O) =
      fibreRestrictionMod C J (Stacks.SheafOfModules.Tensor.ringSheaf O) n := rfl

end Stacks.SimplicialModules

end
