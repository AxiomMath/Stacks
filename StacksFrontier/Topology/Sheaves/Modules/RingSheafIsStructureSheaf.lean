module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomLeftExact
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace

/-!
# The two names for the structure sheaf of a ringed space as a sheaf of rings agree

Two developments in this repository turn the structure sheaf of a ringed space into a
`RingCat`-valued sheaf, so that the abstract `SheafOfModules` API applies to it:

* `structureSheaf` (`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/SheafHomLeftExact.lean`), which
  the invertible-module calculus of `StacksFrontier/AlgebraicGeometry/NormInvertible/` uses, in the
  form `structureSheaf X.sheaf`;
* `structureSheafRing` (`Topology/Sheaves/Functors/Module/RingedSpace.lean:81`),
  which `modulePullback`, `modulePushforward` and `moduleRestriction` use.

**They are the same term**, and this file records that with the one-line proof. Both are
`sheafCompose` of the forgetful functor `CommRingCat ⥤ RingCat` applied to `X.sheaf`, so the
categories of sheaves of modules the two developments work in are *equal*, not merely
equivalent, and a sheaf of modules built by one is directly usable by the other with no
transport, no `eqToHom` and no comparison functor.

## Main results

* `Stacks.RingedSpaceModule.ringSheaf_eq_structureSheaf`: the two sheaves of rings are equal.
* `Stacks.RingedSpaceModule.sheafOfModules_ringSheaf_eq`: hence so are the two categories.

## Implementation notes

This is worth stating rather than leaving to `rfl` at each use site because the two names are
not interchangeable to a *reader*: the duplication is invisible until one of them is unfolded,
and the `NormInvertible` development's own implementation notes already record one
`structureSheaf`-versus-`CommRingCat` spelling hazard. It is also worth stating because the
opposite conclusion was expected: the cocycle and generator calculus was built against
`structureSheaf X.sheaf` with no pullback or restriction functor, and the pullback and
restriction functors were built against `structureSheafRing` with no generator calculus, which is
exactly the shape a genuine fork takes.

**A third `structureSheafRing` and a near-namesake, both deliberately left alone.**
`Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪`
(`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorSheafificationComparison.lean`)
takes the sheaf condition as a separate argument and is the spelling the tensor-product and
tensor-power development uses; it too is equal to the two above when instantiated at a ringed
space, and that identification is `Stacks.SheafOfModules.TensorPower.ringedSpaceIsSheaf` together
with `rfl` (`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorPowerRestrictOpen.lean`), not
stated here because `Tag05NA` is not in this import closure. Separately,
`Stacks.SheafOfModules.ringSheaf_eq_structureSheaf`
(`Algebra/Category/ModuleCat/Sheaf/LocalFiniteFreeSummand.lean:179`) has the same *base* name as
the result below but is a different statement about a different pair — a fourth
`structureSheafRing`, the reducible abbreviation
`⟨Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪, h𝒪⟩` of that file, against
`Stacks.SheafOfModules.TensorSheafification.structureSheaf`. The two fully-qualified names differ,
so the modules are not mutually unimportable; the collision is only on a reader.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.RingedSpaceModule

/-- **The structure sheaf of a ringed space, read as a sheaf of rings, has one value under two
names.** -/
theorem ringSheaf_eq_structureSheaf (X : RingedSpace.{u, u}) :
    structureSheafRing X = structureSheaf X.sheaf :=
  rfl

/-- The two categories of sheaves of modules on a ringed space are the same category. -/
theorem sheafOfModules_ringSheaf_eq (X : RingedSpace.{u, u}) :
    SheafOfModules.{u} (structureSheafRing X) =
      SheafOfModules.{u} (structureSheaf X.sheaf) :=
  rfl

end Stacks.RingedSpaceModule
