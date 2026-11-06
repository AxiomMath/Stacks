module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.AdditiveGaloisCochains
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.Continuous
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.ModuleUniverseLift
import StacksCore.Tactic.StacksAttribute

/-!
# The additive group of a Galois extension as a discrete Galois module

Let `Ω/K` be a Galois extension, possibly infinite. The additive group of `Ω` with the
tautological action of `Gal(Ω/K)` is a discrete Galois module: the orbit maps are locally
constant, equivalently the stabilizers are open, which is
`Stacks.GaloisCohomology.hasOpenStabilizers`. This file records that module as an object of the
coefficient category of continuous group cohomology, together with its coefficient universe
raised.

## Main definitions

* `Stacks.GaloisCohomology.addContinuousGModule`: the discrete `Gal(Ω/K)`-module `(Ω, +)`.
* `Stacks.GaloisCohomology.addContinuousGModuleLift`: the same module with its coefficient
  universe raised, i.e. with carrier `ULift Ω`.

## References

* [Stacks Project, Tag 04JP](https://stacks.math.columbia.edu/tag/04JP): the category this
  module lives in.
* [Stacks Project, Tag 04JR](https://stacks.math.columbia.edu/tag/04JR): the cohomology groups
  it is a coefficient object for.
* [Stacks Project, Tag 03QV](https://stacks.math.columbia.edu/tag/03QV): the example in which
  this module is `K^{sep}` with addition as group law.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.GaloisCohomology

variable (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]

/-- The additive group of `Ω` with the tautological action of `Gal(Ω/K)`, as a discrete
`Gal(Ω/K)`-module. -/
def addContinuousGModule : ContinuousGModule.{u, u} Gal(Ω/K) :=
  Stacks.GroupCohomology.ofDistribMulAction
    (Stacks.GroupCohomology.isContinuous_ofDistribMulAction_iff.mpr hasOpenStabilizers)

/-- The Galois action on `Stacks.GaloisCohomology.addContinuousGModule` is the Galois action on
`Ω`. -/
@[simp] theorem addContinuousGModule_ρ_hom (g : Gal(Ω/K)) (a : Ω) :
    (((addContinuousGModule K Ω).obj.obj.ρ g).asHom.hom a : Ω) = g • a := rfl

/-- **The discrete Galois module `(Ω, +)` with its coefficient universe raised.** The carrier is
`ULift Ω` and the action is the Galois action. -/
def addContinuousGModuleLift.{s, t} (K Ω : Type s) [Field K] [Field Ω] [Algebra K Ω]
    [IsGalois K Ω] : ContinuousGModule.{s, max s t} Gal(Ω/K) :=
  Stacks.GroupCohomology.uliftContinuousModule.{0, s, s, t} (addContinuousGModule K Ω)

/-- The Galois action on the raised module is the action on the unraised one. -/
@[simp] theorem addContinuousGModuleLift_ρ_hom.{s, t} (K Ω : Type s) [Field K] [Field Ω]
    [Algebra K Ω] [IsGalois K Ω] (g : Gal(Ω/K))
    (a : (addContinuousGModuleLift.{s, t} K Ω).obj.obj.V) :
    (((addContinuousGModuleLift.{s, t} K Ω).obj.obj.ρ g).asHom.hom a).down =
      ((addContinuousGModule K Ω).obj.obj.ρ g).asHom.hom a.down := rfl

end Stacks.GaloisCohomology

end
