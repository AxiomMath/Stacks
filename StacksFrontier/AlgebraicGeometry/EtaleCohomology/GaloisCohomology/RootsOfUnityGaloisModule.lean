module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.MultiplicativeGroupGaloisModule
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.InverseImage
import StacksCore.Tactic.StacksAttribute

/-!
# The discrete Galois module of the `n`-th roots of unity

Let `Ω/K` be a Galois extension, possibly infinite.  A Galois automorphism of `Ω` restricts to an
automorphism of the group `μ_n(Ω)` of `n`-th roots of unity, and the resulting action is
continuous for the discrete topology because the stabilizer of a root of unity is the stabilizer
of the underlying element of `Ω`, which is open.  This file records `μ_n(Ω)` as an object of the
coefficient category of continuous group cohomology, together with its coefficient universe
raised, which is the universe in which étale cohomology over `Spec K` computes stalks.

At `Ω = Kˢᵉᵖ` this is the Galois module written `μ_n(K^{sep})` in [Stacks, Tag 03QV], whose
correspondence with the sheaf `μ_n` is clause (4) of that example.

## Main definitions

* `Stacks.GaloisCohomology.rootsOfUnityGalHom`: a Galois automorphism, restricted to `μ_n(Ω)`.
* `Stacks.GaloisCohomology.rootsOfUnityContinuousGModule`: the discrete `Gal(Ω/K)`-module
  `μ_n(Ω)`.
* `Stacks.GaloisCohomology.rootsOfUnityContinuousGModuleLift`: the same module with its
  coefficient universe raised, i.e. with carrier `ULift (Additive μ_n(Ω))`.

## Main results

* `Stacks.GaloisCohomology.isContinuous_ofMulDistribMulAction_rootsOfUnity`: the action is
  continuous, i.e. the stabilizers are open.

## Implementation notes

**No new tag content.**  This is [Stacks, Tag 04JP] — the definition of a discrete `G`-module —
instantiated at the `n`-th roots of unity, in exactly the way
`Stacks.GaloisCohomology.unitsContinuousGModule` instantiates it at the multiplicative group and
`Stacks.GaloisCohomology.addContinuousGModule` at the additive group.  The registration of 04JP
stays on `Stacks.GroupCohomology.ofRepresentation`, of which this is an application.

The action is obtained from `MulEquiv.restrictRootsOfUnity`, which restricts a multiplicative
automorphism of `Ω` to one of `μ_n(Ω)`, through `MulDistribMulAction.compHom`; this avoids
introducing a `SMul` instance on a subgroup of `Ωˣ` that would compete with the pointwise one.

**Universe binders are explicit** on `rootsOfUnityContinuousGModuleLift`, as on its
multiplicative and additive siblings: the raised universe `t` cannot be recovered from the type
of the result, since `max s t` does not determine `t`.

## References

* [Stacks Project, Tag 04JP](https://stacks.math.columbia.edu/tag/04JP): the category this
  module lives in.
* [Stacks Project, Tag 04JR](https://stacks.math.columbia.edu/tag/04JR): the cohomology groups
  it is a coefficient object for.
* [Stacks Project, Tag 03QV](https://stacks.math.columbia.edu/tag/03QV): the example in which
  this module is `μ_n(K^{sep})`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.GaloisCohomology

/-- `ℤ`-modules are regarded as topological spaces with the discrete topology, which is what
makes continuity of an action of a topological group on them a meaningful condition.  This is the
local instance of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.DiscreteModules`, repeated here
because it is local there. -/
local instance : HasForget₂ (ModuleCat.{u} ℤ) TopCat.{u} :=
  { forget₂ := forget (ModuleCat.{u} ℤ) ⋙ TopCat.discrete
    forget_comp := rfl }

section Module

variable (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] (n : ℕ)

/-- **A Galois automorphism restricts to an automorphism of the `n`-th roots of unity.** -/
def rootsOfUnityGalHom : Gal(Ω/K) →* MulAut ↥(rootsOfUnity n Ω) where
  toFun g := MulEquiv.restrictRootsOfUnity g.toRingEquiv.toMulEquiv n
  map_one' := by
    refine MulEquiv.ext fun ζ => Subtype.ext (Units.ext ?_)
    simp
  map_mul' g h := by
    refine MulEquiv.ext fun ζ => Subtype.ext (Units.ext ?_)
    simp

/-- **The Galois action on the `n`-th roots of unity of a Galois extension.** -/
@[instance_reducible] def rootsOfUnityMulDistribMulAction :
    MulDistribMulAction Gal(Ω/K) ↥(rootsOfUnity n Ω) :=
  MulDistribMulAction.compHom _ (rootsOfUnityGalHom K Ω n)

attribute [local instance] rootsOfUnityMulDistribMulAction

omit [IsGalois K Ω] in
/-- The Galois action on the `n`-th roots of unity, computed on the underlying element. -/
theorem coe_coe_rootsOfUnity_smul (g : Gal(Ω/K)) (ζ : ↥(rootsOfUnity n Ω)) :
    (((g • ζ : ↥(rootsOfUnity n Ω)) : Ωˣ) : Ω) = g ((ζ : Ωˣ) : Ω) :=
  rfl

/-- **The Galois action on the `n`-th roots of unity is continuous for the discrete topology**:
the stabilizer of a root of unity is the stabilizer of the underlying element of `Ω`, which is
open because `Ω` is a discrete Galois module. -/
theorem isContinuous_ofMulDistribMulAction_rootsOfUnity :
    (Stacks.GroupCohomology.actionOfRepresentation ℤ Gal(Ω/K) (Additive ↥(rootsOfUnity n Ω))
      (Representation.ofMulDistribMulAction Gal(Ω/K) ↥(rootsOfUnity n Ω))).IsContinuous := by
  rw [Stacks.GroupCohomology.isContinuous_actionOfRepresentation_iff]
  intro x
  have hset : {g : Gal(Ω/K) |
        Representation.ofMulDistribMulAction Gal(Ω/K) ↥(rootsOfUnity n Ω) g x = x} =
      {g : Gal(Ω/K) |
        g • (((Additive.toMul x : ↥(rootsOfUnity n Ω)) : Ωˣ) : Ω) =
          (((Additive.toMul x : ↥(rootsOfUnity n Ω)) : Ωˣ) : Ω)} := by
    ext g
    exact ⟨fun h => congrArg (fun z : ↥(rootsOfUnity n Ω) => ((z : Ωˣ) : Ω))
        (Additive.toMul.injective h),
      fun h => congrArg Additive.ofMul (Subtype.ext (Units.ext h))⟩
  rw [hset]
  exact hasOpenStabilizers _

/-- **Stacks Project, Tag 04JP at the `n`-th roots of unity of a Galois extension.**  The group
`μ_n(Ω)`, written additively, as a discrete `Gal(Ω/K)`-module.  At `Ω = Kˢᵉᵖ` this is the Galois
module `μ_n(Kˢᵉᵖ)` of [Stacks, Tag 03QV]. -/
def rootsOfUnityContinuousGModule : ContinuousGModule.{_, _} Gal(Ω/K) :=
  Stacks.GroupCohomology.ofRepresentation
    (Representation.ofMulDistribMulAction Gal(Ω/K) ↥(rootsOfUnity n Ω))
    (isContinuous_ofMulDistribMulAction_rootsOfUnity K Ω n)

/-- The Galois action on `Stacks.GaloisCohomology.rootsOfUnityContinuousGModule` is the Galois
action on the roots of unity. -/
@[simp] theorem rootsOfUnityContinuousGModule_ρ_hom (g : Gal(Ω/K))
    (ζ : Additive ↥(rootsOfUnity n Ω)) :
    ((((rootsOfUnityContinuousGModule K Ω n).obj.obj.ρ g).asHom.hom ζ :
        Additive ↥(rootsOfUnity n Ω))) =
      Additive.ofMul (rootsOfUnityGalHom K Ω n g ζ.toMul) := rfl

end Module

section Lift

/-- **The discrete Galois module `μ_n(Ω)` with its coefficient universe raised.**  The carrier is
`ULift (Additive μ_n(Ω))` and the action is the Galois action.  At the raise `u + 1` this is the
abelian group in which étale cohomology over `Spec K` computes the stalk of `μ_n`. -/
def rootsOfUnityContinuousGModuleLift.{s, t} (K Ω : Type s) [Field K] [Field Ω] [Algebra K Ω]
    [IsGalois K Ω] (n : ℕ) : ContinuousGModule.{s, max s t} Gal(Ω/K) :=
  Stacks.GroupCohomology.uliftContinuousModule.{0, s, s, t}
    (rootsOfUnityContinuousGModule K Ω n)

end Lift

end Stacks.GaloisCohomology

end
