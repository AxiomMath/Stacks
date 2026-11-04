module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.NodalPushforward
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherentModules
public import StacksFrontier.AlgebraicGeometry.Topologies.FiniteTypeFromGlobalGenerators

/-!
# A module which is not of finite presentation on its site

`AlgebraicGeometry.Stack.IsCoherent` of Stacks 0GR6 is the conjunction of conditions (1) and (2)
of Stacks 0GR5, and condition (2) is `SheafOfModules.IsFinitePresentationOnSite`, part (7) of
Stacks 03DL.  Nothing in this library refutes that condition for any module, so nothing rules out
the possibility that it, and with it coherence, holds of every module for formal reasons.

This file refutes it.  The necessary condition is that a module of finite presentation on a site
is of finite type in Mathlib's sense, which holds whenever the module and the coefficient rings
share a universe and each slice of the site admits sheafification; the module refuting it is the
direct image of the structure sheaf of the punctured affine line `Spec k[s, 1/s]` along its
closed immersion onto the node `Spec {f ∈ k[s] ∣ f(0) = f(1)}`, which
`Stacks.NodalCurve.not_isFiniteType_pushforward_unit` shows is not of finite type.

## Main results

* `Stacks.CoherentModulesWitness.isFiniteType_of_isFinitePresentationOnSite`: a module of finite
  presentation on a site is of finite type in Mathlib's sense.  This is the necessary condition,
  obtained by composing Stacks 03DL(7) ⟹ 03DL(5) with the comparison of the two renderings of
  part (5).
* `Stacks.CoherentModulesWitness.not_isFiniteTypeOnSite_nodalPushforward` and
  `Stacks.CoherentModulesWitness.not_isFinitePresentationOnSite_nodalPushforward`: the direct
  image of the structure sheaf of the punctured affine line on the node is neither of finite type
  nor of finite presentation on the Zariski site of the node.
* `AlgebraicGeometry.Stack.not_isCoherent_of_not_isFiniteTypeOnSite`: a module on the big fppf
  site of an algebraic stack which is not of finite type on that site is not coherent.

## Implementation notes

The witness lives on the Zariski site of a scheme, not on the big fppf site of an algebraic
stack, so it does not by itself produce a module with `¬ AlgebraicGeometry.Stack.IsCoherent`.
What it settles is that `SheafOfModules.IsFinitePresentationOnSite`, the second conjunct of
`AlgebraicGeometry.Stack.IsCoherent`, is a contingent condition on a ringed site rather than one
that holds of every module: coherence as Stacks 0GR6 states it is therefore not trivially true
for want of content in its definition.  Carrying the witness itself onto a stack would need the
comparison between modules on the big fppf site of a scheme and modules on its Zariski site,
Stacks 03DX, which this library does not have;
`AlgebraicGeometry.Stack.not_isCoherent_of_not_isFiniteTypeOnSite` is the statement such a
comparison would be fed into.

The necessary condition is stated at module universe equal to the ring universe and with
sheafification on every slice, because that is where Mathlib's `SheafOfModules.IsFiniteType` is
defined; both hold on the Zariski site of a scheme and neither holds on the big fppf site of an
algebraic stack, whose objects lie one universe above its coefficient rings.  This is the same
universe constraint that made `AlgebraicGeometry.Stack.IsQuasicoherentFiniteTypeModule` use the
universe-flexible `SheafOfModules.IsFiniteTypeOnSite` in the first place.

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 0GR5](https://stacks.math.columbia.edu/tag/0GR5)
* [Stacks Project, Tag 0GR6](https://stacks.math.columbia.edu/tag/0GR6)
* [Stacks Project, Tag 09VG](https://stacks.math.columbia.edu/tag/09VG)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u v w

namespace Stacks.CoherentModulesWitness

/-- **A sheaf of modules of finite presentation on a site is of finite type in Mathlib's
sense.**  Part (7) of Stacks 03DL implies part (5) in its categorical form, by
`SheafOfModules.isFiniteTypeOnSite_of_isFinitePresentationOnSite`, and the categorical form
implies Mathlib's `SheafOfModules.IsFiniteType`, by
`Stacks.SheafOfModules.isFiniteType_of_isFiniteTypeOnSite`.

This is the necessary condition used below to refute finite presentation on a site. -/
theorem isFiniteType_of_isFinitePresentationOnSite {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}} (M : SheafOfModules.{w} R)
    [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
    [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
    (h : M.IsFinitePresentationOnSite) : M.IsFiniteType :=
  have := h
  Stacks.SheafOfModules.isFiniteType_of_isFiniteTypeOnSite M inferInstance

/-- The direct image `i_* 𝒪_{Spec B}` of the structure sheaf of the punctured affine line
`B = k[s, 1/s]` along the closed immersion `i : Spec B ⟶ Spec A` onto the node
`A = {f ∈ k[s] ∣ f(0) = f(1)}`, as a module on the Zariski site of `Spec A`. -/
noncomputable abbrev nodalPushforwardUnit (k : Type u) [Field k] :
    Scheme.Modules (Spec (Stacks.NodalCurve.nodeRingCat k)) :=
  (Scheme.Modules.pushforward (Stacks.NodalCurve.puncturedLineToNode k)).obj
    (SheafOfModules.unit (Spec (Stacks.NodalCurve.puncturedLineCat k)).ringCatSheaf)

/-- **`i_* 𝒪_{Spec B}` is not of finite type on the Zariski site of the node**, in the
categorical form `SheafOfModules.IsFiniteTypeOnSite` of Stacks 03DL(5).  Were it, it would be of
finite type in Mathlib's sense by `Stacks.SheafOfModules.isFiniteType_of_isFiniteTypeOnSite`,
which `Stacks.NodalCurve.not_isFiniteType_pushforward_unit` forbids: `B` is not a finite
`A`-module. -/
theorem not_isFiniteTypeOnSite_nodalPushforward (k : Type u) [Field k] :
    ¬ SheafOfModules.IsFiniteTypeOnSite (nodalPushforwardUnit k) := fun h ↦
  Stacks.NodalCurve.not_isFiniteType_pushforward_unit k
    (Stacks.SheafOfModules.isFiniteType_of_isFiniteTypeOnSite (nodalPushforwardUnit k) h)

/-- **`i_* 𝒪_{Spec B}` is not of finite presentation on the Zariski site of the node**, in the
sense of `SheafOfModules.IsFinitePresentationOnSite`, part (7) of Stacks 03DL.  It is not even of
finite type there, by `Stacks.CoherentModulesWitness.not_isFiniteTypeOnSite_nodalPushforward`.

This is a concrete module refuting the second conjunct of `AlgebraicGeometry.Stack.IsCoherent`,
so that condition is not one which holds of every module for formal reasons. -/
theorem not_isFinitePresentationOnSite_nodalPushforward (k : Type u) [Field k] :
    ¬ SheafOfModules.IsFinitePresentationOnSite (nodalPushforwardUnit k) := fun h ↦
  have := h
  not_isFiniteTypeOnSite_nodalPushforward k
    (SheafOfModules.isFiniteTypeOnSite_of_isFinitePresentationOnSite (nodalPushforwardUnit k))

end Stacks.CoherentModulesWitness

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A module which is not of finite type on the big fppf site of an algebraic stack is not
coherent.**  Coherence contains condition (1) of Stacks 0GR5, which contains finite type.

This is the shape a negative witness for `AlgebraicGeometry.Stack.IsCoherent` would take: a
module on the site of a stack failing `SheafOfModules.IsFiniteTypeOnSite`, as
`Stacks.CoherentModulesWitness.nodalPushforwardUnit` fails it on the Zariski site of a
scheme. -/
theorem not_isCoherent_of_not_isFiniteTypeOnSite {𝒳 : AlgebraicStacks.{u, v} B S hS}
    {M : SheafOfModules.{w} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids B.topology le_rfl)}
    (hM : ¬ M.IsFiniteTypeOnSite) : ¬ IsCoherent B S hS 𝒳 M :=
  fun h ↦ hM h.1.2

end AlgebraicGeometry.Stack

end
