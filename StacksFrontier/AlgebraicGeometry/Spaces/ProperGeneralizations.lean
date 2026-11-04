module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianPoints

/-!
# Proper generalizations of a point of an algebraic space

Let `X` be an algebraic space over `S` and let `x` be a point of `X`. The *proper
generalizations* of `x` are the points `x'` of `X` with `x' ⤳ x` and `x' ≠ x`; they form a
subspace of the point space of Stacks 03BX. When `X` is locally Noetherian this subspace is a
Noetherian topological space.

## Main results

* `AlgebraicGeometry.Space.noetherianSpace_properGeneralizations` is the Noetherian half of
  **Stacks 0ED2**.

## Implementation notes

The source assumes `X` decent and locally Noetherian and concludes that the subspace is
Noetherian, spectral, sober and Jacobson. Noetherianity needs neither decency nor
quasi-compactness: by Stacks 04ZF the point space of a locally Noetherian algebraic space is
locally Noetherian, so `x` has a Noetherian open neighbourhood `U`, and every proper
generalization of `x` already lies in `U`. The subspace is therefore a continuous image of an
open subspace of `U`.

`AlgebraicGeometry.Space.pointTopology` is a plain definition rather than an instance and is
made a local instance here.

## References

* [Stacks Project, Tag 0ED2](https://stacks.math.columbia.edu/tag/0ED2)
* [Stacks Project, Tag 04ZF](https://stacks.math.columbia.edu/tag/04ZF)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-- **Stacks 0ED2, the Noetherian property.** The proper generalizations of a point `x` of a
locally Noetherian algebraic space over `S` form a Noetherian topological space. -/
@[stacks 0ED2 "the Noetherian property"]
theorem noetherianSpace_properGeneralizations (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B S hS X)
    (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} ↦ IsLocallyNoetherian Y))
    (x : points B S hS X) :
    NoetherianSpace {x' : points B S hS X // x' ⤳ x ∧ x' ≠ x} := by
  obtain ⟨U, hUopen, hxU, hUN⟩ :=
    isLocallyNoetherianSpace_of_isLocallyNoetherian B S hS X hX hN x
  have : NoetherianSpace U := hUN
  exact NoetherianSpace.of_subset (W := U) fun _ hx' ↦ hx'.1.mem_open hUopen hxU

end AlgebraicGeometry.Space

end
