module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Defs

/-!
# Étale morphisms are unramified

Every étale morphism of schemes is unramified.

## Main results

* `AlgebraicGeometry.unramified_of_etale`: an étale morphism of schemes is unramified.

## References

* [Stacks Project, Tag 03II](https://stacks.math.columbia.edu/tag/03II)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- An étale morphism of schemes is unramified. -/
@[stacks 03II "etale_unramified"]
theorem unramified_of_etale {X S : Scheme.{u}} (f : X ⟶ S) [Etale f] : Unramified f := by
  refine ⟨fun x => ?_⟩
  obtain ⟨U, hU, hx, V, hV, hUV, hEt⟩ := (etale_iff_forall_etaleAt f).mp inferInstance x
  let : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
  have : Algebra.Etale Γ(S, V) Γ(X, U) := hEt
  exact ⟨U, hU, hx, V, hV, hUV, inferInstance⟩

end AlgebraicGeometry
