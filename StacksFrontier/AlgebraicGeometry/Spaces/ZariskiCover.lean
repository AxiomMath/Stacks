module

public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms

/-!
# Zariski coverings of algebraic spaces

A *Zariski covering* of an algebraic space over a scheme `S` is a family of open subspaces
whose coproduct maps onto it locally for the fppf topology.

## Main definitions

* `AlgebraicGeometry.Space.IsZariskiCover` says that a family of subfunctors of a presheaf
  on the big fppf site of `S` is a Zariski covering of it.

## References

* [Stacks Project, Tag 02YY](https://stacks.math.columbia.edu/tag/02YY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- A family `U` of subfunctors of a presheaf `F` on the big fppf site of `S` is a *Zariski
covering* of `F` when every member is an open subspace and the map from the coproduct of the
members to `F` is locally surjective for the fppf topology. -/
@[stacks 02YY]
abbrev IsZariskiCover (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (I : Type u) (U : I → Subfunctor F) : Prop :=
  (∀ i, IsOpenSubspace B S hS (U i)) ∧
    Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
      (Sigma.desc fun i ↦ (U i).ι)

end AlgebraicGeometry.Space

end
