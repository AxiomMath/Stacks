module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.Separated

/-!
# Descent along a directed inverse system of algebraic spaces

A directed inverse system of quasi-compact and quasi-separated algebraic spaces over a
scheme `S` with affine transition morphisms, together with a chosen limit and a chosen
index, is the standing situation for descent along such a system. It is the algebraic-space
counterpart of `AlgebraicGeometry.DescentSituation`.

## Main definitions

* `AlgebraicGeometry.Space.DescentSituation` is the standing situation for descent along a
  directed inverse system of algebraic spaces with affine transition morphisms.

## Main results

There are no propositional results; this is a standing situation rather than a theorem.

## Implementation notes

Algebraic spaces over `S` are their functors of points on the big fppf site of `S`, so the
inverse system is a functor from the opposite of the directed preorder into that presheaf
category; its chosen limiting presheaf, the projections and their naturality are bundled as
a limit cone, and the algebraic-space condition is imposed on each stage and on the limit
separately. The index universe stays independent of the universe of the site.

Quasi-separatedness is the absolute notion of Stacks 03BS, which is quasi-separatedness over
the terminal scheme; the ambient site therefore has to contain the terminal scheme as well as
the base, which is the hypothesis `hZ`.

## References

* [Stacks Project, Tag 09RH](https://stacks.math.columbia.edu/tag/09RH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace AlgebraicGeometry.Space

/-- **Stacks 09RH.** A directed inverse system of quasi-compact and quasi-separated algebraic
spaces over `S` whose transition morphisms are affine, equipped with a chosen limit cone and a
chosen index. -/
@[stacks 09RH]
structure DescentSituation (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u})) (I : Type v) [Preorder I] [IsDirected I (· ≤ ·)] where
  /-- The inverse system of functors of points. -/
  system : Iᵒᵖ ⥤ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  /-- Each stage is an algebraic space over the base. -/
  algebraicSpace : ∀ i : I, IsAlgebraicSpace B S hS (system.obj (Opposite.op i))
  /-- Every transition morphism is affine. -/
  transition_affine : ∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom B S hS (system.map f)
  /-- Every stage is quasi-compact. -/
  quasiCompact : ∀ i : I, IsQuasiCompactSpace B S hS (system.obj (Opposite.op i))
  /-- Every stage is quasi-separated. -/
  quasiSeparated :
    ∀ i : I, IsAbsolutelyQuasiSeparated B S hS hZ (system.obj (Opposite.op i))
  /-- The chosen cone exhibiting the limit and its projections. -/
  limitCone : Cone system
  /-- The chosen cone is limiting. -/
  isLimit : IsLimit limitCone
  /-- The limit is an algebraic space over the base. -/
  limitAlgebraicSpace : IsAlgebraicSpace B S hS limitCone.pt
  /-- The fixed index of the system. -/
  base : I

end AlgebraicGeometry.Space

end
