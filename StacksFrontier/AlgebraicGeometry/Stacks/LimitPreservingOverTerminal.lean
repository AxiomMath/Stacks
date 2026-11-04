module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalOverTerminal
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.LimitPreservingOnObjects

/-!
# Limit preservation of the structure morphism, at a free morphism universe

`AlgebraicGeometry.BigFppfOver.IsLimitPreservingOnObjects` (Stacks 06CU) takes its source and
target as two objects of one 2-category of categories fibred in groupoids, so they must have the
same morphism and object universes. The structure morphism of `𝒳` has as its target
`AlgebraicGeometry.Stack.terminalCFG`, the site itself, whose morphism universe is the site's own
`u`. Stating limit preservation of the structure morphism therefore pins `𝒳` to morphism
universe `u` as well — even though the condition says nothing about the morphisms of the target
beyond those of the site.

That pinning is what keeps Artin's criterion from applying to a category fibred in groupoids
whose fibres have large hom types, such as `AlgebraicGeometry.curvesFiberedCategory`, where a
morphism of families carries a morphism of algebraic spaces and so lives in `Type (u + 1)`.

`IsLimitPreservingOverTerminal` is the same condition written out for the structure morphism
alone, with no mention of the target as an object of the 2-category, and so with `𝒳`'s universes
free. It agrees with the pinned form definitionally wherever the latter is stated.

## Main definitions

* `AlgebraicGeometry.Stack.IsLimitPreservingOverTerminal` — limit preservation on objects of the
  structure morphism `𝒳 ⟶ (Sch/S)_{fppf}`, at a free morphism universe for `𝒳`.

## Main results

* `AlgebraicGeometry.Stack.isLimitPreservingOverTerminal_iff` — it is the pinned condition.

## References

* [Stacks Project, Tag 06CU](https://stacks.math.columbia.edu/tag/06CU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u v w v₂ u₂

/-- **Stacks 06CU for the structure morphism, at a free morphism universe for `𝒳`.** Every object
of `𝒳` over an affine cofiltered limit descends, up to a vertical isomorphism, to a finite stage,
compatibly with a prescribed cartesian comparison in the site.

This is `AlgebraicGeometry.BigFppfOver.IsLimitPreservingOnObjects` of the structure morphism
`𝒳 ⟶ (Sch/S)_{fppf}`, written out: the target of that morphism is the site, whose fibres are
those of the identity functor, so nothing in the condition refers to a second category fibred in
groupoids and the universes of `𝒳` are unconstrained. -/
public def IsLimitPreservingOverTerminal
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 : CatFiberedInGroupoids.{u, v₂, u + 1, u₂} (BigFppfOver B S hS)) : Prop :=
  ∀ (I : Type v) [Category.{w} I] [IsCofiltered I]
    (D : I ⥤ BigAffineFppf B S hS) (c : Cone D),
    IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c) →
    ∀ (i : I)
      (y : (𝟭 (BigFppfOver B S hS)).Fiber
        ((BigAffineFppf.inclusion B S hS).obj (D.obj i)))
      (x : 𝒳.val.p.Fiber ((BigAffineFppf.inclusion B S hS).obj c.pt))
      (γ : 𝒳.val.p.obj x.1 ⟶ y.1),
      (𝟭 (BigFppfOver B S hS)).IsStronglyCartesian
        ((BigAffineFppf.inclusion B S hS).map (c.π.app i)) γ →
      ∃ (i' : I) (j : i' ⟶ i)
        (x' : 𝒳.val.p.Fiber ((BigAffineFppf.inclusion B S hS).obj (D.obj i')))
        (xU : 𝒳.val.p.Fiber ((BigAffineFppf.inclusion B S hS).obj c.pt))
        (δ : xU.1 ⟶ x'.1) (β : xU.1 ⟶ x.1)
        (γ' : 𝒳.val.p.obj x'.1 ⟶ y.1),
        𝒳.val.p.IsStronglyCartesian
          ((BigAffineFppf.inclusion B S hS).map (c.π.app i')) δ ∧
        𝒳.val.p.IsHomLift
          (𝟙 ((BigAffineFppf.inclusion B S hS).obj c.pt)) β ∧ IsIso β ∧
        (𝟭 (BigFppfOver B S hS)).IsStronglyCartesian
          ((BigAffineFppf.inclusion B S hS).map (D.map j)) γ' ∧
        𝒳.val.p.map δ ≫ γ' = 𝒳.val.p.map β ≫ γ

/-- The free-universe condition is the pinned one, wherever the latter can be stated. -/
public theorem isLimitPreservingOverTerminal_iff
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)) :
    IsLimitPreservingOverTerminal.{u, v, w} B S hS 𝒳 ↔
      BigFppfOver.IsLimitPreservingOnObjects.{u, v, w, u, u + 1} B S hS 𝒳
        (terminalCFG B S hS)
        (Bicategory.InducedBicategory.mkHom (toTerminalCFG B S hS 𝒳)) :=
  Iff.rfl

end AlgebraicGeometry.Stack

end
