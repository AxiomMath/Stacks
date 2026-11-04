module

public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.HilbertCoverDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.IsStackFromRepresentableDiagonal

/-!
# The morphism presheaves of the category of finite locally free covers are sheaves

The category `ℋ_d` of degree-`d` finite locally free covers in the big fppf site of a scheme `S`
(`AlgebraicGeometry.Stack.finiteCoverCategory`) has a diagonal representable by algebraic
spaces: that is `AlgebraicGeometry.Stack.hasRepresentableDiagonal_finiteCoverFibered`. Through
the equivalence of conditions (1) and (2) of Stacks 045G this makes its `Isom` presheaves
sheaves, which is condition (2) of Stacks 02ZI, and over a category fibred in groupoids the
`Isom` presheaf of a pair of objects of a fibre is all of its `Mor` presheaf. So the `Mor`
presheaves of `ℋ_d` are sheaves as well, which is condition (2) of Stacks 026F.

The two readings are not interchangeable for the consumer. `AlgebraicGeometry.Stack.isStack_of_\
hasRepresentableDiagonal` produces all three conditions of Stacks 026F at once, but only out of
a proof of effectivity of descent data; a proof of that effectivity which first refines the
covering — `CategoryTheory.Functor.hasEffectiveDescent_of_refinements`, the source's own "in
order to prove effectivity we may first refine the covering" — consumes condition (2) of 026F
as an input and therefore cannot take it from there. This file supplies it on its own, with no
effectivity in hand.

## Main results

* `AlgebraicGeometry.Stack.isMorSheaf_finiteCoverFibered`: the presheaves `Mor(x, y)` of
  Stacks 02ZB attached to two degree-`d` finite locally free covers of one and the same object
  of the site are sheaves for the induced topology on the slice at that object.

## Implementation notes

The statement is made about `(AlgebraicGeometry.Stack.finiteCoverFibered B S hS d).val.p` and
not about `AlgebraicGeometry.Stack.finiteCoverProjection`, although the two are the same
functor: the implementation notes of
`StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.HilbertCoverDiagonal` record that unfolding
the comparison between them exhausts the heartbeat limit, and the consumers of this statement —
`AlgebraicGeometry.Stack.isStack_of_hasRepresentableDiagonal` and the refinement criterion for
effectivity — are stated at the former.

No `@[stacks]` attribute is attached. Condition (2) is one of the three conditions of
Stacks 026F and one of the three of Stacks 02ZI, and neither tag is proved by it alone.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Stack

/-- **Condition (2) of Stacks 026F for the category of degree-`d` finite locally free covers.**
The presheaves `Mor(x, y)` of Stacks 02ZB attached to two degree-`d` finite locally free covers
of one and the same object `U` of the big fppf site of `S` are sheaves on the slice of the site
at `U`.

The `Isom` presheaves are sheaves because the diagonal of `ℋ_d` is representable by algebraic
spaces (`AlgebraicGeometry.Stack.hasRepresentableDiagonal_finiteCoverFibered`, read through
`AlgebraicGeometry.Stack.isSheaf_isomPresheaf_of_hasRepresentableDiagonal`), and `ℋ_d` is
fibred in groupoids, so each `Isom` presheaf is the whole of the corresponding `Mor` presheaf
(`CategoryTheory.Functor.isomSubpresheaf` is the top subpresheaf), and being a sheaf is invariant
under isomorphism of presheaves. -/
theorem isMorSheaf_finiteCoverFibered (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (d : ℕ) :
    letI : (finiteCoverFibered B S hS d).val.p.IsFibered :=
      (finiteCoverFibered B S hS d).isFiberedInGroupoids.isFibered
    ∀ (U : BigFppfOver B S hS) (x y : (finiteCoverFibered B S hS d).val.p.Fiber U),
      (finiteCoverFibered B S hS d).val.p.IsMorSheaf (BigFppfOver.topology B S hS) U x y := by
  let : (finiteCoverFibered B S hS d).val.p.IsFibered :=
    (finiteCoverFibered B S hS d).isFiberedInGroupoids.isFibered
  intro U x y
  have htop : (finiteCoverFibered B S hS d).val.p.isomSubpresheaf x y = ⊤ :=
    le_antisymm le_top fun g m _ => by
      have := (finiteCoverFibered B S hS d).isFiberedInGroupoids.fiber_isGroupoid g.unop.left
      rw [Functor.mem_isomSubpresheaf_obj]
      infer_instance
  have hι : IsIso ((finiteCoverFibered B S hS d).val.p.isomSubpresheaf x y).ι :=
    ((finiteCoverFibered B S hS d).val.p.isomSubpresheaf x y).eq_top_iff_isIso.1 htop
  exact (Presheaf.isSheaf_of_iso_iff (@asIso _ _ _ _ _ hι)).1
    (isSheaf_isomPresheaf_of_hasRepresentableDiagonal B S hS (finiteCoverFibered B S hS d)
      (hasRepresentableDiagonal_finiteCoverFibered B S hS d) U x y)

end AlgebraicGeometry.Stack

end
