module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.AbelianSumFormula.CommaDecomposition

/-!
# The summand decomposition of a component inclusion's comma category is natural in the base

Let `Cs` be a simplicial site, that is, case (A) of the simplicial-site situation of Stacks 09WE,
and let `ι_k` denote the inclusion of its degree-`k` component into the total category. The comma
category of `ι_n` over an object `(m, W)` is the disjoint union, over the simplex maps
`ψ : n ⟶ m`, of the comma categories of the transition functors `u_ψ` over `W`; the summand
inclusions are `Stacks.Sites.AbelianSumFormula.summandInclusion`.

The sum formula of Stacks 09WG (6) is an isomorphism of *presheaves* on the degree-`m` component,
so the summand decomposition has to be compatible with the structure maps of those presheaves:
for a morphism `f : W' ⟶ W` of the degree-`m` component, the square of comma categories formed by
the summand inclusions and the two precomposition functors must commute. This file proves that,
and reads off the consequence for the canonical comparison maps between the colimits over those
comma categories.

## Main results

* `Stacks.Sites.ComponentSumFormula.coGrothendieck_ι_map_comp`: in the contravariant Grothendieck
  construction of any pseudofunctor, composing a morphism in the image of the fibre inclusion
  `CategoryTheory.Pseudofunctor.CoGrothendieck.ι` with an arbitrary morphism out of that fibre
  just precomposes the fibre component: `ι_S(f) ≫ ⟨b, h⟩ = ⟨b, f ≫ h⟩`.
* `Stacks.Sites.ComponentSumFormula.summandInclusion_comp_structuredArrowMap`: the square of
  comma categories commutes, as an equality of functors.
* `Stacks.Sites.ComponentSumFormula.summandInclusion_op_comp_structuredArrowMap_op`: the same
  square on the opposite comma categories.

## Implementation notes

`coGrothendieck_ι_map_comp` is stated and proved at the generality of an arbitrary pseudofunctor
into `Cat`, where it is a corollary of Mathlib's own left unit law for the contravariant
Grothendieck construction: the fibre component of `ι_S(f)` is `f` followed by the fibre component
of the identity, so the composite is the composite computed by `Category.id_comp` with `f`
prefixed. No pseudofunctor coherence axiom has to be touched, and in particular the identity is
not proved by rewriting the base component of `ι_S(f)` to an identity — a rewrite whose motive is
not type-correct, because the base component occurs inside the type of the fibre component. The
base components of the two sides of the identity differ by the left unit law of the base category,
which for `SimplexCategory` is not definitional, so the statement genuinely needs
`CategoryTheory.Pseudofunctor.CoGrothendieck.Hom.ext`.

Both of the first two proofs end on a *term* rather than a rewrite. After the `change` that
puts the goal into the normal form in which the composition in the Grothendieck construction has
been evaluated, the goal is no longer type-correct at `implicit` transparency — the fibre of an
object of the total category is stated through the pseudofunctor while the local hypotheses state
it through the underlying diagram of categories — so `rw` and `simp` cannot build their motives,
while `exact` checks at default transparency and goes through.

The square is recorded as an equality of functors rather than as a compatibility of the induced
maps on colimits. An equation between those maps is not well typed: the two composites of index
functors are equal only propositionally, so the two colimits they index are equal types only along
that equality, and the statement would have to carry an `eqToHom`. The functor equality gives the
compatibility through `CategoryTheory.Limits.colimit.pre_pre`, which expresses both composites as
the single comparison map along the composite index functor.

## References

* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pseudofunctor Opposite
open Stacks.Sites.AbelianSumFormula

universe v₁ v₂ u₁ u₂ v u

namespace Stacks.Sites.ComponentSumFormula

section Pseudofunctor

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {F : Pseudofunctor (LocallyDiscrete 𝒮ᵒᵖ) Cat.{v₂, u₂}}

/-- **Composing with the fibre inclusion of a contravariant Grothendieck construction just
precomposes the fibre component.** For a morphism `f : a ⟶ b` of the fibre over `S` and a
morphism `g` of the total category out of `⟨S, b⟩`, the composite `ι_S(f) ≫ g` has the same base
component as `g` and fibre component `f ≫ g.fiber`. -/
theorem coGrothendieck_ι_map_comp (S : 𝒮) {a b : F.obj ⟨op S⟩} (f : a ⟶ b)
    {Y : CoGrothendieck F} (g : (⟨S, b⟩ : CoGrothendieck F) ⟶ Y) :
    (CoGrothendieck.ι F S).map f ≫ g = { base := g.base, fiber := f ≫ g.fiber } := by
  refine CoGrothendieck.Hom.ext _ _ (Category.id_comp _) ?_
  have key := CoGrothendieck.Hom.congr (Category.id_comp g)
  simp only [CoGrothendieck.categoryStruct_comp_fiber, CoGrothendieck.categoryStruct_id_fiber,
    CoGrothendieck.categoryStruct_id_base] at key
  change (f ≫ (F.mapId ⟨op S⟩).inv.toNatTrans.app b) ≫
      (F.map (𝟙 S).op.toLoc).toFunctor.map g.fiber ≫
        (F.mapComp g.base.op.toLoc (𝟙 S).op.toLoc).inv.toNatTrans.app Y.fiber = _
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun x => f ≫ x) key).trans (Category.assoc _ _ _).symm)

end Pseudofunctor

section Simplicial

variable {Cs : SimplicialSite.{u}} {m n : SimplexCategory} {W W' : Cs.underlying.obj m}

/-- **The summand decomposition of the comma category of a component inclusion is natural in the
base object.** For a morphism `f : W' ⟶ W` of the degree-`m` component and a simplex map
`ψ : n ⟶ m`, the square formed by the two summand inclusions and the functors precomposing with
`f` and with its image under the degree-`m` component inclusion commutes. -/
theorem summandInclusion_comp_structuredArrowMap (ψ : n ⟶ m) (f : W' ⟶ W) :
    summandInclusion (W := W) ψ ⋙
        StructuredArrow.map ((CoGrothendieck.ι Cs.totalPseudofunctor (op m)).map f) =
      StructuredArrow.map f ⋙ summandInclusion (W := W') ψ := by
  have hobj : ∀ x : StructuredArrow W (Cs.underlying.map ψ).toFunctor,
      (summandInclusion (W := W) ψ ⋙
          StructuredArrow.map ((CoGrothendieck.ι Cs.totalPseudofunctor (op m)).map f)).obj x =
        (StructuredArrow.map f ⋙ summandInclusion (W := W') ψ).obj x := fun x =>
    congrArg (fun z => StructuredArrow.mk
        (S := (⟨op m, W'⟩ : CoGrothendieck Cs.totalPseudofunctor))
        (T := CoGrothendieck.ι Cs.totalPseudofunctor (op n)) (Y := x.right) z)
      (coGrothendieck_ι_map_comp (F := Cs.totalPseudofunctor) (op m) f
        (Y := (⟨op n, x.right⟩ : CoGrothendieck Cs.totalPseudofunctor)) ⟨ψ.op, x.hom⟩)
  refine CategoryTheory.Functor.ext hobj ?_
  intro x y k
  refine StructuredArrow.hom_ext _ _ ?_
  change k.right = (eqToHom (hobj x)).right ≫ k.right ≫ (eqToHom (hobj y).symm).right
  erw [StructuredArrow.eqToHom_right, StructuredArrow.eqToHom_right, Category.id_comp,
    Category.comp_id]

/-- The summand decomposition square, read on the opposite comma categories, which is the shape
over which a left Kan extension to the total site is computed. -/
theorem summandInclusion_op_comp_structuredArrowMap_op (ψ : n ⟶ m) (f : W' ⟶ W) :
    (summandInclusion (W := W) ψ).op ⋙
        (StructuredArrow.map ((CoGrothendieck.ι Cs.totalPseudofunctor (op m)).map f)).op =
      (StructuredArrow.map f).op ⋙ (summandInclusion (W := W') ψ).op :=
  congrArg CategoryTheory.Functor.op (summandInclusion_comp_structuredArrowMap ψ f)

end Simplicial

end Stacks.Sites.ComponentSumFormula

end
