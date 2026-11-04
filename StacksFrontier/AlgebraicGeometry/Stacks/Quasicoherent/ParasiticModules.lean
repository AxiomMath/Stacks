module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfSite
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.StructureSheaf

/-!
# Parasitic modules on an algebraic stack (Stacks 0773)

Let `𝒳` be an algebraic stack over `S`. A presheaf of `𝒪_𝒳`-modules is *parasitic* when its
module of sections vanishes at every object of `𝒳` that lies over a scheme `U` for which the
corresponding 1-morphism `x : U → 𝒳` is flat.

The condition is stated for a presheaf of modules over the ring-valued structure sheaf of any
one of the five sites associated with `𝒳` by **Stacks 06TP**, since the parasitic condition is
about the values of the presheaf on objects and makes no reference to the topology.

## Main definitions

* `AlgebraicGeometry.Stack.IsParasitic`: **Stacks 0773** — the parasitic condition.

## Implementation notes

The flat objects of `𝒳` are exactly those singled out by
`AlgebraicGeometry.Stack.flatObject`, which says of an object `x` that the 1-morphism it names
under the 2-Yoneda lemma, out of the category represented by the scheme `x` lies over, is flat.
Quantifying over the objects of `𝒳` and testing them with that predicate is the literal reading
of the source, and it reuses the notion the flat-fppf site of **Stacks 0787** is already built
from, so the two cannot drift apart. The source's own phrasing quantifies instead over pairs of
a scheme `U` and a 1-morphism `x : U → 𝒳`; under the 2-Yoneda equivalence
`CategoryTheory.Functor.twoYonedaEvaluation` those pairs are precisely the objects of `𝒳` over
`U`, and the section module is unchanged along the resulting isomorphism of objects, so the two
readings agree.

Vanishing of a module is expressed as `Subsingleton` on its carrier rather than as an equality
of objects, which is the form a consumer can use pointwise without transporting along an
isomorphism of module categories. The predicate is an `abbrev`, so its pointwise content is
available to consumers by definitional unfolding.

## References

* [Stacks Project, Tag 06TP](https://stacks.math.columbia.edu/tag/06TP)
* [Stacks Project, Tag 0773](https://stacks.math.columbia.edu/tag/0773)
* [Stacks Project, Tag 0787](https://stacks.math.columbia.edu/tag/0787)
-/

@[expose] public section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Stack

universe u w t

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS) (τ : SiteKind)

/-- **Stacks 0773.** A presheaf of modules over the structure sheaf of one of the sites
associated with an algebraic stack `𝒳` is *parasitic* when its module of sections at every flat
object of `𝒳` vanishes — an object being flat, as in **Stacks 0787**, when the 1-morphism it
names out of the scheme it lies over is flat. -/
@[stacks 0773 "parasitic"]
abbrev IsParasitic
    (F : PresheafOfModules.{t}
      (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids τ).obj) : Prop :=
  ∀ x : 𝒳.val.val.obj, flatObject B S hS 𝒳.val x → Subsingleton (F.obj (op x))

end AlgebraicGeometry.Stack

end
