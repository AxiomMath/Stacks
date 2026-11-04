module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleStructureSheaf
public import StacksFrontier.CategoryTheory.Sites.Pretopology.SmallSubsite
public import StacksCore.Tactic.StacksAttribute

/-!
# Parasitic presheaves of modules

A presheaf of modules on a site of schemes over `S` is *parasitic* when its sections vanish on
every object which is flat over `S`, and *parasitic for the topology* when its sections vanish
on the members of every covering of `S` itself. The two notions are the two parts of the
source definition, and they are the hypotheses under which the cohomology of a presheaf of
modules on a big site vanishes.

## Main definitions

* `AlgebraicGeometry.IsParasitic` — vanishing on objects flat over the base.
* `AlgebraicGeometry.IsParasiticFor` — vanishing on the members of coverings of the base.

## Implementation notes

Both predicates are stated for an abstract category `C` equipped with a functor to schemes
over `S`, so that they apply unchanged to each of the five standard big sites and to their
small and affine variants. The ring presheaf is a free variable: the condition does not
mention it, so there is no reason to fix it to be the presheaf of global functions
`Stacks.Sites.structurePresheaf`, and leaving it free lets these predicates be applied to a
module over a pushforward of a structure sheaf without transporting along an equation of ring
presheaves. Vanishing of a module is `Subsingleton` on its carrier, and a covering counts as a
covering *of the base* when its target has an invertible structure morphism — this avoids
choosing a representative of the terminal object of the site.

Both are abbreviations, so that the universal-quantifier and `Subsingleton` API applies to
them without unfolding.

## References

* [Stacks Project, Tag 06ZL](https://stacks.math.columbia.edu/tag/06ZL)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry

/-- A presheaf of modules is *parasitic* when its sections vanish on every object of the site
which is flat over the base scheme. -/
@[stacks 06ZL "part (1)"]
public abbrev IsParasitic (S : Scheme.{u}) {C : Type (u + 1)} [Category.{u} C]
    (toOver : C ⥤ Over S) {𝒪 : Cᵒᵖ ⥤ RingCat.{u}} (F : PresheafOfModules.{u} 𝒪) : Prop :=
  ∀ X : C, Flat (toOver.obj X).hom → Subsingleton (F.obj (op X))

/-- A presheaf of modules is *parasitic for a topology* when its sections vanish on every
member of every covering family of the base scheme. -/
@[stacks 06ZL "part (2)"]
public abbrev IsParasiticFor (S : Scheme.{u}) {C : Type (u + 1)} [Category.{u} C]
    (toOver : C ⥤ Over S) (isCovering : Covering C → Prop)
    {𝒪 : Cᵒᵖ ⥤ RingCat.{u}} (F : PresheafOfModules.{u} 𝒪) : Prop :=
  ∀ E : Covering C, IsIso (toOver.obj E.1).hom → isCovering E →
    ∀ i : E.2.I₀, Subsingleton (F.obj (op (E.2.X i)))

end AlgebraicGeometry

end
