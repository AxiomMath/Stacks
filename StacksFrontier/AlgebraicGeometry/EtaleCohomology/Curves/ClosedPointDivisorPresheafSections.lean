module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.ClosedPointDivisorPresheafCoproduct
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.FundamentalExactSequenceSections

/-!
# The divisor map on sections, read in the presheaf coproduct

`Stacks.EtaleCohomology.closedPointDivisorSheaf.homOfPresheafHom` builds a morphism into
`⨁_x i_{x,*} 𝐙` out of a morphism of presheaves into the coproduct of the underlying presheaves
of the skyscrapers. The datum it asks for over an étale `X`-scheme `U` is a section of that
presheaf coproduct, while
`Stacks.EtaleCohomology.genericFibreDivisorSections` produces an element of the direct sum
`⨁_{x ∈ X_0} ((i_x)_* 𝐙)(U)` of the groups of sections of the summands. This file supplies the
map between the two, and composes it with the divisor map on sections.

The map is not an isomorphism and is not claimed to be one: a coproduct in a category of
presheaves is computed pointwise, so the two groups are in fact isomorphic, but nothing below
needs that. Only the direction from the direct sum into the coproduct is used, and it is
available from the universal property of the direct sum alone — the summand inclusions of the
presheaf coproduct, evaluated at `U`, are a family of maps out of the summands, and a finitely
supported family of sections is a finite sum of their images.

## Main definitions

* `Stacks.EtaleCohomology.closedPointDivisorSheaf.presheafCoproductSectionOfDirectSum`: a
  finitely supported family of sections of the skyscrapers over an étale `X`-scheme, read as a
  section of the coproduct of their underlying presheaves.
* `Stacks.EtaleCohomology.genericFibreDivisorPresheafSection`: **the second map of the
  fundamental exact sequence of Stacks 03RI over an irreducible étale `X`-scheme, valued in the
  presheaf coproduct** — the datum
  `Stacks.EtaleCohomology.closedPointDivisorSheaf.homOfPresheafHom` asks for at that object.

## Main results

* `Stacks.EtaleCohomology.closedPointDivisorSheaf.map_comp_presheafCoproductSectionOfDirectSum`:
  **the passage is natural in the étale `X`-scheme** — restricting the resulting section of the
  presheaf coproduct along a morphism of the small étale site is the same as restricting the
  family of sections of the summands first.
* `Stacks.EtaleCohomology.genericFibreDivisorPresheafSection_restrict_eq_zero`: **the sequence is
  still a complex after the passage** — an invertible global function on `U` has trivial image.

## Implementation notes

What this file does *not* supply is naturality. A morphism of presheaves asks for these maps at
every object of the small étale site and for a commuting square at every morphism of it, and the
maps built here exist only at an irreducible object: `genericFibreDivisorSections` is stated for
an irreducible étale `X`-scheme, the order of vanishing being taken in the function field of
`U`. Both missing halves — the extension to a general object through its decomposition into
irreducible components, and the commuting square — are recorded in the module docstring of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.FundamentalExactSequenceSections`.

The decidable equality on the closed points is supplied classically, as in
`Stacks.EtaleCohomology.directSumOfFiniteSupport`. It is an artefact of
`DirectSum.toAddMonoid`, which needs to decide whether a coordinate is in the support, and it
does not appear in any statement below. The price is that the characterisation of the map on a
single summand is not stated: it would have to name a `DecidableEq` instance for
`DirectSum.of`, and that instance would not be the classical one used here.

## References

* [Stacks Project, Tag 03RI](https://stacks.math.columbia.edu/tag/03RI): the fundamental exact
  sequence.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v

namespace Stacks.EtaleCohomology

attribute [local instance 10000] hasCoproduct_closedPointSkyscraper
  hasCoproduct_closedPointSkyscraper_obj

namespace closedPointDivisorSheaf

variable (X : Scheme.{u}) (U : X.Etale)

/-- **A finitely supported family of sections of the skyscrapers, as a section of the coproduct of
their underlying presheaves.** The summand inclusions of the presheaf coproduct, evaluated at an
étale `X`-scheme `U`, are a family of homomorphisms out of the groups of sections of the
summands, so the universal property of the direct sum turns a finitely supported family into a
single section.

This is the passage from the target of `Stacks.EtaleCohomology.genericFibreDivisorSections` to
the datum that `Stacks.EtaleCohomology.closedPointDivisorSheaf.homOfPresheafHom` asks for. -/
def presheafCoproductSectionOfDirectSum :
    DirectSum ↥(closedPoints X)
        (fun x : closedPoints X ↦ (closedPointSkyscraper.{u, v} X x).obj.obj (op U)) →+
      (∐ fun x : closedPoints X ↦ (closedPointSkyscraper.{u, v} X x).obj).obj (op U) :=
  letI : DecidableEq ↥(closedPoints X) := Classical.decEq _
  DirectSum.toAddMonoid fun x ↦
    ((Sigma.ι (fun x : closedPoints X ↦ (closedPointSkyscraper.{u, v} X x).obj) x).app (op U)).hom

/-- **The passage from the direct sum of the groups of sections to the sections of the presheaf
coproduct is natural in the étale `X`-scheme.** Restricting the resulting section along a morphism
`g : U ⟶ V` of the small étale site is the same as restricting each member of the family of
sections of the summands and then forming the section of the presheaf coproduct over `U`.

Only the summand inclusions are involved, so this is their naturality: the summand inclusions of
the presheaf coproduct are morphisms of presheaves, and both composites are homomorphisms out of
the direct sum, so they agree as soon as they agree on each summand. -/
theorem map_comp_presheafCoproductSectionOfDirectSum {W V : X.Etale} (g : W ⟶ V) :
    (((∐ fun x : closedPoints X ↦ (closedPointSkyscraper.{u, v} X x).obj).map g.op).hom).comp
        (presheafCoproductSectionOfDirectSum.{u, v} X V) =
      (presheafCoproductSectionOfDirectSum.{u, v} X W).comp
        (DirectSum.map fun x : closedPoints X ↦
          ((closedPointSkyscraper.{u, v} X x).obj.map g.op).hom) := by
  let : DecidableEq ↥(closedPoints X) := Classical.decEq _
  refine DirectSum.addHom_ext fun x s ↦ ?_
  rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, presheafCoproductSectionOfDirectSum,
    DirectSum.toAddMonoid_of, DirectSum.map_of, presheafCoproductSectionOfDirectSum,
    DirectSum.toAddMonoid_of]
  exact (NatTrans.naturality_apply
    (Sigma.ι (fun y : closedPoints X ↦ (closedPointSkyscraper.{u, v} X y).obj) x) g.op s).symm

end closedPointDivisorSheaf

/-! ### The divisor map over an irreducible étale neighbourhood, valued in the presheaf
coproduct -/

section Section

variable {X : Scheme.{u}} [IsIntegral X] (U : X.Etale) [IsIntegral U.left]
  [IsLocallyNoetherian U.left] [NoetherianSpace U.left]

/-- **The second map of the fundamental exact sequence of Stacks 03RI over an irreducible étale
`X`-scheme, valued in the coproduct of the underlying presheaves of the skyscrapers.** This is
`Stacks.EtaleCohomology.genericFibreDivisorSections` followed by
`Stacks.EtaleCohomology.closedPointDivisorSheaf.presheafCoproductSectionOfDirectSum`.

It is the datum `Stacks.EtaleCohomology.closedPointDivisorSheaf.homOfPresheafHom` asks for at
this one object; what is still missing before that construction applies is the same map at a
general object of the small étale site, and naturality. -/
def genericFibreDivisorPresheafSection :
    Additive ((Γ(pullback U.hom (genericPointInclusion X), ⊤))ˣ) →+
      (∐ fun x : closedPoints X ↦ (closedPointSkyscraper.{u, v} X x).obj).obj (op U) :=
  (closedPointDivisorSheaf.presheafCoproductSectionOfDirectSum.{u, v} X U).comp
    (genericFibreDivisorSections.{u, v} U)

/-- **An invertible global function on `U` has trivial image in the presheaf coproduct**: the
sequence of Stacks 03RI is still a complex after the passage from the direct sum of the groups of
sections to the sections of the presheaf coproduct. -/
theorem genericFibreDivisorPresheafSection_restrict_eq_zero (a : (Γ(U.left, ⊤))ˣ) :
    genericFibreDivisorPresheafSection.{u, v} U (Additive.ofMul (Units.map
      (pullback.fst U.hom (genericPointInclusion X)).appTop.hom.toMonoidHom a)) = 0 :=
  (congrArg (closedPointDivisorSheaf.presheafCoproductSectionOfDirectSum.{u, v} X U)
    (genericFibreDivisorSections_restrict_eq_zero.{u, v} U a)).trans (map_zero _)

end Section

end Stacks.EtaleCohomology

end
