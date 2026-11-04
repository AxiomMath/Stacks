module

public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.ChosenCoverings
public import StacksFrontier.AlgebraicGeometry.Topologies.SyntomicTopology.Coverings

/-!
# The four coarser topologies of a chosen big fppf site are nested

The Zariski, étale, smooth and syntomic sites carried by a chosen big fppf site `B` have one
category `Sch_κ`, four sub-collections of the chosen fppf covering families, and four topologies.
These topologies are nested:

`B.zariskiTopology ≤ B.etaleTopology ≤ B.smoothTopology ≤ B.syntomicTopology ≤ B.topology`,

the last inequality being `AlgebraicGeometry.BigFppfSite.baseTopology_le_topology`.

Each sub-collection is the intersection of the chosen fppf covering families with a geometric
covering predicate, and each predicate says of the image family in schemes that it is jointly
surjective with every member having a morphism property.  So each of the three inequalities
comes from one implication between morphism properties — an open immersion is étale, an étale
morphism is smooth, a smooth morphism is syntomic — and no site axiom and no choice made in the
construction of `B` enters: it is literally the same chosen fppf family on both sides, with the
same cardinal bound on its index type.

The identity functor `(Sch/X)_τ → (Sch/X)_{τ'}` is a morphism of sites exactly when `τ` is a
stronger topology than `τ'`, and these inequalities are that condition, for each of the ten pairs
of distinct topologies Topologies, Section 03FE lists.

## Main results

* `AlgebraicGeometry.BigFppfSite.chosenPrecoverage_mono`: a containment of collections of
  covering families gives a containment of the precoverages they present.
* `AlgebraicGeometry.BigFppfSite.etaleCovering_of_zariskiCovering`,
  `.smoothCovering_of_etaleCovering` and `.syntomicCovering_of_smoothCovering`: the three
  containments of the sub-collections.
* `AlgebraicGeometry.BigFppfSite.zariskiTopology_le_etaleTopology`,
  `.etaleTopology_le_smoothTopology` and `.smoothTopology_le_syntomicTopology`: the three
  resulting inequalities of topologies.  Chained, they give the inequality for each of the ten
  pairs of distinct topologies.

## Implementation notes

`AlgebraicGeometry.IsZariskiCovering`, `AlgebraicGeometry.IsEtaleCovering` and
`AlgebraicGeometry.SmoothCovering` are membership of the image presieve in
`AlgebraicGeometry.Scheme.zariskiPretopology`, `AlgebraicGeometry.Scheme.etalePrecoverage` and
`AlgebraicGeometry.Scheme.precoverage @Smooth`, and all three of those are the precoverage of a
morphism property up to unfolding — `AlgebraicGeometry.Scheme.zariskiPretopology` is
`CategoryTheory.Precoverage.toPretopology` of the precoverage of `IsOpenImmersion`, which leaves
the collection of covering presieves unchanged.  So the first two containments are
`AlgebraicGeometry.Scheme.precoverage_mono` applied to a morphism-property implication, with no
unfolding of the covering predicates at all.

`AlgebraicGeometry.SyntomicCovering` is instead stated for an indexed family, with the joint
surjectivity as an equality of sets, so the third containment is
`AlgebraicGeometry.isSyntomicCovering_of_mem_smoothPrecoverage`, which does exactly that
repackaging.

Each morphism property is named with its universe and ascribed to
`CategoryTheory.MorphismProperty Scheme`: `@Etale` and `@Smooth` are families of propositions
rather than syntactically a `MorphismProperty`, so an unascribed occurrence leaves the argument
of `AlgebraicGeometry.Scheme.precoverage` a metavariable.  The implications themselves are
supplied by instance search from the hypothesis, which is a local hypothesis of class type and
so a local instance; Mathlib states `IsOpenImmersion f → Etale f` and `Etale f → Smooth f` as
anonymous instances with no name to cite.

## References

* [Stacks Project, Tag 03FF](https://stacks.math.columbia.edu/tag/03FF)
* [Stacks Project, Tag 03FE](https://stacks.math.columbia.edu/tag/03FE)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.BigFppfSite

variable (B : BigFppfSite.{u})

/-- A containment of collections of covering families of `Sch_κ` gives a containment of the
precoverages they present: a covering presieve of the smaller is presented by a family of the
smaller collection, hence by one of the larger. -/
public theorem chosenPrecoverage_mono {P Q : Covering B.Schemes → Prop}
    (hPQ : ∀ E, P E → Q E) : B.chosenPrecoverage P ≤ B.chosenPrecoverage Q := by
  intro X R hR
  obtain ⟨E, rfl, hE⟩ := hR
  exact ⟨E, rfl, hPQ _ hE⟩

/-! ### The three containments of the chosen sub-collections -/

/-- **A chosen Zariski covering family is a chosen étale covering family**, an open immersion
being étale.  It is the same chosen fppf family, so nothing about the index bound changes. -/
public theorem etaleCovering_of_zariskiCovering {E : Covering B.Schemes}
    (hE : B.zariskiCovering E) : B.etaleCovering E :=
  ⟨hE.1, Scheme.precoverage_mono
    (P := (@IsOpenImmersion.{u} : MorphismProperty Scheme.{u}))
    (Q := (@Etale.{u} : MorphismProperty Scheme.{u}))
    (fun _ _ _ hf => have := hf; inferInstance) _ hE.2⟩

/-- **A chosen étale covering family is a chosen smooth covering family**, an étale morphism
being smooth. -/
public theorem smoothCovering_of_etaleCovering {E : Covering B.Schemes}
    (hE : B.etaleCovering E) : B.smoothCovering E :=
  ⟨hE.1, Scheme.precoverage_mono
    (P := (@Etale.{u} : MorphismProperty Scheme.{u}))
    (Q := (@Smooth.{u} : MorphismProperty Scheme.{u}))
    (fun _ _ _ hf => have := hf; inferInstance) _ hE.2⟩

/-- **A chosen smooth covering family is a chosen syntomic covering family**, a smooth morphism
being syntomic. -/
public theorem syntomicCovering_of_smoothCovering {E : Covering B.Schemes}
    (hE : B.smoothCovering E) : B.syntomicCovering E :=
  ⟨hE.1, isSyntomicCovering_of_mem_smoothPrecoverage hE.2⟩

/-! ### The three inequalities of topologies -/

/-- **The big Zariski topology of a chosen big fppf site is coarser than its big étale
topology.**  Hence the identity functor `(Sch/X)_étale → (Sch/X)_{Zar}` is a morphism of sites,
which is entry (14) of the list of Topologies, Section 03FE. -/
public theorem zariskiTopology_le_etaleTopology : B.zariskiTopology ≤ B.etaleTopology :=
  Precoverage.toGrothendieck_mono
    (B.chosenPrecoverage_mono fun _ hE => B.etaleCovering_of_zariskiCovering hE)

/-- **The big étale topology of a chosen big fppf site is coarser than its big smooth
topology.**  Hence the identity functor `(Sch/X)_smooth → (Sch/X)_étale` is a morphism of
sites. -/
public theorem etaleTopology_le_smoothTopology : B.etaleTopology ≤ B.smoothTopology :=
  Precoverage.toGrothendieck_mono
    (B.chosenPrecoverage_mono fun _ hE => B.smoothCovering_of_etaleCovering hE)

/-- **The big smooth topology of a chosen big fppf site is coarser than its big syntomic
topology.**  Hence the identity functor `(Sch/X)_syntomic → (Sch/X)_smooth` is a morphism of
sites. -/
public theorem smoothTopology_le_syntomicTopology : B.smoothTopology ≤ B.syntomicTopology :=
  Precoverage.toGrothendieck_mono
    (B.chosenPrecoverage_mono fun _ hE => B.syntomicCovering_of_smoothCovering hE)

end AlgebraicGeometry.BigFppfSite

end
