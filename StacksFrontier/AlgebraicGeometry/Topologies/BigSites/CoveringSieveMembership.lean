module

public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.StandardCoveringSieves

/-!
# A `τ`-covering family of a localized big site generates a covering sieve

Fix one of the five big sites `B` of a topology `τ` and localize it at a scheme `S` of the
site.  A family in the localization whose underlying morphisms of schemes are `τ`-covering
morphisms and are jointly surjective generates a covering sieve of the localized topology.

This is the general form of
`AlgebraicGeometry.IsOverStandardCovering.sieve₀_mem_overTopology`, whose family is additionally
required to be a *standard* `τ`-covering: finite, with affine target and affine sources, and
with each member of the standard affine shape attached to `τ`.  None of that is used in the
proof of sieve membership, and the general statement is what a construction producing an
arbitrary `τ`-covering family of the site — a base change of a covering, say — needs.

## Main results

* `AlgebraicGeometry.sieve₀_mem_overTopology_of_coveringMorphismProperty` — the sieve generated
  by a `τ`-covering family of a localized big site is a covering sieve.

## Implementation notes

The index type of the family is arbitrary, while the chosen covering families of a big site are
indexed in `Type (u + 1)`.  The gap is crossed by `CategoryTheory.PreZeroHypercover.shrink`,
the deduplication of a family along the arrows it consists of: its index type is a type of
arrows of the site, hence lies in `Type (u + 1)` whatever the original index type was, and
`CategoryTheory.PreZeroHypercover.presieve₀_shrink` says it generates the same presieve.  This
is cheaper than the `ULift` reindexing of
`AlgebraicGeometry.exists_isCovering_presieve₀_eq`, which can only lower `Type u` to
`Type (u + 1)` and so leaves the `Type 0`-indexed families of
`Stacks.Adequate.BigSite.affineCov` out of reach.

The statement is at a variable topology `τ` and a variable big site, and the five-way case
analysis on `τ` happens only inside the two results quoted from
`StacksFrontier/AlgebraicGeometry/Topologies/BigSites/StandardCoveringSieves.lean`.  No `@[stacks]`
attribute is attached: the mathematical content is that of [Stacks, Tag 03WV] and its four
siblings, which are structure fields of the five big sites, and this is their uniform
packaging transported to the localization.

## References

* [Stacks Project, Tag 03WV](https://stacks.math.columbia.edu/tag/03WV)
* [Stacks Project, Tag 03X8](https://stacks.math.columbia.edu/tag/03X8)
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry

variable (τ : CoveringTopology) (B : BigSite.{u} τ) (S : Scheme.{u})
  (hS : S.size < cutoff τ B)

/-- **A `τ`-covering family of a localized big site generates a covering sieve.**  If every
member of a family in the localization at `S` of a big `τ`-site is a `τ`-covering morphism of
schemes and the members are jointly surjective, the sieve the family generates belongs to the
topology of the localized site.

The family is combinatorially equivalent to one of the site's own chosen covering families by
`AlgebraicGeometry.exists_isCovering_presieve₀_eq_aux`, after deduplication to bring its index
type into `Type (u + 1)`, and a chosen covering family generates a covering sieve by
`AlgebraicGeometry.generate_mem_siteTopology`. -/
public theorem sieve₀_mem_overTopology_of_coveringMorphismProperty
    {U : Over (base B S hS)} (E : PreZeroHypercover.{v} U)
    (hprop : ∀ i, coveringMorphismProperty τ
      ((schemeBelowInclusion (cutoff τ B)).map (E.f i).left))
    (hsurj : ∀ x : overScheme τ B S hS U, ∃ i,
      x ∈ Set.range ((schemeBelowInclusion (cutoff τ B)).map (E.f i).left)) :
    E.sieve₀ ∈ overTopology τ B S hS U := by
  rw [sieve₀_mem_overTopology_iff]
  set E' := E.map (Over.forget (base B S hS)) with hE'
  have hmem : (E'.shrink.map (schemeBelowInclusion (cutoff τ B))).presieve₀ ∈
      Scheme.precoverage (coveringMorphismProperty τ) (overScheme τ B S hS U) := by
    rw [PreZeroHypercover.presieve₀_map, PreZeroHypercover.presieve₀_shrink,
      ← PreZeroHypercover.presieve₀_map]
    exact (Scheme.ofArrows_mem_precoverage_iff (coveringMorphismProperty τ)).mpr ⟨hsurj, hprop⟩
  obtain ⟨F, hF, hFeq⟩ := exists_isCovering_presieve₀_eq_aux τ B E'.shrink hmem
  have hgen := generate_mem_siteTopology τ B F hF
  rw [← hFeq, PreZeroHypercover.presieve₀_shrink] at hgen
  exact hgen

end AlgebraicGeometry

end
