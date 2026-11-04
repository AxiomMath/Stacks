module

public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.ImageFibreProducts
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.CoverPreserving
public import StacksFrontier.CategoryTheory.Sites.SlicePost.Continuous

/-!
# Continuity of the functor from a localized big site into the slice of all schemes

Fix one of the five big sites `B` of a topology `τ`, localize it at a scheme `S` of the site
and let `AlgebraicGeometry.overToSlice` be the resulting functor
`Over (base B S hS) ⥤ Over S` into the slice of *all* schemes over `S`.  This file proves that
functor **continuous**, both for the localization of the full `τ`-topology on schemes and for
the localization of the fpqc topology.

Continuity is what makes the restriction along `overToSlice` of a sheaf on `Over S` a sheaf on
the localized big site, and it is not available by instance search.  Mathlib derives
*cocontinuity* of `CategoryTheory.Over.post` from cocontinuity of the underlying functor
(`CategoryTheory.Over.post`, in `Mathlib/CategoryTheory/Sites/Over.lean`) but takes
*continuity* as a hypothesis; the same is true of this repository's own slice lemmas.  So the
instance has to be produced, and the route is the one of
`CategoryTheory.Functor.isContinuous_overPost_of_preservesPullbacks`: the underlying inclusion
`AlgebraicGeometry.schemeBelowInclusion` is continuous, the localized big site has fibre
products, and the inclusion preserves them.

Continuity of the inclusion itself is proved from cover preservation alone, through
1-hypercovers (`CategoryTheory.Functor.PreservesOneHypercovers.of_coverPreserving`), so no
compatible-preservation or representable-flatness argument is needed: the underlying category
of a big site has fibre products by [Stacks, Tag 022K] and the inclusion preserves them,
because the size-bounded full subcategory of schemes is closed under them.

## Main definitions

No definitions are introduced.

## Main results

* `AlgebraicGeometry.coveringMorphismProperty_le_flat_inf_locallyOfFinitePresentation`: each of
  the five covering morphism properties is flatness together with local finite presentation.
* `AlgebraicGeometry.coverPreserving_schemeBelowInclusion` and
  `AlgebraicGeometry.coverPreserving_schemeBelowInclusion_fpqc`: the inclusion of the
  underlying category of a big site into all schemes is cover preserving for the `τ`-topology
  and for the fpqc topology.
* `AlgebraicGeometry.isContinuous_schemeBelowInclusion` and
  `AlgebraicGeometry.isContinuous_schemeBelowInclusion_fpqc`: it is continuous for both.
* `AlgebraicGeometry.isContinuous_overToSlice` and
  `AlgebraicGeometry.isContinuous_overToSlice_fpqc`: **the instances this file exists for** —
  `AlgebraicGeometry.overToSlice` is continuous from the topology of the localized big site to
  the localization at `S` of the `τ`-topology, and to the localization at `S` of the fpqc
  topology.

## Implementation notes

`CategoryTheory.Functor.isContinuous_overPost_of_isContinuous`, which needs no hypothesis
beyond continuity of the underlying functor, does not apply here: it is stated for
`SmallCategory` source and target, whereas the underlying category of a big site and the
category of schemes both have objects one universe above their morphisms.  The
fibre-product form `CategoryTheory.Functor.isContinuous_overPost_of_preservesPullbacks` is
what applies, and its hypotheses are exactly the ones available.

The two topologies on `Scheme` are treated separately rather than one being deduced from the
other by monotonicity: cover preservation is not monotone in the target topology in a form
that instance search can use, and the generated-precoverage argument is the same two lines in
both cases.

For the fpqc comparison the Zariski case is not special.  An open immersion is flat and
locally of finite presentation like the members of the other four covering types, so the
single inequality `coveringMorphismProperty_le_flat_inf_locallyOfFinitePresentation` covers
all five topologies and no appeal to quasi-compactness is needed.

## References

* [Stacks Project, Tag 022K](https://stacks.math.columbia.edu/tag/022K)
* [Stacks Project, Tag 03DT](https://stacks.math.columbia.edu/tag/03DT)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (τ : CoveringTopology) (B : BigSite.{u} τ) (S : Scheme.{u})
  (hS : S.size < cutoff τ B)

/-! ### Cover preservation of the inclusion of a big site into all schemes -/

/-- A covering morphism of any of the five topologies is flat and locally of finite
presentation.  For the Zariski topology this is the statement that an open immersion is, which
is what makes the fpqc comparison below uniform in `τ`. -/
public theorem coveringMorphismProperty_le_flat_inf_locallyOfFinitePresentation :
    coveringMorphismProperty τ ≤
      (@Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) := by
  cases τ with
  | fppf => exact le_rfl
  | syntomic => exact fun _ _ _ hf ↦ ⟨flat hf, locallyOfFinitePresentation hf⟩
  | smooth => exact fun _ _ f hf ↦ have : Smooth f := hf; ⟨inferInstance, inferInstance⟩
  | etale => exact fun _ _ f hf ↦ have : Etale f := hf; ⟨inferInstance, inferInstance⟩
  | zariski =>
      exact fun _ _ f hf ↦ have : IsOpenImmersion f := hf; ⟨inferInstance, inferInstance⟩

/-- The inclusion of a big site into all schemes is cover preserving for the topology generated
by a precoverage containing the image of every chosen covering family. -/
private theorem coverPreserving_schemeBelowInclusion_of_mem (K : Precoverage Scheme.{u})
    (h : ∀ {X : siteCategory B} (E : PreZeroHypercover.{u + 1} X), isCovering τ B ⟨X, E⟩ →
      (E.map (schemeBelowInclusion (cutoff τ B))).presieve₀ ∈ K X.obj) :
    CoverPreserving (siteTopology τ B) K.toGrothendieck (schemeBelowInclusion (cutoff τ B)) := by
  rw [siteTopology_eq_toGrothendieck]
  refine coverPreserving_of_generators _ (bigSitePrecoverage τ B) _ ?_
  intro X R hR
  obtain ⟨E, hE, rfl⟩ := (mem_bigSitePrecoverage_iff τ B).mp hR
  rw [← Sieve.generate_map_eq_functorPushforward, PreZeroHypercover.presieve₀,
    Presieve.map_ofArrows]
  exact Precoverage.generate_mem_toGrothendieck (h E hE)

/-- The inclusion of the underlying category of a big site into all schemes is cover
preserving, from the topology of the big site to the `τ`-topology on schemes.  The topology of
the big site is generated by its chosen covering families, each of which is a `τ`-covering of
schemes by `AlgebraicGeometry.mem_precoverage_of_isCovering`. -/
public theorem coverPreserving_schemeBelowInclusion :
    CoverPreserving (siteTopology τ B)
      (Scheme.grothendieckTopology (coveringMorphismProperty τ))
      (schemeBelowInclusion (cutoff τ B)) :=
  coverPreserving_schemeBelowInclusion_of_mem τ B _ (mem_precoverage_of_isCovering τ B)

/-- The inclusion of the underlying category of a big site into all schemes is cover
preserving for the fpqc topology: a `τ`-covering is an fpqc covering, its members being flat
and locally of finite presentation. -/
public theorem coverPreserving_schemeBelowInclusion_fpqc :
    CoverPreserving (siteTopology τ B) Scheme.fpqcTopology.{u}
      (schemeBelowInclusion (cutoff τ B)) :=
  coverPreserving_schemeBelowInclusion_of_mem τ B _ fun E hE ↦
    le_trans
      (Scheme.precoverage_mono
        (coveringMorphismProperty_le_flat_inf_locallyOfFinitePresentation τ))
      Scheme.fppfPrecoverage_le_fpqcPrecoverage _ (mem_precoverage_of_isCovering τ B E hE)

/-! ### Continuity of the inclusion, and of the functor into the slice -/

/-- The inclusion of the underlying category of a big site into all schemes is continuous for
the `τ`-topology.  Cover preservation suffices: the category has fibre products by
[Stacks, Tag 022K] and the inclusion preserves them, so a covering 1-hypercover goes to a
covering 1-hypercover. -/
public instance isContinuous_schemeBelowInclusion :
    (schemeBelowInclusion (cutoff τ B)).IsContinuous (siteTopology τ B)
      (Scheme.grothendieckTopology (coveringMorphismProperty τ)) :=
  haveI : Functor.PreservesOneHypercovers.{u + 1} (schemeBelowInclusion (cutoff τ B))
      (siteTopology τ B) (Scheme.grothendieckTopology (coveringMorphismProperty τ)) :=
    Functor.PreservesOneHypercovers.of_coverPreserving
      (coverPreserving_schemeBelowInclusion τ B)
  inferInstance

/-- The inclusion of the underlying category of a big site into all schemes is continuous for
the fpqc topology. -/
public instance isContinuous_schemeBelowInclusion_fpqc :
    (schemeBelowInclusion (cutoff τ B)).IsContinuous (siteTopology τ B)
      Scheme.fpqcTopology.{u} :=
  haveI : Functor.PreservesOneHypercovers.{u + 1} (schemeBelowInclusion (cutoff τ B))
      (siteTopology τ B) Scheme.fpqcTopology.{u} :=
    Functor.PreservesOneHypercovers.of_coverPreserving
      (coverPreserving_schemeBelowInclusion_fpqc τ B)
  inferInstance

/-- **The functor from a localized big site into the slice of all schemes over `S` is
continuous**, for the localization at `S` of the `τ`-topology on schemes.

This is what lets a `τ`-sheaf on `Over S` be restricted to the localized big site, and it is
the hypothesis `u.IsContinuous` of the Čech-vanishing criterion
`Stacks.CechSite.sheafCohomology_isZero_of_cechCohomology_isZero_of_functor_essentiallySmall`
at `u := AlgebraicGeometry.overToSlice`. -/
public instance isContinuous_overToSlice :
    (overToSlice τ B S hS).IsContinuous (overTopology τ B S hS)
      ((Scheme.grothendieckTopology (coveringMorphismProperty τ)).over S) := by
  rw [overTopology_eq_siteTopology_over]
  exact Functor.isContinuous_overPost_of_preservesPullbacks _ _
    (schemeBelowInclusion (cutoff τ B)) (base B S hS)

/-- **The functor from a localized big site into the slice of all schemes over `S` is
continuous for the localized fpqc topology.**

This is the hypothesis of `Stacks.Sites.isSheaf_associatedPresheaf_of_isContinuous`, so it is
what makes the associated module `Fᵃ` of [Stacks, Tag 03DU] a sheaf on the localized big site
granted [Stacks, Tag 03DT]. -/
public instance isContinuous_overToSlice_fpqc :
    (overToSlice τ B S hS).IsContinuous (overTopology τ B S hS)
      (Scheme.fpqcTopology.{u}.over S) := by
  rw [overTopology_eq_siteTopology_over]
  exact Functor.isContinuous_overPost_of_preservesPullbacks _ _
    (schemeBelowInclusion (cutoff τ B)) (base B S hS)

end AlgebraicGeometry

end
