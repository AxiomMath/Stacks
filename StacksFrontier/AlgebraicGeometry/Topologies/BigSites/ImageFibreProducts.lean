module

public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.AffineFibreProducts
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexAlongAFunctor

/-!
# The iterated fibre products of a covering of a localized big site are preserved

Fix one of the five big sites `B` of a topology `τ`, localize it at a scheme `S` of the site and
let `AlgebraicGeometry.overToSlice` be the functor into the slice of *all* schemes over `S`.
That functor preserves the iterated fibre products `U_{i₀} ×_U ⋯ ×_U U_{iₙ}` of any family of
the localized site, so the comparison maps from the images of those fibre products to the fibre
products of the image family are isomorphisms.

This is condition (2) of Sites, Definition 00WV for `AlgebraicGeometry.overToSlice`, and it is
the hypothesis `hComparison` of
`Stacks.CechSite.sheafCohomology_isZero_of_cechCohomology_isZero_of_functor`: it is what
identifies the Čech complex of a restricted presheaf along the functor with the Čech complex of
the image family.

## Main results

* `AlgebraicGeometry.preservesLimitsOfShape_walkingCospan_overToSlice`: the functor into the
  slice of all schemes over `S` preserves fibre products.
* `AlgebraicGeometry.overStandardCoverings_comparison`: the hypothesis `hComparison` of
  `Stacks.CechSite.sheafCohomology_isZero_of_cechCohomology_isZero_of_functor`.

## Implementation notes

No `@[stacks]` attribute is attached.  Preservation of fibre products by the inclusion of a big
site is part of [Stacks, Tag 022K], which is already tagged; what is added here is its transport
to the localization and the resulting invertibility of the Čech comparison maps.

Preservation of fibre products by `AlgebraicGeometry.overToSlice` is *not* an instance that
typeclass inference finds: Mathlib's `CategoryTheory.Limits.PreservesLimitsOfShape.overPost`
derives preservation of limits of shape `J` by `CategoryTheory.Over.post` from preservation of
limits of shape `WithTerminal J`, which at `J = WalkingCospan` asks more of the inclusion of the
big site than is available.  It is proved instead by reflection along
`CategoryTheory.Over.forget`, which creates — hence reflects — connected limits, together with
`AlgebraicGeometry.overToScheme` preserving fibre products; the composite
`overToSlice ⋙ Over.forget S` *is* `overToScheme`.

The step from preservation of single fibre products to preservation of the iterated ones is
`Stacks.Sites.preservesLimit_fibreProducts_overPost`, by induction on the length of the tuple;
only cospan limits are needed, which is what keeps the argument uniform in `τ`.

## References

* [Stacks Project, Tag 022K](https://stacks.math.columbia.edu/tag/022K)
* [Stacks Project, Tag 00WV](https://stacks.math.columbia.edu/tag/00WV)
* [Stacks Project, Tag 03F9](https://stacks.math.columbia.edu/tag/03F9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (τ : CoveringTopology) (B : BigSite.{u} τ) (S : Scheme.{u})
  (hS : S.size < cutoff τ B)

/-- The functor from a localized big site into the slice of all schemes over `S` preserves fibre
products.  Composing it with `CategoryTheory.Over.forget` gives
`AlgebraicGeometry.overToScheme`, which preserves them, and `Over.forget` reflects connected
limits. -/
public instance preservesLimitsOfShape_walkingCospan_overToSlice :
    PreservesLimitsOfShape WalkingCospan (overToSlice τ B S hS) := by
  let : PreservesLimitsOfShape WalkingCospan (overToSlice τ B S hS ⋙ Over.forget S) :=
    inferInstanceAs (PreservesLimitsOfShape WalkingCospan (overToScheme τ B S hS))
  exact preservesLimitsOfShape_of_reflects_of_preserves _ (Over.forget S)

/-- **`hComparison` for a localized big site.**  The comparison map from the image of an
iterated fibre product of a covering of a localized big site to the corresponding iterated fibre
product of the image covering is an isomorphism.  This is the hypothesis `hComparison` of
`Stacks.CechSite.sheafCohomology_isZero_of_cechCohomology_isZero_of_functor` verbatim, and it is
condition (2) of Sites, Definition 00WV for `AlgebraicGeometry.overToSlice`. -/
public theorem overStandardCoverings_comparison :
    ∀ {U : Over (base B S hS)}
      (E : { E : PreZeroHypercover.{u} U // E.sieve₀ ∈ overTopology τ B S hS U })
      (hE : E ∈ overStandardCoverings τ B S hS U) (p : ℕ) (i : Fin (p + 1) → E.1.I₀),
        letI : ∀ (q : ℕ) (j : Fin (q + 1) → E.1.I₀),
          HasProduct (fun a ↦ Over.mk (E.1.f (j a))) :=
            overStandardCoverings_hasProducts τ B S hS E hE
        letI : ∀ (q : ℕ) (j : Fin (q + 1) → (E.1.map (overToSlice τ B S hS)).I₀),
          HasProduct (fun a ↦ Over.mk ((E.1.map (overToSlice τ B S hS)).f (j a))) :=
            overStandardCoverings_hasImageProducts τ B S hS E hE
        IsIso (Stacks.CechSite.cechProductMapOfFunctor (overToSlice τ B S hS) E.1 p i) := by
  intro U E hE p i
  let := overStandardCoverings_hasProducts τ B S hS E hE
  let := overStandardCoverings_hasImageProducts τ B S hS E hE
  let : PreservesLimit (Discrete.functor (fun a ↦ Over.mk (E.1.f (i a))))
      (Over.post (X := U) (overToSlice τ B S hS)) :=
    Stacks.Sites.preservesLimit_fibreProducts_overPost (overToSlice τ B S hS) E.1
      (fun _ _ _ ↦ inferInstance) (fun _ _ _ ↦ inferInstance) p i
  exact Stacks.CechSite.isIso_cechProductMapOfFunctor (overToSlice τ B S hS) E.1 p i

end AlgebraicGeometry

end
