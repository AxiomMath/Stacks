module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties

/-!
# The reduced closure of a point under an open immersion

For an open immersion `j : U ⟶ X` and a point `x` of `U`, the reduced closure of `x` in `U` maps
to the reduced closure of `j x` in `X`. This file identifies the range of that induced morphism:
it is exactly the locus of the target closure lying over the range of `j`. This is the
topological input to the coherence criterion for a pushforward along an open immersion.

## Main results

* `Stacks.LocalCohomology.range_closure_open_square`: the range of the morphism between the
  reduced closures induced by an open immersion.

## Implementation notes

The reduced closure of `x` is `Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {x})`, whose
support is the topological closure of `{x}`. Both inclusions are computed by transporting along
`Scheme.IdealSheafData.range_subschemeι`, using that a closed immersion is a topological
embedding and that an open immersion commutes with closures of subsets of its source.

The irreducibility, integrality and local Noetherianity of such a subscheme are *not* proved here:
they are `Scheme.IdealSheafData.irreducibleSpace_subscheme`
(`StacksFrontier/AlgebraicGeometry/Limits/ReducedInducedSubscheme.lean`),
`Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure` and
`Scheme.IdealSheafData.isLocallyNoetherian_subscheme`
(`StacksFrontier/AlgebraicGeometry/CoherentPushforwardCriteria/ClosureSubscheme.lean`).

## References

* [Stacks Project, Tag 0BK3](https://stacks.math.columbia.edu/tag/0BK3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.LocalCohomology

/-- For an open immersion `j` and a point `x` of its source, a morphism between the reduced
closure of `x` and the reduced closure of `j x` compatible with `j` has range exactly the points
of the latter whose image lies in the range of `j`. -/
public theorem range_closure_open_square {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [IsLocallyNoetherian U] [IsLocallyNoetherian X] (x : U)
    (j' : (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({x} : Set U))).subscheme ⟶
      (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({j x} : Set X))).subscheme)
    (comm : j' ≫ (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({j x} : Set X))).subschemeι =
      (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({x} : Set U))).subschemeι ≫ j) :
    Set.range j'.base = {z | (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({j x} : Set X))).subschemeι.base z ∈ Set.range j.base} := by
  let iW := Scheme.IdealSheafData.vanishingIdeal
    (Closeds.closure ({x} : Set U))
  let iZ := Scheme.IdealSheafData.vanishingIdeal
    (Closeds.closure ({j x} : Set X))
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨iW.subschemeι.base w, by simpa using (congrArg (fun f => f.base w) comm).symm⟩
  · rintro ⟨u, hu⟩
    have hzcl : iZ.subschemeι.base z ∈ Closeds.closure ({j x} : Set X) := by
      simpa [iZ, Scheme.IdealSheafData.coe_support_vanishingIdeal] using
        iZ.range_subschemeι.le ⟨z, rfl⟩
    obtain ⟨w, rfl⟩ : u ∈ Set.range iW.subschemeι.base := by
      rw [iW.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal,
        Closeds.coe_closure, j.isOpenEmbedding.isInducing.closure_eq_preimage_closure_image,
        Set.image_singleton]
      simpa [hu] using hzcl
    exact ⟨w, (IsPreimmersion.isEmbedding iZ.subschemeι).injective
      ((congrArg (fun f => f.base w) comm).trans hu)⟩

end Stacks.LocalCohomology
