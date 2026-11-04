module

public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnSource.PolynomialGeometry

/-!
# Étaleness at a point is preserved by composition

If `f : X ⟶ Y` is étale at `x` and `g : Y ⟶ Z` is étale at `f x`, then `g ∘ f` is étale at `x`.

Étaleness of a morphism of schemes is stable under composition, and étaleness at a point is
étaleness of the restriction to some open neighbourhood of that point
(`AlgebraicGeometry.etaleAt_iff_exists_open`). Restricting the neighbourhood of `x` to the part
lying over the neighbourhood of `f x` makes the two restrictions composable, and the composite is
étale on that smaller neighbourhood.

## Main results

* `AlgebraicGeometry.etaleAt_comp`: étaleness at a point is preserved by composition.

## Implementation notes

The two existing composition statements in the draft go the other way: Tags 0GSA and 0GSB of
`StacksFrontier.AlgebraicGeometry.Morphisms.Etale.UnibranchComposition` descend étaleness of a
composite to its factors, under unibranch hypotheses. The forward direction needs none of that
and is what a chain of morphisms each étale at the relevant point requires — in particular the
composite `π = r_{n + 1} ∘ ⋯ ∘ r_N` of Stacks 0B0E, whose condition (2) is étaleness at finitely
many points of `X` and is supplied one projection at a time.

`AlgebraicGeometry.etaleAt_postcomp` is the special case in which the second morphism is étale
everywhere, which is too strong here: the projections of Stacks 0B0E are étale only at the chosen
points.

## References

* [Stacks Project, Tag 02GI](https://stacks.math.columbia.edu/tag/02GI)
* [Stacks Project, Tag 0B0E](https://stacks.math.columbia.edu/tag/0B0E)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

universe u

variable {X Y Z : Scheme.{u}}

/-- **Étaleness at a point is preserved by composition.** If `f` is étale at `x` and `g` is étale
at `f x`, then `f ≫ g` is étale at `x`. -/
public theorem etaleAt_comp (f : X ⟶ Y) (g : Y ⟶ Z) {x : X} (hf : EtaleAt f x)
    (hg : EtaleAt g (f.base x)) : EtaleAt (f ≫ g) x := by
  obtain ⟨U, hxU, hU⟩ := (etaleAt_iff_exists_open f x).mp hf
  obtain ⟨W, hfxW, hW⟩ := (etaleAt_iff_exists_open g (f.base x)).mp hg
  let A : U.toScheme.Opens := (U.ι ≫ f) ⁻¹ᵁ W
  have : Etale ((A.ι ≫ U.ι) ≫ f ≫ g) := by
    rw [show (A.ι ≫ U.ι) ≫ f ≫ g = (U.ι ≫ f).resLE W A le_rfl ≫ W.ι ≫ g by simp]
    infer_instance
  exact etaleAt_of_open_precomp (A.ι ≫ U.ι) (f ≫ g) ⟨⟨x, hxU⟩, hfxW⟩
    ((etale_iff_forall_etaleAt _).mp this _)

end AlgebraicGeometry

end
