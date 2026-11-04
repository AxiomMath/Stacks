module

public import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GeometricPointFiber
public import StacksFrontier.CategoryTheory.Filtered.FiniteProductColimit
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.GeometricPointFiber
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finite products commute with the étale stalk

The stalk of a presheaf on a small étale site at a geometric point is the colimit over the
opposite of the category of elements of `AlgebraicGeometry.geometricPointFiber`, the category of
étale neighborhoods of the point inside the chosen big étale site. That category is cofiltered,
so the index category of the stalk is filtered, and the interchange of a filtered colimit with a
finite product — `Stacks.FilteredColimit.colimitPiComparison_bijective` — applies to it
directly, with no transport to a small cofinal family of affine neighborhoods.

Two instances are recorded here, because the cofilteredness they rest on is a *private*
declaration of `StacksFrontier.AlgebraicGeometry.EtaleCohomology.GeometricPointFiber`: without them
a module that does not `import all` that file cannot synthesize `IsFiltered` on the index
category, and every route through Mathlib's filtered-colimit machinery reports itself blocked.

## Main definitions

* `AlgebraicGeometry.etaleStalkPiEquiv` — the interchange at an étale stalk, as an equivalence.

## Main results

* `AlgebraicGeometry.isFiltered_geometricPointFiber_elementsOp` — the index category of an étale
  stalk is filtered.
* `AlgebraicGeometry.preservesFiniteLimits_colim_geometricPointFiber` — colimits over the index
  category of an étale stalk preserve *all* finite limits of sets, not only finite products.
* `AlgebraicGeometry.etaleStalkPiComparison_bijective` — for a finite family of functors on the
  index category of the stalk at a geometric point, the tuple-of-germs map out of the colimit of
  the pointwise product is a bijection.

## Implementation notes

The results are stated for an arbitrary family of functors on the index category rather than for
presheaves on the site, because the intended consumer — the stalk computation for a finite
pushforward, Tag 03QP — needs them for the functors `U ↦ F(W_x(U))` attached to the components
`W_x(U)` of a base change over an étale neighborhood `U`, which are not restrictions of
presheaves on the site along the projection out of the category of elements. Composing with
`(CategoryOfElements.π _).op` recovers the presheaf case.

## References

* [Stacks Project, Tag 002W](https://stacks.math.columbia.edu/tag/002W)
* [Stacks Project, Tag 03QP](https://stacks.math.columbia.edu/tag/03QP)
* [Stacks Project, Tag 040R](https://stacks.math.columbia.edu/tag/040R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X) (x : GeometricPoint X)

/-- **The index category of an étale stalk is filtered.** The étale neighborhoods of a geometric
point inside a chosen big étale site form a cofiltered category, so the opposite category over
which the stalk colimit is taken is filtered. -/
@[sga "4 IV 6.8.2" "filteredness clause", sga "4 VIII 3.9" "filteredness of C_ξ^op"]
public instance isFiltered_geometricPointFiber_elementsOp :
    IsFiltered (geometricPointFiber B X hX x).Elementsᵒᵖ :=
  inferInstance

/-- **Colimits over the index category of an étale stalk preserve finite limits of sets.** This
is the left exactness of the étale stalk at the level of the defining diagram. -/
public instance preservesFiniteLimits_colim_geometricPointFiber :
    PreservesFiniteLimits
      (colim : ((geometricPointFiber B X hX x).Elementsᵒᵖ ⥤ Type (u + 1)) ⥤ Type (u + 1)) :=
  inferInstance

/-- **Finite products commute with the étale stalk.** For a finite family of functors on the
index category of the stalk at a geometric point — in the intended application, the sections of
a sheaf of sets over the components of a base change — the tuple-of-germs map out of the colimit
of the pointwise product is a bijection. -/
public theorem etaleStalkPiComparison_bijective {ι : Type u} [Finite ι]
    (G : ι → ((geometricPointFiber B X hX x).Elementsᵒᵖ ⥤ Type (u + 1))) :
    Function.Bijective (Stacks.FilteredColimit.colimitPiComparison G) :=
  Stacks.FilteredColimit.colimitPiComparison_bijective G

/-- **Finite products commute with the étale stalk**, as an equivalence. -/
public def etaleStalkPiEquiv {ι : Type u} [Finite ι]
    (G : ι → ((geometricPointFiber B X hX x).Elementsᵒᵖ ⥤ Type (u + 1))) :
    colimit (Stacks.FilteredColimit.pointwisePi G) ≃ ∀ i, colimit (G i) :=
  Equiv.ofBijective _ (etaleStalkPiComparison_bijective B X hX x G)

end AlgebraicGeometry

end
