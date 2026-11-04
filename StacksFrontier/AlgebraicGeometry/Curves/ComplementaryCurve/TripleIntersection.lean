module

public import StacksFrontier.AlgebraicGeometry.Curves.ComplementaryCurve.IntersectionDegreeComponents

/-!
# Three irreducible components of a nodal curve have no common point

Let `k` be a field and let `X` be a one-dimensional `k`-scheme, locally of finite type and with at
worst nodal singularities.  Then no point of `X` lies on three pairwise-distinct irreducible
components: a singular point of such a curve is a node, and a node has exactly two branches.

The conclusion is recorded as an identity of ideal sheaves,

`vanishingIdeal C ⊔ vanishingIdeal D ⊔ vanishingIdeal E = ⊤`,

for the three components `C`, `D`, `E`.  The order on ideal sheaves being the order on ideals, a
supremum cuts out a scheme-theoretic intersection and `⊤` cuts out the empty subscheme, so this
says exactly that `C ∩ D ∩ E` is empty as a closed subscheme of `X`.

## Main results

* `Stacks.Curves.sup_sup_vanishingIdeal_eq_top`: **three pairwise-distinct irreducible components
  of a one-dimensional at-worst-nodal `k`-curve have empty common scheme-theoretic
  intersection.**

## References

* [Stacks Project, Tag 0C4J](https://stacks.math.columbia.edu/tag/0C4J)
* [Stacks Project, Tag 0C4D](https://stacks.math.columbia.edu/tag/0C4D)
* [Stacks Project, Tag 0C47](https://stacks.math.columbia.edu/tag/0C47)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.Scheme.IdealSheafData

universe u

namespace Stacks.Curves

/-- **Three pairwise-distinct irreducible components of a one-dimensional nodal curve have empty
common scheme-theoretic intersection.**  A common point would lie on three distinct irreducible
components of `X`, and so `X` would have at least three branches there, while a node has exactly
two: by `Stacks.Curves.irreducibleComponentsThrough_eq_pair_of_hasAtWorstNodalSingularities` the
components through a point lying on the two distinct components `C` and `D` are exactly `C` and
`D`, so the third component `E` is one of them.

The conclusion is stated as an identity of ideal sheaves: the order on ideal sheaves being the
order on ideals, a supremum cuts out a scheme-theoretic intersection and `⊤` cuts out the empty
subscheme. -/
theorem sup_sup_vanishingIdeal_eq_top
    {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    (hX_dimension : topologicalKrullDim X = 1)
    (hX_nodal : HasAtWorstNodalSingularities k X)
    {C D E : Set X} (hC : C ∈ irreducibleComponents X) (hD : D ∈ irreducibleComponents X)
    (hE : E ∈ irreducibleComponents X) (hCD : C ≠ D) (hCE : C ≠ E) (hDE : D ≠ E) :
    Scheme.IdealSheafData.vanishingIdeal (Closeds.closure C) ⊔
        Scheme.IdealSheafData.vanishingIdeal (Closeds.closure D) ⊔
          Scheme.IdealSheafData.vanishingIdeal (Closeds.closure E) = ⊤ := by
  rw [← Scheme.IdealSheafData.support_eq_bot_iff]
  refine SetLike.coe_injective ?_
  simp only [Scheme.IdealSheafData.support_sup, Closeds.coe_inf, Closeds.coe_bot,
    Scheme.IdealSheafData.coe_support_vanishingIdeal, Closeds.coe_closure,
    (isClosed_of_mem_irreducibleComponents C hC).closure_eq,
    (isClosed_of_mem_irreducibleComponents D hD).closure_eq,
    (isClosed_of_mem_irreducibleComponents E hE).closure_eq]
  rw [Set.eq_empty_iff_forall_notMem]
  rintro x ⟨⟨hxC, hxD⟩, hxE⟩
  have hpair := irreducibleComponentsThrough_eq_pair_of_hasAtWorstNodalSingularities
    hX_dimension hX_nodal hC hD hCD hxC hxD
  rcases (hpair ▸ ⟨hE, hxE⟩ : E ∈ ({C, D} : Set (Set X))) with h | h
  exacts [hCE h.symm, hDE h.symm]

end Stacks.Curves

end
