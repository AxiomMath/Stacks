module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.MapHomologyCycles
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.EdgeMorphismOnARingedSite

/-!
# The unit of an adjunction against the two homology comparisons, on complexes

Let `adj : E ⊣ F` be an adjunction of additive functors of abelian categories, `P` a cochain
complex in the source of `E` and `q` a degree. Two canonical comparisons are available:

* `Stacks.MapHomologyCycles.mapHomology`, the comparison `E(H^q P) ⟶ H^q(E P)` that the **right
  exact** `E` supplies, characterised by the cycle-class equation
  `E(π) ≫ mapHomology = mapCycles ≫ π`;
* `Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.homologyComparison`, the comparison
  `H^q(F Z) ⟶ F(H^q Z)` that the **left exact** `F` supplies, characterised by the cycle-class
  equation `π ≫ homologyComparison = cyclesComparison ≫ F(π)`.

This file proves that the degreewise unit of `adj` matches the two: taking `H^q` of the unit
`P ⟶ F(E P)` of complexes and following it with the comparison of `F` at `E P` is the unit of
`adj` at `H^q P` followed by `F` of the comparison of `E` at `P`. That is the complex-level
content of the compatibility of the top-degree pullback comparison of [Stacks, Tag 0EX3] with
the cohomology edge morphism of the derived direct image; everything else in that compatibility
is transport between a complex and the object of the derived category it represents.

## Main results

* `Stacks.EdgeCompat.unit_cyclesMap_comp_cyclesComparison`: the identity on **cycles**, which is
  where the two universal properties meet: both sides composed with `F` of the inclusion of the
  cycles of `E P` are the inclusion of the cycles of `P` followed by the unit in degree `q`.
* `Stacks.EdgeCompat.unit_homologyMap_comp_homologyComparison`: **the identity on homology.**

## Implementation notes

*Both proofs are cancellations against a universal property, not chases.* On cycles the relevant
map is a monomorphism — `F` is left exact, so `F` of the inclusion of the cycles is a kernel
inclusion (`…HomologyComparison.mono_map_iCycles`) — and on homology it is an epimorphism, the
projection from the cycles. Nothing is unfolded: `cyclesComparison` and `mapCycles` are used only
through `…cyclesComparison_comp_map_iCycles` and `Stacks.MapHomologyCycles.mapCycles_i`.

*The degreewise unit is a hypothesis, not `CategoryTheory.Adjunction`'s own.* The unit of
`CategoryTheory.Adjunction.mapHomologicalComplexAdjunction` has target
`(E.mapHomologicalComplex c ⋙ F.mapHomologicalComplex c).obj P`, whereas every comparison here is
stated at `(F.mapHomologicalComplex c).obj ((E.mapHomologicalComplex c).obj P)`. The two are
`rfl`-equal and **not** interchangeable for `rw`: with the unit spelled through the composite
functor, `HomologicalComplex.cyclesMap_i` does not fire, because the instance arguments of
`cyclesMap` are those of the composite spelling. So the unit is taken as a morphism `u` together
with the hypothesis that its components are those of `adj`, and the consumer supplies
`(Adjunction.mapHomologicalComplexAdjunction adj c).unit.app P` in **argument** position, where
the `rfl` is discharged at default transparency.

*Nothing here is about geometry*, and `PreservesFiniteLimits F` and `PreservesFiniteColimits E`
are instance binders rather than consequences of the adjunction: the statement of each comparison
needs them at elaboration time, and for the intended application they are supplied by
`RingedSpaceModuleAdjunction.preservesLimits_modulePushforward` and
`RingedSpaceModuleAdjunction.preservesFiniteColimits_modulePullback`.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Category
open Stacks.Cohomology.HypercohomologyEdge.HomologyComparison

namespace Stacks.EdgeCompat

universe vC uC vD uD

variable {C : Type uC} [Category.{vC} C] [Abelian C]
  {D : Type uD} [Category.{vD} D] [Abelian D]
  {E : D ⥤ C} {F : C ⥤ D} [E.Additive] [F.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits E] (adj : E ⊣ F)
  (P : CochainComplex D ℤ)
  (u : P ⟶ (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
    ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))
  (hu : ∀ n : ℤ, u.f n = adj.unit.app (P.X n)) (q : ℤ)

include hu in
omit [PreservesFiniteColimits E] in
/-- **The degreewise unit against the two cycle comparisons.** Let `u : P ⟶ F(E P)` be the unit
of complexes, that is, a morphism whose component in each degree is the unit of `adj`. The map on
degree-`q` cycles induced by `u`, followed by the comparison `Z^q(F(E P)) ⟶ F(Z^q(E P))` of the
left exact `F`, is the unit of the adjunction at `Z^q P` followed by `F` of the comparison
`E(Z^q P) ⟶ Z^q(E P)`.

`F` of the inclusion of the cycles of `E P` is a monomorphism, `F` being left exact, and both
sides composed with it are the inclusion of the cycles of `P` followed by the unit in degree
`q` — on the left because the cycles comparison is defined by that factorisation, on the right by
the naturality of the unit. -/
theorem unit_cyclesMap_comp_cyclesComparison :
    HomologicalComplex.cyclesMap u q ≫
        cyclesComparison F ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) q =
      adj.unit.app (P.cycles q) ≫ F.map (Stacks.MapHomologyCycles.mapCycles E P q) := by
  have hmono := mono_map_iCycles F ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) q
  apply (cancel_mono (F.map
    (((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P).iCycles q))).1
  rw [assoc, cyclesComparison_comp_map_iCycles, HomologicalComplex.cyclesMap_i, hu, assoc,
    ← F.map_comp, Stacks.MapHomologyCycles.mapCycles_i]
  exact adj.unit.naturality (P.iCycles q)

include hu in
/-- **The degreewise unit against the two homology comparisons.** For the unit `u : P ⟶ F(E P)`
of complexes and a degree `q`,

> `H^q(u) ≫ homologyComparison F (E P) q = adj.unit ≫ F(mapHomology E P q)`,

the left-hand side using the comparison the left exact `F` supplies and the right-hand side the
one the right exact `E` supplies.

The projection from the degree-`q` cycles of `P` onto its homology is an epimorphism, and both
sides precomposed with it are, by the two defining cycle-class equations, the identity
`unit_cyclesMap_comp_cyclesComparison` followed by `F` of the projection of `E P`. -/
theorem unit_homologyMap_comp_homologyComparison :
    HomologicalComplex.homologyMap u q ≫
        homologyComparison F ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) q =
      adj.unit.app (P.homology q) ≫ F.map (Stacks.MapHomologyCycles.mapHomology E P q) := by
  apply (cancel_epi (P.homologyπ q)).1
  have h1 : P.homologyπ q ≫ HomologicalComplex.homologyMap u q ≫
        homologyComparison F ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) q =
      adj.unit.app (P.cycles q) ≫ F.map (Stacks.MapHomologyCycles.mapCycles E P q ≫
        ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P).homologyπ q) := by
    rw [← assoc, HomologicalComplex.homologyπ_naturality, assoc,
      homologyπ_comp_homologyComparison, ← assoc,
      unit_cyclesMap_comp_cyclesComparison adj P u hu q, assoc, ← F.map_comp]
  rw [h1, ← adj.unit_naturality_assoc, ← F.map_comp,
    Stacks.MapHomologyCycles.homologyπ_comp_mapHomology]

end Stacks.EdgeCompat

end
