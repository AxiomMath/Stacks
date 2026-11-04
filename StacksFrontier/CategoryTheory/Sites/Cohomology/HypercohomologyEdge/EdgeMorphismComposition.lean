module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.EdgeMorphismOnARingedSite

/-!
# The cycles and homology comparisons of a composite of two left exact functors

For a left exact additive functor `F` and a complex `K`, `Stacks.Cohomology.HypercohomologyEdge`
`.HomologyComparison.cyclesComparison` and `…homologyComparison` are the canonical maps

> `Z^q(F K) ⟶ F(Z^q K)` and `H^q(F K) ⟶ F(H^q K)`,

the first of which is an isomorphism. This file says what they do to a composite `F ⋙ G` of two
such functors: each is the comparison for `G` at the complex `F K`, followed by `G` applied to the
comparison for `F`.

## Main results

All in the namespace `Stacks.Cohomology.HypercohomologyEdge.HomologyComparison`.

* `cyclesComparison_comp`: the cycles comparison `Z^q((F ⋙ G)K) ⟶ (F ⋙ G)(Z^q K)` of a composite is
  `Z^q(G(F K)) ⟶ G(Z^q(F K)) ⟶ G(F(Z^q K))`.
* `homologyComparison_comp`: the homology comparison `H^q((F ⋙ G)K) ⟶ (F ⋙ G)(H^q K)` of a
  composite is `H^q(G(F K)) ⟶ G(H^q(F K)) ⟶ G(F(H^q K))`.
* `homologyComparisonNatTrans_comp`: the same as an identity of natural transformations of
  functors on cochain complexes.

## References

* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe vA uA vB uB vC uC

namespace Stacks.Cohomology.HypercohomologyEdge.HomologyComparison

variable {A : Type uA} [Category.{vA} A] [Abelian A]
  {B : Type uB} [Category.{vB} B] [Abelian B]
  {C : Type uC} [Category.{vC} C] [Abelian C]
  (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteLimits G]

/-- For `F : A ⥤ B` and `G : B ⥤ C` additive and left exact, a cochain complex `K` of objects of
`A` and a degree `q`, the cycles comparison

> `Z^q((F ⋙ G)K) ⟶ (F ⋙ G)(Z^q K)`

is the comparison for `G` at the complex `F K`, followed by `G` applied to the comparison for `F`
at `K`. -/
theorem cyclesComparison_comp (K : CochainComplex A ℤ) (q : ℤ) :
    cyclesComparison (F ⋙ G) K q =
      cyclesComparison G ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) q ≫
        G.map (cyclesComparison F K q) := by
  have hmono := mono_map_iCycles (F ⋙ G) K q
  apply (cancel_mono ((F ⋙ G).map (K.iCycles q))).1
  rw [cyclesComparison_comp_map_iCycles, Category.assoc,
    show (F ⋙ G).map (K.iCycles q) = G.map (F.map (K.iCycles q)) from rfl, ← G.map_comp,
    cyclesComparison_comp_map_iCycles, cyclesComparison_comp_map_iCycles]
  rfl

/-- For `F : A ⥤ B` and `G : B ⥤ C` additive and left exact, a cochain complex `K` of objects of
`A` and a degree `q`, the homology comparison

> `H^q((F ⋙ G)K) ⟶ (F ⋙ G)(H^q K)`

is the comparison for `G` at the complex `F K`, followed by `G` applied to the comparison for `F`
at `K`. -/
theorem homologyComparison_comp (K : CochainComplex A ℤ) (q : ℤ) :
    homologyComparison (F ⋙ G) K q =
      homologyComparison G ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) q ≫
        G.map (homologyComparison F K q) := by
  have hG : (((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).homologyπ q ≫
        homologyComparison G ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) q =
      cyclesComparison G ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) q ≫
        G.map (((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).homologyπ q) :=
    homologyπ_comp_homologyComparison G
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) q
  apply (cancel_epi
    ((((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).homologyπ q)).1
  rw [homologyπ_comp_homologyComparison, ← Category.assoc, hG, Category.assoc, ← G.map_comp,
    homologyπ_comp_homologyComparison, G.map_comp, cyclesComparison_comp, Category.assoc]
  rfl

/-- The homology comparison of a composite `F ⋙ G`, as a natural transformation of functors on
cochain complexes, is the comparison for `G` whiskered by `F` on the left, followed by the
comparison for `F` whiskered by `G` on the right. -/
theorem homologyComparisonNatTrans_comp (q : ℤ) :
    homologyComparisonNatTrans (F ⋙ G) q =
      Functor.whiskerLeft (F.mapHomologicalComplex (ComplexShape.up ℤ))
          (homologyComparisonNatTrans G q) ≫
        Functor.whiskerRight (homologyComparisonNatTrans F q) G :=
  NatTrans.ext (funext fun K => homologyComparison_comp F G K q)

end Stacks.Cohomology.HypercohomologyEdge.HomologyComparison

end
