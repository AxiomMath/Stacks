module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartEquivalenceClosure
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.ChartCoversTop
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.ModuleFilteredColimitSections

/-!
# Étale charts covering the points of an algebraic space cover its small étale site

A family of étale scheme charts `Vⱼ → X` of an algebraic space whose images cover the set of
points `|X|` is a covering of the final object of the small étale site of `X`.

## Main results

* `AlgebraicGeometry.Space.SmallEtale.coversTop_of_iUnion_range_eq_univ`.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A family of étale charts whose images cover `|X|` covers the small étale site of `X`.**
The charts form an étale covering of `X` by the represented algebraic spaces, the charts of whose
members all map to members of the family. -/
theorem SmallEtale.coversTop_of_iUnion_range_eq_univ (X : AlgebraicSpaces B S hS) {ι : Type v}
    (c : ι → SmallEtale B S hS X.1)
    (hc : (⋃ j, Set.range (pointsMap B S hS (chartSpace B S hS X (c j)).1
      (chartToSpace B S hS X (c j)).hom)) = Set.univ) :
    (SmallEtale.topology B S hS X.1).CoversTop c := by
  have hcov : IsEtaleCovering B S hS (fun j => (chartSpace B S hS X (c j)).1)
      (fun j => (chartToSpace B S hS X (c j)).hom) :=
    ⟨X.2, fun j => (chartSpace B S hS X (c j)).2,
      fun j => isEtale_chartToSpace B S hS X (c j), hc⟩
  refine Stacks.Sites.coversTop_of_exists_hom
    (coversTop_of_isEtaleCovering B S hS (fun j => chartSpace B S hS X (c j))
      (fun j => chartToSpace B S hS X (c j)) hcov) fun p => ⟨p.1, ⟨?_⟩⟩
  exact ObjectProperty.homMk (CostructuredArrow.homMk (yoneda.preimage p.2.1.hom)
    (congrArg (· ≫ (c p.1).1.hom) (yoneda.map_preimage p.2.1.hom)))

end AlgebraicGeometry.Space
