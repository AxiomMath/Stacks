module

public import Mathlib.AlgebraicGeometry.Sites.MorphismProperty
public import Mathlib.CategoryTheory.GlueData
public import Mathlib.CategoryTheory.Sites.Hypercover.One
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf

/-!
# Gluing inputs for the schematic locus of an algebraic space

Stacks 03JH asserts that an algebraic space has a largest open subspace which is a scheme.
The locus itself and the maximality clause are
`AlgebraicGeometry.Space.schematicLocus` and `AlgebraicGeometry.Space.le_schematicLocus` in
`StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspace`; the two remaining clauses, that the
locus is an open subspace and that it is representable, are proved by covering the locus by
the representable open subspaces it is the union of and glueing. This file supplies the two
inputs to that glueing step which are statements about sites rather than about algebraic
spaces, and which are therefore usable by any relative glueing argument over a big fppf
site.

## Main results

* `CategoryTheory.GrothendieckTopology.OneHypercover.ofGlueData`: a glueing datum in a
  category with pullbacks whose pieces generate a covering sieve of the glued object, and
  whose overlaps are the pullbacks of the pieces, is a `1`-hypercover of the glued object.

## Implementation notes

`ofGlueData` takes the covering of the glued object as a hypothesis rather than deriving it,
because the topology is arbitrary: the overlaps `D.V (i, j)` are identified with the
pullbacks of the pieces by the hypothesis `hlim`, and the second condition of a
`1`-hypercover then holds for the maximal sieve, since any pair of maps into a piece which
agree on the glued object factors through the overlap. The index type of the relations is
`PUnit`, so the resulting hypercover has exactly one relation for each pair of pieces.

## References

* [Stacks Project, Tag 03JH](https://stacks.math.columbia.edu/tag/03JH)
* [Stacks Project, Tag 021R](https://stacks.math.columbia.edu/tag/021R)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace CategoryTheory.GrothendieckTopology.OneHypercover

/-- A glueing datum whose pieces generate a covering sieve of the glued object, and whose
overlaps are the pullbacks of the pieces, is a `1`-hypercover of the glued object. -/
public noncomputable def ofGlueData {C : Type*} [Category.{u} C] {J : GrothendieckTopology C}
    [HasPullbacks C] (D : GlueData C) [HasMulticoequalizer D.diagram]
    (hcover : Sieve.generate (Presieve.ofArrows D.U D.ι) ∈ J D.glued)
    (hlim : ∀ i j, IsLimit (D.vPullbackCone i j)) : J.OneHypercover D.glued where
  I₀ := D.J
  X := D.U
  f := D.ι
  I₁ _ _ := PUnit
  Y i₁ i₂ _ := D.V (i₁, i₂)
  p₁ i₁ i₂ _ := D.f i₁ i₂
  p₂ i₁ i₂ _ := D.t i₁ i₂ ≫ D.f i₂ i₁
  w i₁ i₂ _ := by simp only [Category.assoc, GlueData.glue_condition]
  mem₀ := hcover
  mem₁ i₁ i₂ W p₁ p₂ fac := by
    refine J.superset_covering (fun T g _ ↦ ?_) (J.top_mem _)
    have ⟨φ, h₁, h₂⟩ := PullbackCone.IsLimit.lift' (hlim i₁ i₂)
      (g ≫ p₁) (g ≫ p₂) (by simpa using g ≫= fac)
    exact ⟨PUnit.unit, φ, h₁.symm, h₂.symm⟩

end CategoryTheory.GrothendieckTopology.OneHypercover

namespace AlgebraicGeometry.BigFppfSite

end AlgebraicGeometry.BigFppfSite

end
