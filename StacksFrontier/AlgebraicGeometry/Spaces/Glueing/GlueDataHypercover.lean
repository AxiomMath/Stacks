module

public import Mathlib.CategoryTheory.GlueData
public import Mathlib.CategoryTheory.Sites.Hypercover.One

/-!
# The one-hypercover of a glueing datum

A glueing datum in a category with fibre products whose charts generate a covering sieve is a
`1`-hypercover of the glued object, with one relation between any two charts, namely their
intersection.

## Main definitions

* `AlgebraicGeometry.Space.glueDataHypercover` is that `1`-hypercover.

## Implementation notes

The index type of relations between two charts is `PUnit`: the single relation is the chart
intersection `D.V (i, j)`, mapping to the two charts by `D.f i j` and `D.t i j ≫ D.f j i`.
The hypercover's second covering condition asks for a covering sieve of lifts of any pair of
arrows agreeing in the glued object; here the whole maximal sieve works, since the chart
intersection is the fibre product of the two charts.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- A glueing datum whose charts generate a covering sieve and whose chart intersections are
the fibre products of the charts is a `1`-hypercover of the glued object. -/
noncomputable def glueDataHypercover
    {C : Type*} [Category.{u} C] {J : GrothendieckTopology C}
    [HasPullbacks C] (D : CategoryTheory.GlueData C)
    [HasMulticoequalizer D.diagram]
    (hcover : Sieve.generate (Presieve.ofArrows D.U D.ι) ∈ J D.glued)
    (hlim : ∀ i j, IsLimit (D.vPullbackCone i j)) : J.OneHypercover D.glued where
  I₀ := D.J
  X := D.U
  f := D.ι
  I₁ _ _ := PUnit
  Y i₁ i₂ _ := D.V (i₁, i₂)
  p₁ i₁ i₂ _ := D.f i₁ i₂
  p₂ i₁ i₂ _ := D.t i₁ i₂ ≫ D.f i₂ i₁
  w i₁ i₂ _ := by simp only [Category.assoc, CategoryTheory.GlueData.glue_condition]
  mem₀ := hcover
  mem₁ i₁ i₂ W p₁ p₂ fac := by
    refine J.superset_covering (fun T g _ ↦ ?_) (J.top_mem _)
    have ⟨φ, h₁, h₂⟩ := PullbackCone.IsLimit.lift' (hlim i₁ i₂)
      (g ≫ p₁) (g ≫ p₂) (by simpa using g ≫= fac)
    exact ⟨PUnit.unit, φ, h₁.symm, h₂.symm⟩

end AlgebraicGeometry.Space

end
