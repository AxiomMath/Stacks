module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.Topology.Irreducible
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.DoubledOriginSections

/-!
# The doubled origin is not separated over affine space

The coordinate morphism of affine `n`-space with its origin doubled restricts to the identity on
each of the two charts, and those charts cover the source, so the morphism is étale, and hence
flat and locally of finite presentation. In positive dimension it is not separated: the two chart
origins are distinct points with the same image, and the two charts agree on the complement of
the origin, which is dense.

Taking `n = 1` this is the morphism of the example of Stacks 04QI, the affine line with zero
doubled over the affine line. It witnesses that the separatedness hypothesis of Stacks 04QH is
not implied by the remaining hypotheses of that proposition.

## Main results

* `AlgebraicGeometry.chartInclusion_origin_ne`: the two chart origins are distinct points of the
  glued scheme.
* `AlgebraicGeometry.etale_coordinateMorphism`, `AlgebraicGeometry.flat_coordinateMorphism`,
  `AlgebraicGeometry.locallyOfFinitePresentation_coordinateMorphism`: the coordinate morphism is
  étale, flat and locally of finite presentation.
* `AlgebraicGeometry.not_isSeparated_coordinateMorphism`: in positive dimension the coordinate
  morphism is not separated.
* `AlgebraicGeometry.flat_locallyOfFinitePresentation_not_isSeparated_coordinateMorphism`: in
  positive dimension the coordinate morphism is flat and locally of finite presentation but not
  separated.

## References

* [Stacks Project, Tag 04QI](https://stacks.math.columbia.edu/tag/04QI)
* [Stacks Project, Tag 04QH](https://stacks.math.columbia.edu/tag/04QH)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The two chart origins of affine space with doubled origin are distinct points of the glued
scheme. -/
@[stacks 04QI "the example: the two chart origins are distinct points"]
theorem chartInclusion_origin_ne (k : Type u) [Field k] (n : ℕ) :
    chartInclusion k n 0 (affineOrigin k n) ≠ chartInclusion k n 1 (affineOrigin k n) :=
  fun heq => origin_notMem_range_other_chart k n 0 1 (by decide) ⟨affineOrigin k n, heq.symm⟩

/-- A Zariski-local property of the source holds for the coordinate morphism of affine space with
doubled origin as soon as it holds for its restriction to each of the two charts. -/
private theorem coordinateMorphism_of_chartInclusion_comp (P : MorphismProperty Scheme)
    [IsZariskiLocalAtSource P] (k : Type u) [Field k] (n : ℕ)
    (h : ∀ i, P (chartInclusion k n i ≫ coordinateMorphism k n)) : P (coordinateMorphism k n) :=
  IsZariskiLocalAtSource.of_openCover (doubledZeroGlueData k n).openCover fun ⟨i⟩ => h i

/-- The coordinate morphism of affine space with doubled origin is étale. -/
theorem etale_coordinateMorphism (k : Type u) [Field k] (n : ℕ) :
    Etale (coordinateMorphism k n) := by
  have : IsZariskiLocalAtSource (@Etale) :=
    AlgebraicGeometry.HasRingHomProperty.instIsZariskiLocalAtSource
  refine coordinateMorphism_of_chartInclusion_comp (@Etale) k n fun i => ?_
  rw [(coordinateMorphismData k n).property i]
  infer_instance

/-- The coordinate morphism of affine space with doubled origin is flat. -/
theorem flat_coordinateMorphism (k : Type u) [Field k] (n : ℕ) :
    Flat (coordinateMorphism k n) := by
  have : IsZariskiLocalAtSource (@Flat) :=
    AlgebraicGeometry.HasRingHomProperty.instIsZariskiLocalAtSource
  refine coordinateMorphism_of_chartInclusion_comp (@Flat) k n fun i => ?_
  rw [(coordinateMorphismData k n).property i]
  infer_instance

/-- The coordinate morphism of affine space with doubled origin is locally of finite
presentation. -/
theorem locallyOfFinitePresentation_coordinateMorphism (k : Type u) [Field k] (n : ℕ) :
    LocallyOfFinitePresentation (coordinateMorphism k n) := by
  have : IsZariskiLocalAtSource (@LocallyOfFinitePresentation) :=
    AlgebraicGeometry.HasRingHomProperty.instIsZariskiLocalAtSource
  refine coordinateMorphism_of_chartInclusion_comp (@LocallyOfFinitePresentation) k n fun i => ?_
  rw [(coordinateMorphismData k n).property i]
  infer_instance

/-- In positive dimension the inclusion of the complement of the origin into affine space is
dominant. -/
private theorem isDominant_puncturedAffineSpace_ι (k : Type u) [Field k] (n : ℕ) (hn : 0 < n) :
    IsDominant (puncturedAffineSpace k n).ι := by
  rw [isDominant_iff]
  have hne : (↑(puncturedAffineSpace k n) :
      Set (Spec (.of (MvPolynomial (Fin n) k)))).Nonempty := by
    refine ⟨⟨⊥, by simpa using (inferInstance : (⊥ : Ideal (MvPolynomial (Fin n) k)).IsPrime)⟩, ?_⟩
    refine Opens.mem_iSup.mpr ⟨⟨0, hn⟩, ?_⟩
    exact (PrimeSpectrum.mem_basicOpen _ _).mpr (by simp)
  simpa [DenseRange, Scheme.Opens.range_ι] using (puncturedAffineSpace k n).2.dense hne

/-- In positive dimension the coordinate morphism of affine space with doubled origin is not
separated. -/
theorem not_isSeparated_coordinateMorphism (k : Type u) [Field k] (n : ℕ) (hn : 0 < n) :
    ¬ IsSeparated (coordinateMorphism k n) := by
  intro _
  have _ : IsDominant (puncturedAffineSpace k n).ι :=
    isDominant_puncturedAffineSpace_ι k n hn
  have hcharts : chartInclusion k n 0 = chartInclusion k n 1 := by
    refine ext_of_isDominant_of_isSeparated (coordinateMorphism k n) ?_
      (puncturedAffineSpace k n).ι ?_
    · rw [(coordinateMorphismData k n).property 0, (coordinateMorphismData k n).property 1]
    · exact comp_chartInclusion_eq k n _ (by rw [Scheme.Opens.range_ι])
  exact chartInclusion_origin_ne k n (by rw [hcharts])

/-- In positive dimension the coordinate morphism of affine space with doubled origin is flat and
locally of finite presentation but not separated. -/
@[stacks 04QI "the example: flat and locally of finite presentation but not separated"]
theorem flat_locallyOfFinitePresentation_not_isSeparated_coordinateMorphism
    (k : Type u) [Field k] (n : ℕ) (hn : 0 < n) :
    Flat (coordinateMorphism k n) ∧
      LocallyOfFinitePresentation (coordinateMorphism k n) ∧
      ¬ IsSeparated (coordinateMorphism k n) :=
  ⟨flat_coordinateMorphism k n, locallyOfFinitePresentation_coordinateMorphism k n,
    not_isSeparated_coordinateMorphism k n hn⟩

end AlgebraicGeometry

end
