module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.SmoothLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.Coverings
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSmoothLocalCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.Retrofit
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothMorphismProperty

/-!
# Stability properties of the smooth coverings of algebraic spaces

Let `S` be a scheme contained in a big fppf site `B`. The smooth covering families of
algebraic spaces over `S`, `AlgebraicGeometry.Space.IsSmoothCovering`, are the covering
families of the smooth topology of Stacks 03YH. This module proves the three axioms a
collection of covering families must satisfy to present a topology: a singleton family on an
isomorphism is a covering, a covering composed with coverings of its members is a covering,
and the base change of a covering along any morphism of algebraic spaces is a covering.

## Main results

* `AlgebraicGeometry.Space.isSmoothCovering_of_isIso`: **Stacks 041D**, the isomorphism
  clause.
* `AlgebraicGeometry.Space.isSmoothCovering_comp`: **Stacks 041D**, the composition clause.
* `AlgebraicGeometry.Space.isSmoothCovering_fiberProduct`: **Stacks 041D**, the base-change
  clause.

## Implementation notes

Smoothness of a morphism of algebraic spaces over `S` is the every-étale-chart condition of
Stacks 03MJ applied to smoothness of morphisms of schemes, so the property clause of each of
the three statements is the corresponding stability property of that condition:
`AlgebraicGeometry.Space.isSmooth_comp` (Stacks 03ZD),
`AlgebraicGeometry.Space.isSmooth_isStableUnderBaseChange` (Stacks 03ZE), and, for an
isomorphism, invariance of the chart condition under precomposition with an isomorphism
together with smoothness of an identity.

The base-change clause is stated for the chosen fibre product
`AlgebraicGeometry.AlgebraicSpaces.fiberProduct` of Stacks 02X2 and its first projection; the
joint-surjectivity clause is then Stacks 03H4, lifting a point of the new base and a point of
a member of the family with the same image to a point of the fibre product.

## References

* [Stacks Project, Tag 041D](https://stacks.math.columbia.edu/tag/041D)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 041D**, the isomorphism clause. An isomorphism of algebraic spaces over `S`,
regarded as a family indexed by a point, is a smooth covering. -/
@[stacks 041D "isomorphism"]
lemma isSmoothCovering_of_isIso
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X' ⟶ X) [IsIso f]
    (hX : IsAlgebraicSpace B S hS X) :
    IsSmoothCovering B S hS (fun _ : Unit ↦ X') (fun _ ↦ f) := by
  have hX' : IsAlgebraicSpace B S hS X' :=
    isAlgebraicSpace_of_relativelyRepresentable B S hS f
      (Functor.relativelyRepresentable.of_isIso yoneda _) hX
  have hsmooth : IsSmooth B S hS f := by
    simpa using (holdsOnEveryEtaleChart_iso_comp_iff B S hS
      (@AlgebraicGeometry.Smooth.{u} : MorphismProperty Scheme.{u}) f (𝟙 X)).mpr
        (isSmooth_id_presheaf B S hS X)
  have hsurj : Function.Surjective (pointsMap B S hS X' f) := by
    have h : pointsMap B S hS X' f ∘ pointsMap B S hS X (inv f) = id := by
      rw [← pointsMap_comp, IsIso.inv_hom_id, pointsMap_id]
    exact Function.Surjective.of_comp (g := pointsMap B S hS X (inv f))
      (by rw [h]; exact Function.surjective_id)
  exact ⟨hX, fun _ ↦ hX', fun _ ↦ hsmooth, by
    rw [Set.iUnion_const, Set.range_eq_univ]; exact hsurj⟩

/-- **Stacks 041D**, the composition clause. Composing a smooth covering of an algebraic space
over `S` with a smooth covering of each of its members gives a smooth covering. -/
@[stacks 041D "composition"]
theorem isSmoothCovering_comp
    {I : Type v} {J : I → Type w} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (X : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (f : ∀ i, X i ⟶ F)
    (Y : ∀ i, J i → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (g : ∀ i j, Y i j ⟶ X i)
    (hf : IsSmoothCovering B S hS X f)
    (hg : ∀ i, IsSmoothCovering B S hS (Y i) (g i)) :
    IsSmoothCovering B S hS (fun ij : Σ i, J i ↦ Y ij.1 ij.2)
      (fun ij : Σ i, J i ↦ g ij.1 ij.2 ≫ f ij.1) := by
  refine ⟨hf.target_isAlgebraicSpace,
    fun ij ↦ (hg ij.1).source_isAlgebraicSpace ij.2, fun ij ↦ ?_, ?_⟩
  · exact isSmooth_comp B S hS ((hg ij.1).source_isAlgebraicSpace ij.2)
      (hf.source_isAlgebraicSpace ij.1) hf.target_isAlgebraicSpace
      (g ij.1 ij.2) (f ij.1) ((hg ij.1).smooth ij.2) (hf.smooth ij.1)
  · refine Set.eq_univ_iff_forall.mpr fun p ↦ ?_
    have hp := Set.eq_univ_iff_forall.mp hf.jointly_surjective p
    simp only [Set.mem_iUnion, Set.mem_range] at hp ⊢
    obtain ⟨i, q, hq⟩ := hp
    obtain ⟨j, r, hr⟩ := by
      simpa only [Set.mem_iUnion, Set.mem_range] using
        Set.eq_univ_iff_forall.mp (hg i).jointly_surjective q
    exact ⟨⟨i, j⟩, r, by
      rw [pointsMap_comp B S hS (Y i j) (g i j) (f i), Function.comp_apply, hr, hq]⟩

/-- **Stacks 041D**, the base-change clause. The first projections of the fibre products of a
smooth covering of an algebraic space over `S` with a morphism `g` into its target form a
smooth covering of the source of `g`. -/
@[stacks 041D "base_change"]
theorem isSmoothCovering_fiberProduct
    {I : Type v} {X X' : AlgebraicSpaces B S hS} (Xi : I → AlgebraicSpaces B S hS)
    (f : ∀ i, Xi i ⟶ X) (g : X' ⟶ X)
    (hf : IsSmoothCovering B S hS (fun i ↦ (Xi i).1) (fun i ↦ (f i).hom)) :
    IsSmoothCovering B S hS (fun i ↦ (AlgebraicSpaces.fiberProduct B S hS g (f i)).1)
      (fun i ↦ pullback.fst g.hom (f i).hom) := by
  refine ⟨X'.property, fun i ↦ (AlgebraicSpaces.fiberProduct B S hS g (f i)).property,
    fun i ↦ (isSmooth_isStableUnderBaseChange B S hS).of_isPullback
      (AlgebraicSpaces.isPullback_fiberProduct B S hS g (f i)).flip (hf.smooth i), ?_⟩
  refine Set.eq_univ_iff_forall.mpr fun x' ↦ ?_
  obtain ⟨i, xi, hxi⟩ := Set.mem_iUnion.mp (Set.eq_univ_iff_forall.mp hf.jointly_surjective
    (pointsMap B S hS X'.1 g.hom x'))
  obtain ⟨w, hw, -⟩ := exists_point_of_isPullback B S hS
    (AlgebraicSpaces.isPullback_fiberProduct B S hS g (f i)) x' xi hxi.symm
  exact Set.mem_iUnion.mpr ⟨i, ⟨w, hw⟩⟩

end AlgebraicGeometry.Space

end
