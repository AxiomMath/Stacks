module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.PointTopology
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.Points

/-!
# Stacks 086V: the points of an inverse limit of algebraic spaces

Let `X = limit D` be the limit of a cofiltered inverse system `D` of decent algebraic spaces over
a scheme `S` with affine transition morphisms, as in Stacks 07SF.  Stacks 086V says that `|X|` is
the inverse limit of the spaces `|D i|`, as topological spaces.

## Main results

* `AlgebraicGeometry.Space.isHomeomorph_pointsLimitComparison`: **Stacks 086V**, the canonical
  map from the points of the limit to the inverse limit of the point spaces of the stages is a
  homeomorphism.

## Implementation notes

The map is bijective by Stacks 0CUJ, `AlgebraicGeometry.Space.existsUnique_point_limit`, which is
where decency is used, and inducing because the point topology of the limit is the inverse-limit
topology, `AlgebraicGeometry.Space.pointTopology_limit`, which needs no decency.

## References

* [Stacks Project, Tag 086V](https://stacks.math.columbia.edu/tag/086V)
* [Stacks Project, Tag 0CUJ](https://stacks.math.columbia.edu/tag/0CUJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-! ### The points of the limit as a topological space -/

/-- The canonical map from the points of `limit D` to the inverse limit of the point spaces of
the stages: a point of `limit D` goes to the compatible family of its images under the limit
projections. The target is the inverse limit of the spaces `|D i|`: the compatible families,
with the topology they inherit as a subspace of the product of the point topologies. -/
noncomputable def pointsLimitComparison (y : points B S hS (limit D)) :
    {x : ∀ i, points B S hS (D.obj i) //
      ∀ {i j : I} (f : i ⟶ j), pointsMap B S hS (D.obj i) (D.map f) (x i) = x j} :=
  ⟨fun i ↦ pointsMap B S hS (limit D) (limit.π D i) y, fun {i _} f ↦ by
    rw [← Function.comp_apply (f := pointsMap B S hS (D.obj i) (D.map f)), ← pointsMap_comp,
      limit.w]⟩

omit [IsCofiltered I] in
/-- The `i`-th component of `pointsLimitComparison B S hS D y` is the image of `y` under the
limit projection `limit.π D i`. -/
@[simp]
theorem pointsLimitComparison_coe_apply (y : points B S hS (limit D)) (i : I) :
    (pointsLimitComparison B S hS D y).1 i =
      pointsMap B S hS (limit D) (limit.π D i) y :=
  rfl

/-- **Stacks 086V.** Let `D` be a directed inverse system of decent algebraic spaces over `S`
with affine transition morphisms, indexed by a category small enough for the site, so that
`limit D` is an algebraic space by Stacks 07SF. Then `|limit D| = lim |D i|` as topological
spaces: the canonical map `AlgebraicGeometry.Space.pointsLimitComparison` from the points of
the limit to the inverse limit of the point spaces of the stages is a homeomorphism.

It is bijective by Stacks 0CUJ, `AlgebraicGeometry.Space.existsUnique_point_limit`, which is
where decency is used, and it is inducing because the point topology of the limit is the
inverse-limit topology, `AlgebraicGeometry.Space.pointTopology_limit`. -/
@[stacks 086V]
theorem isHomeomorph_pointsLimitComparison (hSize : #I < B.cutoff.ord.cof)
    (hHomSize : ∀ i j : I, #(i ⟶ j) < B.cutoff.ord.cof)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    (hDecent : ∀ i, IsDecentSpace B S hS (D.obj i)) :
    IsHomeomorph (pointsLimitComparison B S hS D) := by
  have hex := existsUnique_point_limit B S hS D hSize hHomSize hD hAffine hDecent
  have hinj : Function.Injective (pointsLimitComparison B S hS D) := by
    intro y z hyz
    obtain ⟨_, -, hw⟩ := hex _ (pointsLimitComparison B S hS D y).2
    rw [hw y fun _ ↦ rfl, hw z fun i ↦ congrFun (congrArg Subtype.val hyz.symm) i]
  have hsurj : Function.Surjective (pointsLimitComparison B S hS D) := by
    intro x
    obtain ⟨y, hy, -⟩ := hex x.1 x.2
    exact ⟨y, Subtype.ext (funext hy)⟩
  have hind : pointTopology B S hS (limit D) =
      TopologicalSpace.induced (pointsLimitComparison B S hS D) inferInstance := by
    rw [pointTopology_limit B S hS D hSize hHomSize hD hAffine]
    change _ = TopologicalSpace.induced (pointsLimitComparison B S hS D)
      (TopologicalSpace.induced Subtype.val Pi.topologicalSpace)
    rw [induced_compose, induced_to_pi]
    rfl
  exact isHomeomorph_iff_isEmbedding_surjective.2 ⟨⟨⟨hind⟩, hinj⟩, hsurj⟩

end AlgebraicGeometry.Space

end
