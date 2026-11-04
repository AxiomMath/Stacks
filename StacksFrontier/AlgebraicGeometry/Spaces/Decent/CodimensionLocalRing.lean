module

public import Mathlib.AlgebraicGeometry.Properties
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PointsOfFibresCardinality
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.QuasiCompactMonomorphicPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.Sober
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.Specializations
public import StacksFrontier.AlgebraicGeometry.Spaces.LocalRingDimension
public import StacksFrontier.Topology.Dimension.Codimension

/-!
# Codimension of an irreducible closed subset and the local ring at its generic point

Let `X` be a decent algebraic space over a scheme `S` and let `T ⊆ |X|` be an irreducible
closed subset. Its generic point `ξ` exists because `|X|` is sober, and the codimension of `T`
in `|X|` is the dimension of the local ring of `X` at `ξ`.

## Main results

* `AlgebraicGeometry.Space.coheight_pointsMap_eq`: an étale chart of a decent algebraic space
  preserves the coheight of a point in the specialization order.
* `AlgebraicGeometry.Space.codimension_eq_localRingDimension`: the codimension of an
  irreducible closed subset of `|X|` is the dimension of the local ring of `X` at its generic
  point.

## References

* [Stacks Project, Tag 02I3](https://stacks.math.columbia.edu/tag/02I3)
* [Stacks Project, Tag 02IZ](https://stacks.math.columbia.edu/tag/02IZ)
* [Stacks Project, Tag 03K2](https://stacks.math.columbia.edu/tag/03K2)
* [Stacks Project, Tag 03K5](https://stacks.math.columbia.edu/tag/03K5)
* [Stacks Project, Tag 03K6](https://stacks.math.columbia.edu/tag/03K6)
* [Stacks Project, Tag 04NA](https://stacks.math.columbia.edu/tag/04NA)
* [Stacks Project, Tag 0BAM](https://stacks.math.columbia.edu/tag/0BAM)
* [Stacks Project, Tag 0ED1](https://stacks.math.columbia.edu/tag/0ED1)
-/

@[expose] public section

open CategoryTheory Order TopologicalSpace

universe u

attribute [local instance] specializationOrder

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### Coheight along an étale chart -/

/-- The map on points of an étale chart of an algebraic space over `S` whose points all have
finite chart fibres preserves the coheight of a point in the specialization order. -/
theorem coheight_pointsMap_eq (hX : IsAlgebraicSpace B S hS X)
    (hfib : HasFiniteChartFibersAtEveryPoint B S hS X) (U : BigFppfOver B S hS)
    (φ : yoneda.obj U ⟶ X)
    (hφ : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) φ)
    [T0Space (points B S hS X)] [T0Space (points B S hS (yoneda.obj U))]
    (u : points B S hS (yoneda.obj U)) :
    coheight u = coheight (pointsMap B S hS (yoneda.obj U) φ u) := by
  refine coheight_eq_of_strictMono (pointsMap B S hS (yoneda.obj U) φ) ?_ ?_ u
  · intro a a' haa'
    have hspec : a' ⤳ a := le_of_lt haa'
    refine lt_of_le_of_ne (hspec.map (continuous_pointsMap B S hS φ)) fun heq ↦ ?_
    exact (ne_of_lt haa')
      (eq_of_specializes_of_pointsMap_eq_of_hasFiniteChartFibers B S hS hX hfib U φ hφ a a' heq
        hspec)
  · intro a b hab
    obtain ⟨a', ha'a, ha'⟩ := exists_specializes_pointsMap_eq_of_isEtale B S hS hX
      (le_of_lt hab) (fun V hV ψ hψ ↦ hfib b V hV ψ hψ) U φ hφ a rfl
    exact ⟨a', lt_of_le_of_ne ha'a fun heq ↦ ne_of_lt hab (by rwa [heq]), ha'⟩

/-! ### Codimension and the local ring at the generic point -/

/-- For an irreducible closed subset `T` of the point space of a decent algebraic space over `S`,
with generic point `ξ`, the codimension of `T` is the dimension of the local ring of the space
at `ξ`. -/
@[stacks 0ED1]
theorem codimension_eq_localRingDimension (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) (T : IrreducibleCloseds (points B S hS X))
    (ξ : points B S hS X) (hξ : IsGenericPoint ξ (T : Set (points B S hS X))) :
    codimension T = localRingDimension B S hS ξ := by
  have := t0Space_points_of_isDecentSpace B S hS hX hdec
  have := quasiSober_points_of_isDecentSpace B S hS hX hdec
  obtain ⟨U, φ, u, hUaff, hφ, huξ⟩ := exists_affine_etale_chart_of_point B S hS X hX ξ
  have := (schemePointsHomeomorph B S hS U).isEmbedding.t0Space
  have := (schemePointsHomeomorph B S hS U).isOpenEmbedding.quasiSober
  have hTeq : (irreducibleSetEquivPoints.symm ξ : IrreducibleCloseds (points B S hS X)) = T :=
    IrreducibleCloseds.ext hξ
  have h1 : codimension T = coheight ξ := by
    rw [codimension_eq_coheight, ← hTeq, coheight_orderIso]
  have h2 : coheight ξ = coheight u := by
    rw [← huξ]
    exact (coheight_pointsMap_eq B S hS hX
      (hasFiniteChartFibersAtEveryPoint_of_isDecentSpace B S hS hdec) U φ hφ u).symm
  have h3 : coheight (pointsToScheme B S hS U u) = coheight u := by
    rw [← schemePointsHomeomorph_apply]
    exact Topology.IsOpenEmbedding.coheight_eq _
      (schemePointsHomeomorph B S hS U).isOpenEmbedding
  have h4 : (localRingDimension B S hS ξ : WithBot ℕ∞) =
      (coheight (pointsToScheme B S hS U u) : WithBot ℕ∞) := by
    rw [localRingDimension_eq_of_chartPoint B S hS hX U φ hφ _ ξ
      (by rw [← huξ]; exact chartPoint_pointsToScheme B S hS U φ u)]
    exact ringKrullDim_stalk_eq_coheight _
  rw [h1, h2, ← h3]
  exact_mod_cast h4.symm

end AlgebraicGeometry.Space

end
