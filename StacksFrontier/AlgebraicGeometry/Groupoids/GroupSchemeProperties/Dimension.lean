module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Groupoids.OverField.Morphisms.Dimension
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.ActionGroupoid
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Equidimensional

/-!
# Dimension of a group scheme over a field

A group scheme locally of finite type over a field is equidimensional, its dimension is its
dimension at every point, and at a closed point that dimension is the Krull dimension of the
local ring.  All three statements are read off from the corresponding statements for the arrow
scheme of a groupoid scheme whose object scheme is the spectrum of the field: a group scheme is
the arrow scheme of the groupoid attached to its trivial action on the final object.

## Main results

* `AlgebraicGeometry.equidimensional_of_groupScheme`: a group scheme locally of finite type over
  a field is equidimensional.
* `AlgebraicGeometry.topologicalKrullDim_eq_topologicalKrullDimAt_of_groupScheme`: its dimension
  is its dimension at every point.
* `AlgebraicGeometry.topologicalKrullDim_eq_ringKrullDim_stalk_of_groupScheme`: at a closed
  point its dimension is the Krull dimension of the local ring.

## Implementation notes

A group scheme over `k` is a scheme over `Spec k` carrying a group-object structure in the
over-category, and "locally algebraic" is the locally-finite-type condition on its structure
morphism.  The one-object groupoid scheme is the action groupoid of the trivial action of the
group scheme on the final object of the over-category; its arrow scheme is canonically
isomorphic to the group scheme by the right unitor.

Equidimensionality transports along a homeomorphism by
`TopologicalSpace.Equidimensional.of_homeomorph`, from
`StacksFrontier.Topology.Dimension.Equidimensional`.

## References

* [Stacks Project, Tag 045X](https://stacks.math.columbia.edu/tag/045X)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace MonoidalCategory
  CartesianMonoidalCategory
open Stacks.Groupoids
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry

/-- A group scheme over a field is the arrow scheme of a groupoid scheme whose object scheme is
the spectrum of that field, namely the action groupoid of its trivial action on the final
object.  Both structure morphisms of that groupoid scheme inherit the finite type condition. -/
theorem exists_groupoidScheme_arrows_iso (k : Type u) [Field k] (G : Scheme.{u})
    [G.Over (Spec (.of k))] [GrpObj (G.asOver (Spec (.of k)))]
    [LocallyOfFiniteType (G ↘ Spec (.of k))] :
    ∃ H : GroupoidScheme (Spec (.of k)), Nonempty (H.objects.left ≅ Spec (.of k)) ∧
      Nonempty (H.arrows.left ≅ G) ∧
      LocallyOfFiniteType H.source.left ∧ LocallyOfFiniteType H.target.left := by
  let S := Spec (.of k)
  let Y : Over S := Over.mk (𝟙 S)
  let A : Over Y.left := G.asOver S
  let B : Over Y.left := 𝟙_ (Over Y.left)
  have : LocallyOfFiniteType A.hom := by
    change LocallyOfFiniteType (G ↘ Spec (.of k))
    infer_instance
  let _ : ModObj A B := ModObj.trivialAction A B
  have h : LocallyOfFiniteType (Limits.pullback.snd A.hom B.hom) := inferInstance
  exact ⟨(groupoidSchemeOfAction Y A B).groupoid, ⟨Iso.refl _⟩,
    ⟨(Over.forget _).mapIso (MonoidalCategory.rightUnitor A)⟩, h, h⟩

/-- **Stacks Project, Tag 045X.** A group scheme locally of finite type over a field is
equidimensional. -/
@[stacks 045X "equidimensionality", sga "3 VIA 2.4.1" "special case", sga "3 VIB 1.5"]
theorem equidimensional_of_groupScheme (k : Type u) [Field k] (G : Scheme.{u})
    [G.Over (Spec (.of k))] [GrpObj (G.asOver (Spec (.of k)))]
    [LocallyOfFiniteType (G ↘ Spec (.of k))] :
    Equidimensional G := by
  obtain ⟨H, ⟨e₀⟩, ⟨e⟩, h, h⟩ := exists_groupoidScheme_arrows_iso k G
  exact Equidimensional.of_homeomorph e.symm.hom.homeomorph
    (GroupoidScheme.equidimensional_arrows H e₀)

/-- **Stacks Project, Tag 045X.** The dimension of a group scheme locally of finite type over a
field is its dimension at every point. -/
@[stacks 045X "dimension at every point",
  ega "IV 15.6.10" "dim(G_y^0) = dim(G_y)",
  sga "3 VIB 1.2" "partial",
  sga "3 VIB 1.5"]
theorem topologicalKrullDim_eq_topologicalKrullDimAt_of_groupScheme (k : Type u) [Field k]
    (G : Scheme.{u}) [G.Over (Spec (.of k))] [GrpObj (G.asOver (Spec (.of k)))]
    [LocallyOfFiniteType (G ↘ Spec (.of k))] (g : G) :
    topologicalKrullDim G = topologicalKrullDimAt G g := by
  obtain ⟨H, ⟨e₀⟩, ⟨e⟩, h, h⟩ := exists_groupoidScheme_arrows_iso k G
  have h := GroupoidScheme.topologicalKrullDim_arrows_eq_topologicalKrullDimAt H e₀ (e.inv g)
  rw [IsHomeomorph.topologicalKrullDim_eq _ e.hom.homeomorph.isHomeomorph,
    topologicalKrullDimAt_eq_of_homeomorph e.hom.homeomorph] at h
  simpa using h

/-- **Stacks Project, Tag 045X.** At a closed point of a group scheme locally of finite type
over a field, the dimension of the scheme is the Krull dimension of the local ring. -/
@[stacks 045X "dimension at a closed point"]
theorem topologicalKrullDim_eq_ringKrullDim_stalk_of_groupScheme (k : Type u) [Field k]
    (G : Scheme.{u}) [G.Over (Spec (.of k))] [GrpObj (G.asOver (Spec (.of k)))]
    [LocallyOfFiniteType (G ↘ Spec (.of k))] (g : G) (hg : IsClosed ({g} : Set G)) :
    topologicalKrullDim G = ringKrullDim (G.presheaf.stalk g) := by
  rw [topologicalKrullDim_eq_topologicalKrullDimAt_of_groupScheme k G g,
    topologicalKrullDimAt_eq_krullDimOfRing_stalk k G (G ↘ Spec (.of k)) g hg]

end AlgebraicGeometry

end
