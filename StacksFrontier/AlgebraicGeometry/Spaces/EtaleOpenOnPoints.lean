module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.PointTopologyEtaleOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopologyUnique
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# An étale morphism of algebraic spaces is open on points

Tag 03IR states that if `X ⟶ Y` is an étale morphism of algebraic spaces over a scheme `S`,
then the associated map `|X| → |Y|` of topological spaces is open.

Étaleness of a morphism of algebraic spaces is Tag 03FR, `AlgebraicGeometry.Space.IsEtale`:
the composite of `f` with every étale morphism from a representable presheaf into its source
is again étale. The point sets and their topology are those of Tags 03BU and 03BX,
`AlgebraicGeometry.Space.points` and `AlgebraicGeometry.Space.pointTopology`.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.isOpenMap_pointsMap_of_isEtale` is Tag 03IR.
* `AlgebraicGeometry.Space.isOpen_range_pointsMap_of_isEtale` is the consequence in which the
  tag is normally used: the image of `|X|` in `|Y|` is an open subset of `|Y|`.

## Implementation notes

The source proof reads the statement off the diagram of Tag 03FS together with clause (3) of
Tag 03BX. The route taken here avoids Tag 03FS, which is only partly available, and uses an
atlas of the *source* alone:

Let `p : h_U ⟶ X` be a surjective étale chart of `X`, which exists because `X` is an
algebraic space (`AlgebraicGeometry.IsAlgebraicSpace.exists_atlas`). The composite `p ≫ f`
is then étale by the very definition of `IsEtale`, so `|U| → |Y|` is open by clause (3) of
Tag 03BX, `AlgebraicGeometry.Space.isOpenMap_pointsMap_of_presheafEtale`. The chart is
surjective on points by Tag 03H5,
`AlgebraicGeometry.Space.presheafSurjective_iff_isSurjective_yoneda`, and continuous on
points for free. Hence for an open `W ⊆ |X|` the set `|p| ⁻¹' W` is open and its image under
`|p ≫ f| = |f| ∘ |p|` is both open and equal to `|f| '' W`, surjectivity of `|p|` supplying
the equality.

Only the source is required to be an algebraic space; the hypothesis on the target is
retained from the source statement as `_hG` but is never used.

`StacksFrontier.AlgebraicGeometry.Spaces.PointsTopologyUnique`, which carries the uniqueness
statement of Tag 03BX and its openness clauses for a morphism out of a scheme, is re-exported:
Tag 03IR is the first consumer of that clause, and the files that use Tag 03IR read the
topology off `AlgebraicGeometry.Space.pointTopologyFamily` there.

## References

* [Stacks Project, Tag 03IR](https://stacks.math.columbia.edu/tag/03IR)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 03IR.** An étale morphism `f : X ⟶ Y` of algebraic spaces over `S` induces an
open map `|X| → |Y|` on the point sets of Tag 03BU, for the topology of Tag 03BX.

The hypothesis `_hG` that the target is an algebraic space is retained from the source
statement but is not used: only an étale chart of the source enters the argument. -/
@[stacks 03IR]
theorem isOpenMap_pointsMap_of_isEtale (f : F ⟶ G) (hF : IsAlgebraicSpace B S hS F)
    (_hG : IsAlgebraicSpace B S hS G) (hf : IsEtale B S hS f) :
    @IsOpenMap _ _ (pointTopology B S hS F) (pointTopology B S hS G)
      (pointsMap B S hS F f) := by
  obtain ⟨U, p, hpSurj, hpEt⟩ := hF.exists_atlas
  let _ : TopologicalSpace (points B S hS (yoneda.obj U)) := pointTopology B S hS _
  let _ : TopologicalSpace (points B S hS F) := pointTopology B S hS F
  let _ : TopologicalSpace (points B S hS G) := pointTopology B S hS G
  -- The chart is surjective on points, by Tag 03H5.
  have hsurj : Function.Surjective (pointsMap B S hS _ p) :=
    (presheafSurjective_iff_isSurjective_yoneda B S hS F hF U p).mp hpSurj
  -- The composite `h_U ⟶ Y` is étale, hence open on points by clause (3) of Tag 03BX.
  have hopen : @IsOpenMap _ _ (pointTopology B S hS _) (pointTopology B S hS G)
      (pointsMap B S hS _ (p ≫ f)) :=
    isOpenMap_pointsMap_of_presheafEtale B S hS (p ≫ f) (hf U p hpEt)
  -- The chart is continuous on points.
  have hcont : @Continuous _ _ (pointTopology B S hS _) (pointTopology B S hS F)
      (pointsMap B S hS _ p) := continuous_pointsMap B S hS p
  intro W hW
  have hpre : @IsOpen _ (pointTopology B S hS _) (pointsMap B S hS _ p ⁻¹' W) :=
    hcont.isOpen_preimage W hW
  have himg : pointsMap B S hS _ (p ≫ f) '' (pointsMap B S hS _ p ⁻¹' W) =
      pointsMap B S hS F f '' W := by
    rw [pointsMap_comp, Set.image_comp, Set.image_preimage_eq _ hsurj]
  exact himg ▸ hopen _ hpre

/-- The point set of the source of an étale morphism of algebraic spaces over `S` has open
image in the point set of the target. This is the form in which Tag 03IR is used to produce
the open subspace of `Y` through which an étale `X ⟶ Y` factors. -/
theorem isOpen_range_pointsMap_of_isEtale (f : F ⟶ G) (hF : IsAlgebraicSpace B S hS F)
    (hG : IsAlgebraicSpace B S hS G) (hf : IsEtale B S hS f) :
    @IsOpen _ (pointTopology B S hS G) (Set.range (pointsMap B S hS F f)) := by
  let _ : TopologicalSpace (points B S hS F) := pointTopology B S hS F
  let _ : TopologicalSpace (points B S hS G) := pointTopology B S hS G
  exact (isOpenMap_pointsMap_of_isEtale B S hS f hF hG hf).isOpen_range

end AlgebraicGeometry.Space

end
