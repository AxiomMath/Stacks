module

public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.GenericProjectionIntersection

/-!
# The projection away from a point is constant on the lines through it

Let `p` be a point of `𝐏(V)` and let `z` be a closed point distinct from `p`. Every point of the
line joining `p` to `z` other than `p` has the same image as `z` under the projection away from
`p`. This is the converse of
`AlgebraicGeometry.ProjectiveSpaceOfModule.mem_linearSubspace_inf_of_projection_eq`, and with it
the set swept out by the fibres of the projection through a set `Z` of closed points is exactly
the union of the lines joining `p` to the points of `Z`, with `p` removed.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.projection_eq_of_mem_linearSubspace_lineSubmodule`:
  a point of the domain of definition lying on the line joining `p` to a closed point `z` has
  the same image as `z`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.iUnion_lines_diff_subset_projectionCone`: the union
  of the lines joining `p` to the closed points of `Z`, with `p` removed, lies in the cone swept
  out by the projection away from `p` through `Z`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.projectionCone_eq_iUnion_lines_diff`: the two are
  equal when every point of `Z` is closed, which is the identification of the closed subset `E`
  of [Stacks, Tag 0B1R] with a union of lines.

## Implementation notes

The closedness of `z` is what makes the statement true: it is used to write `z` as the point cut
out by a nonzero linear functional `f`, whose restriction to the hyperplane of `p` is nonzero
exactly because `z` lies in the domain of definition of the projection. The projection of `z` is
then the point of `𝐏(W_p)` cut out by that restriction, by
`AlgebraicGeometry.ProjectiveSpaceOfModule.projection_eq_linearFunctionalPoint`, and so is the
projection of any point of the line, by
`AlgebraicGeometry.ProjectiveSpaceOfModule.projection_eq_linearFunctionalPoint_of_mem`, since
every vector of `W_p` killed by that restriction is killed by `f` and so lies in the equations
`lineSubmodule k V p z` of the line.

No closedness of `p` is needed, nor closedness of the point of the line: the argument runs
through the equations of the line rather than through a coordinate description of its points.

## References

* [Stacks Project, Tag 0B1R](https://stacks.math.columbia.edu/tag/0B1R)
-/

@[expose] public noncomputable section

open AlgebraicGeometry TopologicalSpace
open Stacks.AlgebraicGeometry.ProjShared

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V]

/-- **The projection away from `p` is constant on the line joining `p` to a closed point.** A
point `y` of the domain of definition of the projection away from `p` that lies on the linear
subspace cut out by the degree-one forms vanishing at both `p` and a closed point `z` of that
domain has the same image as `z`. This is the converse of
`AlgebraicGeometry.ProjectiveSpaceOfModule.mem_linearSubspace_inf_of_projection_eq`. -/
public theorem projection_eq_of_mem_linearSubspace_lineSubmodule [IsAlgClosed k]
    [Module.Finite k V] (p : projectiveSpaceOfModule k V)
    (y z : (projectionDomain k V (pointSubmodule k V p)).toScheme)
    (hz : IsClosed ({(z.val : projectiveSpaceOfModule k V)} :
      Set (projectiveSpaceOfModule k V)))
    (hy : (y.val : projectiveSpaceOfModule k V) ∈
      linearSubspace k V (lineSubmodule k V p z.val)) :
    projection k V (pointSubmodule k V p) y = projection k V (pointSubmodule k V p) z := by
  obtain ⟨f, hf, hfz⟩ := exists_eq_linearFunctionalPoint k V z.val hz
  have hzdom : (z.val : projectiveSpaceOfModule k V) ∈
      ((projectionDomain k V (pointSubmodule k V p) :
        (projectiveSpaceOfModule k V).Opens) : Set (projectiveSpaceOfModule k V)) := z.2
  rw [coe_mapDomain_subtype] at hzdom
  have hfW : f ∘ₗ (pointSubmodule k V p).subtype ≠ 0 := by
    intro h0
    refine hzdom ((mem_linearSubspace_iff k V (pointSubmodule k V p) _).mpr fun w hw => ?_)
    rw [hfz, pointSubmodule_linearFunctionalPoint]
    exact LinearMap.mem_ker.mpr (congrArg
      (fun g : Module.Dual k ↥(pointSubmodule k V p) => g ⟨w, hw⟩) h0)
  rw [projection_eq_linearFunctionalPoint k V (pointSubmodule k V p) z f hf hfW hfz]
  refine projection_eq_linearFunctionalPoint_of_mem k V (pointSubmodule k V p) y _ hfW
    (lineSubmodule k V p z.val) (fun w hw => Submodule.mem_inf.mpr ⟨w.2, ?_⟩) hy
  rw [hfz, pointSubmodule_linearFunctionalPoint]
  exact LinearMap.mem_ker.mpr hw

/-- The domain of definition of the projection away from a closed point `p` is the complement
of `p`. -/
private theorem range_projectionDomain_ι_eq [IsAlgClosed k] [Module.Finite k V]
    (p : projectiveSpaceOfModule k V) (hp : IsClosed ({p} : Set (projectiveSpaceOfModule k V))) :
    Set.range (projectionDomain k V (pointSubmodule k V p)).ι.base = {p}ᶜ := by
  rw [Scheme.Opens.range_ι, coe_mapDomain_pointSubmodule k V p hp]

/-- **The lines joining `p` to the closed points of `Z` lie in the cone swept out by the
projection away from `p` through `Z`.** This is the converse inclusion to
`AlgebraicGeometry.ProjectiveSpaceOfModule.projectionCone_subset_iUnion_lines`, for a closed
point `p` outside `Z` and closed points of `Z`. -/
public theorem iUnion_lines_diff_subset_projectionCone [IsAlgClosed k] [Module.Finite k V]
    (p : projectiveSpaceOfModule k V)
    (hp : IsClosed ({p} : Set (projectiveSpaceOfModule k V)))
    (Z : Set (projectiveSpaceOfModule k V)) (hpZ : p ∉ Z)
    (hZ : ∀ z ∈ Z, IsClosed ({z} : Set (projectiveSpaceOfModule k V))) :
    (⋃ z ∈ Z, linearSubspace k V (lineSubmodule k V p z)) \ {p} ⊆
      projectionCone k V p Z := by
  have hdom := range_projectionDomain_ι_eq k V p hp
  rintro x ⟨hxU, hxp⟩
  obtain ⟨z, hzZ, hxz⟩ := Set.mem_iUnion₂.mp hxU
  obtain ⟨y, hy⟩ : x ∈ Set.range (projectionDomain k V (pointSubmodule k V p)).ι.base := by
    rw [hdom]
    exact hxp
  obtain ⟨w, hw⟩ : z ∈ Set.range (projectionDomain k V (pointSubmodule k V p)).ι.base := by
    rw [hdom]
    exact fun h => hpZ (Set.mem_singleton_iff.mp h ▸ hzZ)
  refine ⟨y, ⟨w, by rw [Set.mem_preimage, hw]; exact hzZ, ?_⟩, hy⟩
  exact (projection_eq_of_mem_linearSubspace_lineSubmodule k V p y w
    (by rw [show (w.val : projectiveSpaceOfModule k V) = z from hw]; exact hZ z hzZ)
    (by rw [show (y.val : projectiveSpaceOfModule k V) = x from hy,
      show (w.val : projectiveSpaceOfModule k V) = z from hw]; exact hxz)).symm

/-- **The cone swept out by a projection through a set of closed points is a union of lines.**
For a closed point `p` outside a set `Z` all of whose points are closed, the set
`r_p^{-1}(r_p(Z))` is exactly the union of the lines joining `p` to the points of `Z`, with `p`
removed. -/
public theorem projectionCone_eq_iUnion_lines_diff [IsAlgClosed k] [Module.Finite k V]
    (p : projectiveSpaceOfModule k V)
    (hp : IsClosed ({p} : Set (projectiveSpaceOfModule k V)))
    (Z : Set (projectiveSpaceOfModule k V)) (hpZ : p ∉ Z)
    (hZ : ∀ z ∈ Z, IsClosed ({z} : Set (projectiveSpaceOfModule k V))) :
    projectionCone k V p Z =
      (⋃ z ∈ Z, linearSubspace k V (lineSubmodule k V p z)) \ {p} := by
  refine le_antisymm (fun x hx => ⟨projectionCone_subset_iUnion_lines k V p Z hx, ?_⟩)
    (iUnion_lines_diff_subset_projectionCone k V p hp Z hpZ hZ)
  obtain ⟨y, -, rfl⟩ := hx
  exact (range_projectionDomain_ι_eq k V p hp).le (Set.mem_range_self y)

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
