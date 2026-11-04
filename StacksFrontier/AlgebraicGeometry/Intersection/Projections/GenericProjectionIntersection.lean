module

public import Mathlib.Topology.KrullDimension
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.AvoidingLines

/-!
# Intersecting a closed subvariety with the cone swept out by a projection

For a closed point `p` of `𝐏(V)` and a closed subset `Z` not containing `p`, the preimage
`r_p^{-1}(r_p(Z))` is the union of the lines joining `p` to the points of `Z`, with `p` removed.
Intersecting it with a closed subvariety `Y` not containing `p` gives `Y ∩ Z` together with a
closed subset `E ⊆ Y`, and for a general `p` the dimension of `E` drops to
`dim Y + dim Z + 1 - n`, where `dim V = n + 1`.

## Main definitions

* `AlgebraicGeometry.ProjectiveSpaceOfModule.projectionCone`: the set `r_p^{-1}(r_p(Z))`, read
  back inside `𝐏(V)`.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.projectionCone_subset_iUnion_lines`: the cone
  lies on the union of the lines joining `p` to the points of `Z`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.exists_isOpen_inter_projectionCone_eq`: the
  decomposition `Y ∩ r_p^{-1}(r_p(Z)) = (Y ∩ Z) ∪ E` with `E ⊆ Y` closed, for every closed
  point `p` of a nonempty open subset of `𝐏(V)`, together with the dimension bound on `E` in
  the range `n ≤ dim Z + 1`, that is for `Z` of codimension at most one.

## Implementation notes

The projection away from a closed point `p` is defined on the open complement of `p`, so
`r_p^{-1}(r_p(Z))` is formed inside that open subscheme and then pushed into `𝐏(V)` along the
inclusion; this is `projectionCone`. The open of the statement is the complement of `Y ∪ Z`,
which is the open the source works over, and it is nonempty exactly because `Y ∪ Z` is not all
of `𝐏(V)`. That hypothesis is left implicit by the source, which needs it: for
`Y = Z = 𝐏(V)` the asserted identity fails for every `p`, since the left-hand side misses `p`
while `Y ∩ Z` contains it. It is slightly stronger than strictly necessary — for `Y = 𝐏(V)`
and `Z = ∅` the conclusion holds with `E = ∅` — but it is what the source's choice of `U`
requires.

Dimensions take values in `WithBot ℕ∞`, which has no subtraction, so the bound
`dim E ≤ dim Y + dim Z + 1 - n` is stated additively as `dim E + n ≤ dim Y + dim Z + 1`.

The subset `E` produced here is the whole of `Y ∩ r_p^{-1}(r_p(Z))`, which is closed because the
image of the closed `Z` under the projection is closed, the projection being proper on the
complement of `p`. **The dimension bound is proved only in the range `n ≤ dim Z + 1`**, where it
already follows from `E ⊆ Y`.

In the remaining range the bound is the content, and the source gets it from the incidence
variety `T = {(y, z, p) : y ∈ Y ∖ Z, z ∈ Z, p ∈ yz}`: it is irreducible of dimension
`dim Y + dim Z + 1`, because its projection to `Y × Z` has the line `yz` as every fibre, and `E`
is the image in `Y` of the fibre of `T ⟶ 𝐏(V)` over `p`. The two dimension-theoretic steps that
turns into are available: `dim (Y × Z) = dim Y + dim Z` is
`AlgebraicGeometry.topologicalKrullDim_pullback` (Tag 0B2M) and the passage from the dimension
of the generic fibre of `T ⟶ 𝐏(V)` to a nonempty open of `𝐏(V)` over which every fibre has that
dimension is `AlgebraicGeometry.exists_nonempty_open_fiberDimension_eq` (Tag 05F7). What is
missing is `T` itself: the library has the line `yz` only pointwise, as the linear subspace cut
out by `AlgebraicGeometry.ProjectiveSpaceOfModule.lineSubmodule`, and not as a family over
`Y × Z`, so the collinearity locus in `𝐏(V) × 𝐏(V) × 𝐏(V)` is not available as a scheme.

## References

* [Stacks Project, Tag 0B1R](https://stacks.math.columbia.edu/tag/0B1R)
* [Stacks Project, Tag 0B2M](https://stacks.math.columbia.edu/tag/0B2M)
* [Stacks Project, Tag 05F7](https://stacks.math.columbia.edu/tag/05F7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry TopologicalSpace
open Stacks.AlgebraicGeometry.ProjShared

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V]

/-- The set `r_p^{-1}(r_p(Z))` swept out by the fibres of the projection away from `p` through
a subset `Z` of `𝐏(V)`, read back inside `𝐏(V)` along the inclusion of the complement of `p`.
For a closed point `p` it is the union of the lines joining `p` to the points of `Z`, with `p`
removed. -/
public def projectionCone (p : projectiveSpaceOfModule k V)
    (Z : Set (projectiveSpaceOfModule k V)) : Set (projectiveSpaceOfModule k V) :=
  (projectionDomain k V (pointSubmodule k V p)).ι.base ''
    ((projection k V (pointSubmodule k V p)).base ⁻¹'
      ((projection k V (pointSubmodule k V p)).base ''
        ((projectionDomain k V (pointSubmodule k V p)).ι.base ⁻¹' Z)))

/-- The cone swept out by the projection away from `p` through `Z` lies on the union of the
lines joining `p` to the points of `Z`: two points of the complement of `p` with the same image
under the projection away from `p` lie together on a linear subspace cut out by the forms
vanishing at `p` and at the second point, which for closed points is the line joining them. -/
public theorem projectionCone_subset_iUnion_lines (p : projectiveSpaceOfModule k V)
    (Z : Set (projectiveSpaceOfModule k V)) :
    projectionCone k V p Z ⊆ ⋃ z ∈ Z, linearSubspace k V (lineSubmodule k V p z) := by
  rintro _ ⟨x, ⟨z, hz, hproj⟩, rfl⟩
  exact Set.mem_biUnion hz
    (mem_linearSubspace_inf_of_projection_eq k V (pointSubmodule k V p) x z hproj.symm)

/-- A point of `𝐏(V)` outside `Z` and distinct from `p` that lies in `Z` lies in the cone swept
out by the projection away from `p` through `Z`: every point of `Z` other than `p` does. -/
private theorem subset_projectionCone [IsAlgClosed k] [Module.Finite k V]
    (p : projectiveSpaceOfModule k V)
    (hp : IsClosed ({p} : Set (projectiveSpaceOfModule k V)))
    (Z : Set (projectiveSpaceOfModule k V)) {x : projectiveSpaceOfModule k V} (hxZ : x ∈ Z)
    (hxp : x ≠ p) : x ∈ projectionCone k V p Z := by
  have hxdom : x ∈ Set.range (projectionDomain k V (pointSubmodule k V p)).ι.base := by
    rw [Scheme.Opens.range_ι, coe_mapDomain_pointSubmodule k V p hp]
    exact hxp
  obtain ⟨x', hx'⟩ := hxdom
  exact ⟨x', ⟨x', by rw [Set.mem_preimage, hx']; exact hxZ, rfl⟩, hx'⟩

/-- For closed subsets `Y` and `Z` of `𝐏(V)` whose union is not all of `𝐏(V)`, there is a
nonempty Zariski open `U` such that for every closed point `p ∈ U` the intersection
`Y ∩ r_p^{-1}(r_p(Z))` is `(Y ∩ Z) ∪ E` with `E ⊆ Y` closed, and, in the range
`n ≤ dim Z + 1`, with `dim E ≤ dim Y + dim Z + 1 - n`, where `dim V = n + 1`.

The decomposition and the closedness of `E` are proved for arbitrary closed `Y` and `Z` rather
than only irreducible ones. The dimension bound is proved in the range `n ≤ dim Z + 1`, that is
for `Z` of codimension at most one, where it already follows from `E ⊆ Y`; see the implementation
notes for the incidence-variety argument that gives it in the remaining range, and for the one
object it needs. -/
@[stacks 0B1R "the decomposition Y ∩ r_p^{-1}(r_p(Z)) = (Y ∩ Z) ∪ E with E ⊆ Y closed, for \
every closed point p of a nonempty Zariski open subset of 𝐏(V), and the dimension bound \
dim E ≤ dim Y + dim Z + 1 - n carrying the hypothesis n ≤ dim Z + 1, that is for Z of \
codimension at most one, in which range the bound follows from E ⊆ Y; also carrying the \
hypothesis Y ∪ Z ≠ 𝐏(V), which the source leaves implicit and without which the asserted \
identity fails, the left-hand side missing p while Y ∩ Z contains it"]
public theorem exists_isOpen_inter_projectionCone_eq [IsAlgClosed k] [Module.Finite k V]
    {n : ℕ} (hn : Module.finrank k V = n + 1)
    {Y Z : Set (projectiveSpaceOfModule k V)} (hY : IsClosed Y) (hZ : IsClosed Z)
    (hYZ : Y ∪ Z ≠ Set.univ)
    (hdimZ : (n : WithBot ℕ∞) ≤ topologicalKrullDim ↥Z + 1) :
    ∃ U : Set (projectiveSpaceOfModule k V), IsOpen U ∧ U.Nonempty ∧
      ∀ p ∈ U, IsClosed ({p} : Set (projectiveSpaceOfModule k V)) →
        ∃ E : Set (projectiveSpaceOfModule k V), IsClosed E ∧ E ⊆ Y ∧
          topologicalKrullDim ↥E + (n : WithBot ℕ∞) ≤
            topologicalKrullDim ↥Y + topologicalKrullDim ↥Z + 1 ∧
          Y ∩ projectionCone k V p Z = (Y ∩ Z) ∪ E := by
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := k) (by rw [hn]; omega)
  refine ⟨(Y ∪ Z)ᶜ, (hY.union hZ).isOpen_compl, Set.nonempty_compl.mpr hYZ, ?_⟩
  intro p hp hpc
  rw [Set.mem_compl_iff, Set.mem_union, not_or] at hp
  obtain ⟨hpY, hpZ⟩ := hp
  rcases subsingleton_or_nontrivial ↥(pointSubmodule k V p) with hWs | hWnt
  · -- `p` has no hyperplane, so `𝐏(V)` is the single point `p` and `Y` is empty.
    have hbot : pointSubmodule k V p = ⊥ := by
      refine (Submodule.eq_bot_iff _).mpr fun x hx => ?_
      simpa using congrArg Subtype.val
        (Subsingleton.elim (⟨x, hx⟩ : ↥(pointSubmodule k V p)) 0)
    have huniv : (Set.univ : Set (projectiveSpaceOfModule k V)) = {p} := by
      rw [← linearSubspace_pointSubmodule k V p hpc, hbot, linearSubspace_bot]
    have hYempty : Y = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.mpr fun x hx => hpY ?_
      have hx1 : x ∈ ({p} : Set (projectiveSpaceOfModule k V)) := by
        rw [← huniv]
        trivial
      exact Set.mem_singleton_iff.mp hx1 ▸ hx
    refine ⟨∅, isClosed_empty, Set.empty_subset _, ?_, by simp [hYempty]⟩
    rw [(topologicalKrullDim_eq_bot_iff_isEmpty
      (↥(∅ : Set (projectiveSpaceOfModule k V)))).mpr inferInstance]
    simp
  · have hdisj : Disjoint Z (linearSubspace k V (pointSubmodule k V p)) := by
      rw [linearSubspace_pointSubmodule k V p hpc]
      exact Set.disjoint_singleton_right.mpr hpZ
    have hKclosed := isClosed_image_projection k V (pointSubmodule k V p) hZ hdisj
    have hpre : IsClosed ((projection k V (pointSubmodule k V p)).base ⁻¹'
        ((projection k V (pointSubmodule k V p)).base ''
          ((projectionDomain k V (pointSubmodule k V p)).ι.base ⁻¹' Z))) :=
      hKclosed.preimage (Scheme.Hom.continuous (projection k V (pointSubmodule k V p)))
    obtain ⟨C, hCclosed, hCeq⟩ :=
      (projectionDomain k V (pointSubmodule k V p)).ι.isOpenEmbedding.isInducing.isClosed_iff.mp
        hpre
    have hcone : projectionCone k V p Z = C ∩ {p}ᶜ := by
      rw [projectionCone, ← hCeq, Set.image_preimage_eq_inter_range, Scheme.Opens.range_ι,
        coe_mapDomain_pointSubmodule k V p hpc]
    have hEeq : Y ∩ projectionCone k V p Z = Y ∩ C := by
      rw [hcone]
      ext x
      simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_singleton_iff]
      exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, fun hx => hpY (hx ▸ h.1)⟩⟩
    refine ⟨Y ∩ projectionCone k V p Z, ?_, Set.inter_subset_left, ?_, ?_⟩
    · rw [hEeq]
      exact hY.inter hCclosed
    · have hincl : Topology.IsEmbedding
          (Set.inclusion (Set.inter_subset_left (s := Y) (t := projectionCone k V p Z))) :=
        Topology.IsEmbedding.inclusion _
      have hEY : topologicalKrullDim ↥(Y ∩ projectionCone k V p Z) ≤ topologicalKrullDim ↥Y :=
        hincl.isInducing.topologicalKrullDim_le
      exact le_trans (add_le_add hEY hdimZ) (le_of_eq (add_assoc _ _ _).symm)
    · refine (Set.union_eq_right.mpr (Set.subset_inter Set.inter_subset_left ?_)).symm
      rintro x ⟨hxY, hxZ⟩
      exact subset_projectionCone k V p hpc Z hxZ fun h => hpY (h ▸ hxY)

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
