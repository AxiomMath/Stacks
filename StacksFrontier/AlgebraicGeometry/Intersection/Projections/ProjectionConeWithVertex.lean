module

public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.ProjectionConeDimension
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.ProjectionConstantOnLine

/-!
# The cone over a closed subset with a given vertex

The projection away from a closed point `p` of `𝐏(V)` is defined on the complement of `p`, so
the set `AlgebraicGeometry.ProjectiveSpaceOfModule.projectionCone k V p Z` it sweeps out through
a subset `Z` never contains `p`. Read that way the decomposition of [Stacks, Tag 0B1R] is false,
by
`AlgebraicGeometry.ProjectiveSpaceOfModule.not_exists_isOpen_inter_projectionCone_univ_eq`: for
`Y = Z = 𝐏(V)` the left-hand side misses `p` while `Y ∩ Z` contains it.

The object the source means by `r_p^{-1}(r_p(Z))` is the cone over `Z` with vertex `p`, the union
of the lines joining `p` to the points of `Z`. That is `projectionConeWithVertex`, defined here as
the closure of the union of the lines joining `p` to the *closed* points of `Z`. With it [Stacks,
Tag 0B1R] holds for arbitrary closed `Y` and `Z` with no further hypothesis, which is
`exists_isOpen_inter_projectionConeWithVertex_eq`.

The restriction to closed points of `Z` is not cosmetic. For a non-closed point `z` the submodule
`lineSubmodule k V p z` is the intersection of `pointSubmodule k V p` with the degree-one forms
vanishing on the whole closure of `z`, which is far too small, so the subspace it cuts out is far
too large: for `Z` a conic inside a plane of `𝐏^3` and `p` off that plane the generic point of `Z`
contributes all of `𝐏^3`, whereas the cone over `Z` with vertex `p` is a surface. The union over
every point of `Z` therefore violates the dimension bound of [Stacks, Tag 0B1R], while the union
over the closed points of `Z` does not.

## Main definitions and results

* `projectionConeWithVertex`: the cone over `Z` with vertex `p`.
* `subset_projectionConeWithVertex`: a closed `Z` lies on the cone over it.
* `projectionConeWithVertex_diff_singleton_subset_projectionCone`: away from `p` the cone agrees
  with the set swept out by the projection, for arbitrary closed `Z` avoiding `p`.
* `exists_isOpen_inter_projectionConeWithVertex_eq`: [Stacks, Tag 0B1R].
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace
open Stacks.AlgebraicGeometry.ProjShared

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V]

/-! ### The cone over a closed subset with a given vertex -/

/-- **The cone over `Z` with vertex `p`**: the closure of the union of the lines joining `p` to
the closed points of `Z`.

This is the vertex-inclusive reading of `r_p^{-1}(r_p(Z))`, the one [Stacks, Tag 0B1R] means. It
contains `p` as soon as `Z` has a closed point, and it is empty for `Z` empty, the two features
that `projectionCone k V p Z` and `projectionCone k V p Z ∪ {p}` respectively fail to have.

Only the closed points of `Z` contribute: for a non-closed `z` the submodule
`lineSubmodule k V p z` cuts out not the line joining `p` to `z` but the join of `p` with the
linear span of the closure of `z`, which is too large to respect the dimension bound of
[Stacks, Tag 0B1R]. Over an algebraically closed field `Z` is the closure of its closed points, so
nothing is lost by restricting to them. -/
public def projectionConeWithVertex (p : projectiveSpaceOfModule k V)
    (Z : Set (projectiveSpaceOfModule k V)) : Set (projectiveSpaceOfModule k V) :=
  closure (⋃ z ∈ Z ∩ closedPoints (projectiveSpaceOfModule k V),
    linearSubspace k V (lineSubmodule k V p z))

/-- The cone over `Z` with vertex `p` is closed, being a closure. -/
public theorem isClosed_projectionConeWithVertex (p : projectiveSpaceOfModule k V)
    (Z : Set (projectiveSpaceOfModule k V)) :
    IsClosed (projectionConeWithVertex k V p Z) :=
  isClosed_closure

/-- The cone over the empty set is empty: there is no line to sweep out. -/
@[simp]
public theorem projectionConeWithVertex_empty (p : projectiveSpaceOfModule k V) :
    projectionConeWithVertex k V p (∅ : Set (projectiveSpaceOfModule k V)) = ∅ := by
  simp [projectionConeWithVertex]

/-- The set swept out by the projection away from `p` is monotone in the subset projected. -/
public theorem projectionCone_mono (p : projectiveSpaceOfModule k V)
    {Z Z' : Set (projectiveSpaceOfModule k V)} (h : Z ⊆ Z') :
    projectionCone k V p Z ⊆ projectionCone k V p Z' :=
  Set.image_mono (Set.preimage_mono (Set.image_mono (Set.preimage_mono h)))

/-- The vertex lies on the cone over a set with a closed point: it lies on each of the lines. -/
public theorem mem_projectionConeWithVertex (p : projectiveSpaceOfModule k V)
    {Z : Set (projectiveSpaceOfModule k V)} {z : projectiveSpaceOfModule k V} (hzZ : z ∈ Z)
    (hzc : IsClosed ({z} : Set (projectiveSpaceOfModule k V))) :
    p ∈ projectionConeWithVertex k V p Z :=
  subset_closure (Set.mem_biUnion ⟨hzZ, (mem_closedPoints_iff).mpr hzc⟩
    (left_mem_linearSubspace_lineSubmodule k V p z))

/-- The closure of the closed points of `Z` lies on the cone over `Z` with vertex `p`. -/
private theorem closure_inter_closedPoints_subset_projectionConeWithVertex
    (p : projectiveSpaceOfModule k V) (Z : Set (projectiveSpaceOfModule k V)) :
    closure (Z ∩ closedPoints (projectiveSpaceOfModule k V)) ⊆
      projectionConeWithVertex k V p Z :=
  closure_mono fun z hz => Set.mem_biUnion hz (right_mem_linearSubspace_lineSubmodule k V p z)

section Comparison

variable [FiniteDimensional k V] [Nontrivial V]

/-- Projective space over a field is a Jacobson space. -/
private theorem jacobsonSpace_projectiveSpaceOfModule :
    JacobsonSpace (projectiveSpaceOfModule k V) :=
  LocallyOfFiniteType.jacobsonSpace (projectiveSpaceOfModuleToSpec k V)

/-- **A closed subset lies on the cone over it.** Each closed point of `Z` lies on the line
joining it to `p`, and over an algebraically closed field `Z` is the closure of its closed
points. -/
public theorem subset_projectionConeWithVertex [IsAlgClosed k]
    (p : projectiveSpaceOfModule k V) {Z : Set (projectiveSpaceOfModule k V)} (hZ : IsClosed Z) :
    Z ⊆ projectionConeWithVertex k V p Z := by
  have := jacobsonSpace_projectiveSpaceOfModule k V
  calc Z = closure (Z ∩ closedPoints (projectiveSpaceOfModule k V)) := by
          rw [JacobsonSpace.closure_inter_closedPoints_eq_closure hZ.isLocallyClosed,
            hZ.closure_eq]
    _ ⊆ projectionConeWithVertex k V p Z :=
        closure_inter_closedPoints_subset_projectionConeWithVertex k V p Z

/-- **The cone over all of `𝐏(V)` is all of `𝐏(V)`.** Every closed point lies on the line
joining it to `p`, and the closed points are dense. -/
public theorem projectionConeWithVertex_univ [IsAlgClosed k] (p : projectiveSpaceOfModule k V) :
    projectionConeWithVertex k V p (Set.univ : Set (projectiveSpaceOfModule k V)) = Set.univ := by
  have := jacobsonSpace_projectiveSpaceOfModule k V
  refine Set.eq_univ_of_univ_subset ?_
  calc (Set.univ : Set (projectiveSpaceOfModule k V))
      = closure (Set.univ ∩ closedPoints (projectiveSpaceOfModule k V)) := by
        rw [Set.univ_inter, closure_closedPoints]
    _ ⊆ projectionConeWithVertex k V p Set.univ :=
        closure_inter_closedPoints_subset_projectionConeWithVertex k V p Set.univ

/-- **The set swept out by a projection is closed away from the centre.** For a closed point `p`
outside a closed subset `Z`, the image of `Z` under the projection away from `p` is closed, so
`r_p^{-1}(r_p(Z))` is the trace on the complement of `p` of a closed subset of `𝐏(V)`. -/
public theorem closure_projectionCone_diff_singleton_subset [IsAlgClosed k]
    {p : projectiveSpaceOfModule k V}
    (hpc : IsClosed ({p} : Set (projectiveSpaceOfModule k V)))
    [Nontrivial ↥(pointSubmodule k V p)]
    {Z : Set (projectiveSpaceOfModule k V)} (hZ : IsClosed Z) (hpZ : p ∉ Z) :
    closure (projectionCone k V p Z) \ {p} ⊆ projectionCone k V p Z := by
  have hdisj : Disjoint Z (linearSubspace k V (pointSubmodule k V p)) := by
    rw [linearSubspace_pointSubmodule k V p hpc]
    exact Set.disjoint_singleton_right.mpr hpZ
  have hpre : IsClosed ((projection k V (pointSubmodule k V p)).base ⁻¹'
      ((projection k V (pointSubmodule k V p)).base ''
        ((projectionDomain k V (pointSubmodule k V p)).ι.base ⁻¹' Z))) :=
    (isClosed_image_projection k V (pointSubmodule k V p) hZ hdisj).preimage
      (Scheme.Hom.continuous (projection k V (pointSubmodule k V p)))
  obtain ⟨C, hCclosed, hCeq⟩ :=
    (projectionDomain k V (pointSubmodule k V p)).ι.isOpenEmbedding.isInducing.isClosed_iff.mp
      hpre
  have hcone : projectionCone k V p Z = C ∩ {p}ᶜ := by
    rw [projectionCone, ← hCeq, Set.image_preimage_eq_inter_range, Scheme.Opens.range_ι,
      coe_mapDomain_pointSubmodule k V p hpc]
  rw [hcone]
  exact fun x hx =>
    ⟨(hCclosed.closure_subset_iff.mpr Set.inter_subset_left) hx.1, hx.2⟩

/-- **Away from its vertex the cone over `Z` is the set swept out by the projection.** This is the
comparison of the two readings of `r_p^{-1}(r_p(Z))`, for an arbitrary closed `Z` avoiding the
closed point `p`.

The library's `projectionCone_eq_iUnion_lines_diff` identifies the two for a `Z` all of whose
points are closed, which an arbitrary closed `Z` violates; the inclusion proved here is the one
the decomposition of [Stacks, Tag 0B1R] needs, and it holds without that restriction. -/
public theorem projectionConeWithVertex_diff_singleton_subset_projectionCone [IsAlgClosed k]
    {p : projectiveSpaceOfModule k V}
    (hpc : IsClosed ({p} : Set (projectiveSpaceOfModule k V)))
    [Nontrivial ↥(pointSubmodule k V p)]
    {Z : Set (projectiveSpaceOfModule k V)} (hZ : IsClosed Z) (hpZ : p ∉ Z) :
    projectionConeWithVertex k V p Z \ {p} ⊆ projectionCone k V p Z := by
  -- each line joining `p` to a closed point of `Z` lies, off `p`, on the swept-out set
  have hlines : (⋃ z ∈ Z ∩ closedPoints (projectiveSpaceOfModule k V),
      linearSubspace k V (lineSubmodule k V p z)) ⊆ projectionCone k V p Z ∪ {p} := by
    intro x hx
    by_cases hxp : x = p
    · exact Or.inr hxp
    have hxc : x ∈ projectionCone k V p (Z ∩ closedPoints (projectiveSpaceOfModule k V)) :=
      iUnion_lines_diff_subset_projectionCone k V p hpc
        (Z ∩ closedPoints (projectiveSpaceOfModule k V)) (fun h => hpZ h.1)
        (fun _ hz => (mem_closedPoints_iff).mp hz.2) ⟨hx, by simpa using hxp⟩
    exact Or.inl (projectionCone_mono k V p (Set.inter_subset_left
      (s := Z) (t := closedPoints (projectiveSpaceOfModule k V))) hxc)
  have h1 : projectionConeWithVertex k V p Z ⊆ closure (projectionCone k V p Z) ∪ {p} := by
    rw [projectionConeWithVertex]
    calc closure (⋃ z ∈ Z ∩ closedPoints (projectiveSpaceOfModule k V),
            linearSubspace k V (lineSubmodule k V p z))
        ⊆ closure (projectionCone k V p Z ∪ {p}) := closure_mono hlines
      _ = closure (projectionCone k V p Z) ∪ {p} := by rw [closure_union, hpc.closure_eq]
  intro x hx
  rcases h1 hx.1 with h | h
  · exact closure_projectionCone_diff_singleton_subset k V hpc hZ hpZ ⟨h, hx.2⟩
  · exact absurd h hx.2

end Comparison

/-! ### The tag -/

/-- **Stacks 0B1R.** Let `V` be a vector space of dimension `n + 1` over an algebraically closed
field and let `Y, Z ⊆ 𝐏(V)` be closed subsets. There is a nonempty Zariski open `U ⊆ 𝐏(V)` such
that for every closed point `p ∈ U`

`Y ∩ r_p^{-1}(r_p(Z)) = (Y ∩ Z) ∪ E`

with `E ⊆ Y` closed and `dim E ≤ dim Y + dim Z + 1 - n`, where `r_p^{-1}(r_p(Z))` is the cone
over `Z` with vertex `p`.

No hypothesis beyond the closedness of `Y` and `Z` is needed, and in particular none on `Y ∪ Z`
or on `dim Z`. The source asks for `Y` and `Z` to be closed subvarieties; the statement is proved
here for arbitrary closed subsets, which is more general, a subvariety being an irreducible
reduced closed subscheme.

The open subset produced is `U₀ ∖ Z` for `U₀` the open of the general-fibre bound, when `Z` is
neither empty nor everything; in those two degenerate cases the cone is respectively empty and
everything, and `E = ∅` serves over all of `𝐏(V)`. The subset `E` produced in the main case is
the closure of `(Y ∖ Z) ∩ r_p^{-1}(r_p(Z))`, and its dimension is bounded through the incidence
variety `T = {(y, z, p) : y ∈ Y ∖ Z, z ∈ Z, p on the line joining y and z}` exactly as in
`AlgebraicGeometry.ProjectiveSpaceOfModule.exists_isOpen_inter_projectionCone_eq_of_union_ne_univ`,
whose hypothesis `p ∉ Y` is not available here: the vertex `p` may well lie on `Y`, and when it
does it is itself a point of `(Y ∖ Z) ∩ r_p^{-1}(r_p(Z))` whose membership of the image of the
fibre is witnessed by the collinear triple `(p, z₀, p)` for any closed point `z₀` of `Z`.

With the punctured reading of `r_p^{-1}(r_p(Z))` carried by
`AlgebraicGeometry.ProjectiveSpaceOfModule.projectionCone` the statement is false, by
`AlgebraicGeometry.ProjectiveSpaceOfModule.not_exists_isOpen_inter_projectionCone_univ_eq`, and
the registrations of this tag on
`AlgebraicGeometry.ProjectiveSpaceOfModule.exists_isOpen_inter_projectionCone_eq` carry the
hypotheses that reading forces. -/
@[stacks 0B1R "the decomposition Y ∩ r_p^{-1}(r_p(Z)) = (Y ∩ Z) ∪ E with E ⊆ Y closed and \
dim E ≤ dim Y + dim Z + 1 - n, for every closed point p of a nonempty Zariski open subset of \
𝐏(V), with no hypothesis beyond the closedness of Y and Z, reading r_p^{-1}(r_p(Z)) as the cone \
over Z with vertex p"]
public theorem exists_isOpen_inter_projectionConeWithVertex_eq [IsAlgClosed k] [Module.Finite k V]
    {n : ℕ} (hn : Module.finrank k V = n + 1)
    {Y Z : Set (projectiveSpaceOfModule k V)} (hY : IsClosed Y) (hZ : IsClosed Z) :
    ∃ U : Set (projectiveSpaceOfModule k V), IsOpen U ∧ U.Nonempty ∧
      ∀ p ∈ U, IsClosed ({p} : Set (projectiveSpaceOfModule k V)) →
        ∃ E : Set (projectiveSpaceOfModule k V), IsClosed E ∧ E ⊆ Y ∧
          topologicalKrullDim ↥E + (n : WithBot ℕ∞) ≤
            topologicalKrullDim ↥Y + topologicalKrullDim ↥Z + 1 ∧
          Y ∩ projectionConeWithVertex k V p Z = (Y ∩ Z) ∪ E := by
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := k) (by omega)
  have := jacobsonSpace_projectiveSpaceOfModule k V
  have hEempty : topologicalKrullDim ↥(∅ : Set (projectiveSpaceOfModule k V)) +
      (n : WithBot ℕ∞) ≤ topologicalKrullDim ↥Y + topologicalKrullDim ↥Z + 1 := by
    rw [(topologicalKrullDim_eq_bot_iff_isEmpty
      (↥(∅ : Set (projectiveSpaceOfModule k V)))).mpr inferInstance]
    simp
  rcases eq_or_ne Z ∅ with rfl | hZne
  · -- the cone over the empty set is empty, and so is the asserted decomposition
    exact ⟨Set.univ, isOpen_univ, (IrreducibleSpace.isIrreducible_univ _).1,
      fun p _ _ => ⟨∅, isClosed_empty, Set.empty_subset _, hEempty, by simp⟩⟩
  rcases eq_or_ne Z Set.univ with rfl | hZuniv
  · -- the cone over all of `𝐏(V)` is all of `𝐏(V)`, so the left-hand side is `Y` itself
    refine ⟨Set.univ, isOpen_univ, (IrreducibleSpace.isIrreducible_univ _).1,
      fun p _ _ => ⟨∅, isClosed_empty, Set.empty_subset _, hEempty, ?_⟩⟩
    rw [projectionConeWithVertex_univ k V p, Set.union_empty]
  -- the main case: `Z` is a proper nonempty closed subset, and `p` is chosen off `Z`
  obtain ⟨U₀, hU₀open, hU₀ne, hU₀⟩ :=
    exists_isOpen_forall_topologicalKrullDim_fiber_incidenceVarietyToProj_add_le k V Y Z hY hZ hn
  refine ⟨U₀ ∩ Zᶜ, hU₀open.inter hZ.isOpen_compl, ?_, ?_⟩
  · -- `𝐏(V)` is irreducible, so two nonempty open subsets meet
    simpa using (IrreducibleSpace.isIrreducible_univ (projectiveSpaceOfModule k V)).2
      U₀ Zᶜ hU₀open hZ.isOpen_compl (by simpa using hU₀ne)
      (by simpa using Set.nonempty_compl.mpr hZuniv)
  intro p hp hpc
  obtain ⟨hpU₀, hpZ⟩ := hp
  rw [Set.mem_compl_iff] at hpZ
  -- `p` has a hyperplane: otherwise `𝐏(V)` is the single point `p`, forcing `Z = ∅`
  have hWnt : Nontrivial ↥(pointSubmodule k V p) := by
    rcases subsingleton_or_nontrivial ↥(pointSubmodule k V p) with hWs | hWnt
    · refine absurd ?_ hZne
      have hbot : pointSubmodule k V p = ⊥ := by
        refine (Submodule.eq_bot_iff _).mpr fun x hx => ?_
        simpa using congrArg Subtype.val
          (Subsingleton.elim (⟨x, hx⟩ : ↥(pointSubmodule k V p)) 0)
      have huniv : (Set.univ : Set (projectiveSpaceOfModule k V)) = {p} := by
        rw [← linearSubspace_pointSubmodule k V p hpc, hbot, linearSubspace_bot]
      refine Set.eq_empty_iff_forall_notMem.mpr fun x hx => hpZ ?_
      have hx1 : x ∈ ({p} : Set (projectiveSpaceOfModule k V)) := by rw [← huniv]; trivial
      exact Set.mem_singleton_iff.mp hx1 ▸ hx
    · exact hWnt
  -- the cone is closed, so its trace on `Y` is closed with no condition on `p`
  have hYconeClosed : IsClosed (Y ∩ projectionConeWithVertex k V p Z) :=
    hY.inter (isClosed_projectionConeWithVertex k V p Z)
  have hcomp := projectionConeWithVertex_diff_singleton_subset_projectionCone k V hpc hZ hpZ
  refine ⟨closure ((Y \ Z) ∩ projectionConeWithVertex k V p Z), isClosed_closure,
    closure_minimal (fun x hx => hx.1.1) hY, ?_, ?_⟩
  · -- the dimension bound
    set f := incidenceVarietyToProj k V (offDiagBaseToProdTwo k V Y Z hY hZ) with hf
    set F := f.base ⁻¹' {p} with hF
    have hFclosed : IsClosed F := hpc.preimage (Scheme.Hom.continuous f)
    -- a closed point of `Z`, the second vertex of a collinear triple through `p`
    obtain ⟨z₀, hz₀Z, hz₀cl⟩ := nonempty_inter_closedPoints
      (Set.nonempty_iff_ne_empty.mpr hZne) hZ.isLocallyClosed
    have hz₀c : IsClosed ({z₀} : Set (projectiveSpaceOfModule k V)) :=
      (mem_closedPoints_iff).mp hz₀cl
    -- every closed point of the difference is in the image of the fibre
    have hsubimg : ((Y \ Z) ∩ projectionConeWithVertex k V p Z) ∩
        closedPoints (projectiveSpaceOfModule k V) ⊆
          (offDiagIncidenceFst k V Y Z hY hZ).base '' F := by
      rintro x ⟨⟨⟨hxY, hxZ⟩, hxcone⟩, hxcl⟩
      rw [mem_closedPoints_iff] at hxcl
      by_cases hxp : x = p
      · -- the vertex itself, when it lies on `Y`: the triple `(p, z₀, p)` is collinear
        have hxz₀ : x ≠ z₀ := fun h => hxZ (by rw [h]; exact hz₀Z)
        have hpline : p ∈ linearSubspace k V (lineSubmodule k V x z₀) := by
          rw [← hxp]
          exact left_mem_linearSubspace_lineSubmodule k V x z₀
        obtain ⟨t, htp, htx⟩ := exists_point_offDiagIncidenceVariety k V Y Z hY hZ
          hxcl hz₀c hxY hxZ hz₀Z hxz₀ hpline
        exact ⟨t, htp, htx⟩
      · -- away from the vertex the cone is the set swept out by the projection
        have hxcone' : x ∈ projectionCone k V p Z := hcomp ⟨hxcone, by simpa using hxp⟩
        obtain ⟨z, hzZ, hzcl, hzL⟩ :=
          exists_isClosed_mem_inter_linearSubspace_lineSubmodule k V hZ hxcone'
        have hpx : p ≠ x := fun h => hxp h.symm
        have hzx : z ≠ x := fun h => hxZ (h ▸ hzZ)
        have hpline : p ∈ linearSubspace k V (lineSubmodule k V x z) := by
          rw [lineSubmodule_comm]
          exact mem_linearSubspace_lineSubmodule_swap k V hpc hzcl hxcl hpx hzx hzL
        obtain ⟨t, htp, htx⟩ := exists_point_offDiagIncidenceVariety k V Y Z hY hZ
          hxcl hzcl hxY hxZ hzZ (Ne.symm hzx) hpline
        exact ⟨t, htp, htx⟩
    have hlc : IsLocallyClosed ((Y \ Z) ∩ projectionConeWithVertex k V p Z) := by
      have hrw : (Y \ Z) ∩ projectionConeWithVertex k V p Z =
          (Y ∩ projectionConeWithVertex k V p Z) ∩ Zᶜ := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_sdiff, Set.mem_compl_iff]
        tauto
      rw [hrw]
      exact hYconeClosed.isLocallyClosed.inter hZ.isOpen_compl.isLocallyClosed
    have hEle : topologicalKrullDim
        ↥(closure ((Y \ Z) ∩ projectionConeWithVertex k V p Z)) ≤ topologicalKrullDim ↥F := by
      have h1 : closure ((Y \ Z) ∩ projectionConeWithVertex k V p Z) ⊆
          closure ((offDiagIncidenceFst k V Y Z hY hZ).base '' F) := by
        rw [← JacobsonSpace.closure_inter_closedPoints_eq_closure hlc]
        exact closure_mono hsubimg
      refine le_trans (topologicalKrullDim_le_of_subset h1) ?_
      exact topologicalKrullDim_closure_image_le k (offDiagIncidenceFst k V Y Z hY hZ)
        (offDiagIncidenceVarietyToSpec k V Y Z hY hZ) (projectiveSpaceOfModuleToSpec k V)
        (offDiagIncidenceFst_comp_toSpec k V Y Z hY hZ) hFclosed
    have hFdim : topologicalKrullDim ↥F = topologicalKrullDim (f.fiber p) :=
      ((f.fiberHomeo p).isHomeomorph.topologicalKrullDim_eq).symm
    refine le_trans (add_le_add (hEle.trans (le_of_eq hFdim)) (le_refl (n : WithBot ℕ∞))) ?_
    exact hU₀ p hpU₀
  · -- the decomposition
    refine Set.Subset.antisymm (fun x hx => ?_) ?_
    · by_cases hxZ : x ∈ Z
      · exact Or.inl ⟨hx.1, hxZ⟩
      · exact Or.inr (subset_closure ⟨⟨hx.1, hxZ⟩, hx.2⟩)
    refine Set.union_subset (Set.subset_inter Set.inter_subset_left ?_) ?_
    · exact Set.inter_subset_right.trans (subset_projectionConeWithVertex k V p hZ)
    · exact closure_minimal (fun x hx => ⟨hx.1.1, hx.2⟩) hYconeClosed

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
