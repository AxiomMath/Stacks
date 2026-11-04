module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineLimitExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DirectedComapNhds
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.PointTopology
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyCompactPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.SpectralPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.OpenSubspaces

/-!
# Descending a quasi-compact open subspace along a limit of algebraic spaces

Let `X = limit D` be the limit of a cofiltered inverse system `D` of algebraic spaces over a
scheme `S` with affine transition morphisms, as in Situation 084R. Stacks 0827 says that every
quasi-compact open subspace `U ⊆ X` is the inverse image of a quasi-compact open subspace of
one of the stages. This file proves it.

## Main results

All names below are in the namespace `AlgebraicGeometry.Space`.

* `exists_stage_isCompact_isOpen_preimage_eq_of_isSiteSmall` is the statement at the level of
  point sets: a quasi-compact open subset of `|X|` is the preimage of a quasi-compact open subset
  of `|D i|` for some stage `i`.
* `exists_isOpenSubspace_isQuasiCompactSpace_preimage_eq_of_isSiteSmall` is **Stacks 0827**: a
  quasi-compact open subspace of `X` is the inverse image of a quasi-compact open subspace of a
  stage, as an equality of subfunctors.
* `exists_isOpenSubspace_isQuasiCompactSpace_preimage_eq_of_siteContainsBaseChangeLimits` is
  Stacks 0827 for a system satisfying the convention of Section 70.2 (tag 07SD) in place of the
  size condition, with point-set content
  `exists_stage_isCompact_isOpen_preimage_eq_of_siteContainsBaseChangeLimits`.

## Implementation notes

*The hypotheses.* The situation is Situation 084R with the stages' quasi-separatedness and
quasi-compactness dropped and the two size hypotheses of Stacks 07SF added — the standing form
of the neighbouring tags of the section, `AlgebraicGeometry.Space.pointTopology_limit` (086V),
`AlgebraicGeometry.Space.nonempty_points_limit` (086W) and
`AlgebraicGeometry.Space.existsUnique_point_limit` (0CUJ). The size hypotheses are what makes
the limit an algebraic space at all (`AlgebraicGeometry.Space.isAlgebraicSpace_limit`), so they
are not an extra assumption but the form Situation 084R takes once the limit is formed inside
the site rather than postulated. Of the hypotheses the source does impose, neither
quasi-separatedness of the stages nor their quasi-compactness is used: the argument below runs
on an arbitrary cofiltered system of algebraic spaces with affine transition morphisms, so the
result is proved in that generality and applies in particular to Situation 084R.

*The argument.* The source proof says the statement "follows formally" from the construction of
the limit and the corresponding result for schemes, Stacks 01Z4 (1). The route taken here is
the point-set one, which the development already supports end to end and which needs no further
étale presentation of the limit.

Everything reduces to the topology. By Tag 03BZ (part (1)) an open subspace of an algebraic
space is determined by, and can be manufactured from, its set of points
(`AlgebraicGeometry.Space.openSubspaceOfPoints`,
`AlgebraicGeometry.Space.eq_openSubspaceOfPoints_range_pointsMap`), inverse images of such
subspaces are the subspaces cut out by the preimages of the point sets
(`AlgebraicGeometry.Space.preimage_openSubspaceOfPoints`), and quasi-compactness of an open
subspace is compactness of its point set
(`AlgebraicGeometry.Space.isQuasiCompactSpace_of_isCompact_range`, Tag 03E4). So the tag is
equivalent to its point-set form, which is
`AlgebraicGeometry.Space.exists_stage_isCompact_isOpen_preimage_eq_of_isSiteSmall`.

That form is proved from Stacks 086V, that `|X|` carries the inverse-limit topology, in two
passes over the compactness of the given open `W`. The first pass covers `W` by preimages of
opens of the stages, extracts a finite subcover, and moves it to one stage `j` by
cofilteredness; this exhibits `W` as the preimage of a single open `V'` of `|D j|`, but says
nothing more about `V'`. Both passes are needed, because a preimage of a quasi-compact open
along a transition morphism need not be quasi-compact, so the quasi-compact opens have to be
chosen *at* the stage `j` rather than transported to it. The second pass therefore shrinks,
around each point of `W`, the open `V'` to a quasi-compact open neighbourhood inside it — Tag
04NN, `AlgebraicGeometry.Space.hasBasis_nhds_isOpen_isCompact` — and extracts a finite subcover
again; the union of that finite family is a quasi-compact open of `|D j|` whose preimage is
still `W`.

## References

* [Stacks Project, Tag 0827](https://stacks.math.columbia.edu/tag/0827)
* [Stacks Project, Tag 084R](https://stacks.math.columbia.edu/tag/084R)
* [Stacks Project, Tag 086V](https://stacks.math.columbia.edu/tag/086V)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 03E4](https://stacks.math.columbia.edu/tag/03E4)
* [Stacks Project, Tag 04NN](https://stacks.math.columbia.edu/tag/04NN)
* [Stacks Project, Tag 07SF](https://stacks.math.columbia.edu/tag/07SF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-! ### Neighbourhoods coming from a single stage -/

/-- Around any one of its points, an open subset of the point space of the limit contains the
preimage of an open neighbourhood at a single stage.

The point topology of the limit is the inverse-limit topology by Stacks 086V (here the hypothesis
`htop`), so a neighbourhood of a point is a finite intersection of preimages of neighbourhoods at
stages, and cofilteredness of the index category lets a single stage be used. -/
private theorem exists_stage_nbhd_of_pointTopology_eq
    (htop : pointTopology B S hS (limit D) =
      ⨅ i : I, TopologicalSpace.induced (pointsMap B S hS (limit D) (limit.π D i))
        (pointTopology B S hS (D.obj i)))
    {W : Set (points B S hS (limit D))} (hW : IsOpen W) (x : points B S hS (limit D))
    (hx : x ∈ W) :
    ∃ (i : I) (V : Set (points B S hS (D.obj i))), IsOpen V ∧
      pointsMap B S hS (limit D) (limit.π D i) x ∈ V ∧
      pointsMap B S hS (limit D) (limit.π D i) ⁻¹' V ⊆ W := by
  have _ : Nonempty I := IsCofiltered.nonempty
  have hmem : W ∈ nhds x := hW.mem_nhds hx
  rw [htop] at hmem
  simp only [nhds_iInf, nhds_induced] at hmem
  obtain ⟨i, hi⟩ :=
    (Filter.mem_iInf_of_directed (directedGE_comap_nhds_limitπ B S hS D x) W).1 hmem
  obtain ⟨V, hV, hVW⟩ := Filter.mem_comap.1 hi
  obtain ⟨V', hV'V, hV'open, hxV'⟩ := mem_nhds_iff.1 hV
  exact ⟨i, V', hV'open, hxV', fun y hy ↦ hVW (hV'V hy)⟩

/-- An open subset of the point space of the limit which is compact is the preimage of a single
open subset of the point space of a single stage.

This is the first of the two passes of the proof of
`AlgebraicGeometry.Space.exists_stage_isCompact_isOpen_preimage_eq_of_isSiteSmall`: a finite
subcover of the preimages supplied by
`AlgebraicGeometry.Space.exists_stage_nbhd_of_pointTopology_eq` is transported to a common stage,
which exists because the index category is cofiltered. Nothing is claimed about the open set
produced; in particular it need not be quasi-compact. -/
private theorem exists_stage_isOpen_preimage_eq_of_pointTopology_eq
    (htop : pointTopology B S hS (limit D) =
      ⨅ i : I, TopologicalSpace.induced (pointsMap B S hS (limit D) (limit.π D i))
        (pointTopology B S hS (D.obj i)))
    {W : Set (points B S hS (limit D))} (hWopen : IsOpen W) (hWcompact : IsCompact W) :
    ∃ (i : I) (V : Set (points B S hS (D.obj i))), IsOpen V ∧
      pointsMap B S hS (limit D) (limit.π D i) ⁻¹' V = W := by
  classical
  have _ : Nonempty I := IsCofiltered.nonempty
  choose! stage nbhd hOpen hMem hSub using
    exists_stage_nbhd_of_pointTopology_eq B S hS D htop hWopen
  obtain ⟨t, htW, htcover⟩ := hWcompact.elim_nhds_subcover
    (fun x ↦ pointsMap B S hS (limit D) (limit.π D (stage x)) ⁻¹' nbhd x)
    fun x hx ↦ ((hOpen x hx).preimage
      (continuous_pointsMap B S hS (limit.π D (stage x)))).mem_nhds (hMem x hx)
  obtain ⟨j, hj⟩ := IsCofiltered.inf_objs_exists (t.image stage)
  -- The transition morphism from the common stage to the stage chosen at a point of `t`.
  let trans : ∀ x : {y // y ∈ t}, j ⟶ stage x.1 := fun x ↦
    (hj (Finset.mem_image_of_mem stage x.2)).some
  refine ⟨j, ⋃ x : {y // y ∈ t},
    pointsMap B S hS (D.obj j) (D.map (trans x)) ⁻¹' nbhd x.1,
    isOpen_iUnion fun x ↦ (hOpen x.1 (htW x.1 x.2)).preimage
      (continuous_pointsMap B S hS (D.map (trans x))), ?_⟩
  -- Each transported preimage is the original preimage, so the union is `W`.
  have hfactor : ∀ x : {y // y ∈ t},
      pointsMap B S hS (limit D) (limit.π D j) ⁻¹'
          (pointsMap B S hS (D.obj j) (D.map (trans x)) ⁻¹' nbhd x.1) =
        pointsMap B S hS (limit D) (limit.π D (stage x.1)) ⁻¹' nbhd x.1 := by
    intro x
    rw [← Set.preimage_comp, ← pointsMap_comp, limit.w]
  rw [Set.preimage_iUnion]
  refine Set.Subset.antisymm (Set.iUnion_subset fun x ↦ ?_) ?_
  · rw [hfactor x]
    exact hSub x.1 (htW x.1 x.2)
  · refine le_trans htcover (Set.iUnion₂_subset fun x hx ↦ ?_)
    rw [← hfactor ⟨x, hx⟩]
    exact Set.subset_iUnion
      (fun y : {z // z ∈ t} ↦ pointsMap B S hS (limit D) (limit.π D j) ⁻¹'
        (pointsMap B S hS (D.obj j) (D.map (trans y)) ⁻¹' nbhd y.1)) ⟨x, hx⟩

/-- The point-set content of Stacks 0827 for any cofiltered system whose limit carries the
inverse-limit topology on its points: a quasi-compact open subset of `|X|` is the preimage of a
quasi-compact open subset of `|D i|` for some stage `i`.

This is the second pass of the argument: the open set of the first pass is shrunk, around each
point of `W`, to a quasi-compact open neighbourhood (Tag 04NN), and a finite subcover is taken. -/
private theorem exists_stage_isCompact_isOpen_preimage_eq_of_pointTopology_eq
    (htop : pointTopology B S hS (limit D) =
      ⨅ i : I, TopologicalSpace.induced (pointsMap B S hS (limit D) (limit.π D i))
        (pointTopology B S hS (D.obj i)))
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    {W : Set (points B S hS (limit D))} (hWopen : IsOpen W) (hWcompact : IsCompact W) :
    ∃ (i : I) (V : Set (points B S hS (D.obj i))), IsOpen V ∧ IsCompact V ∧
      pointsMap B S hS (limit D) (limit.π D i) ⁻¹' V = W := by
  classical
  obtain ⟨j, V', hV'open, hV'pre⟩ :=
    exists_stage_isOpen_preimage_eq_of_pointTopology_eq B S hS D htop hWopen hWcompact
  -- Shrink `V'` to a quasi-compact open neighbourhood at each point of `W`, by Tag 04NN.
  have hshrink : ∀ y ∈ W, ∃ K : Set (points B S hS (D.obj j)),
      (IsOpen K ∧ IsCompact K ∧ pointsMap B S hS (limit D) (limit.π D j) y ∈ K) ∧ K ⊆ V' :=
    fun y hy ↦ (hasBasis_nhds_isOpen_isCompact B S hS (D.obj j) (hD j)
      (pointsMap B S hS (limit D) (limit.π D j) y)).mem_iff.mp
      (hV'open.mem_nhds (by rw [← hV'pre] at hy; exact hy))
  choose! K hK hKsub using hshrink
  obtain ⟨t, htW, htcover⟩ := hWcompact.elim_nhds_subcover
    (fun y ↦ pointsMap B S hS (limit D) (limit.π D j) ⁻¹' K y)
    fun y hy ↦ ((hK y hy).1.preimage
      (continuous_pointsMap B S hS (limit.π D j))).mem_nhds (hK y hy).2.2
  refine ⟨j, ⋃ y : {z // z ∈ t}, K y.1,
    isOpen_iUnion fun y ↦ (hK y.1 (htW y.1 y.2)).1,
    isCompact_iUnion fun y ↦ (hK y.1 (htW y.1 y.2)).2.1, ?_⟩
  rw [Set.preimage_iUnion]
  refine Set.Subset.antisymm (Set.iUnion_subset fun y ↦ ?_) ?_
  · rw [← hV'pre]
    exact Set.preimage_mono (hKsub y.1 (htW y.1 y.2))
  · refine le_trans htcover (Set.iUnion₂_subset fun y hy ↦ ?_)
    exact Set.subset_iUnion
      (fun z : {w // w ∈ t} ↦ pointsMap B S hS (limit D) (limit.π D j) ⁻¹' K z.1) ⟨y, hy⟩

/-- A quasi-compact open subspace of the limit descends to a stage as soon as the point-set form
of the statement holds for the limit and the stages are algebraic spaces. -/
private theorem exists_isOpenSubspace_isQuasiCompactSpace_preimage_eq_of_exists_stage
    (hlim : IsAlgebraicSpace B S hS (limit D))
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hpts : ∀ {W : Set (points B S hS (limit D))}, IsOpen W → IsCompact W →
      ∃ (i : I) (V : Set (points B S hS (D.obj i))), IsOpen V ∧ IsCompact V ∧
        pointsMap B S hS (limit D) (limit.π D i) ⁻¹' V = W)
    (U : Subfunctor (limit D)) (hU : IsOpenSubspace B S hS U)
    (hUqc : IsQuasiCompactSpace B S hS U.toFunctor) :
    ∃ (i : I) (V : Subfunctor (D.obj i)), IsOpenSubspace B S hS V ∧
      IsQuasiCompactSpace B S hS V.toFunctor ∧ V.preimage (limit.π D i) = U := by
  have _ : Nonempty I := IsCofiltered.nonempty
  have hUcompact : CompactSpace (points B S hS U.toFunctor) :=
    (isQuasiCompactSpace_iff_compactSpace_points B S hS U.toFunctor hU.1).mp hUqc
  obtain ⟨i, V, hVopen, hVcompact, hVpre⟩ :=
    hpts (isOpen_range_pointsMap_of_isOpenImmersion B S hS U.ι hU.2)
      (isCompact_range (continuous_pointsMap B S hS U.ι))
  have hVsub : IsOpenSubspace B S hS (openSubspaceOfPoints B S hS (D.obj i) V) :=
    isOpenSubspace_openSubspaceOfPoints B S hS (hD i) V hVopen
  refine ⟨i, openSubspaceOfPoints B S hS (D.obj i) V, hVsub, ?_, ?_⟩
  · refine isQuasiCompactSpace_of_isCompact_range B S hS (hD i) hVsub ?_
    rw [range_pointsMap_ι_openSubspaceOfPoints]
    exact hVcompact
  · rw [preimage_openSubspaceOfPoints, hVpre,
      ← eq_openSubspaceOfPoints_range_pointsMap B S hS hlim U hU]

/-- Around any one of its points, an open subset of the point space of the limit contains the
preimage of an open neighbourhood at a single stage.

The point topology of the limit is the inverse-limit topology by Stacks 086V, so a
neighbourhood of a point is a finite intersection of preimages of neighbourhoods at stages,
and cofilteredness of the index category lets a single stage be used. -/
private theorem exists_stage_nbhd_of_limit_of_isSiteSmall (hb : IsSiteSmall B S hS D)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    {W : Set (points B S hS (limit D))} (hW : IsOpen W) (x : points B S hS (limit D))
    (hx : x ∈ W) :
    ∃ (i : I) (V : Set (points B S hS (D.obj i))), IsOpen V ∧
      pointsMap B S hS (limit D) (limit.π D i) x ∈ V ∧
      pointsMap B S hS (limit D) (limit.π D i) ⁻¹' V ⊆ W := by
  have _ : Nonempty I := IsCofiltered.nonempty
  have hmem : W ∈ nhds x := hW.mem_nhds hx
  rw [pointTopology_limit_of_isSiteSmall B S hS D hb hD hAffine] at hmem
  simp only [nhds_iInf, nhds_induced] at hmem
  obtain ⟨i, hi⟩ :=
    (Filter.mem_iInf_of_directed (directedGE_comap_nhds_limitπ B S hS D x) W).1 hmem
  obtain ⟨V, hV, hVW⟩ := Filter.mem_comap.1 hi
  obtain ⟨V', hV'V, hV'open, hxV'⟩ := mem_nhds_iff.1 hV
  exact ⟨i, V', hV'open, hxV', fun y hy ↦ hVW (hV'V hy)⟩

/-- Around any one of its points, an open subset of the point space of the limit contains the
preimage of an open neighbourhood at a single stage.

The point topology of the limit is the inverse-limit topology by Stacks 086V, so a
neighbourhood of a point is a finite intersection of preimages of neighbourhoods at stages,
and cofilteredness of the index category lets a single stage be used. -/
private theorem exists_stage_nbhd_of_limit (hSize : #I < B.cutoff.ord.cof)
    (hHomSize : ∀ i j : I, #(i ⟶ j) < B.cutoff.ord.cof)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    {W : Set (points B S hS (limit D))} (hW : IsOpen W) (x : points B S hS (limit D))
    (hx : x ∈ W) :
    ∃ (i : I) (V : Set (points B S hS (D.obj i))), IsOpen V ∧
      pointsMap B S hS (limit D) (limit.π D i) x ∈ V ∧
      pointsMap B S hS (limit D) (limit.π D i) ⁻¹' V ⊆ W :=
  exists_stage_nbhd_of_limit_of_isSiteSmall B S hS D (.of_lt_cof hSize hHomSize) hD hAffine hW x hx


/-! ### Descent of a quasi-compact open set of points -/

/-- A quasi-compact open subset of the point space of the limit of a cofiltered inverse system
of algebraic spaces over `S` with affine transition morphisms is the preimage of a
quasi-compact open subset of the point space of one of the stages.

This is the point-set content of Stacks 0827. -/
theorem exists_stage_isCompact_isOpen_preimage_eq_of_isSiteSmall (hb : IsSiteSmall B S hS D)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    {W : Set (points B S hS (limit D))} (hWopen : IsOpen W) (hWcompact : IsCompact W) :
    ∃ (i : I) (V : Set (points B S hS (D.obj i))), IsOpen V ∧ IsCompact V ∧
      pointsMap B S hS (limit D) (limit.π D i) ⁻¹' V = W :=
  exists_stage_isCompact_isOpen_preimage_eq_of_pointTopology_eq B S hS D
    (pointTopology_limit_of_isSiteSmall B S hS D hb hD hAffine) hD hWopen hWcompact

/-- A quasi-compact open subset of the point space of the limit of a cofiltered inverse system
of algebraic spaces over `S` with affine transition morphisms is the preimage of a
quasi-compact open subset of the point space of one of the stages.

This is the point-set content of Stacks 0827. -/
theorem exists_stage_isCompact_isOpen_preimage_eq (hSize : #I < B.cutoff.ord.cof)
    (hHomSize : ∀ i j : I, #(i ⟶ j) < B.cutoff.ord.cof)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    {W : Set (points B S hS (limit D))} (hWopen : IsOpen W) (hWcompact : IsCompact W) :
    ∃ (i : I) (V : Set (points B S hS (D.obj i))), IsOpen V ∧ IsCompact V ∧
      pointsMap B S hS (limit D) (limit.π D i) ⁻¹' V = W :=
  exists_stage_isCompact_isOpen_preimage_eq_of_isSiteSmall B S hS D (.of_lt_cof hSize hHomSize) hD
      hAffine hWopen hWcompact

/-! ### Descent of a quasi-compact open subspace -/

/-- **Stacks 0827.** Notation and assumptions as in Situation 084R: let `X = limit D` be the
limit of a cofiltered inverse system `D` of algebraic spaces over `S` with affine transition
morphisms, the index category being small enough for the site so that `X` is an algebraic space
by Stacks 07SF. Then for every quasi-compact open subspace `U ⊆ X` there is a stage `i` and a
quasi-compact open subspace of `D i` whose inverse image in `X` is `U`.

Neither quasi-separatedness nor quasi-compactness of the stages, which Situation 084R also
assumes, is needed. -/
@[stacks 0827, ega "IV 8.2.11"]
theorem exists_isOpenSubspace_isQuasiCompactSpace_preimage_eq_of_isSiteSmall (hb : IsSiteSmall B S
    hS D)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    (U : Subfunctor (limit D)) (hU : IsOpenSubspace B S hS U)
    (hUqc : IsQuasiCompactSpace B S hS U.toFunctor) :
    ∃ (i : I) (V : Subfunctor (D.obj i)), IsOpenSubspace B S hS V ∧
      IsQuasiCompactSpace B S hS V.toFunctor ∧ V.preimage (limit.π D i) = U :=
  exists_isOpenSubspace_isQuasiCompactSpace_preimage_eq_of_exists_stage B S hS D
    (isAlgebraicSpace_limit_of_isSiteSmall B S hS D hb hD hAffine) hD
    (exists_stage_isCompact_isOpen_preimage_eq_of_isSiteSmall B S hS D hb hD hAffine) U hU hUqc

/-- **Stacks 0827.** Notation and assumptions as in Situation 084R: let `X = limit D` be the
limit of a cofiltered inverse system `D` of algebraic spaces over `S` with affine transition
morphisms, the index category being small enough for the site so that `X` is an algebraic space
by Stacks 07SF. Then for every quasi-compact open subspace `U ⊆ X` there is a stage `i` and a
quasi-compact open subspace of `D i` whose inverse image in `X` is `U`.

Neither quasi-separatedness nor quasi-compactness of the stages, which Situation 084R also
assumes, is needed. -/
@[stacks 0827, ega "IV 8.2.11"]
theorem exists_isOpenSubspace_isQuasiCompactSpace_preimage_eq (hSize : #I < B.cutoff.ord.cof)
    (hHomSize : ∀ i j : I, #(i ⟶ j) < B.cutoff.ord.cof)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    (U : Subfunctor (limit D)) (hU : IsOpenSubspace B S hS U)
    (hUqc : IsQuasiCompactSpace B S hS U.toFunctor) :
    ∃ (i : I) (V : Subfunctor (D.obj i)), IsOpenSubspace B S hS V ∧
      IsQuasiCompactSpace B S hS V.toFunctor ∧ V.preimage (limit.π D i) = U :=
  exists_isOpenSubspace_isQuasiCompactSpace_preimage_eq_of_isSiteSmall B S hS D (.of_lt_cof hSize
      hHomSize) hD hAffine U hU hUqc

/-! ### Under the chapter's standing convention -/

/-- **The point-set content of Stacks 0827, under the chapter's standing convention.** A
quasi-compact open subset of the point space of the limit of a cofiltered inverse system of
algebraic spaces over `S` with affine transition morphisms is the preimage of a quasi-compact
open subset of the point space of one of the stages.

This is `AlgebraicGeometry.Space.exists_stage_isCompact_isOpen_preimage_eq` with its smallness
hypothesis replaced by the convention of Section 70.2 (tag 07SD),
`AlgebraicGeometry.Space.SiteContainsBaseChangeLimits`, through which Stacks 086V holds. Nothing
is asked of the index. -/
theorem exists_stage_isCompact_isOpen_preimage_eq_of_siteContainsBaseChangeLimits
    (hconv : SiteContainsBaseChangeLimits B S hS D)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    {W : Set (points B S hS (limit D))} (hWopen : IsOpen W) (hWcompact : IsCompact W) :
    ∃ (i : I) (V : Set (points B S hS (D.obj i))), IsOpen V ∧ IsCompact V ∧
      pointsMap B S hS (limit D) (limit.π D i) ⁻¹' V = W :=
  exists_stage_isCompact_isOpen_preimage_eq_of_pointTopology_eq B S hS D
    (pointTopology_limit_of_siteContainsBaseChangeLimits B S hS D hconv hD hAffine) hD
    hWopen hWcompact

/-- **Stacks 0827, under the chapter's standing convention.** Let `X = limit D` be the limit of
a cofiltered inverse system `D` of algebraic spaces over `S` with affine transition morphisms,
which is an algebraic space. Then for every quasi-compact open subspace `U ⊆ X` there is a stage
`i` and a quasi-compact open subspace of `D i` whose inverse image in `X` is `U`.

This is `AlgebraicGeometry.Space.exists_isOpenSubspace_isQuasiCompactSpace_preimage_eq` with its
smallness hypothesis replaced by the convention of Section 70.2 (tag 07SD),
`AlgebraicGeometry.Space.SiteContainsBaseChangeLimits`; nothing is asked of the index. That the
limit is an algebraic space is part of Situation 084R, which takes `X` to be the algebraic space
of Stacks 07SF. -/
theorem exists_isOpenSubspace_isQuasiCompactSpace_preimage_eq_of_siteContainsBaseChangeLimits
    (hconv : SiteContainsBaseChangeLimits B S hS D)
    (hlim : IsAlgebraicSpace B S hS (limit D))
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    (U : Subfunctor (limit D)) (hU : IsOpenSubspace B S hS U)
    (hUqc : IsQuasiCompactSpace B S hS U.toFunctor) :
    ∃ (i : I) (V : Subfunctor (D.obj i)), IsOpenSubspace B S hS V ∧
      IsQuasiCompactSpace B S hS V.toFunctor ∧ V.preimage (limit.π D i) = U :=
  exists_isOpenSubspace_isQuasiCompactSpace_preimage_eq_of_exists_stage B S hS D hlim hD
    (exists_stage_isCompact_isOpen_preimage_eq_of_siteContainsBaseChangeLimits B S hS D hconv hD
      hAffine) U hU hUqc

/-- The scheme-free form of Stacks 0827 for any cofiltered system whose limit is an algebraic space
carrying the inverse-limit topology on its points (`htop`): a quasi-compact open subspace of the
limit is the inverse image of a quasi-compact open subspace of some stage. -/
theorem exists_isOpenSubspace_isQuasiCompactSpace_preimage_eq_of_pointTopology
    (htop : pointTopology B S hS (limit D) =
      ⨅ i : I, TopologicalSpace.induced (pointsMap B S hS (limit D) (limit.π D i))
        (pointTopology B S hS (D.obj i)))
    (hlim : IsAlgebraicSpace B S hS (limit D))
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (U : Subfunctor (limit D)) (hU : IsOpenSubspace B S hS U)
    (hUqc : IsQuasiCompactSpace B S hS U.toFunctor) :
    ∃ (i : I) (V : Subfunctor (D.obj i)), IsOpenSubspace B S hS V ∧
      IsQuasiCompactSpace B S hS V.toFunctor ∧ V.preimage (limit.π D i) = U :=
  exists_isOpenSubspace_isQuasiCompactSpace_preimage_eq_of_exists_stage B S hS D hlim hD
    (exists_stage_isCompact_isOpen_preimage_eq_of_pointTopology_eq B S hS D htop hD) U hU hUqc

end AlgebraicGeometry.Space

end
