module

public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationChartsBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AffineChartSystemSizeBound
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendOpens
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.NonemptyLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.PointTopology
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.SchemeStage
import all StacksFrontier.AlgebraicGeometry.Spaces.Limits.PointTopology
import all StacksFrontier.AlgebraicGeometry.Spaces.Limits.SchemeStage
import all StacksFrontier.AlgebraicGeometry.Spaces.OverFields.PurelyTranscendentalDescent

/-!
# A limit which is a scheme has a stage which is a scheme, for systems with bounded charts

In the situation of Stacks 084R — a directed inverse system of quasi-compact and quasi-separated
algebraic spaces over `S` with affine transition morphisms — if the limit is a scheme then some
stage is a scheme (Stacks 07SR). This file proves it for a system whose charts are bounded in the
sense of `AlgebraicGeometry.Space.ChartsBounded`, with no bound on the cardinality of the index
beyond the site's cutoff itself.

## Main results

* `AlgebraicGeometry.Space.pointTopology_limit_of_chartsBounded`,
  `AlgebraicGeometry.Space.nonempty_points_limit_of_chartsBounded` and
  `AlgebraicGeometry.Space.exists_isOpenSubspace_isQuasiCompactSpace_preimage_eq_of_chartsBounded`:
  Stacks 086V, 086W and 0827 for a system with bounded charts.
* `AlgebraicGeometry.Space.ChartsBounded.of_mono`: a subsystem of a system with bounded charts
  and affine transition morphisms, included by monomorphisms, has bounded charts; and
  `AlgebraicGeometry.Space.ChartsBounded.of_isPullback`: so does a system cartesian over it.
* `AlgebraicGeometry.Space.DescentSituation.exists_isRepresentable_system_obj_of_chartsBounded`:
  Stacks 07SR for a descent situation with bounded charts (not registered under the tag, whose
  statement carries no bound).

## Implementation notes

The library's forms of Stacks 086V, 086W and 0827 bound the index by the cofinality of the site's
cutoff, and so does the form
`AlgebraicGeometry.Space.DescentSituation.exists_base_le_isRepresentable_system_obj` of
Stacks 07SR built on them. Their proofs use that bound at one place only: to keep the limits of
the affine chart systems inside the site, which is Stacks 07SF. Boundedness of the charts is the
hypothesis Stacks 07SF actually needs (`AlgebraicGeometry.Space.ChartsBounded.sizeBound`), it is
the hypothesis of Stacks 07SQ
(`AlgebraicGeometry.Space.hasAffineStageDescent_of_chartsBounded`), and it is what the systems of
étale quotients built in the proof of Stacks 07SU satisfy
(`AlgebraicGeometry.Space.EtaleRelationSystem.chartsBounded`) although their index sets are as
large as the rings involved. So the three tags are proved again here with that hypothesis, by the
same arguments.

The proof of Stacks 07SR is the one of `StacksFrontier.AlgebraicGeometry.Spaces.Limits.SchemeStage`.
It applies Stacks 07SQ to the systems of inverse images of a quasi-compact open subspace of a
stage, and Stacks 086W to the system of reduced closed complements of the schematic loci of the
stages; both are subsystems of the given one included by monomorphisms (open, respectively
closed, immersions), and `AlgebraicGeometry.Space.ChartsBounded.of_mono` carries boundedness of
the charts to them: the base change of an affine scheme-valued point along a transition morphism
of the subsystem is a subscheme of its base change along the transition morphism of the system,
so its size is bounded by Stacks 000I's bound for monomorphisms
(`AlgebraicGeometry.Scheme.size_le_of_mono`).

## References

* [Stacks Project, Tag 07SR](https://stacks.math.columbia.edu/tag/07SR)
* [Stacks Project, Tag 07SQ](https://stacks.math.columbia.edu/tag/07SQ)
* [Stacks Project, Tag 0827](https://stacks.math.columbia.edu/tag/0827)
* [Stacks Project, Tag 086V](https://stacks.math.columbia.edu/tag/086V)
* [Stacks Project, Tag 086W](https://stacks.math.columbia.edu/tag/086W)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

section Limit

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- **Stacks 086V, for a system with bounded charts.** The point topology of the limit of a
cofiltered inverse system of algebraic spaces over `S` with affine transition morphisms is the
inverse-limit topology as soon as the charts of the system are bounded in the sense of
`AlgebraicGeometry.Space.ChartsBounded`. The proof is that of
`AlgebraicGeometry.Space.pointTopology_limit`, which uses its bound on the index only to keep
the limits of the affine charts inside the site; here that is
`AlgebraicGeometry.Space.AffineChartSystem.limitBridgeOfSizeBound`. -/
theorem pointTopology_limit_of_chartsBounded (hb : ChartsBounded B S hS D)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f)) :
    pointTopology B S hS (limit D) =
      ⨅ i : I, TopologicalSpace.induced (pointsMap B S hS (limit D) (limit.π D i))
        (pointTopology B S hS (D.obj i)) := by
  classical
  refine le_antisymm
    (le_iInf fun i ↦ continuous_iff_le_induced.mp (continuous_pointsMap B S hS (limit.π D i))) ?_
  intro W hW
  refine isOpen_iInf_of_forall_exists_nbhd (fun i ↦ pointTopology B S hS (D.obj i)) _ W ?_
  intro x hx
  obtain ⟨i₀⟩ := IsCofiltered.nonempty (C := I)
  obtain ⟨U₀, f₀, hf₀, a₀, ha₀⟩ := exists_affine_etale_chart_point B S hS (D.obj i₀) (hD i₀)
    (pointsMap B S hS (limit D) (limit.π D i₀) x)
  set C := affineChartSystem B S hS i₀ D U₀ f₀ hAffine
  set L := C.limitBridgeOfSizeBound (hb.sizeBound C)
  obtain ⟨a, ha, -⟩ := exists_points_of_isPullback B S hS L.isPullback x a₀ ha₀.symm
  have _ : ∀ {j k : Over i₀} (g : j ⟶ k),
      _root_.AlgebraicGeometry.IsAffineHom (C.schemeDiagram.map g) := fun g ↦ C.isAffineHom_map g
  have hf : ∀ j : Over i₀, (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (C.stageMap j) := fun j ↦
    presheaf_of_isPullback B S hS (C.isPullback j).flip hf₀
  obtain ⟨j, V, hV, hxV, hsub⟩ := exists_nbhd_of_chart
    (pointsMap B S hS (yoneda.obj L.cone.pt) L.toLimit)
    (fun j : Over i₀ ↦
      pointsMap B S hS (yoneda.obj L.cone.pt) (yoneda.map (L.cone.π.app j)))
    (fun j : Over i₀ ↦ pointsMap B S hS (limit D) (limit.π D j.left))
    (fun j : Over i₀ ↦
      pointsMap B S hS (yoneda.obj (C.siteDiagram.obj j)) (C.stageMap j))
    (fun j y ↦ by
      rw [← pointsMap_comp_apply, ← pointsMap_comp_apply, L.toLimit_comp_limitπ j])
    (continuous_pointsMap B S hS L.toLimit)
    (fun j ↦ isOpenMap_pointsMap_of_presheafEtale B S hS (C.stageMap j) (hf j))
    (fun j z w hzw ↦ exists_points_of_isPullback B S hS (L.isPullback_stage j) z w hzw)
    (exists_stage_nbhd_points_of_isLimit B S hS C.siteDiagram L.cone L.schemeIsLimit)
    W hW a (by rwa [ha])
  refine ⟨j.left, V, hV, ?_, hsub⟩
  rwa [← ha]

/-- **Stacks 086W, for a system with bounded charts.** The inverse limit of a cofiltered
inverse system of nonempty quasi-compact algebraic spaces over `S` with affine transition
morphisms has a point as soon as the charts of the system are bounded in the sense of
`AlgebraicGeometry.Space.ChartsBounded`. The proof is that of
`AlgebraicGeometry.Space.nonempty_points_limit`. -/
theorem nonempty_points_limit_of_chartsBounded (hb : ChartsBounded B S hS D)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    (hCompact : ∀ i, IsQuasiCompactSpace B S hS (D.obj i))
    (hNonempty : ∀ i, Nonempty (points B S hS (D.obj i))) :
    Nonempty (points B S hS (limit D)) := by
  classical
  obtain ⟨i₀⟩ := IsCofiltered.nonempty (C := I)
  obtain ⟨V₀, f₀, hV₀, hf₀surj, -⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS (D.obj i₀)
      (hD i₀)).mp (hCompact i₀)
  have hsurj : Function.Surjective (pointsMap B S hS (yoneda.obj V₀) f₀) :=
    (surjective_iff_surjective_pointsMap B S hS (D.obj i₀) (hD i₀) V₀ f₀).mp hf₀surj
  set C := affineChartSystem B S hS i₀ D ⟨V₀, hV₀⟩ f₀ hAffine with hC
  set L := C.limitBridgeOfSizeBound (hb.sizeBound C) with hL
  have _ : ∀ j, Nonempty (C.schemeDiagram.obj j) :=
    nonempty_affineChartSystem_obj B S hS D C hsurj hNonempty
  have _ : ∀ j, IsAffine (C.schemeDiagram.obj j) := C.isAffine_obj
  have _ : ∀ j, CompactSpace (C.schemeDiagram.obj j) := fun j ↦ inferInstance
  have _ : ∀ {j k : Over i₀} (g : j ⟶ k),
      _root_.AlgebraicGeometry.IsAffineHom (C.schemeDiagram.map g) := fun g ↦ C.isAffineHom_map g
  obtain ⟨z⟩ : Nonempty ((BigFppfOver.toScheme B S hS).obj L.cone.pt) :=
    Scheme.nonempty_of_isLimit C.schemeDiagram _ L.schemeIsLimit
  exact ⟨pointsMap B S hS (yoneda.obj L.cone.pt) L.toLimit
    ((schemePointRepresentative B S hS L.cone.pt z).class B S hS (yoneda.obj L.cone.pt))⟩

/-! ### Neighbourhoods coming from a single stage -/

/-- Around any one of its points, an open subset of the point space of the limit contains the
preimage of an open neighbourhood at a single stage.

The point topology of the limit is the inverse-limit topology by Stacks 086V, so a
neighbourhood of a point is a finite intersection of preimages of neighbourhoods at stages,
and cofilteredness of the index category lets a single stage be used. -/
private theorem exists_stage_nbhd_of_limit_of_chartsBounded (hb : ChartsBounded B S hS D)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    {W : Set (points B S hS (limit D))} (hW : IsOpen W) (x : points B S hS (limit D))
    (hx : x ∈ W) :
    ∃ (i : I) (V : Set (points B S hS (D.obj i))), IsOpen V ∧
      pointsMap B S hS (limit D) (limit.π D i) x ∈ V ∧
      pointsMap B S hS (limit D) (limit.π D i) ⁻¹' V ⊆ W := by
  have _ : Nonempty I := IsCofiltered.nonempty
  have hmem : W ∈ nhds x := hW.mem_nhds hx
  rw [pointTopology_limit_of_chartsBounded B S hS D hb hD hAffine] at hmem
  simp only [nhds_iInf, nhds_induced] at hmem
  obtain ⟨i, hi⟩ :=
    (Filter.mem_iInf_of_directed (directedGE_comap_nhds_limitπ B S hS D x) W).1 hmem
  obtain ⟨V, hV, hVW⟩ := Filter.mem_comap.1 hi
  obtain ⟨V', hV'V, hV'open, hxV'⟩ := mem_nhds_iff.1 hV
  exact ⟨i, V', hV'open, hxV', fun y hy ↦ hVW (hV'V hy)⟩

/-- A compact set covered by neighbourhoods of its points, each contained in the set, is the
union of finitely many of them. -/
private theorem exists_finset_iUnion_eq_of_isCompact {X : Type*} [TopologicalSpace X] {W : Set X}
    (hW : IsCompact W) (A : X → Set X) (hA : ∀ x ∈ W, A x ∈ nhds x) (hsub : ∀ x ∈ W, A x ⊆ W) :
    ∃ t : Finset X, (∀ x ∈ t, x ∈ W) ∧ ⋃ x : t, A x = W := by
  obtain ⟨t, htW, htcover⟩ := hW.elim_nhds_subcover A hA
  refine ⟨t, htW, Set.Subset.antisymm (Set.iUnion_subset fun x ↦ hsub x (htW x x.2)) ?_⟩
  exact htcover.trans (Set.iUnion₂_subset fun x hx ↦ Set.subset_iUnion (fun y : t ↦ A y) ⟨x, hx⟩)

/-- An open subset of the point space of the limit which is compact is the preimage of a single
open subset of the point space of a single stage.

This is the first of the two passes of the proof of
`AlgebraicGeometry.Space.exists_stage_isCompact_isOpen_preimage_eq`: a finite subcover of the
preimages supplied by `AlgebraicGeometry.Space.exists_stage_nbhd_of_limit` is transported to a
common stage, which exists because the index category is cofiltered. Nothing is claimed about
the open set produced; in particular it need not be quasi-compact. -/
private theorem exists_stage_isOpen_preimage_eq_of_chartsBounded (hb : ChartsBounded B S hS D)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    {W : Set (points B S hS (limit D))} (hWopen : IsOpen W) (hWcompact : IsCompact W) :
    ∃ (i : I) (V : Set (points B S hS (D.obj i))), IsOpen V ∧
      pointsMap B S hS (limit D) (limit.π D i) ⁻¹' V = W := by
  classical
  have _ : Nonempty I := IsCofiltered.nonempty
  choose! stage nbhd hOpen hMem hSub using
    exists_stage_nbhd_of_limit_of_chartsBounded B S hS D hb hD hAffine hWopen
  obtain ⟨t, htW, htcover⟩ := exists_finset_iUnion_eq_of_isCompact hWcompact
    (fun x ↦ pointsMap B S hS (limit D) (limit.π D (stage x)) ⁻¹' nbhd x)
    (fun x hx ↦ ((hOpen x hx).preimage
      (continuous_pointsMap B S hS (limit.π D (stage x)))).mem_nhds (hMem x hx)) hSub
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
        pointsMap B S hS (limit D) (limit.π D (stage x.1)) ⁻¹' nbhd x.1 := fun x ↦ by
    rw [← Set.preimage_comp, ← pointsMap_comp, limit.w]
  rw [Set.preimage_iUnion]
  simp only [hfactor]
  exact htcover

/-! ### Descent of a quasi-compact open set of points -/

/-- A quasi-compact open subset of the point space of the limit of a cofiltered inverse system
of algebraic spaces over `S` with affine transition morphisms is the preimage of a
quasi-compact open subset of the point space of one of the stages.

This is the point-set content of Stacks 0827, for a system with bounded charts. -/
theorem exists_stage_isCompact_isOpen_preimage_eq_of_chartsBounded (hb : ChartsBounded B S hS D)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    {W : Set (points B S hS (limit D))} (hWopen : IsOpen W) (hWcompact : IsCompact W) :
    ∃ (i : I) (V : Set (points B S hS (D.obj i))), IsOpen V ∧ IsCompact V ∧
      pointsMap B S hS (limit D) (limit.π D i) ⁻¹' V = W := by
  classical
  obtain ⟨j, V', hV'open, hV'pre⟩ := exists_stage_isOpen_preimage_eq_of_chartsBounded B S hS D hb
    hD hAffine hWopen hWcompact
  -- Shrink `V'` to a quasi-compact open neighbourhood at each point of `W`, by Tag 04NN.
  have hshrink : ∀ y ∈ W, ∃ K : Set (points B S hS (D.obj j)),
      (IsOpen K ∧ IsCompact K ∧ pointsMap B S hS (limit D) (limit.π D j) y ∈ K) ∧ K ⊆ V' :=
    fun y hy ↦ (hasBasis_nhds_isOpen_isCompact B S hS (D.obj j) (hD j)
      (pointsMap B S hS (limit D) (limit.π D j) y)).mem_iff.mp
      (hV'open.mem_nhds (by rwa [← hV'pre] at hy))
  choose! K hK hKsub using hshrink
  obtain ⟨t, htW, htcover⟩ := exists_finset_iUnion_eq_of_isCompact hWcompact
    (fun y ↦ pointsMap B S hS (limit D) (limit.π D j) ⁻¹' K y)
    (fun y hy ↦ ((hK y hy).1.preimage
      (continuous_pointsMap B S hS (limit.π D j))).mem_nhds (hK y hy).2.2)
    fun y hy ↦ hV'pre ▸ Set.preimage_mono (hKsub y hy)
  refine ⟨j, ⋃ y : {z // z ∈ t}, K y.1,
    isOpen_iUnion fun y ↦ (hK y.1 (htW y.1 y.2)).1,
    isCompact_iUnion fun y ↦ (hK y.1 (htW y.1 y.2)).2.1, ?_⟩
  rwa [Set.preimage_iUnion]

/-! ### Descent of a quasi-compact open subspace -/

/-- **Stacks 0827, for a system with bounded charts.** Let `X = limit D` be the limit of a
cofiltered inverse system `D` of algebraic spaces over `S` with affine transition morphisms and
bounded charts, and assume `X` is an algebraic space. Then every quasi-compact open subspace
`U ⊆ X` is the inverse image of a quasi-compact open subspace of some stage. The proof is that
of `AlgebraicGeometry.Space.exists_isOpenSubspace_isQuasiCompactSpace_preimage_eq`, run on
`AlgebraicGeometry.Space.pointTopology_limit_of_chartsBounded`. -/
theorem exists_isOpenSubspace_isQuasiCompactSpace_preimage_eq_of_chartsBounded
    (hb : ChartsBounded B S hS D)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    (hlim : IsAlgebraicSpace B S hS (limit D))
    (U : Subfunctor (limit D)) (hU : IsOpenSubspace B S hS U)
    (hUqc : IsQuasiCompactSpace B S hS U.toFunctor) :
    ∃ (i : I) (V : Subfunctor (D.obj i)), IsOpenSubspace B S hS V ∧
      IsQuasiCompactSpace B S hS V.toFunctor ∧ V.preimage (limit.π D i) = U := by
  have hWopen : IsOpen (Set.range (pointsMap B S hS U.toFunctor U.ι)) :=
    isOpen_range_pointsMap_of_isOpenImmersion B S hS U.ι hU.2
  have hUcompact : CompactSpace (points B S hS U.toFunctor) :=
    (isQuasiCompactSpace_iff_compactSpace_points B S hS U.toFunctor hU.1).mp hUqc
  have hWcompact : IsCompact (Set.range (pointsMap B S hS U.toFunctor U.ι)) :=
    isCompact_range (continuous_pointsMap B S hS U.ι)
  obtain ⟨i, V, hVopen, hVcompact, hVpre⟩ :=
    exists_stage_isCompact_isOpen_preimage_eq_of_chartsBounded
    B S hS D hb hD hAffine hWopen hWcompact
  have hVsub : IsOpenSubspace B S hS (openSubspaceOfPoints B S hS (D.obj i) V) :=
    isOpenSubspace_openSubspaceOfPoints B S hS (hD i) V hVopen
  refine ⟨i, openSubspaceOfPoints B S hS (D.obj i) V, hVsub, ?_, ?_⟩
  · exact isQuasiCompactSpace_of_isCompact_range B S hS (hD i) hVsub
      (by rwa [range_pointsMap_ι_openSubspaceOfPoints])
  · rw [preimage_openSubspaceOfPoints, hVpre,
      ← eq_openSubspaceOfPoints_range_pointsMap B S hS hlim U hU]

end Limit

/-! ### Subsystems of a system with bounded charts -/

section Subsystem

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A subsystem included by monomorphisms has bounded charts.** Let `η : E ⟶ D` be a morphism
of inverse systems of presheaves whose components are, after every representable base change,
monomorphisms of schemes, and let the transition morphisms of `D` be affine. If `D` has bounded
charts then so does `E`.

For an affine scheme-valued point `f₀` of `E i₀` and a transition morphism `a : j ⟶ i₀`, the base
change `W` of `f₀` along `E.map a` is the base change, along the component `η j`, of the base
change `W'` of `f₀ ≫ η i₀` along `D.map a` (`η i₀` being a monomorphism); so `W ⟶ W'` is a
monomorphism of schemes, and `size W ≤ max (2 ^ #W') (size W') ≤ 2 ^ 2 ^ μ` when `size W' ≤ μ`
(`AlgebraicGeometry.Scheme.size_le_of_mono`, `AlgebraicGeometry.Scheme.mk_le_two_pow_size`). -/
theorem ChartsBounded.of_mono {I : Type u} [Category.{u} I]
    {D E : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (h : ChartsBounded B S hS D) (η : E ⟶ D)
    (hη : ∀ j, (MorphismProperty.inverseImage (MorphismProperty.monomorphisms Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (η.app j))
    (hD : ∀ {i j : I} (a : i ⟶ j), IsAffineHom B S hS (D.map a)) :
    ChartsBounded B S hS E where
  mk_lt := h.mk_lt
  mk_over_lt := h.mk_over_lt
  bound i₀ U₀ f₀ := by
    obtain ⟨mu, hmu, hb⟩ := h.bound i₀ U₀ (f₀ ≫ η.app i₀)
    have hstrong := B.cutoff_isStrongPrelimit
    refine ⟨max (2 ^ 2 ^ mu) mu, max_lt (hstrong (hstrong hmu)) hmu, fun j a W e => ?_⟩
    have hmono : Mono (η.app i₀) := MorphismProperty.presheaf_monomorphisms_le_monomorphisms _
      (MorphismProperty.relative_monotone
        (fun _ _ f hf => (BigFppfOver.toScheme B S hS).mono_of_mono_map hf) _ (hη i₀))
    obtain ⟨W', p', q', hpb'⟩ := hD a U₀ (f₀ ≫ η.app i₀)
    have hW' : ((BigFppfOver.toScheme B S hS).obj
        ((BigAffineFppf.inclusion B S hS).obj W')).size ≤ mu :=
      hb j a _ hpb'.isoPullback
    let x : yoneda.obj W ⟶ E.obj j := e.hom ≫ pullback.fst _ _
    let y : yoneda.obj W ⟶ yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) :=
      e.hom ≫ pullback.snd _ _
    have hW : IsPullback x y (E.map a) f₀ :=
      IsPullback.of_iso_pullback ⟨by simp [x, y, pullback.condition]⟩ e (by simp [x])
        (by simp [y])
    have hW₂ : IsPullback x y (η.app j ≫ D.map a) (f₀ ≫ η.app i₀) := by
      have hsq : IsPullback f₀ (𝟙 _) (η.app i₀) (f₀ ≫ η.app i₀) := by
        simpa using (IsPullback.of_vert_isIso ⟨by simp⟩ :
          IsPullback f₀ (𝟙 _) (𝟙 _) f₀).paste_horiz (IsKernelPair.id_of_mono (η.app i₀))
      rw [← η.naturality]
      simpa using hW.paste_vert hsq
    let l : yoneda.obj W ⟶ yoneda.obj ((BigAffineFppf.inclusion B S hS).obj W') :=
      hpb'.lift (x ≫ η.app j) y (by simpa [Category.assoc] using hW₂.w)
    let m := yoneda.preimage l
    have hm : yoneda.map m = l := Functor.map_preimage _ _
    have hsq : IsPullback x (yoneda.map m) (η.app j) p' := by
      refine IsPullback.of_bot (v₂₁ := yoneda.map q') ?_ (by simp [hm, l]) hpb'
      rw [hm]
      convert hW₂ using 1
      simp [l]
    have hmm : Mono ((BigFppfOver.toScheme B S hS).map m) := (hη j).2 _ _ _ hsq
    calc ((BigFppfOver.toScheme B S hS).obj W).size
        ≤ max (2 ^ #((BigFppfOver.toScheme B S hS).obj
            ((BigAffineFppf.inclusion B S hS).obj W'))) ((BigFppfOver.toScheme B S hS).obj
            ((BigAffineFppf.inclusion B S hS).obj W')).size :=
          Scheme.size_le_of_mono ((BigFppfOver.toScheme B S hS).map m)
      _ ≤ max (2 ^ 2 ^ mu) mu := max_le_max
          (power_le_power_left two_ne_zero ((Scheme.mk_le_two_pow_size _).trans
            (power_le_power_left two_ne_zero hW'))) hW'

/-- **A system cartesian over a system with bounded charts has bounded charts.** Let
`η : E ⟶ D` be a morphism of inverse systems of presheaves all of whose naturality squares are
cartesian, as for the system `E j = Y ×_{D i} D j` of base changes of a presheaf over one stage.
If `D` has bounded charts then so does `E`: the base change of an affine scheme-valued point `f₀`
of `E i₀` along `E.map a` is the base change of `f₀ ≫ η i₀` along `D.map a`. -/
theorem ChartsBounded.of_isPullback {I : Type u} [Category.{u} I]
    {D E : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (h : ChartsBounded B S hS D) (η : E ⟶ D)
    (hη : ∀ {i j : I} (a : i ⟶ j), IsPullback (η.app i) (E.map a) (D.map a) (η.app j)) :
    ChartsBounded B S hS E where
  mk_lt := h.mk_lt
  mk_over_lt := h.mk_over_lt
  bound i₀ U₀ f₀ := by
    obtain ⟨mu, hmu, hb⟩ := h.bound i₀ U₀ (f₀ ≫ η.app i₀)
    exact ⟨mu, hmu, fun j a W e => hb j a W (e.trans
      ((IsPullback.of_hasPullback (E.map a) f₀).flip.paste_vert (hη a).flip).flip.isoPullback)⟩

end Subsystem

/-- A morphism of presheaves which is, after every representable base change, a morphism of
schemes in a class of monomorphisms is, after every representable base change, a monomorphism of
schemes. -/
theorem presheaf_monomorphisms_of_le {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {P : MorphismProperty Scheme.{u}} (hP : P ≤ MorphismProperty.monomorphisms Scheme.{u})
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : F ⟶ G}
    (hf : (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).presheaf f) :
    (MorphismProperty.inverseImage (MorphismProperty.monomorphisms Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f :=
  MorphismProperty.relative_monotone (fun _ _ _ hg => hP _ hg) _ hf

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space.DescentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})}

/-- **Stacks 0827 on a descent situation with bounded charts.** Every quasi-compact open
subspace of the limit of a descent situation with bounded charts is the inverse image of a
quasi-compact open subspace of some stage under the projection of the chosen limit cone. -/
theorem exists_isOpenSubspace_isQuasiCompactSpace_preimage_eq_of_chartsBounded {I : Type u}
    [Preorder I] [IsDirected I (· ≤ ·)] (D : DescentSituation B S hS hZ I)
    (hb : ChartsBounded B S hS D.system)
    (U : Subfunctor D.limitCone.pt) (hU : IsOpenSubspace B S hS U)
    (hUqc : IsQuasiCompactSpace B S hS U.toFunctor) :
    ∃ (i : I) (V : Subfunctor (D.system.obj (Opposite.op i))), IsOpenSubspace B S hS V ∧
      IsQuasiCompactSpace B S hS V.toFunctor ∧
        V.preimage (D.limitCone.π.app (Opposite.op i)) = U := by
  have : Nonempty I := ⟨D.base⟩
  let e := D.isLimit.conePointUniqueUpToIso (limit.isLimit D.system)
  have he (a) : e.hom ≫ limit.π D.system a = D.limitCone.π.app a :=
    D.isLimit.conePointUniqueUpToIso_hom_comp (limit.isLimit D.system) a
  have hlim : IsAlgebraicSpace B S hS (limit D.system) :=
    isAlgebraicSpace_of_iso B S hS e D.limitAlgebraicSpace
  let U' := U.preimage e.inv
  have hU' : IsOpenSubspace B S hS U' :=
    isOpenSubspace_preimage B S hS e.inv U D.limitAlgebraicSpace hlim hU
  have : IsIso (U.fromPreimage e.inv) :=
    (Subfunctor.isPullback_fromPreimage U e.inv).isIso_fst_of_isIso
  have hU'qc : IsQuasiCompactSpace B S hS U'.toFunctor :=
    isQuasiCompactSpace_of_iso B S hS (asIso (U.fromPreimage e.inv)).symm hUqc
  obtain ⟨a, V, hV, hVqc, hVpre⟩ :=
    Space.exists_isOpenSubspace_isQuasiCompactSpace_preimage_eq_of_chartsBounded B S hS D.system hb
      (fun a => D.algebraicSpace a.unop) D.transition_affine hlim U' hU' hU'qc
  refine ⟨a.unop, V, hV, hVqc, ?_⟩
  rw [← he, Subfunctor.preimage_comp, hVpre, ← Subfunctor.preimage_comp, e.hom_inv_id,
    Subfunctor.preimage_id]

end AlgebraicGeometry.Space.DescentSituation

namespace Stacks.SchemeStage

open AlgebraicGeometry.Space (presheaf_monomorphisms_of_le)

attribute [local instance] AlgebraicGeometry.Space.pointTopology

private theorem exists_isRepresentable_preimage_of_chartsBounded
    {B : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} {hZ : B.Contains (⊤_ Scheme.{u})}
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : AlgebraicGeometry.Space.DescentSituation B S hS hZ I)
    (hb : AlgebraicGeometry.Space.ChartsBounded B S hS D.system)
    (i : I) (U : Subfunctor (D.system.obj (Opposite.op i)))
    (hU : AlgebraicGeometry.Space.IsOpenSubspace B S hS U)
    (hUqc : AlgebraicGeometry.Space.IsQuasiCompactSpace B S hS U.toFunctor)
    (hlim : AlgebraicGeometry.Space.IsAffineSpace B S hS
      (U.preimage (D.limitCone.π.app (Opposite.op i))).toFunctor) :
    ∃ (j : I) (hij : i ≤ j),
      (U.preimage (D.system.map (homOfLE hij).op)).toFunctor.IsRepresentable := by
  have : Nonempty (LimitTail I i) := ⟨⟨i, le_rfl⟩⟩
  have : IsDirected (LimitTail I i) (· ≤ ·) := by
    refine ⟨fun x y => ?_⟩
    obtain ⟨k, hxk, hyk⟩ := IsDirected.directed (r := (· ≤ ·)) x.1 y.1
    exact ⟨⟨k, x.2.trans hxk⟩, hxk, hyk⟩
  let G : (LimitTail I i)ᵒᵖ ⥤ Iᵒᵖ :=
    (limitTailOverEquiv i).functor ⋙ Over.forget (Opposite.op i)
  have : G.Initial := by
    dsimp only [G]
    infer_instance
  let ct : Cone (G ⋙ D.system) := D.limitCone.whisker G
  have hct : IsLimit ct :=
    (Functor.Initial.isLimitWhiskerEquiv G D.limitCone).symm D.isLimit
  let τ : (G ⋙ D.system) ⟶
      (Functor.const ((LimitTail I i)ᵒᵖ)).obj (D.system.obj (Opposite.op i)) :=
    { app := fun j => D.system.map (homOfLE j.unop.2).op
      naturality := fun j k φ =>
        ((D.system.map_comp (G.map φ) ((homOfLE k.unop.2).op)).symm.trans
            (congrArg (fun x : G.obj j ⟶ Opposite.op i => D.system.map x)
              (Subsingleton.elim _ _))).trans
          (Category.comp_id _).symm }
  have hσ : ∀ j, ct.π.app j ≫ τ.app j = D.limitCone.π.app (Opposite.op i) := fun j =>
    D.limitCone.w (homOfLE j.unop.2).op
  have hVp : ∀ j : (LimitTail I i)ᵒᵖ,
      AlgebraicGeometry.Space.IsOpenSubspace B S hS (U.preimage (τ.app j)) :=
    fun j => AlgebraicGeometry.Space.isOpenSubspace_preimage B S hS (τ.app j) U (D.algebraicSpace i)
      (D.algebraicSpace j.unop.1) hU
  have hqc : ∀ j : LimitTail I i, AlgebraicGeometry.Space.IsQuasiCompactSpace B S hS
      ((Subfunctor.preimageDiagram τ U).obj (Opposite.op j)) := fun j =>
    AlgebraicGeometry.PurelyTranscendentalDescent.isQuasiCompact_of_isAffineHom B S hS
      (U.fromPreimage (τ.app (Opposite.op j)))
      (hVp (Opposite.op j)).1 hU.1
      (AlgebraicGeometry.Space.isAffineHom_of_isPullback
        (Subfunctor.isPullback_fromPreimage U (τ.app (Opposite.op j))).flip
        (D.transition_affine _)) hUqc
  let d : AlgebraicGeometry.Space.DescentSituation B S hS hZ (LimitTail I i) :=
    { system := Subfunctor.preimageDiagram τ U
      algebraicSpace := fun j => (hVp (Opposite.op j)).1
      transition_affine := fun φ => AlgebraicGeometry.Space.isAffineHom_of_isPullback
        (Subfunctor.isPullback_preimageDiagram_map τ U φ).flip (D.transition_affine _)
      quasiCompact := hqc
      quasiSeparated := fun j =>
        AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ
        (hVp (Opposite.op j)).1 (D.quasiSeparated j.1)
        (AlgebraicGeometry.Space.isQuasiSeparated_of_mono B S hS
          (U.preimage (τ.app (Opposite.op j))).ι inferInstance)
      limitCone := Subfunctor.preimageCone τ U hσ
      isLimit := Subfunctor.isLimitPreimageCone τ U hσ hct
      limitAlgebraicSpace := (AlgebraicGeometry.Space.isOpenSubspace_preimage B S hS _ U
        (D.algebraicSpace i)
        D.limitAlgebraicSpace hU).1
      base := ⟨i, le_rfl⟩ }
  have hJ : #((LimitTail I i)ᵒᵖ) < B.cutoff := by
    rw [Cardinal.mk_congr (Opposite.equivToOpposite (α := LimitTail I i)).symm]
    refine (Cardinal.mk_subtype_le _).trans_lt ?_
    rw [Cardinal.mk_congr (Opposite.equivToOpposite (α := I))]
    exact hb.mk_lt
  have hJover : ∀ j : (LimitTail I i)ᵒᵖ, #(Over j) < B.cutoff :=
    AlgebraicGeometry.mk_over_lt_of_mk_lt B.aleph0_lt_cutoff hJ
      (fun _ _ => (Cardinal.le_one_iff_subsingleton.2 inferInstance).trans Cardinal.one_le_aleph0)
  let ι : Subfunctor.preimageDiagram τ U ⟶ G ⋙ D.system :=
    { app := fun j => (U.preimage (τ.app j)).ι
      naturality := fun _ _ φ => (Subfunctor.isPullback_preimageDiagram_map τ U φ).w }
  have hb : AlgebraicGeometry.Space.ChartsBounded B S hS d.system :=
    (hb.comp G hJ hJover).of_mono ι (fun j => presheaf_monomorphisms_of_le
      (fun _ _ f (_ : IsOpenImmersion f) => MorphismProperty.monomorphisms.infer_property f)
      (hVp j).2) (fun φ => D.transition_affine (G.map φ))
  obtain ⟨j, -, T, -, ⟨e⟩⟩ :=
    AlgebraicGeometry.Space.hasAffineStageDescent_of_chartsBounded B S hS hZ d hb hlim
  exact ⟨j.1, j.2, Functor.IsRepresentable.mk' e.symm⟩

private theorem exists_schematicOpen_preimage_affineOpen_of_chartsBounded
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (hZ : B.Contains (⊤_ Scheme.{u}))
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : AlgebraicGeometry.Space.DescentSituation B S hS hZ I)
    (hb : AlgebraicGeometry.Space.ChartsBounded B S hS D.system)
    [D.limitCone.pt.IsRepresentable]
    (U : ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj
      D.limitCone.pt.reprX).affineOpens) :
    ∃ (j : I) (V : Subfunctor (D.system.obj (Opposite.op j))),
      AlgebraicGeometry.Space.IsOpenSubspace B S hS V ∧ V.toFunctor.IsRepresentable ∧
      V.preimage (D.limitCone.π.app (Opposite.op j)) =
        affineOpenSubspace B S hS D.limitCone.pt.reprW U := by
  obtain ⟨i, V, hV, hVqc, hpre⟩ :=
    D.exists_isOpenSubspace_isQuasiCompactSpace_preimage_eq_of_chartsBounded hb
      (affineOpenSubspace B S hS D.limitCone.pt.reprW U)
      (affineOpenSubspace_isOpen B S hS U)
      (affineOpenSubspace_isQuasiCompact B S hS U)
  have hlim : AlgebraicGeometry.Space.IsAffineSpace B S hS
      (V.preimage (D.limitCone.π.app (Opposite.op i))).toFunctor := by
    rw [hpre]
    exact affineOpenSubspace_isAffine B S hS U
  obtain ⟨j, hij, hj⟩ := exists_isRepresentable_preimage_of_chartsBounded D hb i V hV hVqc hlim
  refine ⟨j, V.preimage (D.system.map (homOfLE hij).op),
    AlgebraicGeometry.Space.isOpenSubspace_preimage B S hS _ V (D.algebraicSpace i)
      (D.algebraicSpace j) hV, hj, ?_⟩
  rw [← Subfunctor.preimage_comp, D.limitCone.w, hpre]

/-- Closed subspaces of the stages of a directed system whose points are the complements of an
increasing family of open subspaces lift along the transition morphisms, provided they are
reduced. -/
private theorem exists_lift_closedSubspace_compl_of_mono
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (hZ : B.Contains (⊤_ Scheme.{u}))
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : AlgebraicGeometry.Space.DescentSituation B S hS hZ I)
    (K : ∀ i : I, Subfunctor (D.system.obj (Opposite.op i)))
    (hK : ∀ i, AlgebraicGeometry.Space.IsOpenSubspace B S hS (K i))
    (hmon : ∀ i j (hij : i ≤ j),
      (K i).preimage (D.system.map (homOfLE hij).op) ≤ K j)
    (Z : ∀ i : I, Subfunctor (D.system.obj (Opposite.op i)))
    (hZclosed : ∀ i, AlgebraicGeometry.Space.IsClosedSubspace B S hS (Z i))
    (hZred : ∀ i, AlgebraicGeometry.Space.HasEtaleLocalProperty B S hS (Z i).toFunctor
      (fun T : Scheme.{u} => IsReduced T))
    (hZrange : ∀ i, Set.range
      (AlgebraicGeometry.Space.pointsMap B S hS (Z i).toFunctor (Z i).ι) =
        (Set.range (AlgebraicGeometry.Space.pointsMap B S hS (K i).toFunctor (K i).ι))ᶜ)
    {i j : Iᵒᵖ} (f : i ⟶ j) :
    ∃ g : (Z i.unop).toFunctor ⟶ (Z j.unop).toFunctor,
      g ≫ (Z j.unop).ι = (Z i.unop).ι ≫ D.system.map f := by
  apply (AlgebraicGeometry.Space.exists_lift_closedSubspace_iff_pointsMap_range_subset B S hS
    (D.algebraicSpace j.unop) (hZclosed i.unop).1
    (Z j.unop) (hZclosed j.unop) (hZred i.unop) _).mpr
  rintro _ ⟨x, rfl⟩
  rw [hZrange]
  intro hx
  have hxi : AlgebraicGeometry.Space.pointsMap B S hS (Z i.unop).toFunctor (Z i.unop).ι x ∈
      (Set.range (AlgebraicGeometry.Space.pointsMap B S hS (K i.unop).toFunctor (K i.unop).ι))ᶜ :=
    (hZrange i.unop).subset ⟨x, rfl⟩
  have hx' : AlgebraicGeometry.Space.pointsMap B S hS _ (D.system.map f)
      (AlgebraicGeometry.Space.pointsMap B S hS _ (Z i.unop).ι x) ∈
      Set.range (AlgebraicGeometry.Space.pointsMap B S hS (K j.unop).toFunctor (K j.unop).ι) := by
    rwa [pointsMap_comp]
  obtain ⟨y, hy⟩ := pointsMap_mem_preimage B S hS
    (D.algebraicSpace i.unop) (D.algebraicSpace j.unop)
    (D.system.map f) (K j.unop) (hK j.unop) _ hx'
  have hm : (K j.unop).preimage (D.system.map f) ≤ K i.unop := by
    have hf : (homOfLE (leOfHom f.unop)).op = f := Subsingleton.elim _ _
    simpa only [hf] using hmon j.unop i.unop (leOfHom f.unop)
  refine hxi ⟨AlgebraicGeometry.Space.pointsMap B S hS _ (Subfunctor.homOfLe hm) y, ?_⟩
  rwa [pointsMap_comp, Subfunctor.homOfLe_ι]

private theorem exists_top_of_covering_limit_of_chartsBounded
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (hZ : B.Contains (⊤_ Scheme.{u}))
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : AlgebraicGeometry.Space.DescentSituation B S hS hZ I)
    (K : ∀ i : I, Subfunctor (D.system.obj (Opposite.op i)))
    (hK : ∀ i, AlgebraicGeometry.Space.IsOpenSubspace B S hS (K i))
    (hmon : ∀ i j (hij : i ≤ j),
      (K i).preimage (D.system.map (homOfLE hij).op) ≤ K j)
    (hb : AlgebraicGeometry.Space.ChartsBounded B S hS D.system)
    (hpoint : ∀ x : AlgebraicGeometry.Space.points B S hS D.limitCone.pt,
      ∃ i, AlgebraicGeometry.Space.pointsMap B S hS D.limitCone.pt
        (D.limitCone.π.app (Opposite.op i)) x ∈
        Set.range (AlgebraicGeometry.Space.pointsMap B S hS (K i).toFunctor (K i).ι)) :
    ∃ i, K i = ⊤ := by
  classical
  have : Nonempty I := ⟨D.base⟩
  let bad (i : I) :=
    (Set.range (AlgebraicGeometry.Space.pointsMap B S hS (K i).toFunctor (K i).ι))ᶜ
  have hbad (i : I) : @IsClosed _
      (AlgebraicGeometry.Space.pointTopology B S hS _) (bad i) :=
    (AlgebraicGeometry.Space.isOpen_range_pointsMap_of_isOpenImmersion B S hS (K i).ι
      (hK i).2).isClosed_compl
  let Z (i : I) := AlgebraicGeometry.Space.reducedClosedSubspace B S hS _ (D.algebraicSpace i)
    (bad i) (hbad i)
  have hZclosed (i : I) : AlgebraicGeometry.Space.IsClosedSubspace B S hS (Z i) :=
    AlgebraicGeometry.Space.isClosedSubspace_reducedClosedSubspace B S hS _ _ _ _
  have hZrange (i : I) : Set.range
      (AlgebraicGeometry.Space.pointsMap B S hS (Z i).toFunctor (Z i).ι) = bad i :=
    AlgebraicGeometry.Space.range_pointsMap_ι_reducedClosedSubspace B S hS _ _ _ _
  have hZred (i : I) :=
    AlgebraicGeometry.Space.hasEtaleLocalProperty_isReduced_reducedClosedSubspace B S hS _
      (D.algebraicSpace i) (bad i) (hbad i)
  have hlift {i j : Iᵒᵖ} (f : i ⟶ j) :=
    exists_lift_closedSubspace_compl_of_mono B S hS hZ D K hK hmon Z hZclosed hZred hZrange f
  let g {i j : Iᵒᵖ} (f : i ⟶ j) := (hlift f).choose
  have hg {i j : Iᵒᵖ} (f : i ⟶ j) :
      g f ≫ (Z j.unop).ι = (Z i.unop).ι ≫ D.system.map f := (hlift f).choose_spec
  let E : Iᵒᵖ ⥤ (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
    { obj i := (Z i.unop).toFunctor
      map f := g f
      map_id i := by
        apply (cancel_mono (Z i.unop).ι).mp
        simp only [hg, D.system.map_id, Category.comp_id, Category.id_comp]
      map_comp f f' := by
        apply (cancel_mono (Z _).ι).mp
        simp only [Category.assoc, hg, D.system.map_comp]
        simp only [← Category.assoc, hg] }
  let η : E ⟶ D.system :=
    { app i := (Z i.unop).ι
      naturality i j f := hg f }
  have hE (i : Iᵒᵖ) : AlgebraicGeometry.IsAlgebraicSpace B S hS (E.obj i) :=
    (hZclosed i.unop).1
  have hιaff (i : I) :=
    AlgebraicGeometry.Space.isAffineHom_of_isClosedImmersion B S hS (Z i).ι (hZclosed i).2
  have hEaff {i j : Iᵒᵖ} (f : i ⟶ j) :
      AlgebraicGeometry.Space.IsAffineHom B S hS (E.map f) := by
    apply isAffineHom_of_comp_mono B S hS (E.map f) (Z j.unop).ι
    show AlgebraicGeometry.Space.IsAffineHom B S hS (g f ≫ (Z j.unop).ι)
    rw [hg]
    exact AlgebraicGeometry.Space.isAffineHom_comp B S hS _ _ (hιaff i.unop) (D.transition_affine f)
  have hEqc (i : Iᵒᵖ) : AlgebraicGeometry.Space.IsQuasiCompactSpace B S hS (E.obj i) :=
    AlgebraicGeometry.Space.isQuasiCompactSpace_of_isClosedImmersion B S hS
      (D.quasiCompact i.unop) (Z i.unop).ι (hZclosed i.unop).2
  refine (em (∃ i, K i = ⊤)).resolve_right fun hne => ?_
  push Not at hne
  have hEne (i : Iᵒᵖ) : Nonempty (AlgebraicGeometry.Space.points B S hS (E.obj i)) := by
    obtain ⟨x, hx⟩ := exists_point_not_mem_openSubspace B S hS
      (D.algebraicSpace i.unop) (K i.unop) (hK i.unop) (hne i.unop)
    obtain ⟨z, -⟩ : x ∈ Set.range
        (AlgebraicGeometry.Space.pointsMap B S hS (Z i.unop).toFunctor (Z i.unop).ι) := by
      rwa [hZrange]
    exact ⟨z⟩
  have hbE : AlgebraicGeometry.Space.ChartsBounded B S hS E :=
    hb.of_mono η (fun i => presheaf_monomorphisms_of_le
      (fun _ _ f (_ : AlgebraicGeometry.IsClosedImmersion f) =>
        MorphismProperty.monomorphisms.infer_property f) (hZclosed i.unop).2)
      D.transition_affine
  obtain ⟨y⟩ := AlgebraicGeometry.Space.nonempty_points_limit_of_chartsBounded B S hS E hbE hE
    hEaff hEqc hEne
  let a : limit E ⟶ D.limitCone.pt := D.isLimit.lift ((Cone.postcompose η).obj (limit.cone E))
  let x := AlgebraicGeometry.Space.pointsMap B S hS (limit E) a y
  obtain ⟨i, hi⟩ := hpoint x
  refine (show AlgebraicGeometry.Space.pointsMap B S hS D.limitCone.pt
      (D.limitCone.π.app (Opposite.op i)) x ∈ bad i from ?_) hi
  rw [← hZrange]
  refine ⟨AlgebraicGeometry.Space.pointsMap B S hS (limit E) (limit.π E (Opposite.op i)) y, ?_⟩
  have ha : a ≫ D.limitCone.π.app (Opposite.op i) = limit.π E (Opposite.op i) ≫ (Z i).ι :=
    D.isLimit.fac _ _
  dsimp only [x]
  rw [pointsMap_comp, pointsMap_comp, ha]

/-- If the limit of an affine inverse system with bounded charts of quasi-compact and
quasi-separated algebraic spaces is a scheme, then one of its stages is a scheme. -/
private theorem exists_isRepresentable_stage_of_chartsBounded
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (hZ : B.Contains (⊤_ Scheme.{u}))
    (I : Type u) [Preorder I] [IsDirected I (· ≤ ·)]
    (D : AlgebraicGeometry.Space.DescentSituation B S hS hZ I)
    (hb : AlgebraicGeometry.Space.ChartsBounded B S hS D.system)
    (hX : D.limitCone.pt.IsRepresentable) :
    ∃ i : I, (D.system.obj (Opposite.op i)).IsRepresentable := by
  classical
  have : D.limitCone.pt.IsRepresentable := hX
  let K (i : I) := AlgebraicGeometry.Space.schematicLocus B S hS (D.system.obj (Opposite.op i))
  suffices h : ∃ i : I, K i = ⊤ by
    obtain ⟨i, hi⟩ := h
    have : (K i).toFunctor.IsRepresentable :=
      (AlgebraicGeometry.Space.isOpenSubspace_and_isRepresentable_schematicLocus_of_isAlgebraicSpace
        B S hS (D.algebraicSpace i)).2
    have : IsIso (K i).ι := (Subfunctor.eq_top_iff_isIso (K i)).mp hi
    exact ⟨i, isRepresentable_of_natIso (K i).toFunctor (asIso (K i).ι)⟩
  have hmon (i j : I) (hij : i ≤ j) :
      (K i).preimage (D.system.map (homOfLE hij).op) ≤ K j :=
    preimage_schematicLocus_le B S hS _ (D.algebraicSpace j) (D.algebraicSpace i)
      (D.transition_affine _)
  have hdesc (U : ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj
      D.limitCone.pt.reprX).affineOpens) :
      ∃ i : I, affineOpenSubspace B S hS D.limitCone.pt.reprW U ≤
        (K i).preimage (D.limitCone.π.app (Opposite.op i)) := by
    obtain ⟨i, V, hVo, hVr, hpre⟩ :=
      exists_schematicOpen_preimage_affineOpen_of_chartsBounded B S hS hZ D hb U
    refine ⟨i, ?_⟩
    rw [← hpre]
    intro T x hx
    exact AlgebraicGeometry.Space.le_schematicLocus B S hS _ V hVo hVr T hx
  have hpoint (x : AlgebraicGeometry.Space.points B S hS D.limitCone.pt) :
      ∃ i : I, AlgebraicGeometry.Space.pointsMap B S hS D.limitCone.pt
        (D.limitCone.π.app (Opposite.op i)) x ∈
        Set.range (AlgebraicGeometry.Space.pointsMap B S hS (K i).toFunctor (K i).ι) := by
    obtain ⟨U, q, hq⟩ := exists_affineOpenSubspace_point B S hS D.limitCone.pt x
    obtain ⟨i, hUi⟩ := hdesc U
    refine ⟨i, AlgebraicGeometry.Space.pointsMap B S hS
      (affineOpenSubspace B S hS D.limitCone.pt.reprW U).toFunctor
      (Subfunctor.homOfLe hUi ≫ (K i).fromPreimage
        (D.limitCone.π.app (Opposite.op i))) q, ?_⟩
    rw [pointsMap_comp, Category.assoc, Subfunctor.fromPreimage_ι,
      ← Category.assoc, Subfunctor.homOfLe_ι, ← pointsMap_comp, hq]
    rfl
  exact exists_top_of_covering_limit_of_chartsBounded B S hS hZ D K
    (fun i =>
      (AlgebraicGeometry.Space.isOpenSubspace_and_isRepresentable_schematicLocus_of_isAlgebraicSpace
        B S hS (D.algebraicSpace i)).1)
    hmon hb hpoint

end Stacks.SchemeStage

namespace AlgebraicGeometry.Space.DescentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})}

/-- **Stacks 07SR.** In the situation of Stacks 084R — a directed inverse system of
quasi-compact and quasi-separated algebraic spaces over `S` with affine transition morphisms —
if the limit `X` is a scheme then some stage `X_i` is a scheme, and `i` may be taken beyond the
distinguished index. The charts of the system are assumed bounded in the sense of
`AlgebraicGeometry.Space.ChartsBounded`, the form in which Stacks 07SQ, which the proof applies,
holds in this development (`AlgebraicGeometry.Space.hasAffineStageDescent_of_chartsBounded`); see
`Stacks.Refute07SQ.not_statement07SQ` for why some bound is needed once the index lives in the
site's universe. The source states the tag with no bound at all, so this theorem is not
registered under it. -/
theorem exists_isRepresentable_system_obj_of_chartsBounded {I : Type u} [Preorder I]
    [IsDirected I (· ≤ ·)]
    (D : DescentSituation B S hS hZ I) (hb : ChartsBounded B S hS D.system)
    (hX : D.limitCone.pt.IsRepresentable) :
    ∃ i, D.base ≤ i ∧ (D.system.obj (Opposite.op i)).IsRepresentable := by
  obtain ⟨i, hi⟩ :=
    Stacks.SchemeStage.exists_isRepresentable_stage_of_chartsBounded B S hS hZ I D hb hX
  obtain ⟨j, hbj, hij⟩ := exists_ge_ge D.base i
  exact ⟨j, hbj, Stacks.SchemeStage.isRepresentable_of_isAffineHom B S hS
    (D.system.map (homOfLE hij).op) (D.algebraicSpace j) (D.algebraicSpace i)
    (D.transition_affine _)⟩

end AlgebraicGeometry.Space.DescentSituation

end
