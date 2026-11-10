module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.EtaleLocalList
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PointsOfFibresCardinality
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.Specializations
public import StacksFrontier.AlgebraicGeometry.Spaces.JacobsonFiniteTypePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PointsOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.Topology.Jacobson.CounterexampleQuasiCompact

/-!
# A decent algebraic space is Jacobson exactly when its point space is

Let `X` be a decent algebraic space over a scheme `S`. **Stacks 0BA6** asserts that `X` is
Jacobson if and only if the topological space `|X|` is Jacobson. The two notions are a priori
different: being Jacobson is a property of the *space* `X`, namely that its étale charts by
schemes are Jacobson schemes, whereas `JacobsonSpace |X|` is a property of the topological
space of points of `X`.

## Main results

* `AlgebraicGeometry.Space.exists_jacobson_atlas_iff_jacobsonSpace_points`: **Stacks 0BA6**,
  the equivalence.
* `AlgebraicGeometry.Space.jacobsonSpace_points_of_exists_jacobson_atlas`: the implication
  from the space to its points.
* `AlgebraicGeometry.Space.jacobsonSpace_etaleChart_of_jacobsonSpace_points`: the implication
  from the points to the space, in the form the source proves it — every étale chart of `X`
  by a scheme is a Jacobson scheme.

## Implementation notes

As in `StacksFrontier/AlgebraicGeometry/Spaces/Jacobson.lean` (Stacks 0BA3) and
`StacksFrontier/AlgebraicGeometry/Spaces/JacobsonFiniteTypePoints.lean` (Stacks 0BA5), the
Jacobson property of `X` is written out as the existence of a surjective étale atlas by a
Jacobson scheme. By Stacks 03E8, `AlgebraicGeometry.Space.exists_atlas_iff_forall_etale`,
applied to the étale-local property `JacobsonSpace` of Stacks 03E7, that spelling is
equivalent to the source's — every scheme étale over `X` is Jacobson — so no generality is
lost in either direction of the equivalence.

The implication from the space to its points is the source's: the finite type points of `X`
are dense in every closed subset of `|X|` by Stacks 06EK, and for a decent Jacobson `X` they
are exactly the closed points of `|X|` by Stacks 0BA5.

For the converse, let `φ : h_U ⟶ X` be an étale chart and suppose `U` is not Jacobson. A
scheme is Kolmogorov and has a basis of quasi-compact opens, so Stacks 02I7 supplies a point
`u` of `U` which is not closed but whose singleton is locally closed. The chart is shrunk
twice by `AlgebraicGeometry.Space.exists_isAffine_etaleChart_range_subset`: first into the
open part of a presentation of `{u}` as a locally closed set, which makes `{u}` closed; then,
the fibre of the shrunken chart above `φ u` being finite because `X` is decent and free of
specializations by Stacks 03K5, into the complement of the closures of the other points of
that fibre. On the twice-shrunken chart `ψ` the fibre above `φ u` is exactly `{u}`, so the
image of the complement of `{u}` is the complement of `{φ u}` in the range of `ψ`; both are
open because an étale morphism is open on points, and therefore `{φ u}` is locally closed in
`|X|`. If `|X|` is Jacobson this forces `{φ u}` to be closed, whence the fibre of `φ` above
it is closed, and Stacks 03K5 collapses the closure of `{u}` inside that fibre to `{u}` —
contradicting the choice of `u`. This replaces the source's appeal to the invariance of
`{u}` under the relation `R = U ×_X U`: that the fibre of the shrunken chart is a singleton
is exactly the invariance the source extracts from `R`.

## References

* [Stacks Project, Tag 02I7](https://stacks.math.columbia.edu/tag/02I7)
* [Stacks Project, Tag 03E8](https://stacks.math.columbia.edu/tag/03E8)
* [Stacks Project, Tag 03K5](https://stacks.math.columbia.edu/tag/03K5)
* [Stacks Project, Tag 06EK](https://stacks.math.columbia.edu/tag/06EK)
* [Stacks Project, Tag 0BA5](https://stacks.math.columbia.edu/tag/0BA5)
* [Stacks Project, Tag 0BA6](https://stacks.math.columbia.edu/tag/0BA6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An étale chart of a represented presheaf by an affine scheme through a prescribed point
and with image inside a prescribed open neighbourhood of it: an affine open neighbourhood of
the corresponding point of the representing scheme inside that open is again an object of the
site, and its inclusion is an open immersion, hence étale and injective on points. -/
theorem exists_isAffine_etaleChart_range_subset (U : BigFppfOver B S hS)
    (W : Set (points B S hS (yoneda.obj U))) (hW : IsOpen W)
    (u : points B S hS (yoneda.obj U)) (hu : u ∈ W) :
    ∃ (V : BigFppfOver B S hS) (j : V ⟶ U) (v : points B S hS (yoneda.obj V)),
      IsAffine ((BigFppfOver.toScheme B S hS).obj V) ∧
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map j) ∧
      Function.Injective (pointsMap B S hS (yoneda.obj V) (yoneda.map j)) ∧
      Set.range (pointsMap B S hS (yoneda.obj V) (yoneda.map j)) ⊆ W ∧
      pointsMap B S hS (yoneda.obj V) (yoneda.map j) v = u := by
  have hWopen : IsOpen ((schemePointsHomeomorph B S hS U).symm ⁻¹' W) :=
    hW.preimage (schemePointsHomeomorph B S hS U).symm.continuous
  obtain ⟨A, hAaff, hAmem, hAsub⟩ :=
    exists_isAffineOpen_mem_and_subset (x := schemePointsHomeomorph B S hS U u)
      (U := ⟨_, hWopen⟩)
      (show schemePointsHomeomorph B S hS U u ∈ (schemePointsHomeomorph B S hS U).symm ⁻¹' W by
        simpa using hu)
  have hAsize : B.Contains (↑A : Scheme.{u}) :=
    (Scheme.size_coe_opens_le ((BigFppfOver.toScheme B S hS).obj U) A).trans_lt U.left.property
  let hAι : B.inclusion.obj (B.obj hAsize) ⟶ B.inclusion.obj U.left := A.ι
  let ι : (B.obj hAsize : B.Schemes) ⟶ U.left := B.inclusion.preimage hAι
  let V : BigFppfOver B S hS := Over.mk (ι ≫ U.hom)
  let j : V ⟶ U := Over.homMk ι
  have hjScheme : (BigFppfOver.toScheme B S hS).map j = A.ι := by
    change B.inclusion.map (B.inclusion.preimage hAι) = A.ι
    rw [B.inclusion.map_preimage]
  have hpm : ∀ y : points B S hS (yoneda.obj V),
      pointsMap B S hS (yoneda.obj V) (yoneda.map j) y =
        (schemePointsHomeomorph B S hS U).symm
          (A.ι (schemePointsHomeomorph B S hS V y)) := by
    intro y
    refine (schemePointsHomeomorph B S hS U).injective ?_
    rw [Homeomorph.apply_symm_apply, ← hjScheme]
    exact pointsToScheme_pointsMap B S hS j y
  have hinj : Function.Injective (pointsMap B S hS (yoneda.obj V) (yoneda.map j)) := by
    intro y₁ y₂ h
    rw [hpm y₁, hpm y₂] at h
    exact (schemePointsHomeomorph B S hS V).injective
      (A.ι.isOpenEmbedding.injective ((schemePointsHomeomorph B S hS U).symm.injective h))
  have hrange : Set.range (pointsMap B S hS (yoneda.obj V) (yoneda.map j)) ⊆ W := by
    rintro _ ⟨y, rfl⟩
    rw [hpm y]
    exact hAsub (A.range_ι.subset (Set.mem_range_self (schemePointsHomeomorph B S hS V y)))
  obtain ⟨q, hq⟩ : schemePointsHomeomorph B S hS U u ∈ Set.range (A.ι : ↑A → _) := by
    rwa [A.range_ι]
  refine ⟨V, j, (schemePointsHomeomorph B S hS V).symm q, hAaff, ?_, hinj, hrange, ?_⟩
  · exact (presheaf_yoneda_map_iff B S hS
      AlgebraicGeometry.Etale.etale_isStableUnderBaseChange j).2
      (by rw [hjScheme]; infer_instance)
  · rw [hpm, Homeomorph.apply_symm_apply, hq, Homeomorph.symm_apply_apply]

/-- **Stacks 0BA6**, the implication from the space to its points. Let `X` be a decent
algebraic space over `S` which is Jacobson, the Jacobson condition being written as the
existence of a surjective étale atlas by a Jacobson scheme. Then the topological space `|X|`
of points of `X` is a Jacobson topological space. -/
theorem jacobsonSpace_points_of_exists_jacobson_atlas
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X)
    (hJac : ∃ (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) a ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) a ∧
      JacobsonSpace ((BigFppfOver.toScheme B S hS).obj U)) :
    JacobsonSpace (points B S hS X) := by
  refine ⟨fun {Z} hZ ↦ ?_⟩
  have hZeq : Z ∩ closedPoints (points B S hS X) = Z ∩ finiteTypePoints B S hS X := by
    rw [finiteTypePoints_eq_setOf_isClosed_singleton B S hS hX hdec hJac]
    ext x
    simp
  rw [hZeq]
  exact closure_inter_finiteTypePoints B S hS X hX hZ

/-- A point `v` is closed if its image lies in a closed set `T` meeting the range of an
injective continuous map only in that image. -/
private theorem isClosed_singleton_of_inter_range_subset {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] {f : α → β} (hf : Continuous f) (hinj : Function.Injective f)
    {T : Set β} (hT : IsClosed T) {v : α} (hv : f v ∈ T) (hsub : T ∩ Set.range f ⊆ {f v}) :
    IsClosed {v} := by
  have : {v} = f ⁻¹' T := Set.ext fun y ↦
    ⟨fun h ↦ h ▸ hv, fun hy ↦ hinj (hsub ⟨hy, y, rfl⟩)⟩
  rw [this]
  exact hT.preimage hf

/-- **Stacks 0BA6**, the implication from the points to the space. Every étale chart by a
scheme of a decent algebraic space whose space of points is a Jacobson topological space is
a Jacobson scheme. -/
theorem jacobsonSpace_etaleChart_of_jacobsonSpace_points
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) (hJ : JacobsonSpace (points B S hS X))
    (U : BigFppfOver B S hS) (φ : yoneda.obj U ⟶ X)
    (hφ : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf φ) :
    JacobsonSpace ((BigFppfOver.toScheme B S hS).obj U) := by
  classical
  have : JacobsonSpace (points B S hS X) := hJ
  have hfin : HasFiniteChartFibersAtEveryPoint B S hS X :=
    hasFiniteChartFibersAtEveryPoint_of_isDecentSpace B S hS hdec
  have hQEc := inverseImage_isStableUnderComposition B S hS etale_isStableUnderComposition.{u}
  have hQEpc : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderComposition :=
    MorphismProperty.relative_isStableUnderComposition _
  suffices h : JacobsonSpace (points B S hS (yoneda.obj U)) by
    have := h
    exact JacobsonSpace.of_isOpenEmbedding
      (schemePointsHomeomorph B S hS U).symm.isOpenEmbedding
  have : T0Space (points B S hS (yoneda.obj U)) :=
    (schemePointsHomeomorph B S hS U).isEmbedding.t0Space
  have : PrespectralSpace (points B S hS (yoneda.obj U)) :=
    (schemePointsHomeomorph B S hS U).isOpenEmbedding.prespectralSpace
  by_contra hcon
  obtain ⟨u, hunc, O, Z, hO, hZ, hOZ⟩ :=
    main_theorem02I7 (points B S hS (yoneda.obj U)) inferInstance hcon
  obtain ⟨x, hx⟩ : ∃ x, pointsMap B S hS (yoneda.obj U) φ u = x := ⟨_, rfl⟩
  have huOZ : u ∈ O ∩ Z := by rw [← hOZ]; exact Set.mem_singleton u
  -- Shrink the chart into `O`, which makes the singleton of the chosen point closed.
  obtain ⟨V₁, j₁, v₁, hV₁aff, hj₁et, hj₁inj, hj₁rng, hj₁v⟩ :=
    exists_isAffine_etaleChart_range_subset B S hS U O hO u huOZ.1
  have hψ₁ : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map j₁ ≫ φ) :=
    MorphismProperty.comp_mem _ (yoneda.map j₁) φ hj₁et hφ
  have hv₁closed : IsClosed ({v₁} : Set (points B S hS (yoneda.obj V₁))) :=
    isClosed_singleton_of_inter_range_subset (continuous_pointsMap B S hS _) hj₁inj hZ
      (by rw [hj₁v]; exact huOZ.2)
      (fun _ ⟨hz, hr⟩ ↦ by rw [hj₁v, hOZ]; exact ⟨hj₁rng hr, hz⟩)
  have hv₁F : pointsMap B S hS (yoneda.obj V₁) (yoneda.map j₁ ≫ φ) v₁ = x := by
    rw [pointsMap_comp_apply, hj₁v]
    exact hx
  have hFfin : (pointsMap B S hS (yoneda.obj V₁) (yoneda.map j₁ ≫ φ) ⁻¹' {x}).Finite :=
    hfin x V₁ hV₁aff _ hψ₁
  -- Shrink again, away from the other points of the fibre above `x`.
  have hW₂open : IsOpen
      ((⋃ w ∈ (pointsMap B S hS (yoneda.obj V₁) (yoneda.map j₁ ≫ φ) ⁻¹' {x}) \ {v₁},
        closure {w})ᶜ) :=
    (hFfin.sdiff.isClosed_biUnion fun _ _ ↦ isClosed_closure).isOpen_compl
  have hv₁W₂ : v₁ ∈ (⋃ w ∈ (pointsMap B S hS (yoneda.obj V₁) (yoneda.map j₁ ≫ φ) ⁻¹' {x}) \ {v₁},
      closure {w})ᶜ := by
    intro hmem
    obtain ⟨w, hw, hv₁w⟩ := Set.mem_iUnion₂.1 hmem
    have hwx : pointsMap B S hS (yoneda.obj V₁) (yoneda.map j₁ ≫ φ) w = x := hw.1
    exact hw.2 (eq_of_specializes_of_pointsMap_eq_of_hasFiniteChartFibers B S hS hX hfin
      V₁ (yoneda.map j₁ ≫ φ) hψ₁ v₁ w (hv₁F.trans hwx.symm)
      (specializes_iff_mem_closure.2 hv₁w)).symm
  obtain ⟨V₂, j₂, v₂, hV₂aff, hj₂et, hj₂inj, hj₂rng, hj₂v⟩ :=
    exists_isAffine_etaleChart_range_subset B S hS V₁ _ hW₂open v₁ hv₁W₂
  have hψ₂ : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map j₂ ≫ yoneda.map j₁ ≫ φ) :=
    MorphismProperty.comp_mem _ (yoneda.map j₂) _ hj₂et hψ₁
  have hv₂closed : IsClosed ({v₂} : Set (points B S hS (yoneda.obj V₂))) :=
    isClosed_singleton_of_inter_range_subset (continuous_pointsMap B S hS _) hj₂inj hv₁closed
      (by rw [hj₂v]; rfl) (fun _ ⟨hz, _⟩ ↦ by rw [hj₂v]; exact hz)
  have hv₂x : pointsMap B S hS (yoneda.obj V₂) (yoneda.map j₂ ≫ yoneda.map j₁ ≫ φ) v₂ = x := by
    rw [pointsMap_comp_apply, hj₂v]
    exact hv₁F
  have hfib : pointsMap B S hS (yoneda.obj V₂) (yoneda.map j₂ ≫ yoneda.map j₁ ≫ φ) ⁻¹' {x} =
      {v₂} := by
    ext y
    refine ⟨fun hy ↦ ?_, ?_⟩
    · have hy' : pointsMap B S hS (yoneda.obj V₁) (yoneda.map j₁ ≫ φ)
          (pointsMap B S hS (yoneda.obj V₂) (yoneda.map j₂) y) = x := by
        rw [← pointsMap_comp_apply]
        exact hy
      have hyv₁ : pointsMap B S hS (yoneda.obj V₂) (yoneda.map j₂) y = v₁ := by
        by_contra hne
        exact hj₂rng ⟨y, rfl⟩ (Set.mem_iUnion₂.2 ⟨_, ⟨hy', hne⟩, subset_closure rfl⟩)
      exact hj₂inj (hyv₁.trans hj₂v.symm)
    · rintro rfl
      exact hv₂x
  -- The image of the twice-shrunken chart is open and meets the fibre above `x` only in
  -- `v₂`, so `{x}` is locally closed in `|X|`.
  have hpopen : IsOpenMap
      (pointsMap B S hS (yoneda.obj V₂) (yoneda.map j₂ ≫ yoneda.map j₁ ≫ φ)) :=
    isOpenMap_pointsMap_of_presheafEtale B S hS _ hψ₂
  have hlc : IsLocallyClosed ({x} : Set (points B S hS X)) := by
    refine ⟨Set.range (pointsMap B S hS (yoneda.obj V₂) (yoneda.map j₂ ≫ yoneda.map j₁ ≫ φ)),
      (pointsMap B S hS (yoneda.obj V₂) (yoneda.map j₂ ≫ yoneda.map j₁ ≫ φ) ''
        ({v₂}ᶜ : Set (points B S hS (yoneda.obj V₂))))ᶜ,
      hpopen.isOpen_range, (hpopen _ hv₂closed.isOpen_compl).isClosed_compl, ?_⟩
    ext y
    refine ⟨?_, ?_⟩
    · rintro rfl
      refine ⟨⟨v₂, hv₂x⟩, ?_⟩
      rintro ⟨w, hw, hwx⟩
      exact hw (show w ∈ ({v₂} : Set (points B S hS (yoneda.obj V₂))) from hfib ▸ hwx)
    · rintro ⟨⟨w, rfl⟩, hnot⟩
      by_contra hne
      exact hnot ⟨w, fun hwv₂ ↦ hne (by rw [show w = v₂ from hwv₂]; exact hv₂x), rfl⟩
  have hxclosed : IsClosed ({x} : Set (points B S hS X)) :=
    isClosed_singleton_of_isLocallyClosed_singleton hlc
  -- Hence the fibre of the original chart above `x` is closed, and carries no
  -- specialization, so the chosen point is closed after all.
  refine hunc (isClosed_of_closure_subset fun y hy ↦ ?_)
  have hyfib : pointsMap B S hS (yoneda.obj U) φ y = x :=
    closure_minimal (by rintro _ rfl; exact hx)
      (hxclosed.preimage (continuous_pointsMap B S hS φ)) hy
  exact eq_of_specializes_of_pointsMap_eq_of_hasFiniteChartFibers B S hS hX hfin U φ hφ
    y u (hyfib.trans hx.symm) (specializes_iff_mem_closure.2 hy)

/-- **Stacks 0BA6.** A decent algebraic space `X` over `S` is Jacobson — the Jacobson
condition being written as the existence of a surjective étale atlas by a Jacobson scheme —
if and only if its topological space `|X|` of points is a Jacobson topological space. -/
@[stacks 0BA6]
theorem exists_jacobson_atlas_iff_jacobsonSpace_points
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) :
    (∃ (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) a ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) a ∧
      JacobsonSpace ((BigFppfOver.toScheme B S hS).obj U)) ↔
    JacobsonSpace (points B S hS X) :=
  ⟨jacobsonSpace_points_of_exists_jacobson_atlas B S hS hX hdec, fun hJ ↦
    (exists_atlas_iff_forall_etale B S hS X (fun Y : Scheme.{u} ↦ JacobsonSpace Y) hX).2
      fun V g hg ↦ jacobsonSpace_etaleChart_of_jacobsonSpace_points B S hS hX hdec hJ V g hg⟩

end AlgebraicGeometry.Space

end
