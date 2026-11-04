module

public import StacksFrontier.AlgebraicGeometry.Spaces.LimitProjectionAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendOpens
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.PointTopology

/-!
# The topology of a limit of algebraic spaces, with no bound on the index

Let `D` be a cofiltered inverse system of algebraic spaces over `S` with affine transition
morphisms whose limit `limit D` is itself an algebraic space.  The library's Stacks 086V,
`AlgebraicGeometry.Space.pointTopology_limit`, and Stacks 0827 bound the index category by the
cofinality of the site's size cutoff, because they form the limit of the affine charts in the site
as the scheme limit.  Without the bound the scheme limit of the charts need not lie in the site,
but the site limit of the charts still exists when `limit D` is an algebraic space: it is the
closed subscheme `Spec(Γ(L)/K)` of the scheme limit `L` of
`AlgebraicGeometry.BigFppfOver.coverCone`.  A closed immersion is an embedding, so on its points
the preimages of opens of the charts still form a neighbourhood basis, which is all the argument
of Stacks 086V uses.

## Main results

Names are in the namespace `AlgebraicGeometry.Space`.

* `AffineChartSystem.exists_chartLimit_isClosedImmersion_of_isAlgebraicSpace`: a chart system of
  `D` has a limit in the site, closed in the limit of the schemes;
  `AffineChartSystem.exists_chartLimit_of_isAlgebraicSpace` gives the stagewise neighbourhood basis
  on its points, and `AffineChartSystem.exists_chartLimit_appTop_of_isAlgebraicSpace` that it is
  affine with every global function pulled back from a chart.
* `pointTopology_limit_of_isAlgebraicSpace`: Stacks 086V for `D`, with no bound on the index
  category.
* `exists_isOpenSubspace_isQuasiCompactSpace_preimage_eq_of_isAlgebraicSpace`: Stacks 0827 for
  `D`, with no bound on the index category.

## References

* [Stacks Project, Tag 086V](https://stacks.math.columbia.edu/tag/086V)
* [Stacks Project, Tag 0827](https://stacks.math.columbia.edu/tag/0827)
* [Stacks Project, Tag 07SF](https://stacks.math.columbia.edu/tag/07SF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

namespace AffineChartSystem

variable {I : Type u} [Category.{u} I] [IsCofiltered I] {i₀ : I}
  {D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U₀ : BigAffineFppf B S hS}
  {f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀}

/-- **A chart system of an inverse system with algebraic limit has a limit in the site, closed in
the limit of the schemes.**  For a cofiltered inverse system `D` of algebraic spaces with affine
transition morphisms whose limit is an algebraic space, every chart system of `D` has a limit in
the big fppf site of `S`, representing the base change of `limit.π D i₀`, whose underlying scheme
is a closed subscheme of the limit of the underlying schemes of the charts, the projections being
the restrictions of the limit projections.  No bound on the index category is needed. -/
theorem exists_chartLimit_isClosedImmersion_of_isAlgebraicSpace
    (C : AffineChartSystem B S hS i₀ D U₀ f₀)
    (hlim : IsAlgebraicSpace B S hS (limit D)) (hD₀ : IsAlgebraicSpace B S hS (D.obj i₀)) :
    ∃ (L : ChartLimit C) (e : Cone C.schemeDiagram) (_ : IsLimit e)
      (ι : (BigFppfOver.toScheme B S hS).obj L.cone.pt ⟶ e.pt),
      _root_.AlgebraicGeometry.IsClosedImmersion ι ∧
        ∀ j, (BigFppfOver.toScheme B S hS).map (L.cone.π.app j) = ι ≫ e.π.app j := by
  classical
  have hbase : IsLimit (stageBaseChangeCone B S hS i₀ D U₀ f₀) :=
    isLimitPullbackLimitOverPost B S hS D i₀ f₀
  have hP : IsLimit ((Cone.postcompose C.iso.inv).obj (stageBaseChangeCone B S hS i₀ D U₀ f₀)) :=
    (IsLimit.postcomposeInvEquiv C.iso _).symm hbase
  have hPalg : IsAlgebraicSpace B S hS (stageBaseChangeCone B S hS i₀ D U₀ f₀).pt :=
    isAlgebraicSpace_pullback B S hS _ _ hlim
      (isAlgebraicSpace_yoneda B S hS ((BigAffineFppf.inclusion B S hS).obj U₀)) hD₀
  obtain ⟨V, a, haS, haE⟩ := hPalg.exists_atlas
  have ha := isLocallySurjective_of_surjective_etale B S hS a haS haE
  have : ∀ k, IsAffine ((BigFppfOver.toScheme B S hS).obj (C.siteDiagram.obj k)) := C.isAffine_obj
  set c' := (Cone.postcompose C.iso.inv).obj (stageBaseChangeCone B S hS i₀ D U₀ f₀) with hc'
  set d := BigFppfOver.coverCone (c := c') C.siteDiagram a with hd
  have hdl : IsLimit d := BigFppfOver.isLimitCoverCone (c := c') C.siteDiagram hP ha
  have hpost : IsLimit ((Cone.postcompose C.iso.hom).obj (yoneda.mapCone d)) :=
    (IsLimit.postcomposeHomEquiv C.iso (yoneda.mapCone d)).symm (isLimitOfPreserves yoneda hdl)
  exact ⟨{ cone := d
           isLimit := hdl
           iso := hpost.conePointUniqueUpToIso hbase
           iso_comp_π := fun j ↦ hpost.conePointUniqueUpToIso_hom_comp hbase j },
    limit.cone _, limit.isLimit _, BigFppfOver.coverι (c := c') C.siteDiagram a, by
      rw [BigFppfOver.coverι]
      exact @_root_.AlgebraicGeometry.IsClosedImmersion.comp _ _ _ _ _
        (_root_.AlgebraicGeometry.IsClosedImmersion.spec_of_surjective _
          Ideal.Quotient.mk_surjective) inferInstance,
    fun j ↦ BigFppfOver.toScheme_map_coverCone_π (c := c') C.siteDiagram a j⟩

/-- **A chart system of an inverse system with algebraic limit has a limit in the site.**  For a
cofiltered inverse system `D` of algebraic spaces with affine transition morphisms whose limit is
an algebraic space, every chart system of `D` has a limit in the big fppf site of `S`,
representing the base change of `limit.π D i₀`, on whose points the preimages of open sets of
the charts form a neighbourhood basis.  No bound on the index category is needed. -/
theorem exists_chartLimit_of_isAlgebraicSpace (C : AffineChartSystem B S hS i₀ D U₀ f₀)
    (hlim : IsAlgebraicSpace B S hS (limit D)) (hD₀ : IsAlgebraicSpace B S hS (D.obj i₀)) :
    ∃ L : ChartLimit C,
      ∀ (a : points B S hS (yoneda.obj L.cone.pt)) (U : Set (points B S hS (yoneda.obj L.cone.pt))),
        IsOpen U → a ∈ U →
        ∃ (j : Over i₀) (V : Set (points B S hS (yoneda.obj (C.siteDiagram.obj j)))),
          IsOpen V ∧ pointsMap B S hS (yoneda.obj L.cone.pt) (yoneda.map (L.cone.π.app j)) a ∈ V ∧
          ∀ a', pointsMap B S hS (yoneda.obj L.cone.pt) (yoneda.map (L.cone.π.app j)) a' ∈ V →
            a' ∈ U := by
  classical
  obtain ⟨L, e, he, ι, hι, hπ⟩ :=
    C.exists_chartLimit_isClosedImmersion_of_isAlgebraicSpace B S hS hlim hD₀
  refine ⟨L, ?_⟩
  have _ : ∀ {j k : Over i₀} (g : j ⟶ k),
      _root_.AlgebraicGeometry.IsAffineHom (C.schemeDiagram.map g) := fun g ↦ C.isAffineHom_map g
  have _ : ∀ k, IsAffine (C.schemeDiagram.obj k) := C.isAffine_obj
  -- the scheme-level neighbourhood basis, through the closed immersion into the scheme limit
  have hscheme : ∀ (x : (BigFppfOver.toScheme B S hS).obj L.cone.pt)
      (U' : Set ((BigFppfOver.toScheme B S hS).obj L.cone.pt)), IsOpen U' → x ∈ U' →
      ∃ (j : Over i₀) (V : Set ((BigFppfOver.toScheme B S hS).obj (C.siteDiagram.obj j))),
        IsOpen V ∧ (BigFppfOver.toScheme B S hS).map (L.cone.π.app j) x ∈ V ∧
        ∀ y, (BigFppfOver.toScheme B S hS).map (L.cone.π.app j) y ∈ V → y ∈ U' := by
    intro x U' hU' hx
    have hemb : Topology.IsEmbedding ι := ι.isClosedEmbedding.isEmbedding
    obtain ⟨U'', hU'', hpre⟩ := hemb.isInducing.isOpen_iff.1 hU'
    obtain ⟨j, V, hV, hmem, hsub⟩ := exists_isOpen_stage_nbhd_of_isLimit C.schemeDiagram e he
      (ι x) U'' hU'' (by rw [← hpre] at hx; exact hx)
    refine ⟨j, V, hV, ?_, fun y hy => ?_⟩
    · rw [hπ]
      exact hmem
    · rw [hπ] at hy
      have := hsub _ hy
      rw [← hpre]
      exact this
  intro x U hU hx
  obtain ⟨j, V, hV, hmem, hsub⟩ := hscheme (schemePointsHomeomorph B S hS L.cone.pt x)
    ((schemePointsHomeomorph B S hS L.cone.pt).symm ⁻¹' U)
    (hU.preimage (schemePointsHomeomorph B S hS L.cone.pt).symm.continuous) (by simpa using hx)
  refine ⟨j, schemePointsHomeomorph B S hS (C.siteDiagram.obj j) ⁻¹' V,
    hV.preimage (schemePointsHomeomorph B S hS (C.siteDiagram.obj j)).continuous, ?_, ?_⟩
  · simpa only [Set.mem_preimage, schemePointsHomeomorph_apply, pointsToScheme_pointsMap]
      using hmem
  · intro a' ha'
    rw [Set.mem_preimage, schemePointsHomeomorph_apply, pointsToScheme_pointsMap] at ha'
    have hmemU := hsub (schemePointsHomeomorph B S hS L.cone.pt a') ha'
    rwa [Set.mem_preimage, Homeomorph.symm_apply_apply] at hmemU

/-- **Global functions on the limit of a chart system come from a chart.**  For a cofiltered
inverse system `D` of algebraic spaces with affine transition morphisms whose limit is an
algebraic space, every chart system of `D` has a limit in the big fppf site of `S` whose
underlying scheme is affine and every global function on which is pulled back from one of the
charts.  No bound on the index category is needed. -/
theorem exists_chartLimit_appTop_of_isAlgebraicSpace (C : AffineChartSystem B S hS i₀ D U₀ f₀)
    (hlim : IsAlgebraicSpace B S hS (limit D)) (hD₀ : IsAlgebraicSpace B S hS (D.obj i₀)) :
    ∃ L : ChartLimit C, IsAffine ((BigFppfOver.toScheme B S hS).obj L.cone.pt) ∧
      ∀ s : Γ((BigFppfOver.toScheme B S hS).obj L.cone.pt, ⊤),
        ∃ (j : Over i₀) (y : Γ(C.schemeDiagram.obj j, ⊤)),
          ((BigFppfOver.toScheme B S hS).map (L.cone.π.app j)).appTop y = s := by
  obtain ⟨L, e, he, ι, hι, hπ⟩ :=
    C.exists_chartLimit_isClosedImmersion_of_isAlgebraicSpace B S hS hlim hD₀
  have _ : ∀ k, IsAffine (C.schemeDiagram.obj k) := C.isAffine_obj
  have _ : IsAffine e.pt := Scheme.isAffine_of_isLimit _ he
  obtain ⟨haff, hsurj⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine ι
  refine ⟨L, haff, fun s => ?_⟩
  obtain ⟨t, rfl⟩ := hsurj s
  obtain ⟨j, y, rfl⟩ := exists_appTop_π_eq_of_isAffine_of_isLimit C.schemeDiagram _ he t
  exact ⟨j, y, by rw [hπ, Scheme.Hom.comp_appTop]; rfl⟩

end AffineChartSystem

/-- **Stacks 086V with no bound on the index.**  The point topology of the limit of a cofiltered
inverse system of algebraic spaces over `S` with affine transition morphisms is the inverse-limit
topology, as soon as that limit is an algebraic space. -/
theorem pointTopology_limit_of_isAlgebraicSpace {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    (hlim : IsAlgebraicSpace B S hS (limit D)) :
    pointTopology B S hS (limit D) =
      ⨅ i : I, TopologicalSpace.induced (pointsMap B S hS (limit D) (limit.π D i))
        (pointTopology B S hS (D.obj i)) :=
  pointTopology_limit_of_chartLimit B S hS D hD hAffine fun i₀ U₀ f₀ _ ↦
    (affineChartSystem B S hS i₀ D U₀ f₀ hAffine).exists_chartLimit_of_isAlgebraicSpace B S hS
      hlim (hD i₀)

/-- **Stacks 0827 with no bound on the index.**  Let `D` be a cofiltered inverse system of
algebraic spaces over `S` with affine transition morphisms whose limit is an algebraic space.
Then every quasi-compact open subspace of `limit D` is the inverse image of a quasi-compact open
subspace of some stage. -/
theorem exists_isOpenSubspace_isQuasiCompactSpace_preimage_eq_of_isAlgebraicSpace {I : Type u}
    [Category.{u} I] [IsCofiltered I] (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    (hlim : IsAlgebraicSpace B S hS (limit D))
    (U : Subfunctor (limit D)) (hU : IsOpenSubspace B S hS U)
    (hUqc : IsQuasiCompactSpace B S hS U.toFunctor) :
    ∃ (i : I) (V : Subfunctor (D.obj i)), IsOpenSubspace B S hS V ∧
      IsQuasiCompactSpace B S hS V.toFunctor ∧ V.preimage (limit.π D i) = U :=
  exists_isOpenSubspace_isQuasiCompactSpace_preimage_eq_of_pointTopology B S hS D
    (pointTopology_limit_of_isAlgebraicSpace B S hS D hD hAffine hlim) hlim hD U hU hUqc

end AlgebraicGeometry.Space
