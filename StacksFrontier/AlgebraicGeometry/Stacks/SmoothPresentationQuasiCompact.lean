module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FromLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopologyUnique
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactTopology
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothMorphismProperty
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStack
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactStack
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyRepresented
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeSmooth
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentingMapFunctorial

/-!
# Quasi-compact algebraic stacks and smooth presentations

An algebraic stack over `S` is quasi-compact exactly when it admits a surjective smooth
1-morphism from an affine scheme; equivalently from a quasi-compact scheme, from a quasi-compact
algebraic space, or, dropping smoothness, when there is a surjective 1-morphism onto it from
some quasi-compact algebraic stack.

## Main definitions

* `AlgebraicGeometry.Stack.schemeFibredCategoryEquivalence`: the equivalence over the site
  between the two models of a scheme over `S` as a category fibred in groupoids.
* `AlgebraicGeometry.Stack.HasAffineSmoothPresentation`: a surjective smooth presentation by an
  affine scheme.
* `AlgebraicGeometry.Stack.HasQuasiCompactSchemeSmoothPresentation` and
  `AlgebraicGeometry.Stack.HasQuasiCompactSpaceSmoothPresentation`: the same by a quasi-compact
  scheme, respectively a quasi-compact algebraic space.
* `AlgebraicGeometry.Stack.HasQuasiCompactStackSurjection`: a surjection from a quasi-compact
  algebraic stack.

## Main results

* `isQuasiCompactStack_iff_hasAffineSmoothPresentation`: an algebraic stack is quasi-compact if and
  only if it has a surjective smooth presentation by an affine scheme.
* `hasAffineSmoothPresentation_iff_hasQuasiCompactSchemeSmoothPresentation`: a surjective smooth
  presentation by an affine scheme exists if and only if one by a quasi-compact scheme does.
* `hasQuasiCompactSchemeSmoothPresentation_iff_hasQuasiCompactSpaceSmoothPresentation`: a
  surjective smooth presentation by a quasi-compact scheme exists if and only if one by a
  quasi-compact algebraic space does.
* `hasQuasiCompactSpaceSmoothPresentation_iff_hasQuasiCompactStackSurjection`: a surjective smooth
  presentation by a quasi-compact algebraic space exists if and only if there is a surjection from
  a quasi-compact algebraic stack.

## References

* [Stacks Project, Tag 04YC](https://stacks.math.columbia.edu/tag/04YC)
-/

@[expose] public section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Comparing the two models of a scheme as an algebraic stack -/

/-- The slice of the big fppf site over `U` and the category of elements of the presheaf `U`
represents are equivalent over the site. -/
noncomputable def schemeFibredCategoryEquivalence (U : BigFppfOver B S hS) :
    BasedCategory.Equivalence (schemeFibredCategory B S hS U).val
      (fibredCategory B S hS (yoneda.obj U)).val :=
  ((PresheafOfCategories.sliceElementsEquivalenceOver U).trans
    (spaceEquivalenceOver B S hS (yoneda.obj U)).symm).toBasedEquivalence

/-! ### Smoothness of a morphism of represented objects -/

/-- A smooth morphism of the big fppf site of `S` is a smooth morphism of the represented
algebraic spaces. -/
private theorem isSmooth_yonedaMap_of_smooth {U V : BigFppfOver B S hS} (j : U ⟶ V)
    (hj : Smooth ((BigFppfOver.toScheme B S hS).map j)) :
    Space.IsSmooth B S hS (yoneda.map j) :=
  let _ : MorphismProperty.IsLocalAtTarget (@Smooth.{u}) Scheme.fppfPrecoverage :=
    MorphismProperty.IsLocalAtTarget.of_le Scheme.fppfPrecoverage_le_fpqcPrecoverage
  (Space.holdsOnEveryEtaleChart_iff_relative B S hS _
    smooth_isEtaleLocalOnSourceAndTarget
    (isAlgebraicSpace_yoneda B S hS U) (isAlgebraicSpace_yoneda B S hS V)
    (yoneda.map j) (Functor.relativelyRepresentable.map yoneda j)).2
    ((Space.presheaf_yoneda_map_iff B S hS smooth_isStableUnderBaseChange j).2 hj)

/-- A smooth morphism of algebraic spaces induces a smooth 1-morphism of the attached categories
of elements. -/
private theorem isRelativelySmooth_associatedMap_of_isSmooth
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (a : F ⟶ G) (ha : Space.IsSmooth B S hS a) :
    IsRelativelySmooth B S hS (associatedMap B S hS a).1 := by
  have hrep : IsRepresentableByAlgebraicSpaces B S hS (associatedMap B S hS a).1.hom :=
    isRepresentableByAlgebraicSpaces_of_isRepresentableByAlgebraicSpace B S hS
      (associatedMap B S hS a).1
      (isRepresentableByAlgebraicSpace_fibredCategory B S hS F hF)
      (isRepresentableByAlgebraicSpace_fibredCategory B S hS G hG)
  refine ⟨hrep, (hasRelativeProperty_iff_prop_representingMap.{u, u} B S hS
    (Space.smoothMorphismProperty B S hS) (associatedMap B S hS a).1 hrep F G hF hG
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _)).2 ?_⟩
  rwa [representingMap_associatedMap]

/-! ### Points of a quasi-compact scheme -/

/-- The point space of a quasi-compact scheme over `S`, read as an algebraic space, is
compact. -/
private theorem representedPointsCompact (U : BigFppfOver B S hS)
    [CompactSpace ((BigFppfOver.toScheme B S hS).obj U)] :
    @CompactSpace (Space.points B S hS (yoneda.obj U))
      (Space.pointTopology B S hS (yoneda.obj U)) :=
  let _ : TopologicalSpace (Space.points B S hS (yoneda.obj U)) :=
    Space.pointTopology B S hS (yoneda.obj U)
  (Space.schemePointsHomeomorph B S hS U).symm.compactSpace

/-! ### The canonical map on points of a chart precomposed with a morphism of spaces -/

/-- Precomposing a chart with the 1-morphism attached to a morphism of algebraic spaces acts on
points by the map on points of that morphism. -/
private theorem spacePointMap_associatedMap_comp
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (h : F ⟶ G)
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (b : (fibredCategory B S hS G).val ⥤ᵇ 𝒳.val) :
    spacePointMap B S hS F 𝒳 (((associatedMap B S hS h).1.hom).comp b) =
      spacePointMap B S hS G 𝒳 b ∘ Space.pointsMap B S hS F h := by
  funext x
  induction x using Quot.inductionOn with
  | h p =>
    let assoc := associatedMap B S hS h
    let src := spaceFieldValuedPoint B S hS F p
    let mid := spaceFieldValuedPoint B S hS G (Space.FieldValuedPoint.map B S hS F h p)
    have hbase : ((CatFiberedInGroupoids.homFunctor assoc.1).obj src.obj).base = mid.obj.base :=
      BasedFunctor.w_obj assoc.1.hom src.obj
    have hobj : (CatFiberedInGroupoids.homFunctor assoc.1).obj src.obj = mid.obj :=
      Pseudofunctor.CoGrothendieck.ext hbase (assoc.2 src.obj)
    have hobj' : (fieldValuedPointMap B S hS (fibredCategory B S hS F).val
          ((assoc.1.hom).comp b) src).obj =
        (fieldValuedPointMap B S hS (fibredCategory B S hS G).val b mid).obj :=
      congrArg b.toFunctor.obj hobj
    calc
      spacePointMap B S hS F 𝒳 ((assoc.1.hom).comp b) (p.class B S hS F) =
          pointClass B S hS 𝒳.val 𝒳.property
            (fieldValuedPointMap B S hS (fibredCategory B S hS F).val
              ((assoc.1.hom).comp b) src) :=
        spacePointMap_class B S hS F 𝒳 ((assoc.1.hom).comp b) p
      _ = pointClass B S hS 𝒳.val 𝒳.property
            (fieldValuedPointMap B S hS (fibredCategory B S hS G).val b mid) :=
        (class_eq_class_iff_hasCommonExtension B S hS 𝒳.val 𝒳.property _ _).2
          ⟨fieldValuedPointMap B S hS (fibredCategory B S hS F).val
            ((assoc.1.hom).comp b) src, ⟨𝟙 _⟩, ⟨eqToHom hobj'⟩⟩
      _ = spacePointMap B S hS G 𝒳 b
            ((Space.FieldValuedPoint.map B S hS F h p).class B S hS G) :=
        (spacePointMap_class B S hS G 𝒳 b (Space.FieldValuedPoint.map B S hS F h p)).symm
      _ = (spacePointMap B S hS G 𝒳 b ∘ Space.pointsMap B S hS F h) (p.class B S hS F) :=
        congrArg (spacePointMap B S hS G 𝒳 b) (Space.pointsMap_class B S hS F h p).symm

/-! ### Refining an open surjection by an affine scheme -/

/-- An open surjection from the points of a scheme `U` over `S` onto a compact space is refined
by an affine scheme smooth over `U`. -/
private theorem exists_affine_refinement_of_open_surjective
    (U : BigFppfOver B S hS) {Z : Type*} [TopologicalSpace Z] [CompactSpace Z]
    (m : Space.points B S hS (yoneda.obj U) → Z)
    (hmOpen : @IsOpenMap _ _ (Space.pointTopology B S hS (yoneda.obj U)) _ m)
    (hmSurj : Function.Surjective m) :
    ∃ (A : BigFppfOver B S hS) (k : A ⟶ U),
      IsAffine ((BigFppfOver.toScheme B S hS).obj A) ∧
        Smooth ((BigFppfOver.toScheme B S hS).map k) ∧
          Function.Surjective
            (m ∘ Space.pointsMap B S hS (yoneda.obj A) (yoneda.map k)) := by
  classical
  let T := BigFppfOver.toScheme B S hS
  let X := T.obj U
  let _ : TopologicalSpace (Space.points B S hS (yoneda.obj U)) :=
    Space.pointTopology B S hS (yoneda.obj U)
  have hv (i : X.affineOpens) : B.Contains i.1.toScheme :=
    Scheme.size_lt_of_isOpenImmersion i.1.ι U.left.property
  let V (i : X.affineOpens) : BigFppfOver B S hS :=
    Over.mk (⟨i.1.ι ≫ B.inclusion.map U.hom⟩ : B.obj (hv i) ⟶ B.obj hS)
  let j (i : X.affineOpens) : V i ⟶ U := Over.homMk ⟨i.1.ι⟩ (by rfl)
  have hj (i : X.affineOpens) : T.map (j i) = i.1.ι := rfl
  let W (i : X.affineOpens) :=
    Set.range (Space.pointsMap B S hS (yoneda.obj (V i)) (yoneda.map (j i)))
  have hW (i : X.affineOpens) : IsOpen (W i) := by
    let _ : TopologicalSpace (Space.points B S hS (yoneda.obj (V i))) :=
      Space.pointTopology B S hS (yoneda.obj (V i))
    have hEt : Etale (T.map (j i)) := by rw [hj]; infer_instance
    have h := Space.isOpenMap_pointsMap_of_etale B S hS
      (isAlgebraicSpace_yoneda B S hS U) (V i) (yoneda.map (j i))
      ((Space.presheaf_yoneda_map_etale_iff B S hS (j i)).2 hEt)
    rw [show W i = Space.pointsMap B S hS (yoneda.obj (V i)) (yoneda.map (j i)) '' Set.univ from
      Set.image_univ.symm]
    exact h _ isOpen_univ
  have hcover : (Set.univ : Set Z) ⊆ ⋃ i, m '' W i := by
    intro x _
    obtain ⟨y, rfl⟩ := hmSurj x
    obtain ⟨i, ⟨V₀, hV₀, rfl⟩, hpV₀, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open
        (show Space.pointsToScheme B S hS U y ∈ (Set.univ : Set X) from trivial)
        isOpen_univ
    let i : X.affineOpens := ⟨V₀, hV₀⟩
    obtain ⟨z, hz⟩ := Space.surjective_pointsToScheme B S hS (V i)
      (show (T.obj (V i) : Type u) from ⟨_, hpV₀⟩)
    have hyz : Space.pointsMap B S hS (yoneda.obj (V i)) (yoneda.map (j i)) z = y := by
      refine Space.injective_pointsToScheme B S hS U ?_
      rw [Space.pointsToScheme_pointsMap, hz]
      rfl
    exact Set.mem_iUnion.mpr ⟨i, y, ⟨z, hyz⟩, rfl⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun i => m '' W i)
    (fun i => hmOpen _ (hW i)) hcover
  let _ : Finite { i : X.affineOpens // i ∈ s } := s.finite_toSet
  let Y (i : s) : Scheme.{u} := i.val.1.toScheme
  let d : (∐ Y) ⟶ X := Limits.Sigma.desc (fun i : s => i.val.1.ι)
  let _ : IsZariskiLocalAtSource (@Smooth.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Smooth)
  have hd : Smooth d := IsZariskiLocalAtSource.sigmaDesc (fun i : s => by
    change Smooth i.val.1.ι; infer_instance)
  have hY : B.Contains (∐ Y) := Scheme.size_sigmaObj_lt B.aleph0_lt_cutoff
    B.aleph0_lt_cutoff_cof Cardinal.mk_le_aleph0 Y (fun i => hv i.val)
  let A : BigFppfOver B S hS :=
    Over.mk (⟨d ≫ B.inclusion.map U.hom⟩ : B.obj hY ⟶ B.obj hS)
  let k : A ⟶ U := Over.homMk ⟨d⟩ (by rfl)
  let l (i : s) : V i.val ⟶ A := Over.homMk ⟨Limits.Sigma.ι Y i⟩ (by
    apply ObjectProperty.hom_ext
    change Limits.Sigma.ι Y i ≫ (d ≫ B.inclusion.map U.hom) = _
    rw [← Category.assoc, Limits.Sigma.ι_comp_desc]
    rfl)
  have hl (i : s) : l i ≫ k = j i.val :=
    Over.OverMorphism.ext (ObjectProperty.hom_ext _ (Limits.Sigma.ι_comp_desc _ i))
  refine ⟨A, k, ?_, (show T.map k = d from rfl) ▸ hd, ?_⟩
  · change IsAffine (∐ Y)
    let instAff (i : s) : IsAffine (Y i) := i.val.2
    infer_instance
  · intro x
    obtain ⟨i, hi, q, hq, hx⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
    obtain ⟨p, hp⟩ := hq
    refine ⟨Space.pointsMap B S hS (yoneda.obj (V i)) (yoneda.map (l ⟨i, hi⟩)) p, ?_⟩
    have hcomp : Space.pointsMap B S hS (yoneda.obj A) (yoneda.map k)
          (Space.pointsMap B S hS (yoneda.obj (V i)) (yoneda.map (l ⟨i, hi⟩)) p) =
        Space.pointsMap B S hS (yoneda.obj (V i)) (yoneda.map (j i)) p := by
      have h := congrFun (Space.pointsMap_comp B S hS (yoneda.obj (V i))
        (yoneda.map (l ⟨i, hi⟩)) (yoneda.map k)).symm p
      rwa [← Functor.map_comp, hl ⟨i, hi⟩] at h
    change m (Space.pointsMap B S hS (yoneda.obj A) (yoneda.map k) _) = x
    rwa [hcomp, hp]

/-! ### The five conditions -/

variable (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- A surjective smooth presentation of an algebraic stack by an affine scheme. -/
abbrev HasAffineSmoothPresentation : Prop :=
  ∃ U : BigFppfOver B S hS,
    IsAffine ((BigFppfOver.toScheme B S hS).obj U) ∧
      let 𝒰 : AlgebraicStacks.{u, w} B S hS :=
        ⟨schemeFibredCategory B S hS U,
          (isDeligneMumfordStack_schemeFibredCategory.{u, w} B S hS U).1⟩
      ∃ f : 𝒰 ⟶ 𝒳, IsSurjective B S hS f ∧ IsRelativelySmooth B S hS f.hom

/-- A surjective smooth presentation of an algebraic stack by a quasi-compact scheme. -/
abbrev HasQuasiCompactSchemeSmoothPresentation : Prop :=
  ∃ U : BigFppfOver B S hS,
    CompactSpace ((BigFppfOver.toScheme B S hS).obj U) ∧
      let 𝒰 : AlgebraicStacks.{u, w} B S hS :=
        ⟨schemeFibredCategory B S hS U,
          (isDeligneMumfordStack_schemeFibredCategory.{u, w} B S hS U).1⟩
      ∃ f : 𝒰 ⟶ 𝒳, IsSurjective B S hS f ∧ IsRelativelySmooth B S hS f.hom

/-- A surjective smooth presentation of an algebraic stack by a quasi-compact algebraic
space. -/
abbrev HasQuasiCompactSpaceSmoothPresentation : Prop :=
  ∃ (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F),
    Space.IsQuasiCompactSpace B S hS F ∧
      let 𝒰 : AlgebraicStacks.{u, w} B S hS :=
        ⟨fibredCategory B S hS F,
          (isDeligneMumfordStack_fibredCategory.{u, w} B S hS F hF).1⟩
      ∃ f : 𝒰 ⟶ 𝒳, IsSurjective B S hS f ∧ IsRelativelySmooth B S hS f.hom

/-- A surjection onto an algebraic stack from a quasi-compact algebraic stack. -/
abbrev HasQuasiCompactStackSurjection : Prop :=
  ∃ (𝒰 : AlgebraicStacks.{u, w} B S hS) (f : 𝒰 ⟶ 𝒳),
    IsQuasiCompactStack.{u, w} B S hS 𝒰.val 𝒰.property ∧ IsSurjective B S hS f

/-- A surjective smooth presentation by a quasi-compact scheme gives one by the quasi-compact
algebraic space it represents. -/
private theorem hasQuasiCompactSpaceSmoothPresentation_of_scheme
    (U : BigFppfOver B S hS) (hU : CompactSpace ((BigFppfOver.toScheme B S hS).obj U))
    (f : schemeFibredCategory B S hS U ⟶ 𝒳.val)
    (hsurj : Function.Surjective (pointsMap B S hS (schemeFibredCategory B S hS U).val
      (schemeFibredCategory B S hS U).property 𝒳.val.property f.hom))
    (hsmooth : IsRelativelySmooth B S hS f) :
    HasQuasiCompactSpaceSmoothPresentation.{u, w} B S hS 𝒳 := by
  let F := yoneda.obj U
  have hF := isAlgebraicSpace_yoneda B S hS U
  let _ : CompactSpace ((BigFppfOver.toScheme B S hS).obj U) := hU
  let _ : TopologicalSpace (Space.points B S hS F) := Space.pointTopology B S hS F
  let _ : CompactSpace (Space.points B S hS F) := representedPointsCompact B S hS U
  have hFqc : Space.IsQuasiCompactSpace B S hS F :=
    (Space.isQuasiCompactSpace_iff_compactSpace_points B S hS F hF).2 inferInstance
  let e := schemeFibredCategoryEquivalence B S hS U
  let 𝒰space : AlgebraicStacks.{u, w} B S hS :=
    ⟨fibredCategory B S hS F, (isDeligneMumfordStack_fibredCategory.{u, w} B S hS F hF).1⟩
  let f' : 𝒰space ⟶ 𝒳 :=
    Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
      (BasedFunctor.comp e.inverse f.hom))
  let _ : Functor.IsEquivalence e.inverse.toFunctor := e.equiv.isEquivalence_inverse
  let _ : Functor.IsEquivalence (BasedFunctor.id 𝒳.val.val).toFunctor :=
    inferInstanceAs (Functor.IsEquivalence (𝟭 𝒳.val.val.obj))
  refine ⟨F, hF, hFqc, f', ?_, ?_⟩
  · intro x
    obtain ⟨y, hy⟩ := hsurj x
    obtain ⟨z, hz⟩ := pointsMap_surjective_of_basedEquivalence B S hS
      (𝒜 := fibredCategory B S hS F) (𝒞 := schemeFibredCategory B S hS U) e.symm y
    refine ⟨z, ?_⟩
    change pointsMap B S hS 𝒰space.val.val 𝒰space.val.property 𝒳.val.property
      (BasedFunctor.comp e.inverse f.hom) z = x
    rwa [← pointsMap_comp B S hS 𝒰space.val.val 𝒰space.val.property
      (schemeFibredCategory B S hS U).property 𝒳.val.property e.inverse f.hom z,
      show pointsMap B S hS 𝒰space.val.val 𝒰space.val.property
        (schemeFibredCategory B S hS U).property e.inverse z = y from hz]
  · exact isRelativelySmooth_of_equivalences B S hS
      (Bicategory.InducedBicategory.mkHom (BasedFunctor.comp e.inverse f.hom) :
        fibredCategory B S hS F ⟶ 𝒳.val)
      f e.inverse (BasedFunctor.id 𝒳.val.val) (Iso.refl _) hsmooth

/-- An algebraic stack with a surjective smooth presentation by a quasi-compact algebraic space
is quasi-compact. -/
private theorem isQuasiCompactStack_of_hasQuasiCompactSpaceSmoothPresentation
    (h : HasQuasiCompactSpaceSmoothPresentation.{u, w} B S hS 𝒳) :
    IsQuasiCompactStack.{u, w} B S hS 𝒳.val 𝒳.property := by
  obtain ⟨F, hF, hFqc, f, hsurj, -⟩ := h
  exact isQuasiCompactStack_of_isSurjective B S hS f
    (isQuasiCompactStack_fibredCategory B S hS F hF hFqc _) hsurj

/-- A quasi-compact algebraic stack has a surjective smooth presentation by an affine
scheme. -/
private theorem hasAffineSmoothPresentation_of_isQuasiCompactStack
    (h𝒳qc : IsQuasiCompactStack.{u, w} B S hS 𝒳.val 𝒳.property) :
    HasAffineSmoothPresentation.{u, w} B S hS 𝒳 := by
  classical
  obtain ⟨_hFib, -, -, U, fU, hfU, hAtlas⟩ := 𝒳.property
  have hU := isAlgebraicSpace_yoneda B S hS U
  let e := schemeFibredCategoryEquivalence B S hS U
  let aU := e.inverse
  let b := BasedFunctor.comp aU fU
  let _ : Functor.IsEquivalence aU.toFunctor := e.equiv.isEquivalence_inverse
  let _ : Functor.IsEquivalence (BasedFunctor.id 𝒳.val.val).toFunctor :=
    inferInstanceAs (Functor.IsEquivalence (𝟭 𝒳.val.val.obj))
  let _ : TopologicalSpace (Space.points B S hS (yoneda.obj U)) :=
    Space.pointTopology B S hS (yoneda.obj U)
  let _ : TopologicalSpace (points B S hS 𝒳.val.val 𝒳.val.property) :=
    pointTopology B S hS 𝒳.val
  let _ : CompactSpace (points B S hS 𝒳.val.val 𝒳.val.property) := h𝒳qc
  let 𝒰scheme : AlgebraicStacks.{u, w} B S hS :=
    ⟨schemeFibredCategory B S hS U, isAlgebraicStack_schemeFibredCategory B S hS U⟩
  let fa : 𝒰scheme ⟶ 𝒳 := Bicategory.InducedBicategory.mkHom
    (Bicategory.InducedBicategory.mkHom fU)
  have hfaSurj := (pointsMap_surjective_iff_isRelativelySurjective.{u, w, u} B S hS
    fa hfU).2 (fun V y hy G hG hE => (hAtlas V y hy G hG hE).1)
  have hbSurj : Function.Surjective (spacePointMap B S hS (yoneda.obj U) 𝒳.val b) := by
    rw [spacePointMap_comp B S hS (yoneda.obj U) (schemeFibredCategory B S hS U) 𝒳.val aU fU]
    exact hfaSurj.comp ((spacePointMap_surjective_iff_pointsMap_surjective B S hS
      (yoneda.obj U) (schemeFibredCategory B S hS U) aU).2
      (pointsMap_surjective_of_basedEquivalence B S hS
        (𝒜 := fibredCategory B S hS (yoneda.obj U))
        (𝒞 := schemeFibredCategory B S hS U) e.symm))
  have hbSmooth : IsRelativelySmooth B S hS
      (Bicategory.InducedBicategory.mkHom b :
        fibredCategory B S hS (yoneda.obj U) ⟶ 𝒳.val) := by
    refine isRelativelySmooth_of_equivalences B S hS _
      (Bicategory.InducedBicategory.mkHom fU : schemeFibredCategory B S hS U ⟶ 𝒳.val)
      aU (BasedFunctor.id 𝒳.val.val) (Iso.refl _)
      ⟨hfU, fun V y hy G hG hE ↦ (hAtlas V y hy G hG hE).2⟩
  have hbOpen : @IsOpenMap _ _ (Space.pointTopology B S hS (yoneda.obj U))
      (pointTopology B S hS 𝒳.val) (spacePointMap B S hS (yoneda.obj U) 𝒳.val b) := by
    refine isOpenMap_spacePointMap B S hS (yoneda.obj U) hU 𝒳.val 𝒳.property b ?_
    intro V y hy G hG hE
    have hsm := hbSmooth.2 V y hy G hG hE
    exact ⟨Space.isFlat_of_isSmooth B S hS _ hsm,
      Space.isLocallyOfFinitePresentation_of_isSmooth B S hS hsm⟩
  obtain ⟨A, k, hA, hk, hkSurj⟩ :=
    exists_affine_refinement_of_open_surjective B S hS U _ hbOpen hbSurj
  let c := BasedFunctor.comp (associatedMap B S hS (yoneda.map k)).1.hom b
  have hcSmooth : IsRelativelySmooth B S hS
      (Bicategory.InducedBicategory.mkHom c :
        fibredCategory B S hS (yoneda.obj A) ⟶ 𝒳.val) := by
    exact isRelativelySmooth_comp B S hS (associatedMap B S hS (yoneda.map k)).1
      (Bicategory.InducedBicategory.mkHom b)
      (isRelativelySmooth_associatedMap_of_isSmooth B S hS
        (isAlgebraicSpace_yoneda B S hS A) hU (yoneda.map k)
        (isSmooth_yonedaMap_of_smooth B S hS k hk)) hbSmooth
  have hcSurj : Function.Surjective (spacePointMap B S hS (yoneda.obj A) 𝒳.val c) := by
    rwa [spacePointMap_associatedMap_comp B S hS (yoneda.map k) 𝒳.val b]
  let eA := schemeFibredCategoryEquivalence B S hS A
  let _ : Functor.IsEquivalence eA.functor.toFunctor := eA.equiv.isEquivalence_functor
  refine ⟨A, hA, Bicategory.InducedBicategory.mkHom
    (Bicategory.InducedBicategory.mkHom (BasedFunctor.comp eA.functor c)), ?_, ?_⟩
  · have hcSurj' := (spacePointMap_surjective_iff_pointsMap_surjective B S hS
      (yoneda.obj A) 𝒳.val c).1 hcSurj
    intro x
    obtain ⟨y, hy⟩ := hcSurj' x
    obtain ⟨z, hz⟩ := pointsMap_surjective_of_basedEquivalence B S hS
      (𝒜 := schemeFibredCategory B S hS A)
      (𝒞 := fibredCategory B S hS (yoneda.obj A)) eA y
    refine ⟨z, ?_⟩
    change pointsMap B S hS (schemeFibredCategory B S hS A).val
      (schemeFibredCategory B S hS A).property 𝒳.val.property
      (BasedFunctor.comp eA.functor c) z = x
    rw [← pointsMap_comp B S hS (schemeFibredCategory B S hS A).val
      (schemeFibredCategory B S hS A).property
      (fibredCategory B S hS (yoneda.obj A)).property 𝒳.val.property eA.functor c z, hz]
    exact hy
  · exact isRelativelySmooth_of_equivalences B S hS _
      (Bicategory.InducedBicategory.mkHom c :
        fibredCategory B S hS (yoneda.obj A) ⟶ 𝒳.val)
      eA.functor (BasedFunctor.id 𝒳.val.val) (Iso.refl _) hcSmooth

/-- An algebraic stack with a surjective smooth presentation by an affine scheme is
quasi-compact. -/
private theorem isQuasiCompactStack_of_hasAffineSmoothPresentation
    (h : HasAffineSmoothPresentation.{u, w} B S hS 𝒳) :
    IsQuasiCompactStack.{u, w} B S hS 𝒳.val 𝒳.property := by
  obtain ⟨U, hU, f, hsurj, hsmooth⟩ := h
  let _ : IsAffine ((BigFppfOver.toScheme B S hS).obj U) := hU
  exact isQuasiCompactStack_of_hasQuasiCompactSpaceSmoothPresentation B S hS 𝒳
    (hasQuasiCompactSpaceSmoothPresentation_of_scheme B S hS 𝒳 U inferInstance f.hom hsurj hsmooth)

/-- An algebraic stack is quasi-compact if and only if it has a surjective smooth presentation by
an affine scheme. -/
@[stacks 04YC "parts (1) and (2)"]
theorem isQuasiCompactStack_iff_hasAffineSmoothPresentation :
    IsQuasiCompactStack.{u, w} B S hS 𝒳.val 𝒳.property ↔
      HasAffineSmoothPresentation.{u, w} B S hS 𝒳 :=
  ⟨hasAffineSmoothPresentation_of_isQuasiCompactStack.{u, w} B S hS 𝒳,
    isQuasiCompactStack_of_hasAffineSmoothPresentation.{u, w} B S hS 𝒳⟩

/-- A surjective smooth presentation by an affine scheme is one by a quasi-compact scheme. -/
private theorem hasQuasiCompactSchemeSmoothPresentation_of_hasAffineSmoothPresentation
    (h : HasAffineSmoothPresentation.{u, w} B S hS 𝒳) :
    HasQuasiCompactSchemeSmoothPresentation.{u, w} B S hS 𝒳 := by
  obtain ⟨U, hU, f, hsurj, hsmooth⟩ := h
  let _ : IsAffine ((BigFppfOver.toScheme B S hS).obj U) := hU
  exact ⟨U, inferInstance, f, hsurj, hsmooth⟩

/-- An algebraic stack has a surjective smooth presentation by an affine scheme if and only if it
has one by a quasi-compact scheme. -/
@[stacks 04YC "parts (2) and (3)"]
theorem hasAffineSmoothPresentation_iff_hasQuasiCompactSchemeSmoothPresentation :
    HasAffineSmoothPresentation.{u, w} B S hS 𝒳 ↔
      HasQuasiCompactSchemeSmoothPresentation.{u, w} B S hS 𝒳 := by
  refine ⟨hasQuasiCompactSchemeSmoothPresentation_of_hasAffineSmoothPresentation B S hS 𝒳, ?_⟩
  rintro ⟨U, hU, f, hsurj, hsmooth⟩
  exact (isQuasiCompactStack_iff_hasAffineSmoothPresentation B S hS 𝒳).1
    (isQuasiCompactStack_of_hasQuasiCompactSpaceSmoothPresentation B S hS 𝒳
      (hasQuasiCompactSpaceSmoothPresentation_of_scheme B S hS 𝒳 U hU f.hom hsurj hsmooth))

/-- An algebraic stack has a surjective smooth presentation by a quasi-compact scheme if and only
if it has one by a quasi-compact algebraic space. -/
@[stacks 04YC "parts (3) and (4)"]
theorem hasQuasiCompactSchemeSmoothPresentation_iff_hasQuasiCompactSpaceSmoothPresentation :
    HasQuasiCompactSchemeSmoothPresentation.{u, w} B S hS 𝒳 ↔
      HasQuasiCompactSpaceSmoothPresentation.{u, w} B S hS 𝒳 := by
  constructor
  · rintro ⟨U, hU, f, hsurj, hsmooth⟩
    exact hasQuasiCompactSpaceSmoothPresentation_of_scheme B S hS 𝒳 U hU f.hom hsurj hsmooth
  · intro h
    exact hasQuasiCompactSchemeSmoothPresentation_of_hasAffineSmoothPresentation B S hS 𝒳
      ((isQuasiCompactStack_iff_hasAffineSmoothPresentation B S hS 𝒳).1
        (isQuasiCompactStack_of_hasQuasiCompactSpaceSmoothPresentation B S hS 𝒳 h))

/-- An algebraic stack has a surjective smooth presentation by a quasi-compact algebraic space if
and only if there is a surjection onto it from a quasi-compact algebraic stack. -/
@[stacks 04YC "parts (4) and (5)"]
theorem hasQuasiCompactSpaceSmoothPresentation_iff_hasQuasiCompactStackSurjection :
    HasQuasiCompactSpaceSmoothPresentation.{u, w} B S hS 𝒳 ↔
      HasQuasiCompactStackSurjection.{u, w} B S hS 𝒳 := by
  constructor
  · rintro ⟨F, hF, hFqc, f, hsurj, -⟩
    exact ⟨_, f, isQuasiCompactStack_fibredCategory B S hS F hF hFqc _, hsurj⟩
  · rintro ⟨𝒰, f, h𝒰, hsurj⟩
    exact (hasQuasiCompactSchemeSmoothPresentation_iff_hasQuasiCompactSpaceSmoothPresentation
      B S hS 𝒳).1 (hasQuasiCompactSchemeSmoothPresentation_of_hasAffineSmoothPresentation B S hS 𝒳
        ((isQuasiCompactStack_iff_hasAffineSmoothPresentation B S hS 𝒳).1
          (isQuasiCompactStack_of_isSurjective B S hS f h𝒰 hsurj)))

end AlgebraicGeometry.Stack

end
