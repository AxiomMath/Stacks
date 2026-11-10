module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceOfPointsFactorization
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SingleDegreeFreeGeometricPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SingleDegreeRankOpenSubspace

/-!
# Existence of the open subspace on which a perfect complex is locally free in one degree

Let `S` be a scheme, let `X` be an algebraic space over `S`, let `E` be a perfect object of
`D(𝒪_X)` and let `i, r ∈ ℤ`. Stacks 0D20: there is an open subspace `U ⊆ X` characterised by
(1) `E|_U ≅ H^i(E|_U)[-i]` with `H^i(E|_U)` finite locally free of rank `r`, and (2) a morphism
`f : Y → X` factors through `U` if and only if `Lf^*E` is a finite locally free module of rank `r`
placed in degree `i`. Clause (1) for an open subspace with property (2), and uniqueness, are
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/SingleDegreeRankOpenSubspace.lean`; this file
proves existence.

The open subspace is cut out by the points lying in the image of an étale chart on which `E` is
`𝒪^{⊕r}[-i]`. A morphism `f` landing there has `Lf^*E` of the required shape by étale locality.
Conversely, if `Lf^*E` has that shape, then at a geometric point of `Y` the fibre of a strictly
perfect model of `E` on an étale neighbourhood is free of rank `r` in degree `i`, and this spreads
to a principal open of the neighbourhood.

## Main results

* `AlgebraicGeometry.Space.exists_isSingleDegreeRankLocus`: **Stacks 0D20**.

## References

* [Stacks Project, Tag 0D20](https://stacks.math.columbia.edu/tag/0D20)
* [Stacks Project, Tag 0BDK](https://stacks.math.columbia.edu/tag/0BDK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace Space

attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable (X : AlgebraicSpaces B S hS)

variable (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
  (i r : ℤ)

/-! ### Existence -/

variable {B S hS X} in
/-- The image of the tautological geometric point of the spectrum of the field of a geometric point
`p`, under the morphism defined by `p` followed by `α`, is the image of `p` under `α`. -/
theorem pointsMap_yonedaEquiv_symm_comp_tautological {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (p : GeometricPoint B S hS F) (α : F ⟶ G) :
    pointsMap B S hS _ (yonedaEquiv.symm p.val.value ≫ α)
        (GeometricPoint.tautological B S hS p).image =
      pointsMap B S hS F α p.image := by
  obtain ⟨⟨k, c, tb, v⟩, hk⟩ := p
  have hv : (yonedaEquiv.symm v ≫ α).app
      (Opposite.op (FieldValuedPoint.siteObject B S hS F ⟨k, c, tb, v⟩))
      (𝟙 (FieldValuedPoint.siteObject B S hS F ⟨k, c, tb, v⟩)) = α.app _ v := by
    change yonedaEquiv (yonedaEquiv.symm v ≫ α) = _
    rw [yonedaEquiv_comp, Equiv.apply_symm_apply]
  exact congrArg (fun w => FieldValuedPoint.class B S hS G ⟨k, c, tb, w⟩) hv

variable {B S hS X} in
/-- **If `Lf^*E` is a finite locally free module of rank `r` placed in degree `i`, then `f` maps
every point into the locus where `E` is free of rank `r` in degree `i`**, for `E` perfect. -/
theorem pointsMap_mem_singleDegreeFreePoints_of_isFiniteLocallyFreeOfIntRankInDegree
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E)
    {Y : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    (hf : IsFiniteLocallyFreeOfIntRankInDegree B S hS Y
      ((smallEtaleDerivedModulePullback B S hS f).obj E) i r)
    (y : points B S hS Y.1) :
    pointsMap B S hS Y.1 f.hom y ∈ singleDegreeFreePoints B S hS E i r := by
  obtain ⟨T, ⟨w, rfl⟩, hT⟩ :=
    (isFiniteLocallyFreeOfIntRankInDegree_iff B S hS Y _ i r).1 hf y
  obtain ⟨t, rfl⟩ := (geometricPoints_large_enough B S hS _ _
    (isAlgebraicSpace_yoneda B S hS T.1.left) (isAlgebraicSpace_yoneda B S hS T.1.left)).1 w
  let a : (⟨yoneda.obj t.val.siteObject, isAlgebraicSpace_yoneda B S hS t.val.siteObject⟩ :
      AlgebraicSpaces B S hS) ⟶ chartSpace B S hS Y T :=
    ObjectProperty.homMk (yonedaEquiv.symm t.val.value)
  have hc := (hT.derivedPullback a).of_iso
    ((smallEtaleDerivedModulePullbackCompIso B S hS a (chartToSpace B S hS Y T)).app _ ≪≫
      (smallEtaleDerivedModulePullbackCompIso B S hS (a ≫ chartToSpace B S hS Y T) f).app E ≪≫
      (smallEtaleDerivedModulePullbackCongr B S hS (Category.assoc _ _ _)).app E)
  have h := pointsMap_mem_singleDegreeFreePoints B S hS E hE i r t _ hc
  rw [← pointsMap_comp_apply]
  exact (pointsMap_yonedaEquiv_symm_comp_tautological t (T.1.hom ≫ f.hom)).symm ▸ h

/-- **Stacks 0D20.** Let `X` be an algebraic space over `S`, let `E` be a perfect object of
`D(𝒪_X)` and let `i, r ∈ ℤ`. There is an open subspace `U ⊆ X`, and only one, characterised by:
(1) `E|_U ≅ M[-i]` for a finite locally free `𝒪_U`-module `M` of rank `r` (so `M = H^i(E|_U)`);
(2) a morphism `f : Y → X` factors through `U` if and only if `Lf^*E` is a finite locally free
module of rank `r` placed in degree `i`. -/
@[stacks 0D20]
theorem exists_isSingleDegreeRankLocus
    (hE : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) E) :
    ∃ U : OpenSubspaces B S hS X.1,
      IsFiniteLocallyFreeOfIntRankInDegree B S hS (openSubspaceAsSpace B S hS U)
        ((smallEtaleDerivedModulePullback B S hS (openSubspaceImmersion B S hS U)).obj E) i r ∧
      IsSingleDegreeRankLocus B S hS X E i r U ∧
      ∀ U' : OpenSubspaces B S hS X.1, IsSingleDegreeRankLocus B S hS X E i r U' → U' = U := by
  let W := singleDegreeFreePoints B S hS E i r
  let U : OpenSubspaces B S hS X.1 := ⟨openSubspaceOfPoints B S hS X.1 W,
    isOpenSubspace_openSubspaceOfPoints B S hS X.2 W (isOpen_singleDegreeFreePoints B S hS E i r)⟩
  have hU : IsSingleDegreeRankLocus B S hS X E i r U := by
    intro Y f _
    have hfac : (∃ g : Y ⟶ openSubspaceAsSpace B S hS U,
        g ≫ openSubspaceImmersion B S hS U = f) ↔
        ∀ y : points B S hS Y.1, pointsMap B S hS Y.1 f.hom y ∈ W := by
      rw [← exists_lift_openSubspaceOfPoints_iff B S hS W f.hom]
      exact ⟨fun ⟨g, hg⟩ => hg ▸ ⟨g.hom, rfl⟩,
        fun ⟨g, hg⟩ => ⟨ObjectProperty.homMk g, InducedCategory.hom_ext hg⟩⟩
    rw [hfac]
    constructor
    · exact fun h => (isFiniteLocallyFreeOfIntRankInDegree_iff B S hS Y _ i r).2 fun y =>
        exists_isFreeOfRankInDegree_chart_of_mem_singleDegreeFreePoints B S hS X f E i r y (h y)
    · exact pointsMap_mem_singleDegreeFreePoints_of_isFiniteLocallyFreeOfIntRankInDegree
        E i r hE f
  exact ⟨U, isFiniteLocallyFreeOfIntRankInDegree_of_isSingleDegreeRankLocus B S hS X E i r U hU,
    hU, fun U' hU' => eq_of_isSingleDegreeRankLocus B S hS X E i r U' U hU' hU⟩

end Space

end AlgebraicGeometry

end
