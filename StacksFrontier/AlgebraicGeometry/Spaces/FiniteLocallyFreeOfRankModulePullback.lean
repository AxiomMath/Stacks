module

public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackOpenInCoherentStack
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartDiagramBaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartMapFinitePresentationClause
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartModulePullbackSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeRankChartScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportedSectionsSubsheaf
public import StacksFrontier.CategoryTheory.Sites.Modules.FiniteLocallyFreeOfRankLocalOnCover

/-!
# The inverse image of a module of rank `r` along a morphism of algebraic spaces

Let `a : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` and let `N` be an
`𝒪_Y`-module on the small étale site which has rank `r` in the sense of the rank clause of
Stacks 0409.  Then the inverse image `a^*N` of Stacks 03LU has rank `r`.  This is the rank-indexed
form of `AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_modulePullback` (Stacks 03DO for the
property 03DL (2)).

## Main results

* `AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_modulePullback`: **the inverse image of a
  module of rank `r` has rank `r`**, for an arbitrary morphism of algebraic spaces and with no
  quasi-coherence hypothesis.

## References

* [Stacks Project, Tag 0409](https://stacks.math.columbia.edu/tag/0409)
* [Stacks Project, Tag 03DO](https://stacks.math.columbia.edu/tag/03DO)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The inverse of the chart localization equivalence is continuous for the étale topologies. -/
private theorem isContinuous_chartLocalizationEquivalence_inverse (Z : AlgebraicSpaces B S hS)
    (V : SmallEtale B S hS Z.1) :
    (SmallEtale.chartLocalizationEquivalence B S hS Z.1 V).inverse.IsContinuous
      ((SmallEtale.topology B S hS Z.1).over V)
      (SmallEtale.topology B S hS (chartSpace B S hS Z V).1) :=
  @Functor.IsDenseSubsite.instIsContinuous _ _ _ _ _ _ _
    (isDenseSubsite_chartLocalizationEquivalence_inverse B S hS Z V)

/-- **A free module of rank `r` on the slice at a chart is free of rank `r` on the chart space.**
If the restriction of an `𝒪_Z`-module to the slice of the small étale site at an étale scheme
chart `V` is a coproduct of `r` copies of the structure sheaf, then so is its inverse image along
the structure morphism of the chart space of `V`. -/
theorem exists_isColimitCofan_modulePullback_chartToSpace_of_over (Z : AlgebraicSpaces B S hS)
    (N : Modules.{u, u} B S hS Z.1 Z.2) (V : SmallEtale B S hS Z.1) {r : ℕ}
    (h : ∃ ι : ∀ _ : Fin r, SheafOfModules.unit ((structureRingSheaf B S hS Z).over V) ⟶ N.over V,
      Nonempty (IsColimit (Cofan.mk (N.over V) ι))) :
    ∃ ι : ∀ _ : Fin r, SheafOfModules.unit (chartStructureRingSheaf B S hS Z V) ⟶
        (modulePullback B S hS (chartToSpace B S hS Z V)).obj N,
      Nonempty (IsColimit
        (Cofan.mk ((modulePullback B S hS (chartToSpace B S hS Z V)).obj N) ι)) := by
  have h₂ := isContinuous_chartLocalizationEquivalence_inverse B S hS Z V
  have hc : ∃ ι : ∀ _ : Fin r, SheafOfModules.unit (chartStructureRingSheaf B S hS Z V) ⟶
        (chartSmallEtaleRestrictionFunctor Z V).obj (N.over V),
      Nonempty (IsColimit (Cofan.mk ((chartSmallEtaleRestrictionFunctor Z V).obj (N.over V)) ι)) :=
    @Stacks.SheafOfModules.exists_isColimitCofan_reindex _ _ _ _
      ((SmallEtale.topology B S hS Z.1).over V)
      (SmallEtale.topology B S hS (chartSpace B S hS Z V).1)
      (SmallEtale.chartLocalizationEquivalence B S hS Z.1 V)
      (isContinuous_chartLocalization_chartSpace B S hS Z V) h₂
      ((structureRingSheaf B S hS Z).over V) (N.over V) _ h
  exact Stacks.SheafOfModules.exists_isColimitCofan_of_iso
    ((chartSmallEtaleRestrictionFunctorObjIso Z N V) ≪≫
      ((modulePullbackIsoEtaleModulePullback B S hS (chartToSpace B S hS Z V)
        (isEtale_chartToSpace B S hS Z V)).app N).symm) hc

/-- **A free module of rank `r` on the chart space is free of rank `r` on the slice at the
chart.**  The converse of
`AlgebraicGeometry.Space.exists_isColimitCofan_modulePullback_chartToSpace_of_over`. -/
theorem exists_isColimitCofan_over_of_modulePullback_chartToSpace (Z : AlgebraicSpaces B S hS)
    (M : Modules.{u, u} B S hS Z.1 Z.2) (W : SmallEtale B S hS Z.1) {r : ℕ}
    (h : ∃ ι : ∀ _ : Fin r, SheafOfModules.unit (chartStructureRingSheaf B S hS Z W) ⟶
        (modulePullback B S hS (chartToSpace B S hS Z W)).obj M,
      Nonempty (IsColimit (Cofan.mk ((modulePullback B S hS (chartToSpace B S hS Z W)).obj M) ι))) :
    ∃ ι : ∀ _ : Fin r, SheafOfModules.unit ((structureRingSheaf B S hS Z).over W) ⟶ M.over W,
      Nonempty (IsColimit (Cofan.mk (M.over W) ι)) := by
  have h₂ := isContinuous_chartLocalizationEquivalence_inverse B S hS Z W
  have hc : ∃ ι : ∀ _ : Fin r, SheafOfModules.unit (chartStructureRingSheaf B S hS Z W) ⟶
        (chartSmallEtaleRestrictionFunctor Z W).obj (M.over W),
      Nonempty (IsColimit (Cofan.mk ((chartSmallEtaleRestrictionFunctor Z W).obj (M.over W)) ι)) :=
    Stacks.SheafOfModules.exists_isColimitCofan_of_iso
      (((modulePullbackIsoEtaleModulePullback B S hS (chartToSpace B S hS Z W)
        (isEtale_chartToSpace B S hS Z W)).app M) ≪≫
          (chartSmallEtaleRestrictionFunctorObjIso Z M W).symm) h
  exact @Stacks.SheafOfModules.exists_isColimitCofan_of_reindex _ _ _ _
    ((SmallEtale.topology B S hS Z.1).over W)
    (SmallEtale.topology B S hS (chartSpace B S hS Z W).1)
    (SmallEtale.chartLocalizationEquivalence B S hS Z.1 W)
    (isContinuous_chartLocalization_chartSpace B S hS Z W) h₂
    ((structureRingSheaf B S hS Z).over W) (M.over W) _ hc

/-- **The inverse image of a free module of rank `r` is free of rank `r`.**  For a morphism
`f : X ⟶ Y` of algebraic spaces, the inverse image of Stacks 03LU of a coproduct of `r` copies of
`𝒪_Y` is a coproduct of `r` copies of `𝒪_X`. -/
theorem exists_isColimitCofan_modulePullback {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (M : Modules.{u, u} B S hS Y.1 Y.2) {r : ℕ}
    (h : ∃ ι : ∀ _ : Fin r, SheafOfModules.unit (structureRingSheaf B S hS Y) ⟶ M,
      Nonempty (IsColimit (Cofan.mk M ι))) :
    ∃ ι : ∀ _ : Fin r, SheafOfModules.unit (structureRingSheaf B S hS X) ⟶
        (modulePullback B S hS f).obj M,
      Nonempty (IsColimit (Cofan.mk ((modulePullback B S hS f).obj M) ι)) := by
  obtain ⟨ι, ⟨hc⟩⟩ := h
  obtain ⟨e⟩ := Stacks.SheafOfModules.nonempty_iso_free_of_exists_isColimitCofan
    (M := M) (I := ULift.{u} (Fin r))
    ⟨fun j => ι j.down, ⟨(Cofan.isColimitEquivOfEquiv Equiv.ulift (Cofan.mk _ ι)) hc⟩⟩
  obtain ⟨ι', ⟨hc'⟩⟩ := Stacks.SheafOfModules.exists_isColimitCofan_of_iso_free
    (modulePullbackFreeIso B S hS f (ULift.{u} (Fin r)) ≪≫ (modulePullback B S hS f).mapIso e)
  exact ⟨fun j => ι' ⟨j⟩, ⟨(Cofan.isColimitEquivOfEquiv Equiv.ulift.symm _) hc'⟩⟩

/-- **Every point of an algebraic space lies in the image of a chart over which a module of rank
`r` is free of rank `r`.** -/
theorem exists_chart_isColimitCofan_mem_range_of_isFiniteLocallyFreeOfRank
    (Z : AlgebraicSpaces B S hS) (N : Modules.{u, u} B S hS Z.1 Z.2) {r : ℕ}
    (hN : RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS Z.1 Z.2) N r)
    (x : points B S hS Z.1) :
    ∃ V : SmallEtale B S hS Z.1,
      (∃ ι : ∀ _ : Fin r, SheafOfModules.unit ((structureRingSheaf B S hS Z).over V) ⟶ N.over V,
        Nonempty (IsColimit (Cofan.mk (N.over V) ι))) ∧
      x ∈ Set.range (pointsMap B S hS
        (yoneda.obj ((SmallEtale.toOver B S hS Z.1).obj V)) V.1.hom) := by
  obtain ⟨U, p, hp⟩ := exists_chart_point B S hS Z.1 Z.2 x
  obtain ⟨I, V, f, hcov, hfree⟩ := hN U
  obtain ⟨W, g, hg, q, hq⟩ := SmallEtale.exists_mem_arrows_pointsMap_eq B S hS Z.1 hcov p
  obtain ⟨i, k, -⟩ := Sieve.ofArrows.exists hg
  refine ⟨V i, hfree i, pointsMap B S hS
    (yoneda.obj ((SmallEtale.toOver B S hS Z.1).obj W)) (yoneda.map k.hom.left) q, ?_⟩
  have hW : yoneda.map ((SmallEtale.toOver B S hS Z.1).map g) ≫ U.obj.hom = W.obj.hom :=
    CostructuredArrow.w g.hom
  have hVi : yoneda.map k.hom.left ≫ (V i).obj.hom = W.obj.hom :=
    CostructuredArrow.w k.hom
  have h₁ := congrFun (pointsMap_comp B S hS
    (yoneda.obj ((SmallEtale.toOver B S hS Z.1).obj W))
    (yoneda.map ((SmallEtale.toOver B S hS Z.1).map g)) U.obj.hom) q
  have h₂ := congrFun (pointsMap_comp B S hS
    (yoneda.obj ((SmallEtale.toOver B S hS Z.1).obj W)) (yoneda.map k.hom.left)
    (V i).obj.hom) q
  simp only [Function.comp_apply] at h₁ h₂
  rw [hW] at h₁
  rw [hVi] at h₂
  have hres : pointsMap B S hS (yoneda.obj (V i).obj.left) (V i).obj.hom
      (pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS Z.1).obj W))
        (yoneda.map k.hom.left) q) = x := by
    rw [← h₂, h₁, hq]
    exact hp
  exact hres

/-- **The inverse image of a module of rank `r` has rank `r`.**  For a morphism `a : X ⟶ Y` of
algebraic spaces over `S` and an `𝒪_Y`-module `N` of rank `r` in the sense of the rank clause of
Stacks 0409, the inverse image `a^*N` of Stacks 03LU has rank `r`. -/
theorem isFiniteLocallyFreeOfRank_modulePullback {X Y : AlgebraicSpaces B S hS} (a : X ⟶ Y)
    (N : Modules.{u, u} B S hS Y.1 Y.2) (r : ℕ)
    (h : RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS Y.1 Y.2) N r) :
    RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS X.1 X.2)
      ((modulePullback B S hS a).obj N) r := by
  let P : SmallEtale B S hS Y.1 → Prop := fun V =>
    ∃ ι : ∀ _ : Fin r, SheafOfModules.unit ((structureRingSheaf B S hS Y).over V) ⟶ N.over V,
      Nonempty (IsColimit (Cofan.mk (N.over V) ι))
  have hPhom : ∀ {V V' : SmallEtale B S hS Y.1}, (V' ⟶ V) → P V → P V' := fun φ hV =>
    Stacks.SheafOfModules.exists_isColimitCofanOfRank_over_of_le _ N φ hV
  have hPcov : ∀ x : points B S hS Y.1, ∃ V : SmallEtale B S hS Y.1, P V ∧
      x ∈ Set.range (pointsMap B S hS
        (yoneda.obj ((SmallEtale.toOver B S hS Y.1).obj V)) V.1.hom) :=
    exists_chart_isColimitCofan_mem_range_of_isFiniteLocallyFreeOfRank B S hS Y N h
  refine (RingedSite.isFiniteLocallyFreeOfRank_iff_exists_cover_isColimit
    (smallEtaleRingedSite B S hS X.1 X.2) ((modulePullback B S hS a).obj N) r).2
    ⟨{W : SmallEtale B S hS X.1 // HasAffineChartDiagramWith B S hS a P W}, Subtype.val,
      fun U => mem_topology_of_hasAffineChartDiagramWith B S hS P a hPhom hPcov U _
        fun {W} _ hW => ⟨⟨W, hW⟩, ⟨𝟙 W⟩⟩, fun i => ?_⟩
  obtain ⟨-, V, q, hq, -, hPV⟩ := i.2
  have hV := exists_isColimitCofan_modulePullback_chartToSpace_of_over B S hS Y N V hPV
  have hq' := exists_isColimitCofan_modulePullback B S hS (chartSpaceMapOver B S hS q) _ hV
  exact exists_isColimitCofan_over_of_modulePullback_chartToSpace B S hS X _ i.1
    (Stacks.SheafOfModules.exists_isColimitCofan_of_iso
      ((modulePullbackCommSquareIso B S hS
        (chartSpaceMapOver_comp_chartToSpace B S hS a q hq)).app N) hq')

end AlgebraicGeometry.Space

end
