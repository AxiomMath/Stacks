module

public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.RelativeWeakAssassin
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.ChartDiagramRelativeAssassin
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.RepresentedFibreComparison
public import StacksFrontier.AlgebraicGeometry.Flatness.PureModules.Purity
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.PurityClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.RelativeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented

/-!
# Universal purity over a represented base, from universal purity of schemes

Let `P` be a situation of Stacks 0CV6 whose source and base are represented by schemes `W` and
`V` of the site, the morphism of the situation being represented by a morphism `α : W ⟶ V` of the
site. Universal purity of `P` above its chosen point — the absence of every impurity of
Stacks 0CV8 — is then implied by universal purity, in the sense of Stacks 05J4, of the
underlying scheme situation: the morphism of schemes `α`, the restriction of the module of `P`
to the scheme `W`, and the point of `V` below the chosen point.

The comparison is direct. An impurity `(T ⟶ Y, t' ⤳ t, ξ)` of `P` has its total space
`T ×_Y X` represented by the fibre product `T ×_V W` formed in the site, because `yoneda`
preserves fibre products; and the functor to schemes preserves them too, so the same object of
the site is a fibre product of schemes. Reading `ξ` as a point of that scheme gives an impurity
diagram of the scheme situation, and it is an impurity:

* the relative weak assassin of Stacks 0CV0 of the represented morphism is the scheme-level
  relative weak assassin of Stacks 05AV of the restricted module,
  `AlgebraicGeometry.Space.isRelativeWeaklyAssociatedPoint_iff_mem_relativeWeaklyAssociatedPoints`,
  which for a morphism locally of finite type is the relative assassin of Stacks 05AT by
  Stacks 05F2; the restriction of a quasi-coherent module commutes with base change along a
  morphism of the site,
  `AlgebraicGeometry.Space.nonempty_restrictToChartScheme_baseChange_of_isQuasicoherent`;
* the comparison bijection of Stacks 03BX is a homeomorphism, so a specialization of the point
  on the scheme lying over `t` would give one of `ξ` lying over `t`.

## Main results

* `AlgebraicGeometry.Space.isUniversallyPureAbove_of_isUniversallyPureAlong_represented`: a
  situation of Stacks 0CV6 with represented source and base is universally pure above its chosen
  point as soon as the underlying scheme situation is universally pure along the fibre.

## References

* [Stacks Project, Tag 0CVD](https://stacks.math.columbia.edu/tag/0CVD)
* [Stacks Project, Tag 05J4](https://stacks.math.columbia.edu/tag/05J4)
* [Stacks Project, Tag 0CV0](https://stacks.math.columbia.edu/tag/0CV0)
* [Stacks Project, Tag 05F2](https://stacks.math.columbia.edu/tag/05F2)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] pointTopology

/-- The relative assassin condition transported to schemes: if `χ : h_{T ×_V W} ≅ T ×_Y X`
identifies the site fibre product with the total space of an impurity diagram `D` compatibly
with the projections, and `ξ` is carried by `χ` to a relative weak assassin point of `D`, then `ξ`
read in schemes lies in the relative assassin of the pulled back module. -/
private theorem pointsToScheme_mem_relativeAssassin_of_represented
    {P : PrePureSituation.{u, u} B S hS} {W V : BigFppfOver B S hS} (α : W ⟶ V)
    [LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map α)]
    (φ : yoneda.obj W ≅ P.X) (M : ((BigFppfOver.toScheme B S hS).obj W).Modules)
    (eM : M ≅ representedChartModule B S hS
      ((modulePullback B S hS (X := ⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩)
        (Y := ⟨P.X, P.hX⟩) (ObjectProperty.homMk φ.hom)).obj P.F))
    (D : ImpurityDiagram P) (γ : D.T ⟶ V) (χ : yoneda.obj (pullback γ α) ≅ pullback D.g P.f)
    (hχfst : χ.hom ≫ pullback.fst D.g P.f = yoneda.map (pullback.fst γ α))
    (hχsnd : χ.hom ≫ pullback.snd D.g P.f = yoneda.map (pullback.snd γ α) ≫ φ.hom)
    {ξW : points B S hS (yoneda.obj (pullback γ α))}
    (hχξ : pointsMap B S hS (yoneda.obj (pullback γ α)) χ.hom ξW = D.xi)
    (hD : D.IsRelativeWeakAssassinPoint D.xi) :
    pointsToScheme B S hS (pullback γ α) ξW ∈ Stacks.Divisors.relativeAssassin
      ((BigFppfOver.toScheme B S hS).map (pullback.fst γ α))
      ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map (pullback.snd γ α))).obj M) := by
  have _ := preservesLimitsOfShape_walkingCospan_toScheme B S hS
  have hLFT : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map (pullback.fst γ α)) :=
    MorphismProperty.of_isPullback
      ((IsPullback.of_hasPullback γ α).map (BigFppfOver.toScheme B S hS)).flip inferInstance
  rw [← relativeWeaklyAssociatedPoints_eq_relativeAssassin]
  let φS : (⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩ : AlgebraicSpaces B S hS) ⟶
      ⟨P.X, P.hX⟩ := ObjectProperty.homMk φ.hom
  let G' := (modulePullback B S hS φS).obj P.F
  have hG'qc : G'.IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS φS P.F
      P.moduleQuasicoherent
  let G'' := (modulePullback B S hS (representedSpaceMap B S hS (pullback.snd γ α))).obj G'
  have eMod : (Scheme.Modules.pullback
        ((BigFppfOver.toScheme B S hS).map (pullback.snd γ α))).obj M ≅
      representedChartModule B S hS G'' :=
    (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map (pullback.snd γ α))).mapIso
        eM ≪≫
      (nonempty_restrictToChartScheme_baseChange_of_isQuasicoherent (pullback.snd γ α) G'
        hG'qc).some.symm
  rw [_root_.AlgebraicGeometry.relativeWeaklyAssociatedPoints_congr _ eMod]
  refine (isRelativeWeaklyAssociatedPoint_iff_mem_relativeWeaklyAssociatedPoints B S hS
    (pullback.fst γ α) G''
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
      (representedSpaceMap B S hS (pullback.snd γ α)) G' hG'qc) ξW).1 ?_
  let χS : (⟨yoneda.obj (pullback γ α), isAlgebraicSpace_yoneda B S hS _⟩ :
      AlgebraicSpaces B S hS) ⟶ P.baseChangeSpace D.T D.g :=
    ObjectProperty.homMk χ.hom
  have h1 := (isRelativeWeaklyAssociatedPoint_modulePullback_iff B S hS χS
    (isEtale_of_isIso B S hS χ.hom) (P.baseChangeToBase D.T D.g) (P.baseChangeModule D.T D.g)
    ξW).2 (by
      rw [show pointsMap B S hS _ χS.hom ξW = D.xi from hχξ]
      exact (D.isRelativeWeakAssassinPoint_iff D.xi).1 hD)
  have hmapT : χS ≫ P.baseChangeToBase D.T D.g =
      representedSpaceMap B S hS (pullback.fst γ α) :=
    ObjectProperty.hom_ext _ hχfst
  have hmapX : χS ≫ P.baseChangeToSource D.T D.g =
      representedSpaceMap B S hS (pullback.snd γ α) ≫ φS :=
    ObjectProperty.hom_ext _ hχsnd
  have eG : (modulePullback B S hS χS).obj (P.baseChangeModule D.T D.g) ≅ G'' :=
    (modulePullbackCompIso B S hS χS (P.baseChangeToSource D.T D.g)).app P.F ≪≫
      eqToIso (congrArg (fun m : (⟨yoneda.obj (pullback γ α),
          isAlgebraicSpace_yoneda B S hS _⟩ : AlgebraicSpaces B S hS) ⟶ ⟨P.X, P.hX⟩ =>
        (modulePullback B S hS m).obj P.F) hmapX) ≪≫
        ((modulePullbackCompIso B S hS (representedSpaceMap B S hS (pullback.snd γ α))
          φS).app P.F).symm
  rw [hmapT] at h1
  exact (isRelativeWeaklyAssociatedPoint_congr _ eG ξW).1 h1

/-- The closure condition transported to schemes: if `χ : h_{T ×_V W} ⟶ T ×_Y X` is compatible
with the projections to `T` and carries `ξ` to the distinguished point of an impurity diagram `D`
none of whose specializations lies over `t`, then no specialization of `ξ` read in schemes lies
in the fibre over `t`. -/
private theorem closure_inter_range_fiberι_eq_empty_of_represented
    {P : PrePureSituation.{u, u} B S hS} {W V : BigFppfOver B S hS} (α : W ⟶ V)
    (D : ImpurityDiagram P) (γ : D.T ⟶ V) (χ : yoneda.obj (pullback γ α) ⟶ pullback D.g P.f)
    (hχfst : χ ≫ pullback.fst D.g P.f = yoneda.map (pullback.fst γ α))
    {ξW : points B S hS (yoneda.obj (pullback γ α))}
    (hχξ : pointsMap B S hS (yoneda.obj (pullback γ α)) χ ξW = D.xi)
    (hD : ∀ θ, D.xi ⤳ θ → pointsMap B S hS D.baseChange D.toT θ ≠ D.t) :
    closure {pointsToScheme B S hS (pullback γ α) ξW} ∩
      Set.range (((BigFppfOver.toScheme B S hS).map (pullback.fst γ α)).fiberι
        (pointsToScheme B S hS D.T D.t)) = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun z ⟨hzcl, hzfib⟩ => ?_
  rw [Scheme.Hom.range_fiberι] at hzfib
  let s := (schemePointsHomeomorph B S hS (pullback γ α)).symm z
  have hsz : pointsToScheme B S hS (pullback γ α) s = z :=
    (schemePointsHomeomorph B S hS (pullback γ α)).apply_symm_apply z
  have hspec : ξW ⤳ s := by
    have h := (specializes_iff_mem_closure.2 hzcl).map
      (schemePointsHomeomorph B S hS (pullback γ α)).symm.continuous
    rwa [show (schemePointsHomeomorph B S hS (pullback γ α)).symm
      (pointsToScheme B S hS (pullback γ α) ξW) = ξW from
      (schemePointsHomeomorph B S hS (pullback γ α)).symm_apply_apply ξW] at h
  refine hD (pointsMap B S hS _ χ s) ?_ ?_
  · rw [← hχξ]
    exact hspec.map (continuous_pointsMap B S hS χ)
  · rw [← pointsMap_comp_apply, hχfst]
    refine injective_pointsToScheme B S hS D.T ?_
    rwa [pointsToScheme_pointsMap_yoneda, hsz]

/-- **Universal purity over a represented base is universal purity of the underlying schemes.**
Let `P` be a situation of Stacks 0CV6 together with identifications `φ : h_W ≅ X` and
`ψ : h_V ≅ Y` of its source and base with the algebraic spaces of schemes `W`, `V` of the site,
under which the morphism of the situation is represented by `α : W ⟶ V`. Let `M` be a finite
type quasi-coherent module on the scheme `W` isomorphic to the restriction of `φ^* ℱ`. If the
scheme situation `(α, M)` is universally pure along the fibre over the point of `V` below the
chosen point of `P`, in the sense of Stacks 05J4, then `ℱ` is universally pure above that point,
in the sense of Stacks 0CVD. -/
theorem isUniversallyPureAbove_of_isUniversallyPureAlong_represented
    (P : PrePureSituation.{u, u} B S hS) {W V : BigFppfOver B S hS} (α : W ⟶ V)
    [LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map α)]
    [QuasiCompact ((BigFppfOver.toScheme B S hS).map α)]
    (φ : yoneda.obj W ≅ P.X) (ψ : yoneda.obj V ≅ P.Y)
    (hcomm : φ.hom ≫ P.f = yoneda.map α ≫ ψ.hom)
    (M : ((BigFppfOver.toScheme B S hS).obj W).Modules) [M.IsFiniteType] [M.IsQuasicoherent]
    (eM : M ≅ representedChartModule B S hS
      ((modulePullback B S hS (X := ⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩)
        (Y := ⟨P.X, P.hX⟩) (ObjectProperty.homMk φ.hom)).obj P.F))
    (hpure : IsUniversallyPureAlong
      ({ S := (BigFppfOver.toScheme B S hS).obj V
         X := (BigFppfOver.toScheme B S hS).obj W
         f := (BigFppfOver.toScheme B S hS).map α
         F := M
         s := pointsToScheme B S hS V (pointsMap B S hS P.Y ψ.inv P.y) } :
        _root_.AlgebraicGeometry.PrePureSituation.{u})) :
    IsUniversallyPureAbove P := by
  classical
  intro D hD
  have _ := preservesLimitsOfShape_walkingCospan_toScheme B S hS
  -- the structure morphism of the diagram, read in the site
  let γ : D.T ⟶ V := yoneda.preimage (D.g ≫ ψ.inv)
  have hγmap : yoneda.map γ = D.g ≫ ψ.inv := yoneda.map_preimage _
  -- the total space of the diagram is represented by the site fibre product
  have sqY : IsPullback (yoneda.map (pullback.fst γ α))
      (yoneda.map (pullback.snd γ α) ≫ φ.hom) D.g P.f :=
    ((IsPullback.of_hasPullback γ α).map yoneda).of_iso (Iso.refl _) (Iso.refl _) φ ψ
      (by simp) (by simp) (by simp [hγmap]) (by simpa using hcomm.symm)
  let χ := sqY.isoPullback
  have hχfst : χ.hom ≫ pullback.fst D.g P.f = yoneda.map (pullback.fst γ α) :=
    sqY.isoPullback_hom_fst
  let ξW := pointsMap B S hS (pullback D.g P.f) χ.inv D.xi
  have hχξ : pointsMap B S hS (yoneda.obj (pullback γ α)) χ.hom ξW = D.xi := by
    rw [← pointsMap_comp_apply, Iso.inv_hom_id, pointsMap_id, id_eq]
  have hfstξ : pointsMap B S hS (yoneda.obj (pullback γ α)) (yoneda.map (pullback.fst γ α)) ξW =
      D.t' := by
    rw [← hχfst, pointsMap_comp_apply, hχξ]
    exact D.xi_liesOver
  -- the same fibre product, read in schemes
  refine hpure
    { T := (BigFppfOver.toScheme B S hS).obj D.T
      g := (BigFppfOver.toScheme B S hS).map γ
      t' := pointsToScheme B S hS D.T D.t'
      t := pointsToScheme B S hS D.T D.t
      specializes := D.specializes
      mapsToChosenPoint := by
        show (BigFppfOver.toScheme B S hS).map γ (pointsToScheme B S hS D.T D.t) = _
        rw [← pointsToScheme_pointsMap_yoneda, hγmap, pointsMap_comp_apply,
          D.mapsToChosenPoint]
      X_T := (BigFppfOver.toScheme B S hS).obj (pullback γ α)
      toX := (BigFppfOver.toScheme B S hS).map (pullback.snd γ α)
      toT := (BigFppfOver.toScheme B S hS).map (pullback.fst γ α)
      isPullback := ((IsPullback.of_hasPullback γ α).map (BigFppfOver.toScheme B S hS)).flip
      xi := pointsToScheme B S hS (pullback γ α) ξW
      xi_liesOver := by
        rw [← pointsToScheme_pointsMap_yoneda, hfstξ] }
    ⟨pointsToScheme_mem_relativeAssassin_of_represented α φ M eM D γ χ hχfst
      sqY.isoPullback_hom_snd hχξ hD.1,
      closure_inter_range_fiberι_eq_empty_of_represented α D γ χ.hom hχfst hχξ
        (D.isImpurity_iff.1 hD).2⟩

end AlgebraicGeometry.Space

end
