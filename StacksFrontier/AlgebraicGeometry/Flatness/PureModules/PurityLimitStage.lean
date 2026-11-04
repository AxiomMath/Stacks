module

public import StacksFrontier.AlgebraicGeometry.Flatness.PureModules.PurityCriterionLimits
public import StacksFrontier.AlgebraicGeometry.Flatness.PureModules.PurityLimitStageCriterion
public import StacksFrontier.AlgebraicGeometry.Flatness.PureModules.PurityLimitStageDescent
public import StacksFrontier.AlgebraicGeometry.Flatness.PureModules.PurityLimitStageFlatModel
public import StacksFrontier.AlgebraicGeometry.StalkFiniteType.FlatFinitePresentation

/-!
# Purity along a fibre passes to a finite stage

Let `S = lim S_k` be the limit of an inverse system of affine schemes indexed by a directed set,
let `f_i : X_i ⟶ S_i` be a morphism of finite presentation at one stage and let `ℱ_i` be a
finitely presented quasi-coherent `𝒪_{X_i}`-module which is flat over `S_i` at every point of the
fibre `(X_i)_{s_i}`. If the base change of `ℱ_i` to the limit is pure along the fibre over `s`,
then already the base change to some finite stage `k ≥ i` is pure along the fibre over `s_k`.

This is the second half of the proof of Tag 05MA.

## Main results

* `AlgebraicGeometry.exists_affine_elementary_chart` repackages Tags 05KW and 05K6 as the chart
  data the purity criterion of Tag 05L4 consumes.
* `AlgebraicGeometry.exists_baseChange_chart` base-changes that chart along an arbitrary morphism
  to the stage `S_i` and identifies the fibrewise containment locus of the base-changed chart
  with the inverse image of the fibrewise containment locus at the stage.
* `AlgebraicGeometry.exists_stage_isPureAlong` is the statement above.

## Implementation notes

The chart of Tags 05KW and 05K6 is produced once, at the stage `i`, and transported to the limit
and to the later stages by `AlgebraicGeometry.exists_baseChange_chart`: the elementary étale
neighbourhood `(A, a)` of `(S_i, s_i)` is replaced by `T ×_{S_i} A`, whose distinguished point
over a point `t` of `T` above `s_i` is produced by
`AlgebraicGeometry.exists_point_pullback_isIso_residueFieldMap`, and the étale chart upstairs is
replaced by its base change. Universal purity of the module on the chart is what survives this
transport, through Tag 05J6, and that is why the chart is produced by Tag 05K6 rather than only
by Tag 05L4.

The containment condition of the criterion is carried in the shape of
`AlgebraicGeometry.chartContainmentLocus`, and the content of the transport is that this locus
base-changes to an inverse image, which is Tag 05KQ in the form
`Stacks.RelativeAssassin.fibrewiseContainment_baseChange`. Since the locus at the stage is
locally constructible — Tag 05KR — and the locus at the limit is a neighbourhood of the
distinguished point, Tags 01Z4 and 05F4 place an open neighbourhood inside the inverse image of
the locus already at a finite stage, which is
`AlgebraicGeometry.exists_stage_isOpen_subset_preimage_of_mem_nhds_preimage`; the sufficiency
half of the criterion then gives purity there.

The index set is a directed set and the system is a functor out of `Iᵒᵖ`, as in the source: that
is the shape in which Tag 05F4 is available.

## References

* [Stacks Project, Tag 05MA](https://stacks.math.columbia.edu/tag/05MA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Topology TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### The fibrewise containment locus of a chart -/

/-- The fibrewise containment locus of a chart is the fibrewise containment locus of Tag 05KR,
taken for the base change of the morphism along the neighbourhood and for the open subscheme
which is the image of the chart. -/
public theorem chartContainmentLocus_eq_fibrewiseContainment {X S X' : Scheme.{u}} (f : X ⟶ S)
    (F : X.Modules) {s : S} (U : EtaleNeighborhood S s) (p : X' ⟶ U.scheme) (g : X' ⟶ X)
    (hcomm : g ≫ f = p ≫ U.toBase) (W : (pullback f U.toBase : Scheme.{u}).Opens)
    (hW : (W : Set (pullback f U.toBase : Scheme.{u})) =
      Set.range ⇑(pullback.lift g p hcomm)) :
    chartContainmentLocus f F U p g hcomm =
      Stacks.RelativeAssassin.fibrewiseContainment (pullback.snd f U.toBase)
        ((Scheme.Modules.pullback (pullback.fst f U.toBase)).obj F) W := by
  ext y
  rw [Stacks.RelativeAssassin.mem_fibrewiseContainment, hW]
  exact Iff.rfl

/-- The covering condition of the purity criterion is membership of the distinguished point of
the neighbourhood in the fibrewise containment locus of the chart. -/
public theorem exists_mem_range_of_mem_chartContainmentLocus {X S X' : Scheme.{u}} (f : X ⟶ S)
    (F : X.Modules) {s : S} (U : EtaleNeighborhood S s) (p : X' ⟶ U.scheme) (g : X' ⟶ X)
    (hcomm : g ≫ f = p ≫ U.toBase)
    (hmem : U.point ∈ chartContainmentLocus f F U p g hcomm) :
    ∀ z : (pullback.snd f U.toBase).fiber U.point,
      z ∈ Stacks.Divisors.associatedPoints
          ((Scheme.Modules.pullback ((pullback.snd f U.toBase).fiberι U.point)).obj
            ((Scheme.Modules.pullback (pullback.fst f U.toBase)).obj F)) →
        ∃ y : X', pullback.lift g p hcomm y =
          (pullback.snd f U.toBase).fiberι U.point z :=
  fun _ hz => hmem hz

/-- **The covering condition of Tag 05KW gives membership in the fibrewise containment locus.**
If every point of the fibre `X_s` is the image of a point of the chart lying over the
distinguished point of an elementary étale neighbourhood, then the distinguished point lies in
the fibrewise containment locus of the chart. -/
public theorem mem_chartContainmentLocus_of_cover {X S X' : Scheme.{u}} (f : X ⟶ S)
    (F : X.Modules) {s : S} (U : EtaleNeighborhood S s) (hU : U.IsElementary)
    (p : X' ⟶ U.scheme) (g : X' ⟶ X) (hcomm : g ≫ f = p ≫ U.toBase)
    (hcover : ∀ x : f.fiber s, ∃ y : X', g y = f.fiberι s x ∧ p y = U.point) :
    U.point ∈ chartContainmentLocus f F U p g hcomm := by
  have hres : IsIso (U.toBase.residueFieldMap U.point) :=
    (EtaleNeighborhood.isElementary_iff U).mp hU
  have hSpecIso : IsIso (Spec.map (U.toBase.residueFieldMap U.point)) := inferInstance
  have hbcf : IsIso (baseChangeFiberMap f U.toBase U.point) :=
    (isPullback_fiberToSpecResidueField_of_isPullback
      (IsPullback.of_hasPullback f U.toBase) U.point).isIso_fst_of_isIso
  have hcover' : ∀ x : f.fiber (U.toBase U.point), ∃ y : X',
      g y = f.fiberι (U.toBase U.point) x ∧ p y = U.point := by
    rw [U.map_point]; exact hcover
  have hliftfst : pullback.lift g p hcomm ≫ pullback.fst f U.toBase = g :=
    pullback.lift_fst _ _ _
  intro z _
  obtain ⟨y, hgy, hpy⟩ := hcover' (baseChangeFiberMap f U.toBase U.point z)
  refine ⟨y, ?_⟩
  have hqy : pullback.snd f U.toBase (pullback.lift g p hcomm y) = U.point := by
    rw [← Scheme.Hom.comp_apply, pullback.lift_snd]; exact hpy
  have hmemy : pullback.lift g p hcomm y ∈ (pullback.snd f U.toBase) ⁻¹' {U.point} := hqy
  have hzz : (pullback.snd f U.toBase).fiberι U.point
      (((pullback.snd f U.toBase).fiberHomeo U.point).symm ⟨_, hmemy⟩) =
        pullback.lift g p hcomm y :=
    (pullback.snd f U.toBase).fiberι_fiberHomeo_symm _ _
  have hpr : pullback.fst f U.toBase (pullback.lift g p hcomm y) = g y := by
    rw [← Scheme.Hom.comp_apply, hliftfst]
  have hz'img : f.fiberι (U.toBase U.point) (baseChangeFiberMap f U.toBase U.point
      (((pullback.snd f U.toBase).fiberHomeo U.point).symm ⟨_, hmemy⟩)) = g y := by
    rw [← Scheme.Hom.comp_apply, baseChangeFiberMap_comp_fiberι, Scheme.Hom.comp_apply,
      hzz, hpr]
  have heqbcf : baseChangeFiberMap f U.toBase U.point
      (((pullback.snd f U.toBase).fiberHomeo U.point).symm ⟨_, hmemy⟩) =
        baseChangeFiberMap f U.toBase U.point z :=
    (f.fiberι (U.toBase U.point)).isEmbedding.injective (hz'img.trans hgy)
  have hzeq : (((pullback.snd f U.toBase).fiberHomeo U.point).symm ⟨_, hmemy⟩) = z :=
    (Scheme.homeoOfIso (asIso _)).injective heqbcf
  rw [← hzz, hzeq]

/-! ### The fibrewise containment locus of an arbitrary base change -/

/-- **Stacks Project, Tag 05KQ** for an arbitrary presentation of the base change. The fibrewise
containment locus of a base change of `(q, G, W)` is the inverse image of the fibrewise
containment locus of `(q, G, W)`, for any cartesian square, any module isomorphic to the
pullback and any open subscheme whose underlying set is the inverse image. -/
public theorem fibrewiseContainment_eq_preimage_of_isPullback {Z B Z' B' : Scheme.{u}}
    (q : Z ⟶ B) [LocallyOfFiniteType q] (G : Z.Modules) [G.IsQuasicoherent] [G.IsFiniteType]
    (W : Z.Opens) {q' : Z' ⟶ B'} {β : B' ⟶ B} {ζ : Z' ⟶ Z} (hpb : IsPullback ζ q' q β)
    (G' : Z'.Modules) (eG : G' ≅ (Scheme.Modules.pullback ζ).obj G)
    (W' : Z'.Opens) (hW' : (W' : Set Z') = ζ ⁻¹' (W : Set Z)) :
    Stacks.RelativeAssassin.fibrewiseContainment q' G' W' =
      β ⁻¹' Stacks.RelativeAssassin.fibrewiseContainment q G W := by
  have hfst : hpb.isoPullback.hom ≫ pullback.fst q β = ζ := hpb.isoPullback_hom_fst
  have hsnd : hpb.isoPullback.hom ≫ pullback.snd q β = q' := hpb.isoPullback_hom_snd
  have hpt : ∀ x : Z', pullback.fst q β (hpb.isoPullback.hom x) = ζ x := fun x => by
    have h : (hpb.isoPullback.hom ≫ pullback.fst q β) x = ζ x :=
      congrArg (fun m : Z' ⟶ Z => m x) hfst
    rwa [Scheme.Hom.comp_apply] at h
  rw [← Stacks.RelativeAssassin.fibrewiseContainment_baseChange q G W β]
  refine Stacks.RelativeAssassin.fibrewiseContainment_eq_of_iso (pullback.snd q β) q'
    hpb.isoPullback hsnd ((Scheme.Modules.pullback (pullback.fst q β)).obj G) G' ?_
    (pullback.fst q β ⁻¹ᵁ W) W' ?_
  · exact eG ≪≫ eqToIso (by rw [hfst]) ≪≫
      ((Scheme.Modules.pullbackComp hpb.isoPullback.hom (pullback.fst q β)).app G).symm
  · refine TopologicalSpace.Opens.ext ?_
    rw [hW']
    ext x
    simp only [Scheme.Hom.coe_preimage, Set.mem_preimage, hpt x]

/-! ### The chart of Tags 05KW and 05K6 -/

/-- The pullback of a finite type module is of finite type. -/
private theorem isFiniteType_pullback_obj {X Y : Scheme.{u}} (g : X ⟶ Y) (F : Y.Modules)
    [F.IsFiniteType] : ((Scheme.Modules.pullback g).obj F).IsFiniteType :=
  SheafOfModules.pullback_isFiniteType g.toLRSHom.toShHom F

/-- The pullback of a quasi-coherent module is quasi-coherent. -/
private theorem isQuasicoherent_pullback_obj {X Y : Scheme.{u}} (g : X ⟶ Y) (F : Y.Modules)
    [F.IsQuasicoherent] : ((Scheme.Modules.pullback g).obj F).IsQuasicoherent :=
  @SheafOfModules.modulePullback_isQuasicoherent X.toRingedSpace Y.toRingedSpace
    g.toLRSHom.toShHom F ‹_›

/-- **Stacks Project, Tags 05KW and 05K6.** For a morphism `f : X ⟶ S` of finite presentation
and a finitely presented quasi-coherent `𝒪_X`-module `ℱ` flat over `S` at every point of the
fibre `X_s`, there are an affine elementary étale neighbourhood `(A, a)` of `(S, s)` and an
affine scheme `Y` étale over `X` and lying over `A` whose points over `a` cover the fibre `X_s`,
such that the pullback of `ℱ` to `Y` is universally pure relative to `A`. -/
public theorem exists_affine_elementary_chart {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFinitePresentation] [F.IsFiniteType] (s : S)
    (hflat : ∀ x : f.fiber s, IsFlatOverAt f.toLRSHom.toShHom F (f.fiberι s x)) :
    ∃ (A : EtaleNeighborhood S s) (_ : A.IsElementary) (_ : IsAffine A.scheme)
      (Y : Scheme.{u}) (_ : IsAffine Y) (p : Y ⟶ A.scheme) (g : Y ⟶ X) (_ : Etale g)
      (_ : LocallyOfFiniteType p) (_ : QuasiCompact p) (_ : g ≫ f = p ≫ A.toBase),
      IsUniversallyPureRelative p ((Scheme.Modules.pullback g).obj F) ∧
        ∀ x : f.fiber s, ∃ y : Y, g y = f.fiberι s x ∧ p y = A.point := by
  have hID : ExistsElementaryEtaleNeighborhoodProjectiveSections.{u} := by
    intro X S f _ F _ _ x hfl
    exact exists_elementaryEtaleNeighborhood_projective_sections_of_isFlatOverAt f F x hfl
  obtain ⟨A, hAelem, hAaff, Y, hYaff, p, g, hgEt, hcomm, hcover, hproj⟩ :=
    exists_elementary_pointed_projective_cover hID f F s
      ⟨inferInstance, inferInstance, inferInstance⟩ hflat
  have : Etale g := hgEt
  have : IsAffine A.scheme := hAaff
  have : IsAffine Y := hYaff
  have : IsAffineHom p := isAffineHom_of_isAffine p
  have hlftc : LocallyOfFiniteType (p ≫ A.toBase) := by
    rw [hcomm]
    infer_instance
  have hlft : LocallyOfFiniteType p := locallyOfFiniteType_of_comp p A.toBase
  have := isFiniteType_pullback_obj g F
  have := isQuasicoherent_pullback_obj g F
  have hUPR : IsUniversallyPureRelative p ((Scheme.Modules.pullback g).obj F) := by
    refine isUniversallyPureRelative_of_pushforward_isLocallyProjective p _ ?_
    let : Module Γ(A.scheme, ⊤) Γ((Scheme.Modules.pullback g).obj F, ⊤) :=
      Module.compHom _ p.appTop.hom
    refine (isLocallyProjective_iff_exists_affineOpen_cover _).2
      ⟨PUnit.{u + 1}, fun _ => ⊤, IsOpenCover.mk (by simp), fun _ => isAffineOpen_top _,
        fun _ => ?_⟩
    exact hproj
  exact ⟨A, hAelem, hAaff, Y, hYaff, p, g, hgEt, hlft, inferInstance, hcomm.symm, hUPR, hcover⟩

/-! ### Base change of the chart -/

/-- **The chart of Tags 05KW and 05K6, base-changed.** Let `(A, π)` be an étale neighbourhood of
the stage `S_i`, carrying an étale chart `g : Y ⟶ X_i` over `A` with `g^*ℱ_i` universally pure
relative to `A`. Along any morphism `v : T ⟶ S_i` and any point `z` of `T ×_{S_i} A` over a point
`t` of `T`, the chart base-changes to a chart over the étale neighbourhood `T ×_{S_i} A` of
`(T, t)`, again with the pullback of the module pure upstairs, and the fibrewise containment
locus of the base-changed chart is the inverse image of the fibrewise containment locus of the
given one. -/
public theorem exists_baseChange_chart {Si Xi A Y T XT : Scheme.{u}}
    (fi : Xi ⟶ Si) [LocallyOfFiniteType fi] [QuasiCompact fi]
    (Fi : Xi.Modules) [Fi.IsFiniteType] [Fi.IsQuasicoherent]
    (π : A ⟶ Si) [Etale π] (p : Y ⟶ A) [LocallyOfFiniteType p] [QuasiCompact p]
    (g : Y ⟶ Xi) [Etale g] (hcomm : g ≫ fi = p ≫ π)
    (hUP : IsUniversallyPureRelative p ((Scheme.Modules.pullback g).obj Fi))
    (Wi : (pullback fi π : Scheme.{u}).Opens)
    (hWi : (Wi : Set (pullback fi π : Scheme.{u})) = Set.range ⇑(pullback.lift g p hcomm))
    (v : T ⟶ Si) {fT : XT ⟶ T} [LocallyOfFiniteType fT] [QuasiCompact fT]
    {toXi : XT ⟶ Xi} (hpbT : IsPullback toXi fT fi v)
    (FT : XT.Modules) [FT.IsFiniteType] [FT.IsQuasicoherent]
    (eFT : FT ≅ (Scheme.Modules.pullback toXi).obj Fi)
    (t : T) (z : (pullback v π : Scheme.{u})) (hzt : pullback.fst v π z = t) :
    ∃ (YT : Scheme.{u}) (pT : YT ⟶ (pullback v π : Scheme.{u})) (gT : YT ⟶ XT)
      (_ : LocallyOfFiniteType pT) (_ : QuasiCompact pT) (_ : Etale gT)
      (hcommT : gT ≫ fT = pT ≫ pullback.fst v π),
      IsPureAlong ({ S := (pullback v π : Scheme.{u}), X := YT, f := pT,
                     F := (Scheme.Modules.pullback gT).obj FT,
                     s := z } : PrePureSituation.{u}) ∧
        chartContainmentLocus fT FT
            ({ scheme := (pullback v π : Scheme.{u}), point := z, toBase := pullback.fst v π,
               map_point := hzt } : EtaleNeighborhood T t) pT gT hcommT =
          pullback.snd v π ⁻¹' Stacks.RelativeAssassin.fibrewiseContainment
            (pullback.snd fi π) ((Scheme.Modules.pullback (pullback.fst fi π)).obj Fi) Wi := by
  classical
  have := isFiniteType_pullback_obj (pullback.fst fi π) Fi
  have := isQuasicoherent_pullback_obj (pullback.fst fi π) Fi
  have := isFiniteType_pullback_obj g Fi
  have := isQuasicoherent_pullback_obj g Fi
  have hEtL : Etale (pullback.lift g p hcomm) := etale_pullback_lift_of_etale fi π g p hcomm
  have hLr : pullback.lift g p hcomm ≫ pullback.fst fi π = g := pullback.lift_fst _ _ _
  have hLq : pullback.lift g p hcomm ≫ pullback.snd fi π = p := pullback.lift_snd _ _ _
  have hZT : pullback.fst fT (pullback.fst v π) ≫ fT =
      pullback.snd fT (pullback.fst v π) ≫ pullback.fst v π := pullback.condition
  have hAT : pullback.fst v π ≫ v = pullback.snd v π ≫ π := pullback.condition
  have hcz : (pullback.fst fT (pullback.fst v π) ≫ toXi) ≫ fi =
      (pullback.snd fT (pullback.fst v π) ≫ pullback.snd v π) ≫ π := by
    rw [Category.assoc, hpbT.w, reassoc_of% hZT, hAT, Category.assoc]
  set ζ : (pullback fT (pullback.fst v π) : Scheme.{u}) ⟶ (pullback fi π : Scheme.{u}) :=
    pullback.lift (pullback.fst fT (pullback.fst v π) ≫ toXi)
      (pullback.snd fT (pullback.fst v π) ≫ pullback.snd v π) hcz with hζdef
  have hζr : ζ ≫ pullback.fst fi π =
      pullback.fst fT (pullback.fst v π) ≫ toXi := by
    rw [hζdef, pullback.lift_fst]
  have hζq : ζ ≫ pullback.snd fi π =
      pullback.snd fT (pullback.fst v π) ≫ pullback.snd v π := by
    rw [hζdef, pullback.lift_snd]
  have houter : IsPullback (ζ ≫ pullback.fst fi π) (pullback.snd fT (pullback.fst v π)) fi
      (pullback.snd v π ≫ π) := by
    rw [hζr, ← hAT]
    exact (IsPullback.of_hasPullback fT (pullback.fst v π)).paste_horiz hpbT
  have hpbζ : IsPullback ζ (pullback.snd fT (pullback.fst v π)) (pullback.snd fi π)
      (pullback.snd v π) :=
    IsPullback.of_right houter hζq (IsPullback.of_hasPullback fi π)
  -- The base-changed chart, as the base change of the chart along `ζ`.
  have hYTcond : pullback.fst (pullback.lift g p hcomm) ζ ≫ pullback.lift g p hcomm =
      pullback.snd (pullback.lift g p hcomm) ζ ≫ ζ := pullback.condition
  have hYTpb : IsPullback (pullback.fst (pullback.lift g p hcomm) ζ)
      (pullback.snd (pullback.lift g p hcomm) ζ ≫ pullback.snd fT (pullback.fst v π))
      p (pullback.snd v π) := by
    have h := (IsPullback.of_hasPullback (pullback.lift g p hcomm) ζ).paste_vert hpbζ
    rwa [hLq] at h
  have hlftpT : LocallyOfFiniteType
      (pullback.snd (pullback.lift g p hcomm) ζ ≫ pullback.snd fT (pullback.fst v π)) :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) hYTpb inferInstance
  have hqcpT : QuasiCompact
      (pullback.snd (pullback.lift g p hcomm) ζ ≫ pullback.snd fT (pullback.fst v π)) :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) hYTpb inferInstance
  have hEtgT : Etale
      (pullback.snd (pullback.lift g p hcomm) ζ ≫ pullback.fst fT (pullback.fst v π)) :=
    inferInstance
  have hcommT : (pullback.snd (pullback.lift g p hcomm) ζ ≫
        pullback.fst fT (pullback.fst v π)) ≫ fT =
      (pullback.snd (pullback.lift g p hcomm) ζ ≫
        pullback.snd fT (pullback.fst v π)) ≫ pullback.fst v π := by
    rw [Category.assoc, Category.assoc, hZT]
  have hliftT : pullback.lift
      (pullback.snd (pullback.lift g p hcomm) ζ ≫ pullback.fst fT (pullback.fst v π))
      (pullback.snd (pullback.lift g p hcomm) ζ ≫ pullback.snd fT (pullback.fst v π))
      hcommT = pullback.snd (pullback.lift g p hcomm) ζ :=
    pullback.hom_ext (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
  -- The image of the base-changed chart.
  have hWTopen : IsOpen (Set.range ⇑(pullback.snd (pullback.lift g p hcomm) ζ)) :=
    (pullback.snd (pullback.lift g p hcomm) ζ).isOpenMap.isOpen_range
  have hWTpre : Set.range ⇑(pullback.snd (pullback.lift g p hcomm) ζ) =
      ζ ⁻¹' (Wi : Set (pullback fi π : Scheme.{u})) := by
    rw [hWi]
    exact Scheme.Pullback.range_snd (pullback.lift g p hcomm) ζ
  -- The comparison of the two modules on the base change.
  have hgTcomp : (pullback.snd (pullback.lift g p hcomm) ζ ≫
        pullback.fst fT (pullback.fst v π)) ≫ toXi =
      pullback.fst (pullback.lift g p hcomm) ζ ≫ g := by
    rw [Category.assoc, ← hζr, ← reassoc_of% hYTcond, hLr]
  have := isFiniteType_pullback_obj (pullback.snd (pullback.lift g p hcomm) ζ ≫
    pullback.fst fT (pullback.fst v π)) FT
  have := isQuasicoherent_pullback_obj (pullback.snd (pullback.lift g p hcomm) ζ ≫
    pullback.fst fT (pullback.fst v π)) FT
  refine ⟨pullback (pullback.lift g p hcomm) ζ,
    pullback.snd (pullback.lift g p hcomm) ζ ≫ pullback.snd fT (pullback.fst v π),
    pullback.snd (pullback.lift g p hcomm) ζ ≫ pullback.fst fT (pullback.fst v π),
    hlftpT, hqcpT, hEtgT, hcommT, ?_, ?_⟩
  · refine (isUniversallyPureAlong_iff_forall_baseChange_isPureAlong
      ({ S := A, X := Y, f := p, F := (Scheme.Modules.pullback g).obj Fi,
         s := pullback.snd v π z } : PrePureSituation.{u})).mp
      (hUP (pullback.snd v π z)) _ (pullback.snd v π) rfl
      (pullback.fst (pullback.lift g p hcomm) ζ) hYTpb ?_
    exact (Scheme.Modules.pullback (pullback.snd (pullback.lift g p hcomm) ζ ≫
        pullback.fst fT (pullback.fst v π))).mapIso eFT ≪≫
      (Scheme.Modules.pullbackComp (pullback.snd (pullback.lift g p hcomm) ζ ≫
        pullback.fst fT (pullback.fst v π)) toXi).app Fi ≪≫
      eqToIso (by rw [hgTcomp]) ≪≫
      ((Scheme.Modules.pullbackComp (pullback.fst (pullback.lift g p hcomm) ζ) g).app Fi).symm
  · rw [chartContainmentLocus_eq_fibrewiseContainment fT FT
      ({ scheme := (pullback v π : Scheme.{u}), point := z, toBase := pullback.fst v π,
         map_point := hzt } : EtaleNeighborhood T t)
      (pullback.snd (pullback.lift g p hcomm) ζ ≫ pullback.snd fT (pullback.fst v π))
      (pullback.snd (pullback.lift g p hcomm) ζ ≫ pullback.fst fT (pullback.fst v π)) hcommT
      ⟨_, hWTopen⟩ (by rw [hliftT]; rfl)]
    refine fibrewiseContainment_eq_preimage_of_isPullback (pullback.snd fi π)
      ((Scheme.Modules.pullback (pullback.fst fi π)).obj Fi) Wi hpbζ _ ?_ ⟨_, hWTopen⟩ hWTpre
    exact (Scheme.Modules.pullback (pullback.fst fT (pullback.fst v π))).mapIso eFT ≪≫
      (Scheme.Modules.pullbackComp (pullback.fst fT (pullback.fst v π)) toXi).app Fi ≪≫
      eqToIso (by rw [hζr]) ≪≫
      ((Scheme.Modules.pullbackComp ζ (pullback.fst fi π)).app Fi).symm


/-! ### The two halves of the criterion, for a base change of the chart -/

/-- **Tag 05L4, necessity, for a base change of the chart.** If the base change of `ℱ_i` along
`v : T ⟶ S_i` is pure along the fibre over `t`, then the inverse image of the fibrewise
containment locus of the chart is a neighbourhood of the distinguished point of the
base-changed neighbourhood. -/
public theorem preimage_fibrewiseContainment_mem_nhds_of_isPureAlong {Si Xi A Y T XT : Scheme.{u}}
    (fi : Xi ⟶ Si) [LocallyOfFiniteType fi] [QuasiCompact fi]
    (Fi : Xi.Modules) [Fi.IsFiniteType] [Fi.IsQuasicoherent]
    (π : A ⟶ Si) [Etale π] (p : Y ⟶ A) [LocallyOfFiniteType p] [QuasiCompact p]
    (g : Y ⟶ Xi) [Etale g] (hcomm : g ≫ fi = p ≫ π)
    (hUP : IsUniversallyPureRelative p ((Scheme.Modules.pullback g).obj Fi))
    (Wi : (pullback fi π : Scheme.{u}).Opens)
    (hWi : (Wi : Set (pullback fi π : Scheme.{u})) = Set.range ⇑(pullback.lift g p hcomm))
    (hlc : IsLocallyConstructible (Stacks.RelativeAssassin.fibrewiseContainment
      (pullback.snd fi π) ((Scheme.Modules.pullback (pullback.fst fi π)).obj Fi) Wi))
    (v : T ⟶ Si) {fT : XT ⟶ T} [LocallyOfFiniteType fT] [QuasiCompact fT]
    {toXi : XT ⟶ Xi} (hpbT : IsPullback toXi fT fi v)
    (FT : XT.Modules) [FT.IsFiniteType] [FT.IsQuasicoherent]
    (eFT : FT ≅ (Scheme.Modules.pullback toXi).obj Fi)
    (t : T) (z : (pullback v π : Scheme.{u})) (hzt : pullback.fst v π z = t)
    (hzres : IsIso ((pullback.fst v π).residueFieldMap z))
    (hzmem : pullback.snd v π z ∈ Stacks.RelativeAssassin.fibrewiseContainment
      (pullback.snd fi π) ((Scheme.Modules.pullback (pullback.fst fi π)).obj Fi) Wi)
    (hflatT : ∀ x : fT.fiber t, IsFlatOverAt fT.toLRSHom.toShHom FT (fT.fiberι t x))
    (hpureT : IsPureAlong
      ({ S := T, X := XT, f := fT, F := FT, s := t } : PrePureSituation.{u})) :
    pullback.snd v π ⁻¹' Stacks.RelativeAssassin.fibrewiseContainment (pullback.snd fi π)
        ((Scheme.Modules.pullback (pullback.fst fi π)).obj Fi) Wi ∈ 𝓝 z := by
  obtain ⟨YT, pT, gT, hlftpT, hqcpT, hEtgT, hcommT, hpureC, hlocus⟩ :=
    exists_baseChange_chart fi Fi π p g hcomm hUP Wi hWi v hpbT FT eFT t z hzt
  have : LocallyOfFiniteType pT := hlftpT
  have : QuasiCompact pT := hqcpT
  have : Etale gT := hEtgT
  have := isFiniteType_pullback_obj gT FT
  have := isQuasicoherent_pullback_obj gT FT
  have hmem : z ∈ chartContainmentLocus fT FT
      ({ scheme := (pullback v π : Scheme.{u}), point := z, toBase := pullback.fst v π,
         map_point := hzt } : EtaleNeighborhood T t) pT gT hcommT := by
    rw [hlocus]; exact Set.mem_preimage.mpr hzmem
  have hcov := exists_mem_range_of_mem_chartContainmentLocus fT FT
    ({ scheme := (pullback v π : Scheme.{u}), point := z, toBase := pullback.fst v π,
       map_point := hzt } : EtaleNeighborhood T t) pT gT hcommT hmem
  have hElc : IsLocallyConstructible (chartContainmentLocus fT FT
      ({ scheme := (pullback v π : Scheme.{u}), point := z, toBase := pullback.fst v π,
         map_point := hzt } : EtaleNeighborhood T t) pT gT hcommT) := by
    rw [hlocus]; exact isLocallyConstructible_preimage _ hlc
  have h := chartContainmentLocus_mem_nhds_of_isPureAlong fT FT t
    ({ scheme := (pullback v π : Scheme.{u}), point := z, toBase := pullback.fst v π,
       map_point := hzt } : EtaleNeighborhood T t)
    ((EtaleNeighborhood.isElementary_iff _).mpr hzres) pT gT hcommT hflatT hpureC hcov hElc
    hpureT
  rw [hlocus] at h
  exact h

/-- **Tag 05L4, sufficiency, for a base change of the chart.** If the inverse image of the
fibrewise containment locus of the chart contains an open neighbourhood of the distinguished
point of the base-changed neighbourhood, then the base change of `ℱ_i` along `v : T ⟶ S_i` is
pure along the fibre over `t`. -/
public theorem isPureAlong_of_isOpen_subset_preimage_fibrewiseContainment
    {Si Xi A Y T XT : Scheme.{u}}
    (fi : Xi ⟶ Si) [LocallyOfFiniteType fi] [QuasiCompact fi]
    (Fi : Xi.Modules) [Fi.IsFiniteType] [Fi.IsQuasicoherent]
    (π : A ⟶ Si) [Etale π] (p : Y ⟶ A) [LocallyOfFiniteType p] [QuasiCompact p]
    (g : Y ⟶ Xi) [Etale g] (hcomm : g ≫ fi = p ≫ π)
    (hUP : IsUniversallyPureRelative p ((Scheme.Modules.pullback g).obj Fi))
    (Wi : (pullback fi π : Scheme.{u}).Opens)
    (hWi : (Wi : Set (pullback fi π : Scheme.{u})) = Set.range ⇑(pullback.lift g p hcomm))
    (v : T ⟶ Si) {fT : XT ⟶ T} [LocallyOfFiniteType fT] [QuasiCompact fT]
    {toXi : XT ⟶ Xi} (hpbT : IsPullback toXi fT fi v)
    (FT : XT.Modules) [FT.IsFiniteType] [FT.IsQuasicoherent]
    (eFT : FT ≅ (Scheme.Modules.pullback toXi).obj Fi)
    (t : T) (z : (pullback v π : Scheme.{u})) (hzt : pullback.fst v π z = t)
    (hzres : IsIso ((pullback.fst v π).residueFieldMap z))
    (hzmem : pullback.snd v π z ∈ Stacks.RelativeAssassin.fibrewiseContainment
      (pullback.snd fi π) ((Scheme.Modules.pullback (pullback.fst fi π)).obj Fi) Wi)
    (hflatT : ∀ x : fT.fiber t, IsFlatOverAt fT.toLRSHom.toShHom FT (fT.fiberι t x))
    (V : Set (pullback v π : Scheme.{u})) (hVopen : IsOpen V) (hVmem : z ∈ V)
    (hVsub : V ⊆ pullback.snd v π ⁻¹' Stacks.RelativeAssassin.fibrewiseContainment
      (pullback.snd fi π) ((Scheme.Modules.pullback (pullback.fst fi π)).obj Fi) Wi) :
    IsPureAlong ({ S := T, X := XT, f := fT, F := FT, s := t } : PrePureSituation.{u}) := by
  obtain ⟨YT, pT, gT, hlftpT, hqcpT, hEtgT, hcommT, hpureC, hlocus⟩ :=
    exists_baseChange_chart fi Fi π p g hcomm hUP Wi hWi v hpbT FT eFT t z hzt
  have : LocallyOfFiniteType pT := hlftpT
  have : QuasiCompact pT := hqcpT
  have : Etale gT := hEtgT
  have := isFiniteType_pullback_obj gT FT
  have := isQuasicoherent_pullback_obj gT FT
  have hmem : z ∈ chartContainmentLocus fT FT
      ({ scheme := (pullback v π : Scheme.{u}), point := z, toBase := pullback.fst v π,
         map_point := hzt } : EtaleNeighborhood T t) pT gT hcommT := by
    rw [hlocus]; exact Set.mem_preimage.mpr hzmem
  have hcov := exists_mem_range_of_mem_chartContainmentLocus fT FT
    ({ scheme := (pullback v π : Scheme.{u}), point := z, toBase := pullback.fst v π,
       map_point := hzt } : EtaleNeighborhood T t) pT gT hcommT hmem
  have hVsub' : V ⊆ chartContainmentLocus fT FT
      ({ scheme := (pullback v π : Scheme.{u}), point := z, toBase := pullback.fst v π,
         map_point := hzt } : EtaleNeighborhood T t) pT gT hcommT := by
    rw [hlocus]; exact hVsub
  exact isPureAlong_of_isOpen_subset_chartContainmentLocus fT FT t
    ({ scheme := (pullback v π : Scheme.{u}), point := z, toBase := pullback.fst v π,
       map_point := hzt } : EtaleNeighborhood T t)
    ((EtaleNeighborhood.isElementary_iff _).mpr hzres) pT gT hcommT hflatT hpureC hcov
    V hVopen hVmem hVsub'

/-! ### Purity at a finite stage -/

/-- Flatness along the fibre over `s₀` of a finitely presented module on a stage passes to its
base change along `g` at the points of the fibre over any `s` with `g s = s₀`. -/
private theorem isFlatOverAt_fiberι_of_isPullback {Xi Si S X : Scheme.{u}} {fi : Xi ⟶ Si}
    {g : S ⟶ Si} {a : X ⟶ Xi} {f : X ⟶ S} (hpb : IsPullback a f fi g) (Fi : Xi.Modules)
    [Fi.IsQuasicoherent] (F : X.Modules) (eF : F ≅ (Scheme.Modules.pullback a).obj Fi)
    (s : S) (s₀ : Si) (hs : g s = s₀)
    (hflat : ∀ x : fi.fiber s₀, IsFlatOverAt fi.toLRSHom.toShHom Fi (fi.fiberι s₀ x)) :
    ∀ x : f.fiber s, IsFlatOverAt f.toLRSHom.toShHom F (f.fiberι s x) := by
  intro x
  have hy : fi (a (f.fiberι s x)) = s₀ := by
    rw [← hs, ← Scheme.Hom.comp_apply, hpb.w, Scheme.Hom.comp_apply, Scheme.Hom.apply_fiberι]
  have hflatpt := hflat ((fi.fiberHomeo s₀).symm ⟨_, hy⟩)
  rw [fi.fiberι_fiberHomeo_symm] at hflatpt
  exact isFlatOverAt_of_moduleIso f.toLRSHom.toShHom eF.symm _
    (@modulePullback_isFlatOverAt Xi Si S X fi g a f hpb Fi ‹_› (f.fiberι s x) hflatpt)

/-- **Stacks Project, Tag 05MA, the purity step.** Let `S = lim S_k` be the limit of an inverse
system of affine schemes indexed by a directed set, let `f_i : X_i ⟶ S_i` be of finite
presentation at a stage `i` and let `ℱ_i` be a finitely presented quasi-coherent
`𝒪_{X_i}`-module which is flat over `S_i` at every point of the fibre `(X_i)_{s_i}`. If the
base change of `ℱ_i` to `S` is pure along the fibre over `s`, then the base change of `ℱ_i` to
some finite stage `k ≥ i` is pure along the fibre over `s_k`. -/
public theorem exists_stage_isPureAlong {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    [Nonempty I] (D : Iᵒᵖ ⥤ Scheme.{u}) [∀ k : Iᵒᵖ, IsAffine (D.obj k)]
    (c : Cone D) (hc : IsLimit c) (i : I) {Xi : Scheme.{u}} (fi : Xi ⟶ D.obj (op i))
    [LocallyOfFinitePresentation fi] [QuasiCompact fi] [QuasiSeparated fi]
    (Fi : Xi.Modules) [Fi.IsQuasicoherent] [Fi.IsFinitePresentation] [Fi.IsFiniteType]
    (s : c.pt) {X : Scheme.{u}} {f : X ⟶ c.pt} [LocallyOfFiniteType f] [QuasiCompact f]
    (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent]
    {a : X ⟶ Xi} (hpb : IsPullback a f fi (c.π.app (op i)))
    (eF : F ≅ (Scheme.Modules.pullback a).obj Fi)
    (hpure : IsPureAlong ({ S := c.pt, X := X, f := f, F := F, s := s } : PrePureSituation.{u}))
    (hflati : ∀ x : fi.fiber (c.π.app (op i) s),
      IsFlatOverAt fi.toLRSHom.toShHom Fi (fi.fiberι (c.π.app (op i) s) x)) :
    ∃ (k : I) (hik : i ≤ k)
      (_ : LocallyOfFiniteType (pullback.snd fi (D.map (homOfLE hik).op)))
      (_ : QuasiCompact (pullback.snd fi (D.map (homOfLE hik).op)))
      (_ : ((Scheme.Modules.pullback
        (pullback.fst fi (D.map (homOfLE hik).op))).obj Fi).IsFiniteType)
      (_ : ((Scheme.Modules.pullback
        (pullback.fst fi (D.map (homOfLE hik).op))).obj Fi).IsQuasicoherent),
      IsPureAlong ({ S := D.obj (op k), X := pullback fi (D.map (homOfLE hik).op),
                     f := pullback.snd fi (D.map (homOfLE hik).op),
                     F := (Scheme.Modules.pullback
                       (pullback.fst fi (D.map (homOfLE hik).op))).obj Fi,
                     s := c.π.app (op k) s } : PrePureSituation.{u}) := by
  classical
  -- Flatness of `ℱ` at the points of `X_s`, transported from the stage.
  have hflatLim := isFlatOverAt_fiberι_of_isPullback hpb Fi F eF s _ rfl hflati
  -- Step 2: the chart of Tags 05KW and 05K6 at the stage `i`.
  obtain ⟨A, hAelem, hAaff, Y, hYaff, p, g, hgEt, hlftp, hqcp, hcomm, hUP, hcov⟩ :=
    exists_affine_elementary_chart fi Fi (c.π.app (op i) s) hflati
  have : Etale g := hgEt
  have : IsAffine A.scheme := hAaff
  have : IsAffine Y := hYaff
  have : LocallyOfFiniteType p := hlftp
  have : QuasiCompact p := hqcp
  have hEtL : Etale (pullback.lift g p hcomm) :=
    etale_pullback_lift_of_etale fi A.toBase g p hcomm
  obtain ⟨Wi, hWi⟩ : ∃ W : (pullback fi A.toBase : Scheme.{u}).Opens,
      (W : Set (pullback fi A.toBase : Scheme.{u})) =
        Set.range ⇑(pullback.lift g p hcomm) :=
    ⟨⟨_, (pullback.lift g p hcomm).isOpenMap.isOpen_range⟩, rfl⟩
  -- Tag 05KR: the fibrewise containment locus at the stage is locally constructible.
  have := isFiniteType_pullback_obj (pullback.fst fi A.toBase) Fi
  have := isQuasicoherent_pullback_obj (pullback.fst fi A.toBase) Fi
  have hGifp :
      ((Scheme.Modules.pullback (pullback.fst fi A.toBase)).obj Fi).IsFinitePresentation :=
    Stacks.AlgebraicGeometry.ModuleLimits.isFinitePresentation_pullback _ Fi
  have hWcpt : IsCompact (Wi : Set (pullback fi A.toBase : Scheme.{u})) := by
    rw [hWi]; exact isCompact_range (pullback.lift g p hcomm).continuous
  have hqsp : QuasiSeparatedSpace (pullback fi A.toBase : Scheme.{u}) :=
    (quasiSeparated_iff_quasiSeparatedSpace (pullback.snd fi A.toBase)).mp inferInstance
  have hWqc : QuasiCompact Wi.ι := quasiCompact_opens_ι hWcpt
  have hEiLC : IsLocallyConstructible
      (Stacks.RelativeAssassin.fibrewiseContainment (pullback.snd fi A.toBase)
        ((Scheme.Modules.pullback (pullback.fst fi A.toBase)).obj Fi) Wi) :=
    Stacks.RelativeAssassin.isLocallyConstructible_fibrewiseContainment
      (pullback.snd fi A.toBase) ⟨inferInstance, inferInstance, inferInstance⟩
      ((Scheme.Modules.pullback (pullback.fst fi A.toBase)).obj Fi) Wi
  have hAmem : A.point ∈ Stacks.RelativeAssassin.fibrewiseContainment
      (pullback.snd fi A.toBase)
      ((Scheme.Modules.pullback (pullback.fst fi A.toBase)).obj Fi) Wi := by
    rw [← chartContainmentLocus_eq_fibrewiseContainment fi Fi A p g hcomm Wi hWi]
    exact mem_chartContainmentLocus_of_cover fi Fi A hAelem p g hcomm hcov
  have hAres : IsIso (A.toBase.residueFieldMap A.point) :=
    (EtaleNeighborhood.isElementary_iff A).mp hAelem
  -- The distinguished point of the base-changed neighbourhood at the limit.
  obtain ⟨zl, hzl1, hzl2, hzl3⟩ := exists_point_pullback_isIso_residueFieldMap
    A.toBase (c.π.app (op i)) A.point s A.map_point.symm hAres
  -- Tag 05L4, necessity, at the limit.
  have hnhdsL := preimage_fibrewiseContainment_mem_nhds_of_isPureAlong fi Fi A.toBase p g
    hcomm hUP Wi hWi hEiLC (c.π.app (op i)) hpb F eF s zl hzl1 hzl3
    (by rw [hzl2]; exact hAmem) hflatLim hpure
  -- Tags 01Z4 and 05F4: an open neighbourhood inside the locus already at a finite stage.
  obtain ⟨k, hik, τ, V, hτfst, hτsnd, hVopen, hVmem, hVsub⟩ :=
    exists_stage_isOpen_subset_preimage_of_mem_nhds_preimage D c hc i A.toBase hEiLC zl hnhdsL
  -- The distinguished point of the base-changed neighbourhood at the stage `k`.
  have hτz1 : pullback.fst (D.map (homOfLE hik).op) A.toBase (τ zl) = c.π.app (op k) s := by
    have h := congrArg
      (fun m : (pullback (c.π.app (op i)) A.toBase : Scheme.{u}) ⟶ D.obj (op k) => m zl) hτfst
    simpa [hzl1] using h
  have hτz2 : pullback.snd (D.map (homOfLE hik).op) A.toBase (τ zl) = A.point := by
    have h := congrArg
      (fun m : (pullback (c.π.app (op i)) A.toBase : Scheme.{u}) ⟶ A.scheme => m zl) hτsnd
    simpa [hzl2] using h
  have hτres : IsIso
      ((pullback.fst (D.map (homOfLE hik).op) A.toBase).residueFieldMap (τ zl)) :=
    isIso_pullback_fst_residueFieldMap_of_isIso (D.map (homOfLE hik).op) A.toBase (τ zl)
      (by rw [hτz2]; exact hAres)
  -- Flatness at the stage `k`.
  have hcw : c.π.app (op k) ≫ D.map (homOfLE hik).op = c.π.app (op i) := c.w _
  have hflatk := isFlatOverAt_fiberι_of_isPullback
    (IsPullback.of_hasPullback fi (D.map (homOfLE hik).op)) Fi _ (Iso.refl _) (c.π.app (op k) s)
    (c.π.app (op i) s) (by rw [← Scheme.Hom.comp_apply, hcw]) hflati
  -- Step 3: the sufficiency half of Tag 05L4 at the stage `k`.
  refine ⟨k, hik, inferInstance, inferInstance,
    isFiniteType_pullback_obj _ Fi, isQuasicoherent_pullback_obj _ Fi, ?_⟩
  exact isPureAlong_of_isOpen_subset_preimage_fibrewiseContainment fi Fi A.toBase p g hcomm
    hUP Wi hWi (D.map (homOfLE hik).op)
    (IsPullback.of_hasPullback fi (D.map (homOfLE hik).op))
    ((Scheme.Modules.pullback (pullback.fst fi (D.map (homOfLE hik).op))).obj Fi)
    (Iso.refl _) (c.π.app (op k) s) (τ zl) hτz1 hτres (by rw [hτz2]; exact hAmem) hflatk
    V hVopen hVmem hVsub

/-! ### Tag 05MA -/

-- Instance search does not see through the `def` `AlgebraicGeometry.Scheme.Modules`, so the
-- passage from finite presentation to finite type is made available to it by hand.
attribute [local instance] Stacks.StalkFiniteType.isFiniteType_of_isFinitePresentation

/-- **Stacks Project, Tag 05MA.** Let `I` be a directed set, let `(S_k)` be an inverse system of
affine schemes indexed by `I` with limit `S`, let `s` be a point of `S` with images `s_k`, let
`f : X ⟶ S` be of finite presentation and let `ℱ` be a quasi-coherent `𝒪_X`-module of finite
presentation which is pure along `X_s` and flat over `S` at every point of `X_s`. Then the whole
situation descends to a finite stage: some `k` carries a finite-presentation morphism
`X_k ⟶ S_k` and a finitely presented quasi-coherent module `ℱ_k` which is pure along
`(X_k)_{s_k}` and flat over `S_k` at every point of that fibre, with `X = X_k ×_{S_k} S` and `ℱ`
the pullback of `ℱ_k`.

The descent of the morphism, of the module and of the flatness over the open locus where it
holds — Stacks Limits 01ZM, 01ZR, 01Z4 and 05LY — is
`AlgebraicGeometry.exists_stage_isFlatOverAt_fiber_of_isLimit`; the passage of purity to a finite
stage, which is the rest of the proof of the source, is
`AlgebraicGeometry.exists_stage_isPureAlong`. -/
@[stacks 05MA]
public theorem exists_stage_isPureAlong_of_isLimit_directed {I : Type u} [Preorder I]
    [IsDirected I (· ≤ ·)] [Nonempty I] (D : Iᵒᵖ ⥤ Scheme.{u}) [∀ k : Iᵒᵖ, IsAffine (D.obj k)]
    (c : Cone D) (hc : IsLimit c) {X : Scheme.{u}} (f : X ⟶ c.pt)
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (F : X.Modules) [F.IsFinitePresentation] [F.IsQuasicoherent] (s : c.pt)
    (hpure : IsPureAlong ({ S := c.pt, X := X, f := f, F := F, s := s } : PrePureSituation.{u}))
    (hflat : ∀ x : f.fiber s,
      IsFlatOverAt f.toLRSHom.toShHom F (f.fiberι s x)) :
    ∃ (k : I) (Xk : Scheme.{u}) (fk : Xk ⟶ D.obj (op k))
      (_ : LocallyOfFinitePresentation fk) (_ : QuasiCompact fk) (_ : QuasiSeparated fk)
      (Fk : Xk.Modules) (_ : Fk.IsQuasicoherent) (_ : Fk.IsFinitePresentation)
      (_ : Fk.IsFiniteType) (a : X ⟶ Xk),
      IsPullback a f fk (c.π.app (op k)) ∧ Nonempty (F ≅ (Scheme.Modules.pullback a).obj Fk) ∧
        (∀ x : fk.fiber (c.π.app (op k) s),
          IsFlatOverAt fk.toLRSHom.toShHom Fk (fk.fiberι (c.π.app (op k) s) x)) ∧
        IsPureAlong ({ S := D.obj (op k), X := Xk, f := fk, F := Fk,
                       s := c.π.app (op k) s } : PrePureSituation.{u}) := by
  classical
  obtain ⟨i, Xi, fi, Fi, a, hfpi, hFiqc, hFifp, hpb, hFe, hflati⟩ :=
    exists_stage_isFlatOverAt_fiber_of_isLimit D c hc f
      (FinitePresentation.mk (f := f) inferInstance inferInstance inferInstance) F
      inferInstance inferInstance s hflat
  obtain ⟨eF⟩ := hFe
  have : LocallyOfFinitePresentation fi := hfpi.1
  have : QuasiCompact fi := hfpi.2.1
  have : QuasiSeparated fi := hfpi.2.2
  have : Fi.IsQuasicoherent := hFiqc
  have : Fi.IsFinitePresentation := hFifp
  have : Fi.IsFiniteType := inferInstance
  obtain ⟨k, hik, hlftk, hqck, hFkft, hFkqc, hpurek⟩ :=
    exists_stage_isPureAlong D c hc i fi Fi s F hpb eF hpure hflati
  have hcw : c.π.app (op k) ≫ D.map (homOfLE hik).op = c.π.app (op i) := c.w _
  have hcomm : a ≫ fi = (f ≫ c.π.app (op k)) ≫ D.map (homOfLE hik).op := by
    rw [Category.assoc, hcw]; exact hpb.w
  have ha : pullback.lift a (f ≫ c.π.app (op k)) hcomm ≫
      pullback.fst fi (D.map (homOfLE hik).op) = a := pullback.lift_fst _ _ _
  have hb : pullback.lift a (f ≫ c.π.app (op k)) hcomm ≫
      pullback.snd fi (D.map (homOfLE hik).op) = f ≫ c.π.app (op k) := pullback.lift_snd _ _ _
  have hpbk : IsPullback (pullback.lift a (f ≫ c.π.app (op k)) hcomm) f
      (pullback.snd fi (D.map (homOfLE hik).op)) (c.π.app (op k)) := by
    refine IsPullback.of_right (h₁₂ := pullback.fst fi (D.map (homOfLE hik).op)) ?_ hb
      (IsPullback.of_hasPullback fi (D.map (homOfLE hik).op))
    rw [ha, hcw]
    exact hpb
  have hFkfp : ((Scheme.Modules.pullback
      (pullback.fst fi (D.map (homOfLE hik).op))).obj Fi).IsFinitePresentation :=
    Stacks.AlgebraicGeometry.ModuleLimits.isFinitePresentation_pullback _ Fi
  have hflatk := isFlatOverAt_fiberι_of_isPullback
    (IsPullback.of_hasPullback fi (D.map (homOfLE hik).op)) Fi _ (Iso.refl _) (c.π.app (op k) s)
    (c.π.app (op i) s) (by rw [← Scheme.Hom.comp_apply, hcw]) hflati
  refine ⟨k, pullback fi (D.map (homOfLE hik).op),
    pullback.snd fi (D.map (homOfLE hik).op), inferInstance, inferInstance, inferInstance,
    (Scheme.Modules.pullback (pullback.fst fi (D.map (homOfLE hik).op))).obj Fi, hFkqc, hFkfp,
    hFkft, pullback.lift a (f ≫ c.π.app (op k)) hcomm, hpbk, ⟨?_⟩, hflatk, hpurek⟩
  refine eF ≪≫ ?_
  refine (eqToIso (by rw [ha]) : (Scheme.Modules.pullback a).obj Fi ≅
    (Scheme.Modules.pullback (pullback.lift a (f ≫ c.π.app (op k)) hcomm ≫
      pullback.fst fi (D.map (homOfLE hik).op))).obj Fi) ≪≫ ?_
  exact ((Scheme.Modules.pullbackComp (pullback.lift a (f ≫ c.π.app (op k)) hcomm)
    (pullback.fst fi (D.map (homOfLE hik).op))).app Fi).symm

end AlgebraicGeometry

end
