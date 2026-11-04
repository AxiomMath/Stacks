module

public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.CodimensionZeroCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatOverFieldTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperNormalIntegralChart

/-!
# Restriction of functions to the generic fibre over a chart is injective

Let `f : X ⟶ Y` be a morphism of algebraic spaces with `X` reduced and decent, let `ξ` be a point
of `Y` of codimension `0`, and suppose every generic point of an irreducible component of `|X|`
maps to `ξ`.  Let `W` be an étale chart of `Y` whose scheme is integral, and let `ι : K ⟶ W` be a
morphism of the site whose underlying morphism of schemes lands in the generic point of `W`.
Then pullback of global functions along the base change `X_K = (X ×_Y W) ×_W K ⟶ X ×_Y W` is
injective.

A global function of `X ×_Y W` is determined by its value on a surjective étale chart `T`, which
is a reduced scheme.  Every generic point `u` of an irreducible component of `T` lies over the
generic point of `W` — it maps to a point of codimension `0` of `X`, hence to `ξ`, and the points
of `W` over `ξ` are generic because `W ⟶ Y` is étale — so `u` lifts to the étale chart
`T ×_W K` of `X_K`.  A function killed on `X_K` therefore vanishes at every such `u`, hence on
all of `T`, the vanishing locus being closed under generization in the complement of a basic open.

## Main results

* `AlgebraicGeometry.Space.injective_globalFunctionsMap_pullback_fst_of_genericPoint`: the
  statement above.

## References

* [Stacks Project, Tag 0AYI](https://stacks.math.columbia.edu/tag/0AYI)
* [Stacks Project, Tag 0ABV](https://stacks.math.columbia.edu/tag/0ABV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- On a reduced scheme a global function vanishing at every generic point of an irreducible
component is zero: its basic open is closed under generization and contains no generic point,
so it is empty. -/
theorem eq_zero_of_forall_genericPoints_not_mem_basicOpen {T : Scheme.{u}} [IsReduced T]
    (s : Γ(T, ⊤)) (h : ∀ u ∈ genericPoints T, u ∉ T.basicOpen s) : s = 0 := by
  apply eq_zero_of_basicOpen_eq_bot
  ext v
  simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
  intro hv
  let Z := irreducibleComponent v
  have hZ : IsIrreducible Z := isIrreducible_irreducibleComponent
  have hZc : IsClosed Z := isClosed_irreducibleComponent
  have hgen := hZ.isGenericPoint_genericPoint_closure
  rw [hZc.closure_eq] at hgen
  have hmem : hZ.genericPoint ∈ genericPoints T := by
    show closure {hZ.genericPoint} ∈ irreducibleComponents T
    rw [hgen.def]
    exact irreducibleComponent_mem_irreducibleComponents v
  have hspec : hZ.genericPoint ⤳ v := by
    rw [specializes_iff_mem_closure, hgen.def]
    exact mem_irreducibleComponent
  exact h _ hmem (hspec.mem_open (T.basicOpen s).isOpen hv)

/-- **The generic points of an étale chart of `X ×_Y W` lie over the generic point of `W`.**
Let `X` be decent, let every generic point of an irreducible component of `|X|` map to a point
`ξ` of `Y` of codimension `0`, and let `W` be an integral étale chart of `Y`.  If `a : T ⟶ X ×_Y W`
is an étale chart and `m : T ⟶ W` is its composite with the projection, then `m` sends the
generic points of the irreducible components of `T` to the generic point of `W`: such a point
maps to a point of codimension `0` of `X` (Stacks 0ABV), hence to `ξ`, and the points of `W` over
the codimension `0` point `ξ` have codimension `0` because `W ⟶ Y` is étale. -/
theorem map_eq_genericPoint_of_mem_genericPoints {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hXdec : IsDecentSpace B S hS X.1) {ξ : points B S hS Y.1}
    (hξ : localRingDimension B S hS ξ = 0)
    (hgen : ∀ x ∈ genericPoints (points B S hS X.1), pointsMap B S hS X.1 f.hom x = ξ)
    (W : SmallEtale B S hS Y.1)
    [IsIntegral ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj W))]
    {T : BigFppfOver B S hS} (a : yoneda.obj T ⟶ (chartBaseChangeSpace B S hS f W).obj)
    (ha : IsEtale B S hS a) (m : T ⟶ (SmallEtale.toOver B S hS Y.1).obj W)
    (hm : yoneda.map m = a ≫ (chartBaseChangeProjection B S hS f W).hom)
    (u : (BigFppfOver.toScheme B S hS).obj T)
    (hu : u ∈ genericPoints ((BigFppfOver.toScheme B S hS).obj T)) :
    (BigFppfOver.toScheme B S hS).map m u =
      genericPoint ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj W)) := by
  have hincl : IsEtale B S hS (chartBaseChangeInclusion B S hS f W).hom :=
    (chartBaseChange B S hS f W).property
  obtain ⟨pu, rfl⟩ := surjective_pointsToScheme B S hS T u
  set x := pointsMap B S hS (yoneda.obj T) a pu with hxdef
  have hx : localRingDimension B S hS x = 0 :=
    (localRingDimension_eq_zero_iff_exists_etale_genericPoint B S hS
      (chartBaseChangeSpace B S hS f W).property _).mpr
        ⟨T, a, pointsToScheme B S hS T pu, ha, chartPoint_pointsToScheme B S hS T a pu, hu⟩
  have hxX : pointsMap B S hS _ (chartBaseChangeInclusion B S hS f W).hom x ∈
      genericPoints (points B S hS X.1) := by
    refine mem_genericPoints_of_localRingDimension_eq_zero B S hS X.2 hXdec ?_
    rwa [localRingDimension_pointsMap_of_etale B S hS (chartBaseChangeSpace B S hS f W).property
      X.2 _ hincl]
  have hwξ : pointsMap B S hS _ W.obj.hom
      (pointsMap B S hS _ (chartBaseChangeProjection B S hS f W).hom x) = ξ := by
    calc _ = pointsMap B S hS _ ((chartBaseChangeProjection B S hS f W).hom ≫ W.obj.hom) x :=
          (pointsMap_comp_apply B S hS _ _ _).symm
      _ = pointsMap B S hS _ ((chartBaseChangeInclusion B S hS f W).hom ≫ f.hom) x :=
        congrArg (fun k => pointsMap B S hS _ k x)
          (isPullback_chartBaseChangeProjection B S hS f W).w
      _ = pointsMap B S hS _ f.hom
          (pointsMap B S hS _ (chartBaseChangeInclusion B S hS f W).hom x) :=
        pointsMap_comp_apply B S hS _ _ _
      _ = ξ := hgen _ hxX
  have hw : localRingDimension B S hS
      (pointsMap B S hS _ (chartBaseChangeProjection B S hS f W).hom x) = 0 :=
    (localRingDimension_pointsMap_of_etale B S hS
      (isAlgebraicSpace_yoneda B S hS ((SmallEtale.toOver B S hS Y.1).obj W)) Y.2 W.obj.hom
      (isEtale_of_presheaf_etale B S hS W.property) _).symm.trans
      ((congrArg (localRingDimension B S hS) hwξ).trans hξ)
  have hwgen := (localRingDimension_eq_zero_iff_all_etale_genericPoints B S hS
    (isAlgebraicSpace_yoneda B S hS ((SmallEtale.toOver B S hS Y.1).obj W)) _).mp hw _ (𝟙 _) _
    (isEtale_of_isIso B S hS (𝟙 _)) (by
      have h2 := chartPoint_pointsToScheme B S hS ((SmallEtale.toOver B S hS Y.1).obj W)
        (𝟙 _) (pointsMap B S hS _ (chartBaseChangeProjection B S hS f W).hom x)
      rwa [pointsMap_id_apply] at h2)
  rw [genericPoints_eq_singleton, Set.mem_singleton_iff] at hwgen
  rw [← hwgen, ← pointsToScheme_pointsMap_yoneda, hm]
  exact congrArg _ (pointsMap_comp_apply B S hS a _ pu)

/-- **Restriction of functions to the generic fibre over an integral chart is injective.**  Let
`X` be reduced and decent, let every generic point of an irreducible component of `|X|` map to a
point `ξ` of `Y` of codimension `0`, let `W` be an integral étale chart of `Y`, and let
`ι : K ⟶ W` land in the generic point of `W`.  Then pullback of global functions along
`(X ×_Y W) ×_W K ⟶ X ×_Y W` is injective. -/
theorem injective_globalFunctionsMap_pullback_fst_of_genericPoint {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y)
    (hXred : HasEtaleLocalProperty B S hS X.1 (fun T : Scheme.{u} => IsReduced T))
    (hXdec : IsDecentSpace B S hS X.1) {ξ : points B S hS Y.1}
    (hξ : localRingDimension B S hS ξ = 0)
    (hgen : ∀ x ∈ genericPoints (points B S hS X.1), pointsMap B S hS X.1 f.hom x = ξ)
    (W : SmallEtale B S hS Y.1)
    [IsIntegral ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj W))]
    {K : BigFppfOver B S hS} (ι : K ⟶ (SmallEtale.toOver B S hS Y.1).obj W)
    (hι : ∀ z, (BigFppfOver.toScheme B S hS).map ι z =
      genericPoint ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj W)))
    [Nonempty ((BigFppfOver.toScheme B S hS).obj K)] :
    Function.Injective (globalFunctionsMap B S hS
      (pullback.fst (chartBaseChangeProjection B S hS f W) (schemeSpaceMap ι))) := by
  classical
  let Wo := (SmallEtale.toOver B S hS Y.1).obj W
  let Wsch := (BigFppfOver.toScheme B S hS).obj Wo
  let XW := chartBaseChangeSpace B S hS f W
  let proj := chartBaseChangeProjection B S hS f W
  let incl := chartBaseChangeInclusion B S hS f W
  let τ := pullback.fst proj (schemeSpaceMap ι)
  let hK := pullback.snd proj (schemeSpaceMap ι)
  rw [injective_iff_map_eq_zero]
  intro s hs
  obtain ⟨T, a, hsurj, hetale⟩ := XW.property.exists_atlas
  let c₀ : SmallEtale B S hS XW.obj := ⟨CostructuredArrow.mk a, hetale⟩
  have hc₀ : IsSurjective B S hS c₀.obj.hom :=
    (surjective_iff_surjective_pointsMap B S hS XW.obj XW.property T a).1 hsurj
  refine injective_globalFunctions_val_of_isSurjective B S hS XW.obj XW.property c₀ hc₀ ?_
  show s.val (op c₀) = (0 : globalFunctions B S hS XW.obj).val (op c₀)
  have hincl : IsEtale B S hS incl.hom := (chartBaseChange B S hS f W).property
  have haX : IsEtale B S hS (a ≫ incl.hom) :=
    isEtale_comp B S hS (isEtale_of_presheaf_etale B S hS hetale) hincl
  have hTred : IsReduced ((BigFppfOver.toScheme B S hS).obj T) :=
    (exists_atlas_iff_forall_etale B S hS X.1 _ X.2).mp hXred T (a ≫ incl.hom)
      (presheaf_etale_of_isEtale B S hS haX)
  let m : T ⟶ Wo := smallEtaleChartMapToBase B S hS proj.hom c₀
  have hm : yoneda.map m = a ≫ proj.hom := yoneda_map_smallEtaleChartMapToBase B S hS _ c₀
  have hgenT : ∀ u ∈ genericPoints ((BigFppfOver.toScheme B S hS).obj T),
      (BigFppfOver.toScheme B S hS).map m u = genericPoint Wsch :=
    map_eq_genericPoint_of_mem_genericPoints f hXdec hξ hgen W a
      (isEtale_of_presheaf_etale B S hS hetale) m hm
  let hrep : yoneda.relativelyRepresentable (yoneda.map m) :=
    Functor.relativelyRepresentable.map yoneda m
  let E := hrep.pullback (yoneda.map ι)
  let fstE : E ⟶ T := hrep.fst' (yoneda.map ι)
  let sndE : E ⟶ K := hrep.snd (yoneda.map ι)
  have hEsq : IsPullback (yoneda.map fstE) (yoneda.map sndE) (yoneda.map m) (yoneda.map ι) :=
    hrep.isPullback' (yoneda.map ι)
  have sqK : IsPullback τ.hom hK.hom proj.hom (yoneda.map ι) :=
    (IsPullback.of_hasPullback proj (schemeSpaceMap ι)).map (ObjectProperty.ι _)
  have hlift : (yoneda.map fstE ≫ a) ≫ proj.hom = yoneda.map sndE ≫ yoneda.map ι := by
    rw [Category.assoc]
    exact (congrArg (yoneda.map fstE ≫ ·) hm.symm).trans hEsq.w
  let e : yoneda.obj E ⟶ (pullback proj (schemeSpaceMap ι)).obj :=
    sqK.lift (yoneda.map fstE ≫ a) (yoneda.map sndE) hlift
  have he₁ : e ≫ τ.hom = yoneda.map fstE ≫ a := sqK.lift_fst _ _ _
  have he₂ : e ≫ hK.hom = yoneda.map sndE := sqK.lift_snd _ _ _
  have hEe : IsPullback e (yoneda.map fstE) τ.hom a := by
    refine IsPullback.of_right ?_ he₁ sqK.flip
    rw [he₂]
    exact hm ▸ hEsq.flip
  have hetE : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) e :=
    (MorphismProperty.relative_isStableUnderBaseChange _ : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderBaseChange).of_isPullback hEe.flip
        hetale
  let cE : SmallEtale B S hS (pullback proj (schemeSpaceMap ι)).obj :=
    ⟨CostructuredArrow.mk e, hetE⟩
  have hval : (globalFunctionsMap B S hS τ s).val (op cE) =
      ((BigFppfOver.toScheme B S hS).map fstE).appTop.hom (s.val (op c₀)) :=
    globalFunctionsMap_val_of_chartHom B S hS τ s cE c₀
      (CostructuredArrow.homMk fstE he₁.symm)
  rw [hs] at hval
  have sqAS : IsPullback (schemeSpaceMap fstE) (schemeSpaceMap sndE) (schemeSpaceMap m)
      (schemeSpaceMap ι) :=
    IsPullback.of_map (F := ObjectProperty.ι _)
      (ObjectProperty.hom_ext _ (by
        show yoneda.map fstE ≫ yoneda.map m = yoneda.map sndE ≫ yoneda.map ι
        exact hEsq.w)) hEsq
  refine @eq_zero_of_forall_genericPoints_not_mem_basicOpen ((BigFppfOver.toScheme B S hS).obj T)
    hTred (s.val (op c₀)) fun u hu hus => ?_
  let zT := (pointsEquivScheme B S hS T).symm u
  have hzT : pointsToScheme B S hS T zT = u := (pointsEquivScheme B S hS T).apply_symm_apply u
  let zK := (pointsEquivScheme B S hS K).symm (Classical.arbitrary _)
  have hagree : pointsMap B S hS (schemeSpace T).1 (schemeSpaceMap m).hom zT =
      pointsMap B S hS (schemeSpace K).1 (schemeSpaceMap ι).hom zK := by
    apply injective_pointsToScheme B S hS Wo
    show pointsToScheme B S hS Wo (pointsMap B S hS _ (yoneda.map m) zT) =
      pointsToScheme B S hS Wo (pointsMap B S hS _ (yoneda.map ι) zK)
    rw [pointsToScheme_pointsMap_yoneda, pointsToScheme_pointsMap_yoneda, hzT, hgenT u hu, hι]
  obtain ⟨w, hw₁, -⟩ := exists_point_of_isPullback B S hS sqAS zT zK hagree
  have hu' : (BigFppfOver.toScheme B S hS).map fstE (pointsToScheme B S hS E w) = u :=
    (pointsToScheme_pointsMap_yoneda B S hS fstE w).symm.trans
      ((congrArg (pointsToScheme B S hS T) hw₁).trans hzT)
  let σ : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) := s.val (op c₀)
  have hzero' : ((BigFppfOver.toScheme B S hS).map fstE).app ⊤ σ = 0 := hval.symm
  have hmem : pointsToScheme B S hS E w ∈
      (BigFppfOver.toScheme B S hS).map fstE ⁻¹ᵁ
        ((BigFppfOver.toScheme B S hS).obj T).basicOpen σ := by
    show (BigFppfOver.toScheme B S hS).map fstE (pointsToScheme B S hS E w) ∈
      ((BigFppfOver.toScheme B S hS).obj T).basicOpen σ
    rwa [hu']
  rwa [Scheme.preimage_basicOpen, hzero', Scheme.basicOpen_zero] at hmem

/-- **Constant global functions on the fibre over a point pass to the fibre over a chart.**  Let
`f : X ⟶ Y` be proper, let `ρ : Kξ ⟶ Y` be a morphism from the spectrum of a field, and suppose
`Γ(Kξ) ⟶ Γ(X ×_Y Kξ)` is bijective.  Let `W` be an étale chart of `Y` and `ι : K ⟶ W` a morphism of
the site factoring the composite `K ⟶ W ⟶ Y` through `ρ` by `g : K ⟶ Kξ`.  Then
`Γ(K) ⟶ Γ((X ×_Y W) ×_W K)` is bijective.

The structure map of `X ×_Y Kξ ⟶ Kξ` is an isomorphism, by
`AlgebraicGeometry.Space.isIso_fSharp_of_bijective_globalFunctionsMap`; the fibre over `K` is its
base change along `g`, which is flat since `Kξ` is the spectrum of a field, so flat base change
(Stacks 073K) makes its structure map an isomorphism too. -/
theorem bijective_globalFunctionsMap_pullback_snd_of_factor {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : IsProper B S hS f.hom) {Kξ : BigFppfOver B S hS}
    (ρ : schemeSpace Kξ ⟶ Y) {k : Type u} [Field k]
    (eκ : (BigFppfOver.toScheme B S hS).obj Kξ ≅ Spec (CommRingCat.of k))
    (h6 : Function.Bijective (globalFunctionsMap B S hS (pullback.snd f ρ)))
    (W : SmallEtale B S hS Y.1) {K : BigFppfOver B S hS}
    (ι : K ⟶ (SmallEtale.toOver B S hS Y.1).obj W) (g : K ⟶ Kξ)
    (hg : schemeSpaceMap g ≫ ρ = schemeSpaceMap ι ≫ ((comparisonFunctor B S hS Y).obj W).obj.hom) :
    Function.Bijective (globalFunctionsMap B S hS
      (pullback.snd (chartBaseChangeProjection B S hS f W) (schemeSpaceMap ι))) := by
  let V := (comparisonFunctor B S hS Y).obj W
  let proj := chartBaseChangeProjection B S hS f W
  let incl := chartBaseChangeInclusion B S hS f W
  have sqXW : IsPullback proj incl V.obj.hom f := (spacesBaseChange B S hS f).isPullback V
  have hξP : IsProper B S hS (pullback.snd f ρ).hom :=
    (isProper_isStableUnderBaseChange B S hS).of_isPullback (IsPullback.of_hasPullback f ρ) hf
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj Kξ) := IsAffine.of_isIso eκ.hom
  have : IsIso (smallEtaleRingedToposHom B S hS (pullback.snd f ρ)).fSharp :=
    isIso_fSharp_of_bijective_globalFunctionsMap _ hξP
      (isAffineSpace_yoneda B S hS Kξ inferInstance) h6
  let τ := pullback.fst proj (schemeSpaceMap ι)
  let hK := pullback.snd proj (schemeSpaceMap ι)
  have hcond : τ ≫ proj = hK ≫ schemeSpaceMap ι := pullback.condition
  have hw : (τ ≫ incl) ≫ f = (hK ≫ schemeSpaceMap g) ≫ ρ := by
    rw [Category.assoc, ← sqXW.w, reassoc_of% hcond, Category.assoc, hg]
    exact Category.assoc _ _ _
  let θ : pullback proj (schemeSpaceMap ι) ⟶ pullback f ρ := pullback.lift _ _ hw
  have hθ : θ ≫ pullback.fst f ρ = τ ≫ incl := pullback.lift_fst _ _ _
  have hout : IsPullback (θ ≫ pullback.fst f ρ) hK f (schemeSpaceMap g ≫ ρ) := by
    rw [hθ, hg]
    exact (IsPullback.of_hasPullback proj (schemeSpaceMap ι)).paste_horiz sqXW.flip
  have hsq : IsPullback θ hK (pullback.snd f ρ) (schemeSpaceMap g) :=
    IsPullback.of_right hout (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback f ρ)
  obtain ⟨hqc, hqs⟩ := isQuasiCompact_isQuasiSeparated_of_isProper B S hS _ hξP
  have hflat : IsFlat B S hS (schemeSpaceMap g).hom :=
    isFlat_to_field B S hS (isAlgebraicSpace_yoneda B S hS K) eκ (yoneda.map g)
  have := isIso_fSharp_of_isPullback_of_isFlat hsq hqc hqs hflat
  exact bijective_globalFunctionsMap_of_isIso_fSharp hK

end AlgebraicGeometry.Space

end
