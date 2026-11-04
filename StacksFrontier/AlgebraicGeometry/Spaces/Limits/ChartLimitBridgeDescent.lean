module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DominantChartLimit

/-!
# Descending morphism properties along an inverse system with limit bridges

Let `(Y_j)` be a cofiltered inverse system of algebraic spaces over a scheme `S` with affine
transition morphisms and limit `Y`, and let `f₀ : X₀ ⟶ Y_m` be a morphism locally of finite
presentation to one of its members, with base changes `f_j : X_j ⟶ Y_j` and `f : X ⟶ Y`. A
property of `f` read on squares of étale charts descends to some `f_j` as soon as the property
of morphisms of schemes behind it descends along limits of affine schemes. This is the argument
of the library's Stacks 07SL, 0CN2 and 08K0 for a morphism descent system, made here without
the bound on the size of the index category those forms carry: what the bound provides, the
limits in the site of the affine charts of the members, is taken as the hypothesis
`AlgebraicGeometry.Space.HasChartLimitBridges` instead.

## Main results

* `AlgebraicGeometry.Space.exists_chartSquare_of_isPullback`: a square of charts of a morphism of
  algebraic spaces base changes to a square of charts of any base change of it.
* `AlgebraicGeometry.Space.exists_holdsOnEveryEtaleChart_of_isPullback_of_hasChartLimitBridges`:
  the descent of a chart-local property along an inverse system with limit bridges.
* `AlgebraicGeometry.Space.exists_isSmooth_of_isPullback_of_hasChartLimitBridges`: **Stacks 0CN2**
  for an inverse system with limit bridges.

## Implementation notes

One chooses an affine étale surjective chart `V₀ ⟶ Y_m` and an affine étale surjective chart
`U₀ ⟶ X₀ ×_{Y_m} V₀`, giving a morphism `U₀ ⟶ V₀` of affine objects of the site. The charts
`V_j = Y_j ×_{Y_m} V₀` of the later members form a system of affine schemes whose limit bridge
charts the limit; base changing `U₀ ⟶ V₀` to the `V_j` and to the limit gives squares of étale
charts of the `f_j` and of `f`, and the statement becomes the descent of the property of
morphisms of schemes along that system. The chart of each base change of `f₀` obtained this way
is surjective, so by Stacks 03MJ the property on that one square is the property on every square
of étale charts.

## References

* [Stacks Project, Tag 0CN2](https://stacks.math.columbia.edu/tag/0CN2)
* [Stacks Project, Tag 0C0C](https://stacks.math.columbia.edu/tag/0C0C)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 07SF](https://stacks.math.columbia.edu/tag/07SF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] MorphismProperty.relative_isStableUnderBaseChange

/-! ### Charts of a base change -/

/-- **A square of charts base changes along a cartesian square.** Let `X' = Y' ×_{Y₀} X₀` be a
base change of `f₀ : X₀ ⟶ Y₀` along `t : Y' ⟶ Y₀`, let `r : U ⟶ V` be a morphism of the site
charting `f₀` through `a : U ⟶ X₀` and `b : V ⟶ Y₀`, and let `W` represent the base change of
`b` along `t`. Then `U ×_V W` charts `X'` by a base change of `a`, over the chart `W ⟶ Y'`. -/
theorem exists_chartSquare_of_isPullback {X₀ Y₀ X' Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f₀ : X₀ ⟶ Y₀} {t : Y' ⟶ Y₀} {q' : X' ⟶ X₀} {f' : X' ⟶ Y'}
    (sq : IsPullback q' f' f₀ t) {U V W : BigFppfOver B S hS} (a : yoneda.obj U ⟶ X₀)
    (b : yoneda.obj V ⟶ Y₀) (r : U ⟶ V) (hr : yoneda.map r ≫ b = a ≫ f₀)
    (p : yoneda.obj W ⟶ Y') (s : W ⟶ V) (hp : IsPullback p (yoneda.map s) t b) :
    ∃ a' : yoneda.obj (pullback r s) ⟶ X',
      IsPullback (yoneda.map (pullback.fst r s)) a' a q' ∧
        yoneda.map (pullback.snd r s) ≫ p = a' ≫ f' := by
  have hw : (yoneda.map (pullback.fst r s) ≫ a) ≫ f₀ =
      (yoneda.map (pullback.snd r s) ≫ p) ≫ t := by
    rw [Category.assoc, ← hr, ← Category.assoc, ← Functor.map_comp, pullback.condition,
      Functor.map_comp, Category.assoc, Category.assoc, hp.w]
  refine ⟨sq.lift _ _ hw, ?_, (sq.lift_snd _ _ hw).symm⟩
  have hbig : IsPullback (yoneda.map (pullback.fst r s)) (sq.lift _ _ hw ≫ f') (a ≫ f₀) t := by
    rw [sq.lift_snd, ← hr]
    exact ((IsPullback.of_hasPullback r s).map yoneda).paste_vert hp.flip
  exact IsPullback.of_bot hbig (sq.lift_fst _ _ hw).symm sq

/-- If a property of presheaf morphisms is multiplicative and stable under base change, then
`cov ≫ pullback.fst f₀ b` has it as soon as `cov` and `b` do. -/
private theorem presheaf_cover_comp_pullback_fst_mem {X₀ Y₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {W : MorphismProperty (BigFppfOver B S hS)} [W.presheaf.IsMultiplicative]
    {U V : BigFppfOver B S hS} (f₀ : X₀ ⟶ Y₀) (b : yoneda.obj V ⟶ Y₀)
    {cov : yoneda.obj U ⟶ pullback f₀ b} (hcov : W.presheaf cov) (hb : W.presheaf b) :
    W.presheaf (cov ≫ pullback.fst f₀ b) :=
  MorphismProperty.comp_mem _ _ _ hcov
    (MorphismProperty.of_isPullback (IsPullback.of_hasPullback f₀ b).flip hb)

/-! ### Stacks 0CN2 along a system with limit bridges -/

section ChartLimitBridges

variable {hZ : B.Contains (⊤_ Scheme.{u})} {J : Type u} [Category.{u} J]

/-- **Descending a chart-local property along an inverse system with limit bridges**, the
argument of Stacks 07SL, 0CN2 and 08K0. Let `(Y_j)` be a cofiltered inverse system of algebraic
spaces over `S` with affine transition morphisms and limit `Y`, whose chart systems along étale
affine points have limit bridges, and let `f₀ : X₀ ⟶ Y_m` be a morphism locally of finite
presentation from a quasi-compact algebraic space to a quasi-compact quasi-separated member of
the system. Let `P` be a property of morphisms of schemes, étale local on the source and target,
which descends from a limit of affine schemes to a member of the system for morphisms locally of
finite presentation of affine schemes. If `P` holds on every square of étale charts of the base
change `f : X ⟶ Y` of `f₀` to the limit, then it holds on every square of étale charts of the
base change of `f₀` to some later member `Y_j`. No bound is put on the size of the index
category. -/
theorem exists_holdsOnEveryEtaleChart_of_isPullback_of_hasChartLimitBridges
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso] (hP : IsEtaleLocalOnSourceAndTarget P)
    (Ys : J ⥤ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) (bridges : HasChartLimitBridges Ys)
    {c : Cone Ys} (hc : IsLimit c) (algYs : ∀ j, IsAlgebraicSpace B S hS (Ys.obj j))
    (affYs : ∀ {j k : J} (a : j ⟶ k), IsAffineHom B S hS (Ys.map a)) {m : J}
    (qcYm : IsQuasiCompactSpace B S hS (Ys.obj m))
    (qsYm : IsAbsolutelyQuasiSeparated B S hS hZ (Ys.obj m))
    {X₀ X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (algX₀ : IsAlgebraicSpace B S hS X₀)
    (qcX₀ : IsQuasiCompactSpace B S hS X₀) (f₀ : X₀ ⟶ Ys.obj m)
    (fp : IsLocallyOfFinitePresentation B S hS f₀)
    {q : X ⟶ X₀} {f : X ⟶ c.pt} (sq : IsPullback q f f₀ (c.π.app m))
    (hdescend : ∀ (Ds : Over m ⥤ Scheme.{u}) (cs : Cone Ds), IsLimit cs →
      (∀ {j k : Over m} (g : j ⟶ k), _root_.AlgebraicGeometry.IsAffineHom (Ds.map g)) →
      ∀ (k₀ : Over m) (X₀ Y₀ : Over (Ds.obj k₀)) (φ : X₀ ⟶ Y₀), IsAffine (Ds.obj k₀) →
        IsAffine X₀.left → IsAffine Y₀.left → LocallyOfFinitePresentation φ.left →
        P ((Over.pullback (cs.π.app k₀)).map φ).left →
        ∃ (k : Over m) (g : k ⟶ k₀), P ((Over.pullback (Ds.map g)).map φ).left)
    (hf : HoldsOnEveryEtaleChart B S hS P f) :
    ∃ (j : J) (a : j ⟶ m),
      ∀ {X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (q' : X' ⟶ X₀) (f' : X' ⟶ Ys.obj j),
        IsPullback q' f' f₀ (Ys.map a) → HoldsOnEveryEtaleChart B S hS P f' := by
  classical
  let T := BigFppfOver.toScheme B S hS
  -- A square of affine étale charts of `f₀`.
  obtain ⟨V, b, hV, hbS, hbE⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS _ (algYs m)).mp qcYm
  have : IsAffine (T.obj V) := hV
  have hbE' := (isEtale_iff_presheaf_of_yoneda B S hS b).mp hbE
  have algP : IsAlgebraicSpace B S hS (pullback f₀ b) :=
    isAlgebraicSpace_pullback B S hS f₀ b algX₀ (isAlgebraicSpace_yoneda B S hS V) (algYs m)
  have qcP : IsQuasiCompactSpace B S hS (pullback f₀ b) :=
    isQuasiCompactSpace_pullback B S hS hZ f₀ b algX₀ (algYs m) qcX₀
      (isQuasiCompactSpace_yoneda_obj B S hS inferInstance) qsYm
  obtain ⟨U, cov, hU, hcS, hcE⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS _ algP).mp qcP
  have : IsAffine (T.obj U) := hU
  have hcE' := (isEtale_iff_presheaf_of_yoneda B S hS cov).mp hcE
  let a : yoneda.obj U ⟶ X₀ := cov ≫ pullback.fst f₀ b
  let r : U ⟶ V := yoneda.preimage (cov ≫ pullback.snd f₀ b)
  have hr : yoneda.map r ≫ b = a ≫ f₀ := by
    simp only [r, a, Functor.map_preimage, Category.assoc, pullback.condition]
  have haE : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) T).presheaf
      a :=
    have := isMultiplicative_presheaf_etale B S hS
    presheaf_cover_comp_pullback_fst_mem f₀ b hcE' hbE'
  have haS : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      T).presheaf a :=
    have := isMultiplicative_presheaf_surjective B S hS
    presheaf_cover_comp_pullback_fst_mem f₀ b hcS hbS
  have hrfp : LocallyOfFinitePresentation (T.map r) := fp U V a b r haE hbE' hr
  -- The system of charts of the later members and its limit bridge.
  let V' : BigAffineFppf B S hS := ⟨V, hV⟩
  let C : AffineChartSystem B S hS m Ys V' b :=
    affineChartSystem B S hS m Ys V' b (fun g => affYs g)
  obtain ⟨L⟩ := bridges m V' b hbE' C
  let stageChart : ∀ j : Over m, C.siteDiagram.obj j ⟶ V := fun j => yoneda.preimage (C.baseMap j)
  have hstage : ∀ j : Over m,
      IsPullback (C.stageMap j) (yoneda.map (stageChart j)) (Ys.map j.hom) b := by
    intro j
    simpa only [stageChart, Functor.map_preimage] using C.isPullback j
  let limitChart : L.cone.pt ⟶ V := yoneda.preimage L.toBase
  let e : limit Ys ≅ c.pt := (limit.isLimit Ys).conePointUniqueUpToIso hc
  have he : e.hom ≫ c.π.app m = limit.π Ys m :=
    (limit.isLimit Ys).conePointUniqueUpToIso_hom_comp hc m
  have hlim : IsPullback (L.toLimit ≫ e.hom) (yoneda.map limitChart) (c.π.app m) b :=
    IsPullback.of_iso L.isPullback (Iso.refl _) e (Iso.refl _) (Iso.refl _) (by simp)
      (by simp [limitChart]) (by simp [he]) (by simp)
  -- The chart morphism of the base change of `f₀` to the limit has `P`.
  have hlimP : P (T.map (pullback.snd r limitChart)) := by
    obtain ⟨a', sa, comm⟩ := exists_chartSquare_of_isPullback sq a b r hr _ limitChart hlim
    exact hf _ _ a' _ _ (MorphismProperty.of_isPullback sa haE)
      (MorphismProperty.of_isPullback hlim.flip hbE') comm
  -- The descent of `P` along the affine schemes charting the members.
  let j₀ : Over m := Over.mk (𝟙 m)
  let fbase := pullback.snd (T.map r) (T.map (stageChart j₀))
  let X₀' : Over (C.schemeDiagram.obj j₀) := Over.mk fbase
  let Y₀' : Over (C.schemeDiagram.obj j₀) := Over.mk (𝟙 (C.schemeDiagram.obj j₀))
  let φ : X₀' ⟶ Y₀' := Over.homMk fbase (Category.comp_id _)
  have hj₀aff : IsAffine (C.schemeDiagram.obj j₀) := C.isAffine_obj j₀
  have : IsAffine (T.obj (C.siteDiagram.obj j₀)) := C.isAffine_obj j₀
  have : _root_.AlgebraicGeometry.IsAffineHom (T.map (stageChart j₀)) := isAffineHom_of_isAffine _
  have : _root_.AlgebraicGeometry.IsAffineHom
      (pullback.fst (T.map r) (T.map (stageChart j₀))) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _).flip ‹_›
  have hX₀aff : IsAffine X₀'.left := isAffine_of_isAffineHom
    (pullback.fst (T.map r) (T.map (stageChart j₀)))
  have hφ : LocallyOfFinitePresentation φ.left :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback (T.map r) (T.map (stageChart j₀)))
      hrfp
  have hqL : (T.mapCone L.cone).π.app j₀ ≫ T.map (stageChart j₀) = T.map limitChart := by
    show T.map (L.cone.π.app j₀) ≫ _ = _
    rw [← Functor.map_comp]
    congr 1
    apply yoneda.map_injective
    simp only [stageChart, limitChart, Functor.map_comp, Functor.map_preimage, L.baseMap_comp]
  have hφlim : P ((Over.pullback ((T.mapCone L.cone).π.app j₀)).map φ).left :=
    (prop_overPullback_map_left_iff_pullback_snd _ fbase _).mpr
      ((prop_iteratedPullback_snd_iff T _ r (stageChart j₀) limitChart _ hqL).mpr hlimP)
  obtain ⟨jj, g, hjj⟩ := hdescend C.schemeDiagram (T.mapCone L.cone) L.schemeIsLimit
    (fun g => C.isAffineHom_map g) j₀ X₀' Y₀' φ hj₀aff hX₀aff hj₀aff hφ hφlim
  have hqj : C.schemeDiagram.map g ≫ T.map (stageChart j₀) = T.map (stageChart jj) := by
    show T.map (C.siteDiagram.map g) ≫ _ = _
    rw [← Functor.map_comp]
    congr 1
    apply yoneda.map_injective
    have hnat : yoneda.map (C.siteDiagram.map g) ≫ C.iso.hom.app j₀ =
        C.iso.hom.app jj ≫ (stageBaseChangeDiagram B S hS m Ys V' b).map g :=
      C.iso.hom.naturality g
    simp only [stageChart, Functor.map_comp, Functor.map_preimage, AffineChartSystem.baseMap]
    rw [← Category.assoc, hnat, Category.assoc, stageBaseChangeDiagram_map_comp_snd]
  have hjjP : P (T.map (pullback.snd r (stageChart jj))) :=
    (prop_iteratedPullback_snd_iff T _ r (stageChart j₀) (stageChart jj) _ hqj).mp
      ((prop_overPullback_map_left_iff_pullback_snd _ fbase _).mp hjj)
  -- Every base change of `f₀` to that member has `P` on every square of étale charts.
  refine ⟨jj.left, jj.hom, fun {X'} q' f' sq' => ?_⟩
  have algX' : IsAlgebraicSpace B S hS X' :=
    isAlgebraicSpace_of_iso B S hS sq'.isoPullback.symm
      (isAlgebraicSpace_pullback B S hS _ _ algX₀ (algYs _) (algYs m))
  obtain ⟨a', sa, comm⟩ := exists_chartSquare_of_isPullback sq' a b r hr _ _ (hstage jj)
  exact (holdsOnEveryEtaleChart_iff_surjectiveChart B S hS P hP algX' (algYs _) f').mpr
    ⟨_, _, a', C.stageMap jj, pullback.snd r (stageChart jj),
      MorphismProperty.of_isPullback sa haE, MorphismProperty.of_isPullback (hstage jj).flip hbE',
      MorphismProperty.of_isPullback sa haS, comm, hjjP⟩

/-- **Stacks 0CN2 for an inverse system with limit bridges.** Let `(Y_j)` be a cofiltered
inverse system of algebraic spaces over `S` with affine transition morphisms and limit `Y`,
whose chart systems along étale affine points have limit bridges, and let
`f₀ : X₀ ⟶ Y_m` be a morphism locally of finite presentation from a quasi-compact algebraic
space to a quasi-compact quasi-separated member of the system. If the base change `f : X ⟶ Y`
of `f₀` to the limit is smooth, then the base change of `f₀` to some later member `Y_j` is
smooth. No bound is put on the size of the index category. -/
theorem exists_isSmooth_of_isPullback_of_hasChartLimitBridges [IsCofiltered J]
    (Ys : J ⥤ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) (bridges : HasChartLimitBridges Ys)
    {c : Cone Ys} (hc : IsLimit c) (algYs : ∀ j, IsAlgebraicSpace B S hS (Ys.obj j))
    (affYs : ∀ {j k : J} (a : j ⟶ k), IsAffineHom B S hS (Ys.map a)) {m : J}
    (qcYm : IsQuasiCompactSpace B S hS (Ys.obj m))
    (qsYm : IsAbsolutelyQuasiSeparated B S hS hZ (Ys.obj m))
    {X₀ X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (algX₀ : IsAlgebraicSpace B S hS X₀)
    (qcX₀ : IsQuasiCompactSpace B S hS X₀) (f₀ : X₀ ⟶ Ys.obj m)
    (fp : IsLocallyOfFinitePresentation B S hS f₀)
    {q : X ⟶ X₀} {f : X ⟶ c.pt} (sq : IsPullback q f f₀ (c.π.app m))
    (smooth : IsSmooth B S hS f) :
    ∃ (j : J) (a : j ⟶ m),
      ∀ {X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (q' : X' ⟶ X₀) (f' : X' ⟶ Ys.obj j),
        IsPullback q' f' f₀ (Ys.map a) → IsSmooth B S hS f' := by
  have : MorphismProperty.RespectsIso (@Smooth.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  refine exists_holdsOnEveryEtaleChart_of_isPullback_of_hasChartLimitBridges (@Smooth.{u})
    Smooth.isEtaleLocalOnSourceAndTarget Ys bridges hc algYs affYs qcYm qsYm algX₀ qcX₀ f₀ fp sq
    ?_ smooth
  intro Ds cs hcs _ k₀ X₀ Y₀ φ _ _ _ _ _
  have : CompactSpace (Ds.obj k₀) := Scheme.compactSpace_of_isAffine _
  have : CompactSpace X₀.left := Scheme.compactSpace_of_isAffine _
  have : CompactSpace Y₀.left := Scheme.compactSpace_of_isAffine _
  exact exists_smooth_baseChange_of_smooth_limitBaseChange Ds cs k₀ X₀ Y₀ φ hcs

end ChartLimitBridges

end AlgebraicGeometry.Space

end
