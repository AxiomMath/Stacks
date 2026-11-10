module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.StableModelLocal
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurveFamilyContractionUniqueness
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.StructureSheafIsoNearSpecialFibreTransport
public import StacksFrontier.AlgebraicGeometry.Descent.RelativeAmpleFpqcLocalOnBaseFull
public import StacksFrontier.AlgebraicGeometry.PowerFamilyBridge.Ample
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleQuotients.Basic
public import StacksFrontier.AlgebraicGeometry.InvertiblePullback.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmple.TensorPower

/-!
# Stable contractions descend along extensions of the ground field

Let `c : X ⟶ W` be a morphism over a field `K`, with `X` proper over `K` of dimension at most one
and `W` a proper nodal curve over `K` with `H⁰(W, 𝒪_W) = K`. If for some extension `K'/K` the
base change `c_{K'}` is a stable contraction (the conditions of Stacks 0E7Q), then so is `c`:
both halves of condition (2) descend along the faithfully flat base change `W_{K'} ⟶ W`
(Stacks 02KH), and `ω_W` is ample because its pullback `ω_{W_{K'}}` is (Stacks 0E32 and
Stacks 0D2P). Consequently condition (2) of Stacks 0E8A descends along a covering of the base,
and holds for a stable model glued from local ones.

## Main results

* `AlgebraicGeometry.C1590Private.isStableContraction_of_isPullback_spec`: stable contractions
  descend along extensions of the ground field.
* `AlgebraicGeometry.C1590Private.IsFibrewiseStableContraction.of_cover`: condition (2) of
  Stacks 0E8A descends along a covering of the base.
* `AlgebraicGeometry.C1590Private.isFibrewiseStableContraction_of_cover`: condition (2) of
  Stacks 0E8A for a glued stable model.
* `AlgebraicGeometry.C1590Private.isStableCurveFamily_of_isFibrewiseStableContraction`: the
  target of a fibrewise stable contraction of a prestable family of genus `g ≥ 2` is stable of
  genus `g`.

## References

* [Stacks Project, Tag 0E8A](https://stacks.math.columbia.edu/tag/0E8A)
* [Stacks Project, Tag 0E7Q](https://stacks.math.columbia.edu/tag/0E7Q)
* [Stacks Project, Tag 0D2P](https://stacks.math.columbia.edu/tag/0D2P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance 2000] HasDerivedCategory.standard

namespace AlgebraicGeometry.C1590Private

universe u

open Stacks.Curves.StableModel in
/-- **Stable contractions descend along extensions of the ground field.** Let `c : X ⟶ W` lie
over `K`, with `X` proper of dimension at most one and `W` a proper nodal curve with
`H⁰(W, 𝒪_W) = K`. If the base change `c' : X' ⟶ W'` of `c` along `Spec K' ⟶ Spec K` is a
stable contraction, then so is `c`. -/
theorem isStableContraction_of_isPullback_spec {K K' : Type u} [Field K] [Field K']
    [Algebra K K'] {X W X' W' : Scheme.{u}} {f : X ⟶ Spec (.of K)} {gW : W ⟶ Spec (.of K)}
    {c : X ⟶ W} (hc : c ≫ gW = f) {f' : X' ⟶ Spec (.of K')} {gW' : W' ⟶ Spec (.of K')}
    {c' : X' ⟶ W'} (pX : X' ⟶ X) (pW : W' ⟶ W)
    (hW : IsPullback pW gW' gW (Spec.map (CommRingCat.ofHom (algebraMap K K'))))
    (hcsq : IsPullback pX c' c pW) [IsProper f] (hdimX : topologicalKrullDim X ≤ 1)
    [IsProper gW] (hdimW : topologicalKrullDim W = 1)
    [IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ gW.appTop)]
    (hnodal : letI : W.Over (Spec (.of K)) := ⟨gW⟩; Stacks.Curves.HasAtWorstNodalSingularities K W)
    (h' : IsStableContraction f' gW' c') : IsStableContraction f gW c := by
  let gK : Spec (.of K') ⟶ Spec (.of K) := Spec.map (CommRingCat.ofHom (algebraMap K K'))
  have : Flat gK := Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  have : Surjective gK := ⟨fun _ => ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩
  have : Flat pW := MorphismProperty.of_isPullback hW.flip inferInstance
  have : Surjective pW := MorphismProperty.of_isPullback hW.flip inferInstance
  have : IsProper (c ≫ gW) := hc ▸ ‹IsProper f›
  have : IsProper c := IsProper.of_comp c gW
  have hdimc : ∀ y : W, topologicalKrullDim (c.fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞) := fun y =>
    (Topology.IsInducing.topologicalKrullDim_le (c.fiberι y).isEmbedding.isInducing).trans hdimX
  obtain ⟨hR, hU⟩ := isZero_and_isIso_of_isPullback_of_surjective hcsq hdimc
    ((Stacks.DerivedIndexing.isZero_rightDerived_obj_iff _ 1 _).1 h'.isZero_rightDerived_one)
    h'.isIso_unitToPushforwardObjUnit
  refine
    { comp_eq := hc
      isProper := inferInstance
      topologicalKrullDim_eq := hdimW
      hasAtWorstNodalSingularities := hnodal
      isIso_unitToPushforwardObjUnit := hU
      isZero_rightDerived_one := (Stacks.DerivedIndexing.isZero_rightDerived_obj_iff _ 1 _).2 hR
      isAmple := ?_ }
  have : IsProper gW' := h'.isProper
  obtain ⟨hω', hL'⟩ := h'.isAmple
  let : W.Over (Spec (.of K)) := ⟨gW⟩
  have : IsProper (W ↘ Spec (.of K)) := inferInstanceAs (IsProper gW)
  have : IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ (W ↘ Spec (.of K)).appTop) :=
    inferInstanceAs (IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ gW.appTop))
  have : ConnectedSpace W := connectedSpace_of_isIso_globalSections K gW
  have hω : AlgebraicGeometry.SheafOfModules.IsInvertible W.presheaf W.ringCatSheaf.2
      (Stacks.Duality.dualizingSheafOverField gW) :=
    isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities K W hdimW hnodal
  have : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace gW
  have : QuasiSeparatedSpace W := quasiSeparatedSpace_of_quasiSeparated gW
  have := hω'
  let e : Stacks.Duality.dualizingSheafOverField gW' ≅
      Stacks.AmpleLocallyClosed.pullbackModule pW (Stacks.Duality.dualizingSheafOverField gW) :=
    (Stacks.Duality.dualizingSheafOverFieldBaseChangeIso gW pW gW' hW).symm ≪≫
      (Stacks.ProjectiveBundleQuotients.pullbackIso pW).app _
  have hA' : Stacks.Ample.IsAmple W'
      (Stacks.AmpleLocallyClosed.pullbackModule pW (Stacks.Duality.dualizingSheafOverField gW)) :=
    (Stacks.RelativeVeryAmple.isAmple_congr _ _ e).1
      (Stacks.PowerFamilyBridge.isAmple_of_modulesIsAmple W' _ hL')
  have hA : Stacks.Ample.IsAmple W (Stacks.Duality.dualizingSheafOverField gW) :=
    Stacks.Descent.isAmple_of_forall_isAmple_pullbackModule_of_affineFlatCover (V := Spec (.of K))
      gW _ (m := 1) (T := fun _ => Spec (.of K')) (t := fun _ => gK)
      (fun v => ⟨0, gK.surjective v⟩) (Y' := fun _ => W') (pr := fun _ => pW)
      (q' := fun _ => gW') (fun _ => hW) (fun _ => hA')
  exact ⟨hω, Stacks.PowerFamilyBridge.modulesIsAmple_of_isAmple W _ hA⟩

/-- A cartesian square stays cartesian when an isomorphism is moved from the right edge to the
bottom edge. -/
theorem isPullback_comp_iso_iff {C : Type*} [Category C] {X Y Z W W' : C} (q : X ⟶ Z)
    (v : X ⟶ Y) (f : Z ⟶ W) (e : W ⟶ W') [IsIso e] (t : Y ⟶ W') :
    IsPullback q v (f ≫ e) t ↔ IsPullback q v f (t ≫ inv e) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · refine IsPullback.of_bot (v₂₁ := 𝟙 Y) (v₂₂ := e) (h₃₁ := t) ?_ ?_
      (IsPullback.of_vert_isIso ⟨by simp⟩)
    · rwa [Category.comp_id]
    · rw [← cancel_mono e, Category.assoc, h.w]
      simp
  · simpa only [Category.comp_id] using h.paste_vert (IsPullback.of_vert_isIso
      (fst := t ≫ inv e) (snd := 𝟙 Y) (f := e) (g := t) ⟨by simp⟩)

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- Given a cartesian square `hA` and a presentation `hq` of a fibre, a cartesian square `sq`
over the point map `ρ` induces a map into the top-left corner of `hA` and a cartesian square
over `pt`. -/
private theorem exists_isPullback_lift_of_paste {C : Type*} [Category C]
    {A' A S' S V V' Pt P' : C} {a₁ : A' ⟶ A} {a₂ : A' ⟶ S'} {F : A ⟶ S} {g : S' ⟶ S}
    {q : V ⟶ A} {v : V ⟶ Pt} {e : Pt ⟶ S} {fV : V' ⟶ V} {sV : V' ⟶ P'} {ρ : P' ⟶ Pt}
    {pt : P' ⟶ S'} (hA : IsPullback a₁ a₂ F g) (hq : IsPullback q v F e)
    (sq : IsPullback fV sV v ρ) (hbot : ρ ≫ e = pt ≫ g) :
    ∃ q' : V' ⟶ A', q' ≫ a₁ = fV ≫ q ∧ q' ≫ a₂ = sV ≫ pt ∧ IsPullback q' sV a₂ pt := by
  have hw : (fV ≫ q) ≫ F = (sV ≫ pt) ≫ g := by
    rw [Category.assoc, hq.w, ← Category.assoc, sq.w, Category.assoc, hbot, Category.assoc]
  refine ⟨hA.lift _ _ hw, hA.lift_fst _ _ _, hA.lift_snd _ _ _, ?_⟩
  refine IsPullback.of_right ?_ (hA.lift_snd _ _ _) hA
  rw [hA.lift_fst, ← hbot]
  exact sq.paste_horiz hq

/-- **Condition (2) of Stacks 0E8A descends along a covering of the base.** Let `a : A ⟶ D` lie
over `U`, and let `u i : U i ⟶ U` be morphisms whose images cover `U`, over which `a` pulls back
to `a i : A i ⟶ D i`. Suppose that the fibres of `a ≫ p` at field points are presented by proper
schemes of dimension at most one, and those of `p` by proper nodal curves with `H⁰ = 𝒪`. If each
`a i` satisfies condition (2), so does `a`. -/
theorem IsFibrewiseStableContraction.of_cover {A D : AlgebraicSpaces B integerBase hZ}
    {U : BigFppfOver B integerBase hZ} {a : A ⟶ D} {p : D ⟶ schemeSpace U}
    (hpres : ∀ P : Space.FieldValuedPoint B integerBase hZ (schemeSpace U).obj,
      ∃ (V : BigFppfOver B integerBase hZ) (v : V ⟶ P.siteObject) (q : yoneda.obj V ⟶ A.obj),
        IsPullback q (yoneda.map v) (a ≫ p).hom (yonedaEquiv.symm P.value))
    (hA : ∀ (P : Space.FieldValuedPoint B integerBase hZ (schemeSpace U).obj)
      ⦃V : BigFppfOver B integerBase hZ⦄ (v : V ⟶ P.siteObject) (q : yoneda.obj V ⟶ A.obj),
      IsPullback q (yoneda.map v) (a ≫ p).hom (yonedaEquiv.symm P.value) →
        IsProper ((BigFppfOver.toScheme B integerBase hZ).map v) ∧
          topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj V) ≤ 1)
    (hD : ∀ (P : Space.FieldValuedPoint B integerBase hZ (schemeSpace U).obj)
      ⦃W : BigFppfOver B integerBase hZ⦄ (w : W ⟶ P.siteObject) (r : yoneda.obj W ⟶ D.obj),
      IsPullback r (yoneda.map w) p.hom (yonedaEquiv.symm P.value) →
        let fW : (BigFppfOver.toScheme B integerBase hZ).obj W ⟶ Spec (.of P.carrier) :=
          (BigFppfOver.toScheme B integerBase hZ).map w
        IsProper fW ∧ topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj W) = 1 ∧
          IsIso ((Scheme.ΓSpecIso (.of P.carrier)).inv ≫ fW.appTop) ∧
          (letI : ((BigFppfOver.toScheme B integerBase hZ).obj W).Over (Spec (.of P.carrier)) :=
              ⟨fW⟩;
            Stacks.Curves.HasAtWorstNodalSingularities P.carrier
              ((BigFppfOver.toScheme B integerBase hZ).obj W)))
    {ι : Type*} {Ui : ι → BigFppfOver B integerBase hZ} (u : ∀ i, Ui i ⟶ U)
    (hsurj : ∀ s, ∃ i, s ∈ Set.range ((BigFppfOver.toScheme B integerBase hZ).map (u i)))
    {Ai Di : ι → AlgebraicSpaces B integerBase hZ} (ai : ∀ i, Ai i ⟶ Di i)
    (pi : ∀ i, Di i ⟶ schemeSpace (Ui i)) (jA : ∀ i, Ai i ⟶ A) (jD : ∀ i, Di i ⟶ D)
    (hDsq : ∀ i, IsPullback (jD i) (pi i) p (schemeSpaceMap (u i)))
    (hAsq : ∀ i, IsPullback (jA i) (ai i ≫ pi i) (a ≫ p) (schemeSpaceMap (u i)))
    (hc : ∀ i, ai i ≫ jD i = jA i ≫ a)
    (h : ∀ i, IsFibrewiseStableContraction B hZ (ai i) (pi i)) :
    IsFibrewiseStableContraction B hZ a p := by
  intro P
  refine ⟨hpres P, fun V W v w q r m hq hr hmw hmr => ?_⟩
  let T := BigFppfOver.toScheme B integerBase hZ
  have : PreservesLimitsOfShape WalkingCospan T :=
    Space.preservesLimitsOfShape_walkingCospan_toScheme B integerBase hZ
  let t : P.siteObject ⟶ U := P.value
  obtain ⟨x₀⟩ : Nonempty (T.obj P.siteObject) := inferInstanceAs (Nonempty (Spec (.of P.carrier)))
  obtain ⟨i, s', hs'⟩ := hsurj (T.map t x₀)
  have hE := (IsPullback.of_hasPullback t (u i)).map T
  obtain ⟨z₀, -, -⟩ := Scheme.Pullback.exists_preimage_pullback x₀ s' hs'.symm
  let z : T.obj (pullback t (u i)) := hE.isoPullback.inv z₀
  let P' := residuePointVia (pullback.snd t (u i)) z
  let ν : P'.siteObject ⟶ pullback t (u i) :=
    Space.residueFieldMap B integerBase hZ (pullback t (u i)) z _
  let ρ : P'.siteObject ⟶ P.siteObject := ν ≫ pullback.fst t (u i)
  have hbot : yoneda.map ρ ≫ yonedaEquiv.symm P.value =
      yonedaEquiv.symm P'.value ≫ (schemeSpaceMap (u i)).hom := by
    rw [yonedaEquiv_symm_value P, yonedaEquiv_symm_value P']
    change yoneda.map ρ ≫ yoneda.map t = yoneda.map (ν ≫ pullback.snd t (u i)) ≫ yoneda.map (u i)
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    simp only [ρ, Category.assoc, pullback.condition]
  let fV := pullback.fst v ρ
  let sV := pullback.snd v ρ
  let fW := pullback.fst w ρ
  let sW := pullback.snd w ρ
  let m' : pullback v ρ ⟶ pullback w ρ := pullback.map v ρ w ρ m (𝟙 _) (𝟙 _)
    (by rw [Category.comp_id, hmw]) (by simp)
  have hm'w : m' ≫ sW = sV := (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  have hm'f : m' ≫ fW = fV ≫ m := pullback.lift_fst _ _ _
  have sqV := (IsPullback.of_hasPullback v ρ).map yoneda
  have sqW := (IsPullback.of_hasPullback w ρ).map yoneda
  have hAi := AlgebraicSpaces.isPullback_hom B integerBase hZ (hAsq i)
  have hDi := AlgebraicSpaces.isPullback_hom B integerBase hZ (hDsq i)
  obtain ⟨q', hq'f, hq'g, hq'⟩ := exists_isPullback_lift_of_paste hAi hq sqV hbot
  obtain ⟨r', hr'f, hr'g, hr'⟩ := exists_isPullback_lift_of_paste hDi hr sqW hbot
  have hm'r : yoneda.map m' ≫ r' = q' ≫ (ai i).hom := by
    refine hDi.hom_ext ?_ ?_
    · have hc' : (ai i).hom ≫ (jD i).hom = (jA i).hom ≫ a.hom := congrArg (fun k => k.hom) (hc i)
      rw [Category.assoc, hr'f, ← Category.assoc, ← Functor.map_comp, hm'f,
        Functor.map_comp, Category.assoc, hmr, Category.assoc, hc', reassoc_of% hq'f]
    · rw [Category.assoc, hr'g, ← Category.assoc, ← Functor.map_comp, hm'w,
        Category.assoc]
      exact hq'g.symm
  have hstab := ((h i) P').2 sV sW q' r' m' hq' hr' hm'w hm'r
  let ρT : Spec (.of P'.carrier) ⟶ Spec (.of P.carrier) := T.map ρ
  let : Algebra P.carrier P'.carrier := (Spec.preimage ρT).hom.toAlgebra
  have hρ : Spec.map (CommRingCat.ofHom (algebraMap P.carrier P'.carrier)) = T.map ρ :=
    Spec.map_preimage ρT
  have hWs : IsPullback (T.map fW) (T.map sW) (T.map w)
      (Spec.map (CommRingCat.ofHom (algebraMap P.carrier P'.carrier))) := by
    rw [hρ]
    exact (IsPullback.of_hasPullback w ρ).map T
  have hcsq : IsPullback fV m' m fW := by
    refine IsPullback.of_bot ?_ hm'f.symm (IsPullback.of_hasPullback w ρ)
    rw [hm'w, hmw]
    exact IsPullback.of_hasPullback v ρ
  obtain ⟨hpv, hdv⟩ := hA P v q hq
  obtain ⟨hpw, hdw, hH0, hnod⟩ := hD P w r hr
  have := hpv
  have := hpw
  have := hH0
  exact isStableContraction_of_isPullback_spec (by rw [← T.map_comp, hmw]) (T.map fV) (T.map fW)
    hWs (hcsq.map T) hdv hdw hnod hstab

/-- **Presentations of the fibres of a family read over an isomorphic base.** If `b` is an
isomorphism from the base of `X`, a fibre of `X.toBase ≫ b` at a field point `P` is a fibre of
`X.toBase` at the image of `P` under `b⁻¹`. -/
theorem isPullback_toBase_comp_iff {X : CurveFamily B hZ} {U : BigFppfOver B integerBase hZ}
    (b : X.base ⟶ U) [IsIso b] (P : Space.FieldValuedPoint B integerBase hZ (schemeSpace U).obj)
    {V : BigFppfOver B integerBase hZ} (v : V ⟶ P.siteObject) (q : yoneda.obj V ⟶ X.total.obj) :
    IsPullback q (yoneda.map v) (X.toBase ≫ schemeSpaceMap b).hom (yonedaEquiv.symm P.value) ↔
      IsPullback q (yoneda.map v) X.toBase.hom (yonedaEquiv.symm
        (Space.FieldValuedPoint.map B integerBase hZ (schemeSpace U).obj
          (schemeSpaceMap (inv b)).hom P).value) := by
  have hval : (yonedaEquiv.symm (Space.FieldValuedPoint.map B integerBase hZ (schemeSpace U).obj
      (schemeSpaceMap (inv b)).hom P).value : yoneda.obj P.siteObject ⟶ (schemeSpace X.base).obj) =
      yonedaEquiv.symm P.value ≫ (schemeSpaceMap (inv b)).hom :=
    (yonedaEquiv_symm_naturality_right _ _ _).symm
  have hb : IsIso (yoneda.map b) := Functor.map_isIso yoneda b
  rw [hval]
  change _ ↔
    IsPullback q (yoneda.map v) X.toBase.hom (yonedaEquiv.symm P.value ≫ yoneda.map (inv b))
  rw [Functor.map_inv]
  exact @isPullback_comp_iso_iff _ _ _ _ _ _ _ q (yoneda.map v) X.toBase.hom (yoneda.map b) hb _

/-- **Condition (2) of Stacks 0E8A for a glued stable model.** Let `c : X ⟶ x` lie over an
isomorphism `b` of bases, with `X` and `x` prestable. Let `φ i : X i ⟶ X` be morphisms of families
whose base maps cover the base of `X`, let `c i : X i ⟶ Y i` be stable models over `b i`, and let
`ψ i : Y i ⟶ x` be morphisms of families compatible with `c i` and `c`. Then `c` satisfies
condition (2). -/
theorem isFibrewiseStableContraction_of_cover {g : ℕ} {X x : CurveFamily B hZ}
    (hX : IsPrestableCurveFamily B hZ X) (hx : IsPrestableCurveFamily B hZ x)
    (b : X.base ⟶ x.base) [IsIso b] (c : X.total ⟶ x.total)
    (hc : c ≫ x.toBase = X.toBase ≫ schemeSpaceMap b) {ι : Type*}
    {Xi Yi : ι → CurveFamily B hZ} (φ : ∀ i, Xi i ⟶ X)
    (hsurj : ∀ s, ∃ i, s ∈ Set.range ((BigFppfOver.toScheme B integerBase hZ).map (φ i).baseMap))
    (bi : ∀ i, (Xi i).base ⟶ (Yi i).base) (ci : ∀ i, (Xi i).total ⟶ (Yi i).total)
    (hi : ∀ i, IsStableModel B hZ g (bi i) (ci i)) (ψ : ∀ i, Yi i ⟶ x)
    (hψb : ∀ i, bi i ≫ (ψ i).baseMap = (φ i).baseMap ≫ b)
    (hψc : ∀ i, ci i ≫ (ψ i).totalMap = (φ i).totalMap ≫ c) :
    IsFibrewiseStableContraction B hZ c x.toBase := by
  let T := BigFppfOver.toScheme B integerBase hZ
  have hiso := fun (P : Space.FieldValuedPoint B integerBase hZ (schemeSpace x.base).obj)
      (V : BigFppfOver B integerBase hZ) (v : V ⟶ P.siteObject) (q : yoneda.obj V ⟶ X.total.obj) =>
    hc ▸ isPullback_toBase_comp_iff b P v q
  refine IsFibrewiseStableContraction.of_cover (fun P => ?_) (fun P V v q hq => ?_)
    (fun P W w r hr => fibre_properties_of_isPrestableCurveFamily hx P w r hr)
    (fun i => (ψ i).baseMap) (fun s => ?_) ci (fun i => (Yi i).toBase) (fun i => (φ i).totalMap)
    (fun i => (ψ i).totalMap) (fun i => (ψ i).cartesian) (fun i => ?_) hψc
    (fun i => (hi i).fibrewiseStable)
  · obtain ⟨V, v, q, hq⟩ := exists_presentation_of_fieldValuedPoint X
      (Space.FieldValuedPoint.map B integerBase hZ (schemeSpace x.base).obj
        (schemeSpaceMap (inv b)).hom P)
    exact ⟨V, v, q, (hiso P V v q).2 hq⟩
  · obtain ⟨hp, hd, -, -⟩ :=
      fibre_properties_of_isPrestableCurveFamily hX (Space.FieldValuedPoint.map B integerBase hZ
        (schemeSpace x.base).obj (schemeSpaceMap (inv b)).hom P) v q ((hiso P V v q).1 hq)
    exact ⟨hp, hd.le⟩
  · obtain ⟨i, y, hy⟩ := hsurj (T.map (inv b) s)
    refine ⟨i, T.map (bi i) y, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← T.map_comp, hψb i, T.map_comp, Scheme.Hom.comp_apply, hy]
    change (T.map (inv b) ≫ T.map b) s = s
    rw [← T.map_comp, IsIso.inv_hom_id, T.map_id]
    rfl
  · rw [(hi i).comp_toBase, hc]
    have := (hi i).isIso_base
    exact isPullback_totalMap_of_isIso (φ i) (ψ i) b (bi i) (hψb i)

/-- **The target of a fibrewise stable contraction of a prestable family of genus `g ≥ 2` is
stable of genus `g`.** Let `c : X ⟶ x` lie over an isomorphism `b` of bases, with `X` prestable
with fibres of genus `g ≥ 2` and `x` prestable. If `c` satisfies condition (2) of Stacks 0E8A,
then `x` is stable with fibres of genus `g`. -/
theorem isStableCurveFamily_of_isFibrewiseStableContraction {g : ℕ} {X x : CurveFamily B hZ}
    (hX : IsPrestableCurveFamily B hZ X) (hgen : X.HasFibresOfGenus g) (hg : 2 ≤ g)
    (hx : IsPrestableCurveFamily B hZ x) (b : X.base ⟶ x.base) [IsIso b]
    (c : X.total ⟶ x.total) (hc : c ≫ x.toBase = X.toBase ≫ schemeSpaceMap b)
    (h : IsFibrewiseStableContraction B hZ c x.toBase) :
    IsStableCurveFamily B hZ x ∧ x.HasFibresOfGenus g := by
  have key : ∀ P : Space.FieldValuedPoint B integerBase hZ (schemeSpace x.base).obj,
      ∃ (W : BigFppfOver B integerBase hZ) (w : W ⟶ P.siteObject)
        (r : yoneda.obj W ⟶ x.total.obj),
        IsPullback r (yoneda.map w) x.toBase.hom (yonedaEquiv.symm P.value) ∧
          HasGenusTwoNoRationalTailNoRationalBridge P.carrier
            ((BigFppfOver.toScheme B integerBase hZ).map w) ∧
          genus ((BigFppfOver.toScheme B integerBase hZ).map w) = g := by
    intro P
    obtain ⟨⟨V, v, q, hq⟩, huniv⟩ := h P
    obtain ⟨W, w, r, hr⟩ := exists_presentation_of_fieldValuedPoint x P
    let l : yoneda.obj V ⟶ yoneda.obj W := hr.lift (q ≫ c.hom) (yoneda.map v) (by
      rw [Category.assoc]
      exact hq.w)
    let m : V ⟶ W := Yoneda.fullyFaithful.preimage l
    have hml : yoneda.map m = l := Yoneda.fullyFaithful.map_preimage l
    have hmw : m ≫ w = v := Yoneda.fullyFaithful.map_injective (by
      rw [Functor.map_comp, hml]
      exact hr.lift_snd _ _ _)
    have hmr : yoneda.map m ≫ r = q ≫ c.hom := by
      rw [hml]
      exact hr.lift_fst _ _ _
    have hcst := huniv v w q r m hq hr hmw hmr
    have hq₀ := (hc ▸ isPullback_toBase_comp_iff b P v q).1 hq
    obtain ⟨hprop, hdim, hH0, -⟩ := fibre_properties_of_isPrestableCurveFamily hX
      (Space.FieldValuedPoint.map B integerBase hZ (schemeSpace x.base).obj
        (schemeSpaceMap (inv b)).hom P) v q hq₀
    have : IsProper ((BigFppfOver.toScheme B integerBase hZ).map v) := hprop
    have : IsIso ((Scheme.ΓSpecIso (.of P.carrier)).inv ≫
        ((BigFppfOver.toScheme B integerBase hZ).map v).appTop) := hH0
    have hgV : genus ((BigFppfOver.toScheme B integerBase hZ).map v) = g :=
      (hgen (Space.FieldValuedPoint.map B integerBase hZ (schemeSpace x.base).obj
        (schemeSpaceMap (inv b)).hom P)).genus_eq v q hq₀
    exact ⟨W, w, r, hr, IsStableContraction.hasGenusTwoNoRationalTailNoRationalBridge hcst hdim
      (hgV ▸ hg), (IsStableContraction.genus_eq hcst hdim).trans hgV⟩
  refine ⟨⟨hx, fun P => ?_⟩, fun P => ?_⟩
  · obtain ⟨W, w, r, hr, hst, -⟩ := key P
    exact ⟨W, w, r, hr, hst⟩
  · obtain ⟨W, w, r, hr, -, hgW⟩ := key P
    exact ⟨W, w, r, hr, hgW⟩

end AlgebraicGeometry.C1590Private

end
