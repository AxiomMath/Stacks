module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.StableContractionDescent

/-!
# The stable model over a scheme chart

Let `X ⟶ S` be a prestable family of curves of genus `g ≥ 2`, and let `h : X_U ⟶ Y` be a
morphism over an étale neighbourhood `U` of a point `u`, whose fibres over `u` are stable
contractions (the output of Stacks 0E7C). Over a smaller étale neighbourhood of `u`, on which both
families are schemes, `h` is a stable model of `X`: condition (1) is Stacks 0E88, the target is
stable by the openness of the stable locus (Stacks 0E76), and the fibrewise condition (2) comes
from the scheme form of Stacks 0E88 on the chart together with the ampleness of the dualizing
sheaf of a stable fibre (Stacks 0E3P).

## Main results

* `AlgebraicGeometry.C1590Private.isAmple_dualizingSheafOverField_of_isStableCurveFamily`: the
  dualizing sheaf of every presentation of a fibre of a stable family is ample.

## References

* [Stacks Project, Tag 0E8A](https://stacks.math.columbia.edu/tag/0E8A)
* [Stacks Project, Tag 0E3P](https://stacks.math.columbia.edu/tag/0E3P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 2000] HasDerivedCategory.standard

namespace AlgebraicGeometry.C1590Private

universe u

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- **The dualizing sheaf of a fibre of a stable family is ample** (Stacks 0E3P), at every
presentation of the fibre: some presentation has genus at least two and no rational tails or
bridges, so its dualizing sheaf is ample, and any two presentations are isomorphic over the
field. -/
theorem isAmple_dualizingSheafOverField_of_isStableCurveFamily {F : CurveFamily B hZ}
    (hF : IsStableCurveFamily B hZ F)
    (Q : Space.FieldValuedPoint B integerBase hZ (schemeSpace F.base).obj)
    {W : BigFppfOver B integerBase hZ} (w : W ⟶ Q.siteObject) (r : yoneda.obj W ⟶ F.total.obj)
    (hr : IsPullback r (yoneda.map w) F.toBase.hom (yonedaEquiv.symm Q.value))
    [IsProper ((BigFppfOver.toScheme B integerBase hZ).map w)] :
    ∃ _ : AlgebraicGeometry.SheafOfModules.IsInvertible
        ((BigFppfOver.toScheme B integerBase hZ).obj W).toRingedSpace.presheaf
        (structureSheafRing ((BigFppfOver.toScheme B integerBase hZ).obj W).toRingedSpace).property
        (Stacks.Duality.dualizingSheafOverField ((BigFppfOver.toScheme B integerBase hZ).map w)),
      Scheme.Modules.IsAmple ((BigFppfOver.toScheme B integerBase hZ).obj W)
        (Stacks.Duality.dualizingSheafOverField
          ((BigFppfOver.toScheme B integerBase hZ).map w)) := by
  let T := BigFppfOver.toScheme B integerBase hZ
  obtain ⟨W₀, w₀, r₀, hr₀, hst⟩ := hF.2 Q
  obtain ⟨hg, htail, hproper, hbridge⟩ := hst
  obtain ⟨hp, hdim, hH0, hnodal⟩ := fibre_properties_of_isPrestableCurveFamily hF.1 Q w r hr
  obtain ⟨hp₀, hdim₀, hH0₀, hnodal₀⟩ :=
    fibre_properties_of_isPrestableCurveFamily hF.1 Q w₀ r₀ hr₀
  have := hp₀
  have := hH0
  -- the two presentations are isomorphic over the field
  let e := hr.isoIsPullback _ _ hr₀
  let e₀ : W ≅ W₀ := Yoneda.fullyFaithful.preimageIso e
  have he₀ : e₀.hom ≫ w₀ = w := Yoneda.fullyFaithful.map_injective (by
    rw [Functor.map_comp, show yoneda.map e₀.hom = e.hom from Yoneda.fullyFaithful.map_preimage _]
    exact hr.isoIsPullback_hom_snd _ _ hr₀)
  -- `ω` of the stable presentation is ample (Stacks 0E3P)
  let : (T.obj W₀).Over (Spec (.of Q.carrier)) := ⟨T.map w₀⟩
  have : IsProper (T.obj W₀ ↘ Spec (.of Q.carrier)) := inferInstanceAs (IsProper (T.map w₀))
  have : IsIso
      ((Scheme.ΓSpecIso (.of Q.carrier)).inv ≫ (T.obj W₀ ↘ Spec (.of Q.carrier)).appTop) :=
    hH0₀
  exact isAmple_dualizingSheafOverField_of_iso (T.map w) (T.map w₀) hdim hnodal (T.mapIso e₀)
    (by rw [Functor.mapIso_hom, ← Functor.map_comp, he₀])
    (isAmple_dualizingSheafOverField_of_hasAtWorstNodalSingularities Q.carrier (T.obj W₀)
      hdim₀ hnodal₀ htail hbridge hg)

/-- `schemeSpaceMap` sends an identity morphism to the identity. -/
private theorem schemeSpaceMap_id_eq_id (U : BigFppfOver B integerBase hZ) :
    schemeSpaceMap (𝟙 U) = 𝟙 (schemeSpace U) :=
  ObjectProperty.hom_ext _ (yoneda.map_id _)

open Stacks.Curves.StableModel in
/-- **Condition (2) of Stacks 0E8A on a scheme chart.** Let `f' : Z_X' ⟶ Z_Y'` over `U'` be the
base change along `ι : U' ⟶ U` of a morphism `f : Z_X ⟶ Z_Y` of schemes over `U`, and suppose that
`f` satisfies the conclusion of the scheme form of Stacks 0E88 (`h0`: `𝒪 = f_*𝒪` and
`R¹f_*𝒪 = 0` after every base change) over an open `N` containing the image of `ι`. If the fibres
of `Z_Y'` are proper nodal curves with ample dualizing sheaf, then `f'` satisfies condition (2). -/
theorem isFibrewiseStableContraction_schemeSpaceMap
    {U U' ZX ZY ZX' ZY' : BigFppfOver B integerBase hZ} {qY : ZY ⟶ U}
    {f : ZX ⟶ ZY} {ι : U' ⟶ U} {qX' : ZX' ⟶ U'} {qY' : ZY' ⟶ U'} {f' : ZX' ⟶ ZY'}
    {jX : ZX' ⟶ ZX} {jY : ZY' ⟶ ZY} (hf' : f' ≫ qY' = qX') (hjY : IsPullback jY qY' qY ι)
    (hjX : IsPullback jX f' f jY) (N : ((BigFppfOver.toScheme B integerBase hZ).obj U).Opens)
    (hι : Set.range ((BigFppfOver.toScheme B integerBase hZ).map ι) ⊆ N)
    (h0 : ∀ ⦃T' Y' X' : Scheme.{u}⦄ (h : T' ⟶ (BigFppfOver.toScheme B integerBase hZ).obj U)
      (iY : Y' ⟶ (BigFppfOver.toScheme B integerBase hZ).obj ZY) (qY'' : Y' ⟶ T')
      (iX : X' ⟶ (BigFppfOver.toScheme B integerBase hZ).obj ZX) (f'' : X' ⟶ Y'),
      Set.range h ⊆ N →
      IsPullback iY qY'' ((BigFppfOver.toScheme B integerBase hZ).map qY) h →
      IsPullback iX f'' ((BigFppfOver.toScheme B integerBase hZ).map f) iY →
      IsIso (Scheme.Modules.unitToPushforwardUnit f'') ∧
        IsZero (((Scheme.Modules.pushforward f'').rightDerived 1).obj
          (SheafOfModules.unit X'.ringCatSheaf)))
    (hpres : ∀ Q : Space.FieldValuedPoint B integerBase hZ (schemeSpace U').obj,
      ∃ (V : BigFppfOver B integerBase hZ) (v : V ⟶ Q.siteObject)
        (q : yoneda.obj V ⟶ yoneda.obj ZX'),
        IsPullback q (yoneda.map v) (yoneda.map qX') (yonedaEquiv.symm Q.value))
    (hY : ∀ (Q : Space.FieldValuedPoint B integerBase hZ (schemeSpace U').obj)
      ⦃W : BigFppfOver B integerBase hZ⦄ (w : W ⟶ Q.siteObject) (r : yoneda.obj W ⟶ yoneda.obj ZY'),
      IsPullback r (yoneda.map w) (yoneda.map qY') (yonedaEquiv.symm Q.value) →
        ∃ hp : IsProper ((BigFppfOver.toScheme B integerBase hZ).map w),
          topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj W) = 1 ∧
          (letI : ((BigFppfOver.toScheme B integerBase hZ).obj W).Over (Spec (.of Q.carrier)) :=
              ⟨(BigFppfOver.toScheme B integerBase hZ).map w⟩;
            Stacks.Curves.HasAtWorstNodalSingularities Q.carrier
              ((BigFppfOver.toScheme B integerBase hZ).obj W)) ∧
          (letI := hp
           ∃ _ : AlgebraicGeometry.SheafOfModules.IsInvertible
              ((BigFppfOver.toScheme B integerBase hZ).obj W).toRingedSpace.presheaf
              (structureSheafRing
                ((BigFppfOver.toScheme B integerBase hZ).obj W).toRingedSpace).property
              (Stacks.Duality.dualizingSheafOverField
                ((BigFppfOver.toScheme B integerBase hZ).map w)),
            Scheme.Modules.IsAmple ((BigFppfOver.toScheme B integerBase hZ).obj W)
              (Stacks.Duality.dualizingSheafOverField
                ((BigFppfOver.toScheme B integerBase hZ).map w)))) :
    IsFibrewiseStableContraction B hZ (schemeSpaceMap f') (schemeSpaceMap qY') := by
  let T := BigFppfOver.toScheme B integerBase hZ
  have : PreservesLimitsOfShape WalkingCospan T :=
    Space.preservesLimitsOfShape_walkingCospan_toScheme B integerBase hZ
  have hcomp : (schemeSpaceMap f' ≫ schemeSpaceMap qY').hom = yoneda.map qX' := by
    rw [← schemeSpaceMap_comp, hf']
    rfl
  intro Q
  refine ⟨?_, fun V W v w q r m hq hr hmw hmr => ?_⟩
  · obtain ⟨V, v, q, hq⟩ := hpres Q
    exact ⟨V, v, q, by rwa [hcomp]⟩
  obtain ⟨hp, hdim, hnodal, hamp⟩ := hY Q w r hr
  rw [hcomp] at hq
  let Qv : Q.siteObject ⟶ U' := Q.value
  rw [yonedaEquiv_symm_value] at hq hr
  have hq₀ : yoneda.map (Yoneda.fullyFaithful.preimage q) = q := Yoneda.fullyFaithful.map_preimage q
  have hr₀ : yoneda.map (Yoneda.fullyFaithful.preimage r) = r := Yoneda.fullyFaithful.map_preimage r
  have sqV : IsPullback (Yoneda.fullyFaithful.preimage q) v qX' Qv :=
    IsPullback.of_map_of_faithful yoneda (by rwa [hq₀])
  have sqW : IsPullback (Yoneda.fullyFaithful.preimage r) w qY' Qv :=
    IsPullback.of_map_of_faithful yoneda (by rwa [hr₀])
  have hmr₀ : m ≫ Yoneda.fullyFaithful.preimage r = Yoneda.fullyFaithful.preimage q ≫ f' :=
    Yoneda.fullyFaithful.map_injective (by rwa [Functor.map_comp, Functor.map_comp, hq₀, hr₀])
  have hcsq : IsPullback (Yoneda.fullyFaithful.preimage q) m f' (Yoneda.fullyFaithful.preimage r) :=
    IsPullback.of_bot (by rwa [hmw, hf']) hmr₀.symm sqW
  have hrange : Set.range (T.map (Qv ≫ ι)) ⊆ N := by
    rintro _ ⟨x, rfl⟩
    exact hι ⟨T.map Qv x, by rw [Functor.map_comp, Scheme.Hom.comp_apply]⟩
  obtain ⟨hU, hR⟩ := h0 (T.map (Qv ≫ ι)) _ _ _ (T.map m) hrange
    ((sqW.paste_horiz hjY).map T) ((hcsq.paste_horiz hjX).map T)
  exact
    { comp_eq := by rw [← Functor.map_comp, hmw]
      isProper := hp
      topologicalKrullDim_eq := hdim
      hasAtWorstNodalSingularities := hnodal
      isIso_unitToPushforwardObjUnit := hU
      isZero_rightDerived_one := hR
      isAmple := hamp }

/-- **The local step of Stacks 0E8A.** Let `X` be a prestable family of curves with fibres of
genus `g ≥ 2`, let `t : Y.base ⟶ X.base` be étale, and let `h : X_{Y.base} ⟶ Y` be a morphism
over `Y.base` whose fibres over a point `u` are stable contractions (the output of Stacks 0E7C
applied to the stable contraction of a fibre, Stacks 0E7Q). Then there is a morphism of families
`φ : X' ⟶ X` with étale base map whose image contains `t u`, and a stable model `c' : X' ⟶ Y'` of
genus `g`. The families `X'` and `Y'` are base changes of `X` and `Y` to an open of a scheme chart
on which both are schemes, chosen inside the opens given by Stacks 0E88 (condition (1) and its
scheme form) and by the openness of the stable locus (Stacks 0E76). -/
theorem exists_isStableModel_of_fibresStableContractionsAt
    (h0E6F : HasEtaleLocalSchemeCharts B hZ)
    (h0E76 : IsOpenCurvesLocus B hZ (IsStableCurveFamily B hZ)) {g : ℕ} {X : CurveFamily B hZ}
    (hX : IsPrestableCurveFamily B hZ X) (hgen : X.HasFibresOfGenus g) (hg : 2 ≤ g)
    (Y : CurveFamily B hZ) (t : Y.base ⟶ X.base)
    (ht : Etale ((BigFppfOver.toScheme B integerBase hZ).map t))
    {A : AlgebraicSpaces B integerBase hZ} (iA : A ⟶ X.total) (pA : A ⟶ schemeSpace Y.base)
    (hsq : IsPullback iA pA X.toBase (schemeSpaceMap t)) (h : A ⟶ Y.total)
    (hh : h ≫ Y.toBase = pA) (u : (BigFppfOver.toScheme B integerBase hZ).obj Y.base)
    (hfib : FibresStableContractionsAt Y pA h u) :
    ∃ (X' Y' : CurveFamily B hZ) (φ : X' ⟶ X) (b' : X'.base ⟶ Y'.base)
      (c' : X'.total ⟶ Y'.total),
      Etale ((BigFppfOver.toScheme B integerBase hZ).map φ.baseMap) ∧
      (BigFppfOver.toScheme B integerBase hZ).map t u ∈
        Set.range ((BigFppfOver.toScheme B integerBase hZ).map φ.baseMap) ∧
      IsStableModel B hZ g b' c' := by
  let T := BigFppfOver.toScheme B integerBase hZ
  have : PreservesLimitsOfShape WalkingCospan T :=
    Space.preservesLimitsOfShape_walkingCospan_toScheme B integerBase hZ
  let XA := curveFamilyOfIsPullback X t iA pA hsq
  let b₀ : XA.base ⟶ Y.base := 𝟙 Y.base
  have : IsIso b₀ := inferInstanceAs (IsIso (𝟙 Y.base))
  have hb₀ : XA.toBase ≫ schemeSpaceMap b₀ = pA := by
    change pA ≫ schemeSpaceMap (𝟙 Y.base) = pA
    rw [schemeSpaceMap_id_eq_id, Category.comp_id]
  have hc : h ≫ Y.toBase = XA.toBase ≫ schemeSpaceMap b₀ := by
    rw [hb₀, hh]
  have hFA := fibreAcyclicAt_of_isStableContraction hX t iA pA hsq h hh u hfib
  have hSt := hasStableFibresAt_of_isStableContraction hX hgen hg t iA pA hsq h hh u hfib
  -- the scheme chart and the three opens
  obtain ⟨U, ZX, ZY, φ, qX, qY, pX, pY, f, hφ, ⟨u₁, hu₁⟩, hXc, hXc', hYc, hf, hfc⟩ :=
    exists_schemeCharts h0E6F (X := XA) b₀ h hc u
  obtain ⟨N₃, hu₃, hN₃⟩ :=
    exists_isOpen_chart_of_fibreAcyclicAt b₀ h hXc hXc' hYc hf hfc hc u₁ (hu₁ ▸ hFA)
  obtain ⟨N₂, hu₂, hN₂⟩ := exists_isOpen_isStable_of_fibre h0E76 Y u hSt
  obtain ⟨N₁, hu₁', hN₁⟩ := exists_isOpen_isUniversallyAcyclic_of_fibre h0E6F (X := XA)
    b₀ h hc u hFA
  let pX₀ : schemeSpace ZX ⟶ A := pX
  have hfc₀ : schemeSpaceMap f ≫ pY = pX₀ ≫ h := hfc
  have hXc₀ : IsPullback pX₀ (schemeSpaceMap qX) pA (schemeSpaceMap φ) := by
    rwa [← hb₀]
  let O : (T.obj U).Opens := N₃ ⊓ T.map φ ⁻¹ᵁ N₂ ⊓ T.map φ ⁻¹ᵁ N₁
  have huO : u₁ ∈ O := by
    refine TopologicalSpace.Opens.mem_inf.2 ⟨TopologicalSpace.Opens.mem_inf.2 ⟨hu₃, ?_⟩, ?_⟩
    · change T.map φ u₁ ∈ N₂
      rwa [hu₁]
    · change T.map φ u₁ ∈ N₁
      rwa [hu₁]
  have hNO : B.Contains O.toScheme := B.contains_of_mono O.ι U.left.2
  let ι := BigFppfOver.siteMapOver B integerBase hZ U hNO O.ι
  let U' := BigFppfOver.siteObjectOver B integerBase hZ U hNO O.ι
  have hO : ∀ x : T.obj U', T.map ι x ∈ O := fun x => by
    change O.ι x ∈ (O : Set (T.obj U))
    rw [← Scheme.Opens.range_ι]
    exact ⟨x, rfl⟩
  let φ' : U' ⟶ Y.base := ι ≫ φ
  have : Etale (T.map φ) := hφ
  have : Etale (T.map t) := ht
  have : Etale (T.map (φ' ≫ t)) := by
    change Etale (O.ι ≫ T.map φ ≫ T.map t)
    infer_instance
  have hrange : ∀ {M : (T.obj Y.base).Opens},
      (∀ x : T.obj U, x ∈ O → T.map φ x ∈ M) → Set.range (T.map φ') ⊆ M := by
    intro M hM
    rintro _ ⟨x, rfl⟩
    rw [Functor.map_comp, Scheme.Hom.comp_apply]
    exact hM _ (hO x)
  -- the restricted charts
  let jX := pullback.fst qX ι
  let qX' := pullback.snd qX ι
  let jY := pullback.fst qY ι
  let qY' := pullback.snd qY ι
  let f' : pullback qX ι ⟶ pullback qY ι := pullback.map qX ι qY ι f (𝟙 _) (𝟙 _)
    (by rw [Category.comp_id, hf]) (by simp)
  have hf' : f' ≫ qY' = qX' := (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  have hfq : schemeSpaceMap f' ≫ schemeSpaceMap qY' = schemeSpaceMap qX' := by
    rw [← schemeSpaceMap_comp, hf']
  have hjf : f' ≫ jY = jX ≫ f := pullback.lift_fst _ _ _
  have hjY : IsPullback jY qY' qY ι := IsPullback.of_hasPullback qY ι
  have hjX : IsPullback jX f' f jY := by
    refine IsPullback.of_bot ?_ hjf.symm hjY
    rw [hf', hf]
    exact IsPullback.of_hasPullback qX ι
  have sqXA : IsPullback (schemeSpaceMap jX ≫ pX₀) (schemeSpaceMap qX') pA
      (schemeSpaceMap φ') := by
    rw [schemeSpaceMap_comp]
    exact (isPullback_schemeSpaceMap (IsPullback.of_hasPullback qX ι)).paste_horiz hXc₀
  have sqX' : IsPullback ((schemeSpaceMap jX ≫ pX₀) ≫ iA) (schemeSpaceMap qX') X.toBase
      (schemeSpaceMap (φ' ≫ t)) := by
    rw [schemeSpaceMap_comp]
    exact sqXA.paste_horiz hsq
  have sqY' : IsPullback (schemeSpaceMap jY ≫ pY) (schemeSpaceMap qY') Y.toBase
      (schemeSpaceMap φ') := by
    rw [schemeSpaceMap_comp]
    exact (isPullback_schemeSpaceMap hjY).paste_horiz hYc
  -- condition (1) on the chart
  have h1 : IsUniversallyAcyclicContraction B hZ (schemeSpaceMap f') (schemeSpaceMap qY') := by
    intro V v A' D' a' iA' iD' p' hD hA hcomm
    refine hN₁ (v ≫ φ') ?_ a' (iA' ≫ schemeSpaceMap jX ≫ pX₀) (iD' ≫ schemeSpaceMap jY ≫ pY) p'
      ?_ ?_ ?_
    · rintro _ ⟨x, rfl⟩
      rw [Functor.map_comp, Scheme.Hom.comp_apply]
      exact hrange (fun y hy => (TopologicalSpace.Opens.mem_inf.1 hy).2) ⟨_, rfl⟩
    · rw [schemeSpaceMap_comp]
      exact hD.paste_horiz sqY'
    · change IsPullback (iA' ≫ schemeSpaceMap jX ≫ pX₀) (a' ≫ p') (h ≫ Y.toBase)
        (schemeSpaceMap (v ≫ φ'))
      rw [schemeSpaceMap_comp, hh]
      have hA' : IsPullback iA' (a' ≫ p') (schemeSpaceMap qX') (schemeSpaceMap v) := by
        rwa [← hfq]
      exact hA'.paste_horiz sqXA
    · have e : schemeSpaceMap f' ≫ schemeSpaceMap jY ≫ pY = schemeSpaceMap jX ≫ pX₀ ≫ h := by
        rw [← Category.assoc, ← schemeSpaceMap_comp, hjf, schemeSpaceMap_comp, Category.assoc,
          hfc₀]
      change a' ≫ iD' ≫ schemeSpaceMap jY ≫ pY = (iA' ≫ schemeSpaceMap jX ≫ pX₀) ≫ h
      rw [← Category.assoc, hcomm, Category.assoc, e, Category.assoc, Category.assoc]
  -- the two families over the chart
  let X' := curveFamilyOfIsPullback X (φ' ≫ t) _ _ sqX'
  let Y' := curveFamilyOfIsPullback Y φ' _ _ sqY'
  have hX' : IsPrestableCurveFamily B hZ X' :=
    CurveFamily.isPrestableCurveFamily_of_hom (curveFamilyOfIsPullbackHom X (φ' ≫ t) _ _ sqX') hX
  have hgen' : X'.HasFibresOfGenus g :=
    hgen.of_hom (curveFamilyOfIsPullbackHom X (φ' ≫ t) _ _ sqX')
  have hY' : IsStableCurveFamily B hZ Y' :=
    hN₂ Y' (curveFamilyOfIsPullbackHom Y φ' _ _ sqY')
      (hrange fun x hx => (TopologicalSpace.Opens.mem_inf.1
        (TopologicalSpace.Opens.mem_inf.1 hx).1).2)
  let b' : X'.base ⟶ Y'.base := 𝟙 U'
  have : IsIso b' := inferInstanceAs (IsIso (𝟙 U'))
  let c' : X'.total ⟶ Y'.total := schemeSpaceMap f'
  have hcomp : c' ≫ Y'.toBase = X'.toBase ≫ schemeSpaceMap b' := by
    change schemeSpaceMap f' ≫ schemeSpaceMap qY' = schemeSpaceMap qX' ≫ schemeSpaceMap (𝟙 U')
    rw [schemeSpaceMap_id_eq_id, Category.comp_id, hfq]
  -- condition (2) on the chart
  have h2₀ : IsFibrewiseStableContraction B hZ (schemeSpaceMap f') (schemeSpaceMap qY') := by
    refine isFibrewiseStableContraction_schemeSpaceMap hf' hjY hjX N₃ ?_ hN₃
      (fun Q => exists_presentation_of_fieldValuedPoint X' Q) (fun Q W w r hr => ?_)
    · rintro _ ⟨x, rfl⟩
      exact (TopologicalSpace.Opens.mem_inf.1 (TopologicalSpace.Opens.mem_inf.1 (hO x)).1).1
    · obtain ⟨hp, hdim, -, hnod⟩ := fibre_properties_of_isPrestableCurveFamily hY'.1 Q w r hr
      have := hp
      exact ⟨hp, hdim, hnod, isAmple_dualizingSheafOverField_of_isStableCurveFamily hY' Q w r hr⟩
  have h2 : IsFibrewiseStableContraction B hZ c' Y'.toBase := h2₀
  obtain ⟨x, hx⟩ : u₁ ∈ Set.range O.ι := by
    rwa [Scheme.Opens.range_ι]
  refine ⟨X', Y', curveFamilyOfIsPullbackHom X (φ' ≫ t) _ _ sqX', b', c', ?_, ⟨x, ?_⟩,
    { isIso_base := inferInstance
      comp_toBase := hcomp
      isStable := hY'
      hasFibresOfGenus := (isStableCurveFamily_of_isFibrewiseStableContraction hX' hgen' hg
        hY'.1 b' c' hcomp h2).2
      universallyAcyclic := h1
      fibrewiseStable := h2 }⟩
  · change Etale (T.map (φ' ≫ t))
    infer_instance
  · change (O.ι ≫ T.map φ ≫ T.map t) x = T.map t u
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hx, hu₁]

end AlgebraicGeometry.C1590Private

end
