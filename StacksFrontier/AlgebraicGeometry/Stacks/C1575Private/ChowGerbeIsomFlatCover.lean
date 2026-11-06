module

public import StacksFrontier.AlgebraicGeometry.Stacks.C1575Private.ChowGerbeStagePullback
public import StacksFrontier.AlgebraicGeometry.Stacks.ChowFiniteCoverFactorizationUnconditional
public import StacksFrontier.AlgebraicGeometry.Stacks.C1575Private.ChowGerbeIsomSectionsOver
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeIsomTotalPresheafProperties
public import StacksFrontier.AlgebraicGeometry.Stacks.PresentationStabilizerFlat
public import StacksFrontier.AlgebraicGeometry.Stacks.ChartSlicingFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.KeelMori.ModuliFiniteTypeEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductUniversalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteProperQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallZariskiSite

/-!
# Zariski-local isomorphisms of two sections after a finite cover (proof of Stacks 0CQ7)

This is the passage from stage (d) to stage (e) of the proof of [Stacks, Tag 0CQ7], one pair of
sections at a time. Let `x_0, x_k` be sections of `f : 𝒳 ⟶ Y` over `p` defined on opens of `Y'`
containing `V'`, where `V'` lies over `V` and `𝒳_V ⟶ V` is a gerbe. Restricted to `V'`, both lift
to `𝒳_V`, and the space `T = Isom(x_0|_{V'}, x_k|_{V'}) ⟶ V'` of isomorphisms of the lifts is
surjective, flat and locally of finite presentation (Stacks 0CPR, through 06QI). Stacks 0CQ6
gives a finite surjective `g : Y'' ⟶ Y'` such that `g⁻¹(V') ⟶ V'` lifts Zariski locally to `T`;
every local lift is an isomorphism of the pulled back `x_0` and `x_k`. So after pulling back the
stage data along `g`, the sections `x_0` and `x_k` are Zariski locally isomorphic over `V''`.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.ChowGerbeLocalIsos.representingMap_comp_eq_of_iso`
* `AlgebraicGeometry.Stack.AlgebraicStacks.ChowGerbeLocalIsos.StageData.exists_pullback_locIso`

## References

* [Stacks Project, Tag 0CQ7](https://stacks.math.columbia.edu/tag/0CQ7)
* [Stacks Project, Tag 0CQ6](https://stacks.math.columbia.edu/tag/0CQ6)
* [Stacks Project, Tag 0CPR](https://stacks.math.columbia.edu/tag/0CPR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.PresheafOfCategories

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks.ChowGerbeLocalIsos

open ChowGerbeMerge ChowGerbeSectionCover

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A 1-morphism of space stacks over a morphism of spaces is a lift of it.** If
`a : A ⟶ T` is a 1-morphism of space stacks and `a ≫ b ≅ c` for morphisms of algebraic spaces
`b : T ⟶ Z` and `c : A ⟶ Z`, then the morphism of representing presheaves of `a` followed by `b`
is `c` (Stacks 04SW). -/
theorem representingMap_comp_eq_of_iso {A T Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hA : IsAlgebraicSpace B S hS A) (hT : IsAlgebraicSpace B S hS T)
    (hZ : IsAlgebraicSpace B S hS Z)
    (a : algebraicSpaceStack.{u, w} B S hS A hA ⟶ algebraicSpaceStack.{u, w} B S hS T hT)
    (b : T ⟶ Z) (c : A ⟶ Z)
    (e : a ≫ algebraicSpaceStackMap.{u, w} B S hS hT hZ b ≅
      algebraicSpaceStackMap.{u, w} B S hS hA hZ c) :
    representingMap B S hS (fibredCategory B S hS A) (fibredCategory B S hS T) A T
        (StacksRepresentableCFG.EquivalenceOver.refl _)
        (StacksRepresentableCFG.EquivalenceOver.refl _) a.hom ≫ b = c := by
  have h1 := representingMap_comp B S hS _ _ _ (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _) a.hom (associatedMap B S hS b).1
  rw [representingMap_associatedMap] at h1
  rw [← h1]
  exact (representingMap_congr_twoIso B S hS _ _ _ _
    { hom := e.hom.hom, inv := e.inv.hom
      hom_inv_id := congrArg Bicategory.InducedBicategory.Hom₂.hom e.hom_inv_id
      inv_hom_id := congrArg Bicategory.InducedBicategory.Hom₂.hom e.inv_hom_id }).trans
    (representingMap_associatedMap B S hS _ _ _)

variable {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hY : IsAlgebraicSpace B S hS Y}
  {𝒳 : AlgebraicStacks.{u, w} B S hS} {f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY}
  {W V : Subfunctor Y} {n : ℕ}

/-- Restricted to `V'`, the section `x_i` lifts to the 2-fibre product `𝒳_V`. -/
theorem StageData.exists_lift_twoFibreProduct (hV : Space.IsOpenSubspace B S hS V)
    (D : StageData hY f W V n) (hVW : ∀ k, D.V'.1 ≤ (D.Wi k).1) (i : ℕ) :
    ∃ z : algebraicSpaceStack.{u, w} B S hS D.V'.1.toFunctor D.V'.2.1 ⟶
        (twoFibreProductSquareAlgebraicStacks B S hS
          (algebraicSpaceStackMap.{u, w} B S hS hV.1 hY V.ι) f).pt,
      Nonempty (algebraicSpaceStackMap.{u, w} B S hS D.V'.2.1 hV.1
          (Subfunctor.homOfLe D.hV'V ≫ V.fromPreimage D.p) ≅
          z ≫ (twoFibreProductSquareAlgebraicStacks B S hS
            (algebraicSpaceStackMap.{u, w} B S hS hV.1 hY V.ι) f).fst) ∧
        Nonempty (algebraicSpaceStackMap.{u, w} B S hS D.V'.2.1 (D.Wi i).2.1
          (Subfunctor.homOfLe (hVW i)) ≫ D.x i ≅
          z ≫ (twoFibreProductSquareAlgebraicStacks B S hS
            (algebraicSpaceStackMap.{u, w} B S hS hV.1 hY V.ι) f).snd) := by
  have hq : (Subfunctor.homOfLe D.hV'V ≫ V.fromPreimage D.p) ≫ V.ι = D.V'.1.ι ≫ D.p := by
    simp only [Category.assoc, Subfunctor.fromPreimage_ι, Subfunctor.homOfLe_ι_assoc]
  obtain ⟨e⟩ := nonempty_comp_iso_of_iso D.V'.2.1 (D.Wi i).2.1 hY f
    (Subfunctor.homOfLe (hVW i)) (D.x i) _ (D.hx i)
  obtain ⟨e'⟩ : Nonempty (algebraicSpaceStackMap.{u, w} B S hS D.V'.2.1 hV.1
      (Subfunctor.homOfLe D.hV'V ≫ V.fromPreimage D.p) ≫
      algebraicSpaceStackMap.{u, w} B S hS hV.1 hY V.ι ≅
      (algebraicSpaceStackMap.{u, w} B S hS D.V'.2.1 (D.Wi i).2.1
        (Subfunctor.homOfLe (hVW i)) ≫ D.x i) ≫ f) := by
    refine ⟨eqToIso ?_ ≪≫ e.symm⟩
    rw [← algebraicSpaceStackMap_comp B S hS D.V'.2.1 hV.1 hY
      (Subfunctor.homOfLe D.hV'V ≫ V.fromPreimage D.p) V.ι, hq, Subfunctor.homOfLe_ι_assoc]
  let L := Bicategory.twoFibreProductPreHom
    (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS _ f) ⟨_, _, _, e'⟩
  exact ⟨L.hom, ⟨L.isoFst⟩, ⟨L.isoSnd⟩⟩

/-- If `O` is an open of `Y''` mapping through `c` into `W'`, and `ι : W' ⟶ Y''` lifts to
`q' : W' ⟶ V'` over `g`, then the restriction of the pulled back section `x_i` to `O` is the
restriction of `x_i` along `c ≫ q'`. -/
theorem StageData.pullback_x_restrict_eq (D : StageData hY f W V n)
    (hVW : ∀ k, D.V'.1 ≤ (D.Wi k).1) {Y'' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY'' : IsAlgebraicSpace B S hS Y'') (g : Y'' ⟶ D.Y'.1) (hg : Space.IsProper B S hS g)
    {O : Subfunctor Y''} (hO : Space.IsOpenSubspace B S hS O)
    (hOV : O ≤ (D.pullback hY'' g hg).V'.1) {W' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hW' : IsAlgebraicSpace B S hS W') (ι : W' ⟶ Y'') (q' : W' ⟶ D.V'.1.toFunctor)
    (hιg : ι ≫ g = q' ≫ D.V'.1.ι) (c : O.toFunctor ⟶ W') (hc : c ≫ ι = O.ι) (i : ℕ) :
    algebraicSpaceStackMap.{u, w} B S hS hO.1 ((D.pullback hY'' g hg).Wi i).2.1
        (Subfunctor.homOfLe (hOV.trans (D.pullback_le hY'' g hg hVW i))) ≫
        (D.pullback hY'' g hg).x i =
      algebraicSpaceStackMap.{u, w} B S hS hO.1 hW' c ≫
        (algebraicSpaceStackMap.{u, w} B S hS hW' D.V'.2.1 q' ≫
          (algebraicSpaceStackMap.{u, w} B S hS D.V'.2.1 (D.Wi i).2.1
            (Subfunctor.homOfLe (hVW i)) ≫ D.x i)) := by
  have hcomm : Subfunctor.homOfLe (hOV.trans (D.pullback_le hY'' g hg hVW i)) ≫
      (D.Wi i).1.fromPreimage g = c ≫ q' ≫ Subfunctor.homOfLe (hVW i) := by
    rw [← cancel_mono (D.Wi i).1.ι]
    simp only [Category.assoc, Subfunctor.homOfLe_ι]
    rw [← hιg, reassoc_of% hc]
    rfl
  exact (stackMap_comp_comp_eq (𝒳 := 𝒳) hO.1 (D.Wi i).2.1 ((D.pullback hY'' g hg).Wi i).2.1 hW'
      (Subfunctor.homOfLe (hOV.trans (D.pullback_le hY'' g hg hVW i)))
      ((D.Wi i).1.fromPreimage g) c (q' ≫ Subfunctor.homOfLe (hVW i)) hcomm (D.x i)).trans
    (congrArg (algebraicSpaceStackMap.{u, w} B S hS hO.1 hW' c ≫ ·)
      (stackMap_comp_assoc (𝒳 := 𝒳) hW' D.V'.2.1 (D.Wi i).2.1 q'
        (Subfunctor.homOfLe (hVW i)) (D.x i)))

/-- If an open immersion `ι : W' ⟶ Y''` lifts to `q' : W' ⟶ V'` over `g` and the restrictions of
`x_0` and `x_k` along `q'` are isomorphic, then around every point of the image of `ι` there is an
open of `V''` over which the pulled back `x_0` and `x_k` are isomorphic. -/
theorem StageData.exists_open_iso_of_lift (D : StageData hY f W V n)
    (hVW : ∀ k, D.V'.1 ≤ (D.Wi k).1) {Y'' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY'' : IsAlgebraicSpace B S hS Y'') (g : Y'' ⟶ D.Y'.1) (hg : Space.IsProper B S hS g)
    {W' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hW' : IsAlgebraicSpace B S hS W') (ι : W' ⟶ Y'')
    (hι : Space.IsOpenImmersion B S hS ι) (q' : W' ⟶ D.V'.1.toFunctor)
    (hιg : ι ≫ g = q' ≫ D.V'.1.ι) {k : ℕ}
    (φ : algebraicSpaceStackMap.{u, w} B S hS hW' D.V'.2.1 q' ≫
        (algebraicSpaceStackMap.{u, w} B S hS D.V'.2.1 (D.Wi 0).2.1
          (Subfunctor.homOfLe (hVW 0)) ≫ D.x 0) ≅
      algebraicSpaceStackMap.{u, w} B S hS hW' D.V'.2.1 q' ≫
        (algebraicSpaceStackMap.{u, w} B S hS D.V'.2.1 (D.Wi k).2.1
          (Subfunctor.homOfLe (hVW k)) ≫ D.x k))
    {v : Space.points B S hS Y''} (hv : v ∈ Set.range (Space.pointsMap B S hS W' ι)) :
    ∃ (O : Subfunctor Y'') (hO : Space.IsOpenSubspace B S hS O)
      (hOV : O ≤ (D.pullback hY'' g hg).V'.1),
      v ∈ Set.range (Space.pointsMap B S hS O.toFunctor O.ι) ∧
      Nonempty (algebraicSpaceStackMap.{u, w} B S hS hO.1 ((D.pullback hY'' g hg).Wi 0).2.1
          (Subfunctor.homOfLe (hOV.trans (D.pullback_le hY'' g hg hVW 0))) ≫
          (D.pullback hY'' g hg).x 0 ≅
        algebraicSpaceStackMap.{u, w} B S hS hO.1 ((D.pullback hY'' g hg).Wi k).2.1
          (Subfunctor.homOfLe (hOV.trans (D.pullback_le hY'' g hg hVW k))) ≫
          (D.pullback hY'' g hg).x k) := by
  classical
  have : Mono ι := Space.mono_of_isOpenImmersion B S hS ι hι
  have hO : Space.IsOpenSubspace B S hS (Subfunctor.range ι) :=
    Space.isOpenSubspace_range_of_open B S hS ι hW' hι
  have hOV : Subfunctor.range ι ≤ (D.pullback hY'' g hg).V'.1 := by
    rintro U _ ⟨a, rfl⟩
    show g.app U (ι.app U a) ∈ D.V'.1.obj U
    have h := congrArg (fun m : W' ⟶ D.Y'.1 => m.app U a) hιg
    simp only [NatTrans.comp_app_apply] at h
    rw [h]
    exact (q'.app U a).2
  refine ⟨_, hO, hOV, by rwa [range_pointsMap_range_ι], ?_⟩
  let c : (Subfunctor.range ι).toFunctor ⟶ W' := inv (Subfunctor.toRange ι)
  have hc : c ≫ ι = (Subfunctor.range ι).ι := by
    simp only [c, IsIso.inv_comp_eq, Subfunctor.toRange_ι]
  exact ⟨eqToIso (D.pullback_x_restrict_eq hVW hY'' g hg hO hOV hW' ι q' hιg c hc 0) ≪≫
    Bicategory.whiskerLeftIso _ φ ≪≫
    eqToIso (D.pullback_x_restrict_eq hVW hY'' g hg hO hOV hW' ι q' hιg c hc k).symm⟩

/-- **Stage (d) to stage (e) of the proof of Stacks 0CQ7, for one pair of sections.** If `V' ⊆ W_k`
for all `k` and `𝒳_V ⟶ V` is a gerbe, then for every `k₀` there is a finite surjective
`g : Y'' ⟶ Y'` (Stacks 0CQ6, applied to `Isom(x_0|_{V'}, x_{k₀}|_{V'}) ⟶ V'`, which is surjective,
flat and locally of finite presentation by Stacks 0CPR) after pulling back along which `x_0` and
`x_{k₀}` are Zariski locally isomorphic over `V'`. -/
theorem StageData.exists_pullback_locIso (hV : Space.IsOpenSubspace B S hS V)
    (hG : IsGerbeOver B S hS (twoFibreProductSquareAlgebraicStacks B S hS
      (algebraicSpaceStackMap.{u, w} B S hS hV.1 hY V.ι) f).fst)
    (D : StageData hY f W V n) (hVW : ∀ k, D.V'.1 ≤ (D.Wi k).1) (k₀ : ℕ) :
    ∃ (Y'' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hY'' : IsAlgebraicSpace B S hS Y'')
      (g : Y'' ⟶ D.Y'.1) (hg : Space.IsProper B S hS g), Space.IsSurjective B S hS g ∧
      (D.pullback hY'' g hg).LocIso (D.pullback_le hY'' g hg hVW) k₀ := by
  classical
  let Q := twoFibreProductSquareAlgebraicStacks B S hS
    (algebraicSpaceStackMap.{u, w} B S hS hV.1 hY V.ι) f
  let Z := D.V'.1.toFunctor
  have hZ : IsAlgebraicSpace B S hS Z := D.V'.2.1
  choose z hzF hzS using D.exists_lift_twoFibreProduct hV hVW
  obtain ⟨e₀⟩ := hzF 0
  obtain ⟨e₁⟩ := hzF k₀
  let α : z 0 ≫ Q.fst ⟶ z k₀ ≫ Q.fst := (e₀.symm ≪≫ e₁).hom
  have hT := isAlgebraicSpace_relativeIsomorphismTotalPresheaf B S hS Z hZ Q.fst (z 0) (z k₀) α
  obtain ⟨hsurj, hflat, hlfp⟩ :=
    isSurjective_isFlat_isLocallyOfFinitePresentation_relativeIsomorphismTotalProj B S hS Z hZ
      Q.fst hG (z 0) (z k₀) α
  let proj := PresheafOfCategories.elementsTotalProj Z
    (TwoFibreProductOver.RelativeDiagonalFibre.relVertHomPresheaf
      (algebraicSpaceStack.{u, w} B S hS V.toFunctor hV.1).val.isFiberedInGroupoids
      Q.pt.val.isFiberedInGroupoids
      (relativeIsomorphismTwistedPoint B S hS Z hZ Q.fst (z 0) (z k₀) α).w Q.fst.hom.hom.w)
  let fT := algebraicSpaceStackMap.{u, w} B S hS hT hZ proj
  have hfs : IsSurjective B S hS fT := by
    intro t
    obtain ⟨t', rfl⟩ := (spacePointsEquiv B S hS Z).surjective t
    obtain ⟨s, hs⟩ := hsurj t'
    exact ⟨spacePointsEquiv B S hS _ s, by
      rw [pointsMap_algebraicSpaceStackMap_spacePointsEquiv.{u, w}, hs]⟩
  -- Stacks 0CQ6
  obtain ⟨Y'', hY'', g, hgf, hgs, J, Wj, hWj, ιj, qj, xj, hιj, hιg, hcovj, hxj⟩ :=
    exists_finite_surjective_zariskiLocal_factorization B S hS
      D.Y'.2 D.qc D.qs D.V'.1 D.V'.2 D.hV'qc fT hfs
      ((isFlat_algebraicSpaceStackMap_iff.{u, w} B S hS hT hZ proj).2 hflat)
      ((isLocallyOfFinitePresentation_algebraicSpaceStackMap_iff.{u, w} B S hS hT hZ proj).2 hlfp)
  have hg : Space.IsProper B S hS g :=
    (Space.isProper_and_isLocallyQuasiFinite_of_isFinite B S hS hY'' D.Y'.2 g hgf).1
  refine ⟨Y'', hY'', g, hg, hgs, fun v hv => ?_⟩
  change v ∈ Set.range (Space.pointsMap B S hS (D.V'.1.preimage g).toFunctor
    (D.V'.1.preimage g).ι) at hv
  rw [Space.range_pointsMap_preimage_ι] at hv
  obtain ⟨j, hj⟩ := hcovj v hv
  let σ := representingMap B S hS (fibredCategory B S hS (Wj j)) (fibredCategory B S hS _) (Wj j)
    _ (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _) (xj j).hom
  let ψ := ChowGerbeIsomOver.twoMorphismOfRelVertFamily (qj j) (hWj j) hZ Q.fst (z 0) (z k₀) α
    (ChowGerbeIsomOver.relativeIsomorphismSectionOverEquiv (qj j) hZ Q.fst (z 0) (z k₀) α
      ⟨σ, (hxj j).elim (representingMap_comp_eq_of_iso (hWj j) hT hZ (xj j) proj (qj j))⟩)
  obtain ⟨eS₀⟩ := hzS 0
  obtain ⟨eS₁⟩ := hzS k₀
  let r := algebraicSpaceStackMap.{u, w} B S hS (hWj j) hZ (qj j)
  exact D.exists_open_iso_of_lift hVW hY'' g hg (hWj j) (ιj j) (hιj j) (qj j) (hιg j)
    (Bicategory.whiskerLeftIso r eS₀ ≪≫ (Bicategory.associator _ _ _).symm ≪≫
      Bicategory.whiskerRightIso (asIso ψ) Q.snd ≪≫ Bicategory.associator _ _ _ ≪≫
      Bicategory.whiskerLeftIso r eS₁.symm) hj

end AlgebraicGeometry.Stack.AlgebraicStacks.ChowGerbeLocalIsos

end
