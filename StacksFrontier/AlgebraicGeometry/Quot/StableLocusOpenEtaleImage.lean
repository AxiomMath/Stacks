module

public import StacksFrontier.AlgebraicGeometry.Curves.StableCurveGroundFieldExtension
public import StacksFrontier.AlgebraicGeometry.Quot.StableLocusOpenCharts
public import StacksFrontier.AlgebraicGeometry.Quot.PrestableStabilizationTransitions

/-!
# Stability descends from an open of an étale chart to its image

Let `G ⟶ S` be a prestable family of curves (Stacks 0E6T), `φ : U ⟶ S` a morphism of the big fppf
site and `W ⊆ U` an open such that every family of curves mapping to `G` over a morphism of bases
factoring through `W` is stable (the conclusion of
`AlgebraicGeometry.CurveFamily.exists_mem_forall_isStableCurveFamily_of_isPullback`). Then every
family of curves mapping to `G` over a morphism of bases with image in `φ(W)` is stable.

Pointwise: a field-valued point `Spec K ⟶ S` landing in `φ(W)` meets `W` after the extension `L/K`
given by the residue field of a point of `Spec K ×_S U` lying over `W`; the fibre over `Spec L` is
the base change of the fibre over `Spec K` and is stable, and stability of a nodal curve descends
along field extensions
(`AlgebraicGeometry.hasGenusTwoNoRationalTailNoRationalBridge_iff_of_isPullback`). For an étale
chart `φ` the extension `L/K` can be taken finite separable and `φ(W)` is open, which is how this
enters the step "after possibly shrinking `U`, `Y → U` is a stable family" of the proof of
Stacks 0E8A, through an étale scheme chart that is not an elementary étale neighbourhood.

## Main results

* `AlgebraicGeometry.CurveFamily.isStableCurveFamily_of_range_subset_image_of_etale`: the descent
  of stability from `W` to `φ(W)`.
* `AlgebraicGeometry.CurveFamily.exists_mem_forall_isStableCurveFamily_of_isPullback_of_etale`:
  through an étale scheme chart, a prestable family is stable over an open neighbourhood of a
  point with stable fibre.

## Implementation notes

Not registered: Stacks 0E74 and 0E76 are not proved here.

## References

* [Stacks Project, Tag 0E8A](https://stacks.math.columbia.edu/tag/0E8A)
* [Stacks Project, Tag 0E76](https://stacks.math.columbia.edu/tag/0E76)
* [Stacks Project, Tag 0E75](https://stacks.math.columbia.edu/tag/0E75)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace CurveFamily

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

local notation "𝒯" => BigFppfOver.toScheme B integerBase hZ

/-- If `t(x)` lies in `φ(W)`, some point of `X ×_Y U` over `x` has residue-field point landing
in `W` under the second projection. -/
private theorem exists_forall_range_snd_subset_of_mem_image {X Y U : BigFppfOver B integerBase hZ}
    (t : X ⟶ Y) (φ : U ⟶ Y) (W : ((𝒯).obj U).Opens) (x : (𝒯).obj X)
    (hx : ((𝒯).map t).base x ∈ ((𝒯).map φ).base '' W) :
    ∃ w : (𝒯).obj (pullback t φ),
      ∀ r : (residueFieldValuedPoint B hZ (pullback t φ) w).siteObject ⟶ pullback t φ,
        r = (residueFieldValuedPoint B hZ (pullback t φ) w).value →
          Set.range ((𝒯).map (r ≫ pullback.snd t φ)) ⊆ W := by
  have := Space.preservesLimitsOfShape_walkingCospan_toScheme B integerBase hZ
  obtain ⟨u, huW, hu⟩ := hx
  have hP : IsPullback ((𝒯).map (pullback.fst t φ)) ((𝒯).map (pullback.snd t φ)) ((𝒯).map t)
      ((𝒯).map φ) := (IsPullback.of_hasPullback t φ).map (𝒯)
  obtain ⟨z, -, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := (𝒯).map t) (g := (𝒯).map φ) x u hu.symm
  let w : (𝒯).obj (pullback t φ) := hP.isoPullback.inv.base z
  have hw₂ : ((𝒯).map (pullback.snd t φ)).base w = u := by
    change (hP.isoPullback.inv ≫ (𝒯).map (pullback.snd t φ)).base z = u
    rw [IsPullback.isoPullback_inv_snd, hz₂]
  refine ⟨w, fun r hr => ?_⟩
  rintro _ ⟨y, rfl⟩
  have : Subsingleton ((𝒯).obj (residueFieldValuedPoint B hZ (pullback t φ) w).siteObject) :=
    inferInstanceAs (Subsingleton (Spec (.of (((𝒯).obj (pullback t φ)).residueField w))))
  have hy₀ : y = IsLocalRing.closedPoint (((𝒯).obj (pullback t φ)).residueField w) :=
    Subsingleton.elim _ _
  have hy : ((𝒯).map r).base y = w := by
    rw [hr, hy₀]
    exact Scheme.fromSpecResidueField_apply _ _
  change ((𝒯).map (pullback.snd t φ)).base (((𝒯).map r).base y) ∈ W
  rwa [hy, hw₂]

/-- A pullback square of representables `V₁ → L` obtained by pasting onto a pullback square of
representables `V → K` over the same presheaf comes from a pullback square `V₁ → V` over
`n : L ⟶ K`. -/
private theorem exists_isPullback_of_isPullback_yoneda {C : Type*} [Category C]
    {E E₁ : Cᵒᵖ ⥤ Type _}
    {X V V₁ L L' K : C} {f : E ⟶ yoneda.obj X} {f₁ : E₁ ⟶ yoneda.obj L'}
    {q : yoneda.obj V ⟶ E} {q₁ : yoneda.obj V₁ ⟶ E₁} {a : E₁ ⟶ E}
    {v : V ⟶ K} {v₁ : V₁ ⟶ L} {p : K ⟶ X} {i : L ⟶ L'} {j : L' ⟶ X} {n : L ⟶ K}
    (hq : IsPullback q (yoneda.map v) f (yoneda.map p))
    (hq₁ : IsPullback q₁ (yoneda.map v₁) f₁ (yoneda.map i))
    (ha : IsPullback a f₁ f (yoneda.map j)) (hij : i ≫ j = n ≫ p) :
    ∃ g : V₁ ⟶ V, IsPullback g v₁ v n := by
  have hbig : IsPullback (q₁ ≫ a) (yoneda.map v₁) f (yoneda.map n ≫ yoneda.map p) := by
    simpa only [← Functor.map_comp, hij] using hq₁.paste_horiz ha
  have hw : (q₁ ≫ a) ≫ f = (yoneda.map v₁ ≫ yoneda.map n) ≫ yoneda.map p :=
    hbig.w.trans (Category.assoc _ _ _).symm
  have hleft : IsPullback (yoneda.map (Yoneda.fullyFaithful.preimage (hq.lift _ _ hw)))
      (yoneda.map v₁) (yoneda.map v) (yoneda.map n) := by
    rw [Functor.FullyFaithful.map_preimage]
    refine IsPullback.of_right ?_ (hq.lift_snd _ _ hw) hq
    rwa [hq.lift_fst _ _ hw]
  exact ⟨_, IsPullback.of_map yoneda (yoneda.map_injective (by simpa only [Functor.map_comp] using
    hleft.w)) hleft⟩

/-- The Yoneda element of a morphism is the representable map. -/
private theorem yonedaEquiv_symm_eq_yoneda_map {C : Type*} [Category C] {X Y : C} (f : X ⟶ Y) :
    yonedaEquiv.symm f = yoneda.map f :=
  yonedaEquiv.symm_apply_eq.2 (yonedaEquiv_yoneda_map f).symm

/-- **Stability descends from an open of a chart to its image.** Let `G` be a prestable family of
curves, `φ : U ⟶ S` a morphism into its base (an étale chart in the application) and `W ⊆ U` an
open such that every family of curves mapping to `G` over a morphism of bases factoring through
`W` is stable. Then a family of curves `F` mapping to `G` over a morphism of bases with image in
`φ(W)` is stable: a field-valued point `Spec K` of the base of `F` acquires a lift to `W` over the
residue field `L` of a point of `Spec K ×_S U`, the fibre of `F` over `Spec L` is stable, and it is
the base change to `L` of the fibre over `Spec K`, along which stability descends. -/
theorem isStableCurveFamily_of_range_subset_image_of_etale
    {G : CurveFamily B hZ} (hG : IsPrestableCurveFamily B hZ G)
    {U : BigFppfOver B integerBase hZ} (φ : U ⟶ G.base)
    (W : ((𝒯).obj U).Opens)
    (hW : ∀ (F : CurveFamily B hZ) (a : F ⟶ G) (b : F.base ⟶ U), b ≫ φ = a.baseMap →
      Set.range ((𝒯).map b) ⊆ W → IsStableCurveFamily B hZ F)
    {F : CurveFamily B hZ} (a : F ⟶ G)
    (haW : Set.range ((𝒯).map a.baseMap) ⊆ ((𝒯).map φ).base '' W) :
    IsStableCurveFamily B hZ F := by
  have hF : IsPrestableCurveFamily B hZ F := isPrestableCurveFamily_of_hom a hG
  refine ⟨hF, fun pF => ?_⟩
  have := Space.preservesLimitsOfShape_walkingCospan_toScheme B integerBase hZ
  -- the fibre of `F` over `pF`, a scheme `V` over `K`
  obtain ⟨V, v, q, hq⟩ := exists_isPullback_fieldValuedPoint B hZ F pF
  have hqy := isPullback_yoneda_of_isPullback_schemeSpace F.toBase pF hq
  refine ⟨V, v, q.hom, hqy, ?_⟩
  obtain ⟨hprop, hH0, hdim, hnodal⟩ := fibre_standing_of_isPrestableCurveFamily hF hqy
  have := hprop
  have := hH0
  have hglob : Function.Bijective ((𝒯).map v).appTop := by
    have : IsIso ((𝒯).map v).appTop :=
      IsIso.of_isIso_comp_left (Scheme.ΓSpecIso (.of pF.carrier)).inv ((𝒯).map v).appTop
    exact (ConcreteCategory.isIso_iff_bijective _).1 inferInstance
  obtain ⟨pv, hpv⟩ : ∃ x : pF.siteObject ⟶ F.base, x = pF.value := ⟨_, rfl⟩
  have hqv : IsPullback q.hom (yoneda.map v) F.toBase.hom (yoneda.map pv) := by
    rwa [hpv, ← yonedaEquiv_symm_eq_yoneda_map]
  -- a point of `Spec K ×_S U` lying over `W`
  let t : pF.siteObject ⟶ G.base := pv ≫ a.baseMap
  obtain ⟨w, hw⟩ := exists_forall_range_snd_subset_of_mem_image t φ W
    (IsLocalRing.closedPoint pF.carrier)
    (by exact haW ⟨((𝒯).map pv).base (IsLocalRing.closedPoint pF.carrier), rfl⟩)
  let P := pullback t φ
  -- the field-valued point over the residue field `L` of `w`
  let pw := residueFieldValuedPoint B hZ P w
  obtain ⟨rP, hrP⟩ : ∃ r : pw.siteObject ⟶ P, r = pw.value := ⟨_, rfl⟩
  let m : pw.siteObject ⟶ pF.siteObject := rP ≫ pullback.fst t φ
  let b : pw.siteObject ⟶ U := rP ≫ pullback.snd t φ
  let F₁ := F.baseChangeAlong (m ≫ pv)
  let a₁ : F₁ ⟶ F := F.homOfIsPullback B hZ (m ≫ pv) _ _
    (AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ F.toBase
      (schemeSpaceMap (m ≫ pv)))
  have hb : b ≫ φ = (a₁ ≫ a).baseMap := by
    have hc : pullback.fst t φ ≫ t = pullback.snd t φ ≫ φ := pullback.condition
    have h₁ : rP ≫ (pullback.snd t φ ≫ φ) = rP ≫ (pullback.fst t φ ≫ t) := by rw [hc]
    exact (Category.assoc _ _ _).trans
      (h₁.trans ((Category.assoc _ _ _).symm.trans (Category.assoc _ _ _).symm))
  have hbW : Set.range ((𝒯).map b) ⊆ W := hw rP hrP
  -- the stable presentation of the fibre of `F₁` over its own `L`-point
  let pid : Space.FieldValuedPoint B integerBase hZ (schemeSpace F₁.base).obj :=
    ⟨pw.carrier, pw.contained, pw.toBase, 𝟙 pw.siteObject⟩
  obtain ⟨idv, hidv⟩ : ∃ i : pid.siteObject ⟶ pw.siteObject, i = pid.value := ⟨_, rfl⟩
  obtain ⟨V₁, v₁, q₁, hq₁, hcond₁⟩ := (hW F₁ (a₁ ≫ a) b hb hbW).2 pid
  obtain ⟨tb₁, htb₁⟩ : ∃ f : F₁.total.obj ⟶ yoneda.obj pw.siteObject, f = F₁.toBase.hom :=
    ⟨_, rfl⟩
  have hq₁c : IsPullback q₁ (yoneda.map v₁) tb₁ (yoneda.map idv) := by
    rwa [htb₁, hidv, ← yonedaEquiv_symm_eq_yoneda_map]
  have hsq₁ : IsPullback a₁.totalMap.hom tb₁ F.toBase.hom (yoneda.map (m ≫ pv)) := by
    rw [htb₁]
    exact AlgebraicSpaces.isPullback_hom B integerBase hZ a₁.cartesian
  obtain ⟨g₁, hsite⟩ := exists_isPullback_of_isPullback_yoneda hqv hq₁c hsq₁
    (Category.assoc idv m pv).symm
  exact (hasGenusTwoNoRationalTailNoRationalBridge_iff_of_isPullback (hsite.map (𝒯)) hdim hglob
    hnodal).2 hcond₁

/-- **A prestable family of curves is stable over an open neighbourhood of a point with stable
fibre, through an étale scheme chart** (Stacks 0E74 (1) ⟹ (2) and the openness of Stacks 0E76,
the step "after possibly shrinking `U`, `Y → U` is a stable family" of Stacks 0E8A). Let `G` be a
prestable family of curves and `G ×_S U ≅ Z` a scheme chart along an étale `φ : U ⟶ S`, with `U`
quasi-compact and quasi-separated. If the fibre of `Z ⟶ U` over `u`, presented by `C₀` over
`Spec κ(u)` with `H⁰(C₀, 𝒪) = κ(u)`, has genus at least two and neither a rational tail nor a
rational bridge, then there is an open neighbourhood `Ω` of `φ(u)` in `S` such that every family
of curves mapping to `G` over a morphism of bases with image in `Ω` is stable: `Ω` is the image of
the open of `AlgebraicGeometry.CurveFamily.exists_mem_forall_isStableCurveFamily_of_isPullback`,
open because `φ` is étale. -/
theorem exists_mem_forall_isStableCurveFamily_of_isPullback_of_etale
    {G : CurveFamily B hZ} (hG : IsPrestableCurveFamily B hZ G)
    {U Z : BigFppfOver B integerBase hZ} {φ : U ⟶ G.base} {p : schemeSpace Z ⟶ G.total}
    {q : Z ⟶ U} (sq : IsPullback p (schemeSpaceMap q) G.toBase (schemeSpaceMap φ))
    (hφ : Etale ((𝒯).map φ))
    [CompactSpace ((𝒯).obj U)] [QuasiSeparatedSpace ((𝒯).obj U)] (u : (𝒯).obj U)
    (hu : ∃ (C₀ : Scheme.{u}) (h₀ : C₀ ⟶ (𝒯).obj Z)
      (g₀ : C₀ ⟶ Spec (.of (((𝒯).obj U).residueField u))),
      IsPullback h₀ g₀ ((𝒯).map q) (((𝒯).obj U).fromSpecResidueField u) ∧
        Function.Bijective g₀.appTop ∧
        HasGenusTwoNoRationalTailNoRationalBridge (((𝒯).obj U).residueField u) g₀) :
    ∃ Ω : ((𝒯).obj G.base).Opens, ((𝒯).map φ).base u ∈ Ω ∧
      ∀ (F : CurveFamily B hZ) (a : F ⟶ G), Set.range ((𝒯).map a.baseMap) ⊆ Ω →
        IsStableCurveFamily B hZ F := by
  obtain ⟨W, huW, hW⟩ := exists_mem_forall_isStableCurveFamily_of_isPullback hG sq u hu
  have := hφ
  exact ⟨⟨((𝒯).map φ).base '' W, ((𝒯).map φ).isOpenMap _ W.isOpen⟩, ⟨u, huW, rfl⟩,
    fun F a ha => isStableCurveFamily_of_range_subset_image_of_etale hG φ W hW a ha⟩

end CurveFamily

end AlgebraicGeometry

end
