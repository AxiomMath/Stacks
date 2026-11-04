module

public import StacksFrontier.AlgebraicGeometry.Quot.StableReduction.SmoothStableContraction
public import StacksFrontier.AlgebraicGeometry.Quot.StableReduction.PrestableMinimalModel

/-!
# The stabilization does not change a smooth fibre of genus at least two

Let `X` be a family of curves and `c : X ⟶ Y` a morphism to a stable family of curves over the
same base, lying over it, whose fibres over field-valued points are contractions to a stable
curve in the sense of [Stacks, Tag 0E7Q] (condition (2) of [Stacks, Tag 0E8A]). If a smooth proper
curve `C` of genus at least two with `H⁰ = k` is a fibre of `X` over a point `Spec k ⟶ S`, then
`C` is also the fibre of `Y` over that point.

## Main results

* `AlgebraicGeometry.BigFppfOver.isIso_of_isIso_toScheme_map`: a morphism of schemes of the site
  over the integers is an isomorphism when its underlying morphism of schemes is.
* `AlgebraicGeometry.CurveFamily.exists_hom_of_stableContractionFibres`: the fibre of `Y` over a
  point where the fibre of `X` is a smooth curve `C` of genus at least two is `C`.

## References

* [Stacks Project, Tag 0E8A](https://stacks.math.columbia.edu/tag/0E8A)
* [Stacks Project, Tag 0E8D](https://stacks.math.columbia.edu/tag/0E8D)
* [Stacks Project, Tag 0E7Q](https://stacks.math.columbia.edu/tag/0E7Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

local notation "𝒯" => BigFppfOver.toScheme B integerBase hZ

/-- A morphism of schemes of the site over the integers lifts to a morphism of the site. -/
def BigFppfOver.liftOfIntegers {V W : BigFppfOver B integerBase hZ} (g : (𝒯).obj V ⟶ (𝒯).obj W) :
    V ⟶ W :=
  Over.homMk (ObjectProperty.homMk g) (by
    apply B.inclusion.map_injective
    exact specULiftZIsTerminal.hom_ext _ _)

/-- The underlying morphism of schemes of `BigFppfOver.liftOfIntegers g` is `g`. -/
theorem BigFppfOver.toScheme_map_liftOfIntegers {V W : BigFppfOver B integerBase hZ}
    (g : (𝒯).obj V ⟶ (𝒯).obj W) : (𝒯).map (BigFppfOver.liftOfIntegers g) = g := rfl

/-- A morphism of schemes of the site over the integers is an isomorphism when its underlying
morphism of schemes is. -/
theorem BigFppfOver.isIso_of_isIso_toScheme_map {V W : BigFppfOver B integerBase hZ}
    (a : V ⟶ W) [IsIso ((𝒯).map a)] : IsIso a := by
  refine ⟨BigFppfOver.liftOfIntegers (inv ((𝒯).map a)), ?_, ?_⟩ <;>
    apply (𝒯).map_injective <;>
    rw [Functor.map_comp, BigFppfOver.toScheme_map_liftOfIntegers,
      CategoryTheory.Functor.map_id] <;> simp

namespace CurveFamily

/-- **The stabilization does not change a smooth fibre of genus at least two.** Let `c : X ⟶ Y`
be a morphism from a family of curves to a stable family of curves over the same base, lying over
it, whose fibres over the field-valued points of the base are contractions to stable curves
(Stacks 0E7Q; condition (2) of Stacks 0E8A). If a smooth proper curve `C` over a field `k` with
`H⁰ = k` and genus at least two is the fibre of `X` over `Spec k ⟶ S`, given by a morphism of
families of curves `φ`, then `C` is the fibre of `Y` over the same point. -/
theorem exists_hom_of_stableContractionFibres {k : Type u} [Field k]
    (hk : B.Contains (Spec (.of k))) {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsProper f]
    [Smooth f] [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)]
    (hdim : topologicalKrullDim C = 1) (hg : 2 ≤ genus f)
    {X Y : CurveFamily B hZ} (hb : Y.base = X.base) (c : X.total ⟶ Y.total)
    (hc : c ≫ Y.toBase ≫ eqToHom (congrArg schemeSpace hb) = X.toBase)
    (hY : IsStableCurveFamily B hZ Y)
    (h2 : ∀ (p : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj)
      (VX VY : BigFppfOver B integerBase hZ) (vX : VX ⟶ p.siteObject) (vY : VY ⟶ p.siteObject)
      (qX : yoneda.obj VX ⟶ X.total.obj) (qY : yoneda.obj VY ⟶ Y.total.obj) (a : VX ⟶ VY),
      IsPullback qX (yoneda.map vX) X.toBase.hom (yonedaEquiv.symm p.value) →
      IsPullback qY (yoneda.map vY) (Y.toBase ≫ eqToHom (congrArg schemeSpace hb)).hom
        (yonedaEquiv.symm p.value) →
      a ≫ vY = vX → qX ≫ c.hom = yoneda.map a ≫ qY →
      Stacks.Curves.StableModel.IsStableContraction ((𝒯).map vX) ((𝒯).map vY) ((𝒯).map a))
    (φ : @curveFamilyOfScheme k _ (Over.mk f) ‹IsProper f› B hZ hk hdim.le ⟶ X) :
    ∃ φ' : @curveFamilyOfScheme k _ (Over.mk f) ‹IsProper f› B hZ hk hdim.le ⟶ Y,
      φ'.baseMap = φ.baseMap ≫ eqToHom hb.symm := by
  obtain ⟨Ybase, Ytotal, YtoBase, Yflat, Yproper, Yfp, Yrel⟩ := Y
  change Ybase = X.base at hb
  subst hb
  simp only [eqToHom_refl, Category.comp_id] at hc h2 ⊢
  have hC : B.Contains C := Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact f hk
  let p : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj :=
    { carrier := k
      contained := hk
      toBase := specULiftZIsTerminal.from _
      value := φ.baseMap }
  let vX : integerSiteObject B hZ hC ⟶ p.siteObject := integerSiteMap B hZ hC hk f
  let pv : p.siteObject ⟶ X.base := @id (p.siteObject ⟶ X.base) p.value
  let ypv : yoneda.obj p.siteObject ⟶ (schemeSpace X.base).obj :=
    @id (yoneda.obj p.siteObject ⟶ (schemeSpace X.base).obj) (yoneda.map pv)
  let qX : yoneda.obj (integerSiteObject B hZ hC) ⟶ X.total.obj :=
    @id (yoneda.obj (integerSiteObject B hZ hC) ⟶ X.total.obj) φ.totalMap.hom
  have hval : yonedaEquiv.symm p.value = ypv :=
    yonedaEquiv.symm_apply_eq.mpr (yonedaEquiv_yoneda_map _).symm
  have hqX : IsPullback qX (yoneda.map vX) X.toBase.hom ypv :=
    AlgebraicSpaces.isPullback_hom B integerBase hZ φ.cartesian
  obtain ⟨VY, vY, qY, hqY, -⟩ := hY.2 p
  rw [hval] at hqY
  have hqY' : IsPullback qY (yoneda.map vY) YtoBase.hom ypv := hqY
  have hw : (qX ≫ c.hom) ≫ YtoBase.hom = yoneda.map vX ≫ ypv := by
    rw [Category.assoc, ← hqX.w]
    exact congrArg (fun t => qX ≫ t.hom) hc
  obtain ⟨l, hl₁, hl₂⟩ : ∃ l, l ≫ qY = qX ≫ c.hom ∧ l ≫ yoneda.map vY = yoneda.map vX :=
    ⟨_, hqY'.lift_fst _ _ hw, hqY'.lift_snd _ _ hw⟩
  obtain ⟨a, ha⟩ : ∃ a, yoneda.map a = l := ⟨_, Yoneda.fullyFaithful.map_preimage l⟩
  have hav : a ≫ vY = vX := Yoneda.fullyFaithful.map_injective (by
    rw [Functor.map_comp, ha, hl₂])
  have haq : qX ≫ c.hom = yoneda.map a ≫ qY := by rw [ha, hl₁]
  have hst := h2 p _ VY vX vY qX qY a (by rw [hval]; exact hqX) (by rw [hval]; exact hqY')
    hav haq
  have : IsIso ((𝒯).map a) :=
    Stacks.Curves.StableModel.isIso_of_isStableContraction_of_smooth f hdim hg hst
  have : IsIso a := BigFppfOver.isIso_of_isIso_toScheme_map a
  have h₁ : IsPullback (yoneda.map a) (yoneda.map vX) (yoneda.map vY) (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [← Functor.map_comp, hav, Category.comp_id]⟩
  have hbig := h₁.paste_horiz hqY'
  rw [Category.id_comp] at hbig
  exact ⟨{ baseMap := φ.baseMap
           totalMap := ObjectProperty.homMk (yoneda.map a ≫ qY)
           cartesian := IsPullback.of_map (ObjectProperty.ι _)
             (ObjectProperty.hom_ext _ hbig.w) hbig }, rfl⟩

end CurveFamily

end AlgebraicGeometry

end
