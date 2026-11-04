module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurveFamilyContractionUniqueness
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.PrestableFibre
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.StableContractionTarget
public import StacksFrontier.AlgebraicGeometry.Curves.StableContraction.StableModelCharacterization

/-!
# Two stable models of a prestable family contract its fibres alike

Let `c₁ : X ⟶ Y₁` and `c₂ : X ⟶ Y₂` be two stable models of genus `g ≥ 2` (Stacks 0E8A) of a
prestable family of curves `X`. At every field-valued point the two morphisms of fibres are stable
contractions of the same curve, hence isomorphic under it by the uniqueness in Stacks 0E7Q. This
is the hypothesis of Stacks 0E89,
`AlgebraicGeometry.C1590Private.FibresContractedAlike`, at every point of the base.

## Main results

* `AlgebraicGeometry.C1590Private.IsStableModel.isStableContraction_of_presentation`: the morphism
  of fibres of a stable model, at any presentation of the fibres, is a stable contraction.
* `AlgebraicGeometry.C1590Private.fibresContractedAlike_of_isStableModel`.

## References

* [Stacks Project, Tag 0E8A](https://stacks.math.columbia.edu/tag/0E8A)
* [Stacks Project, Tag 0E89](https://stacks.math.columbia.edu/tag/0E89)
* [Stacks Project, Tag 0E7Q](https://stacks.math.columbia.edu/tag/0E7Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.C1590Private

universe u

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- **The fibres of a stable model are stable contractions.** Let `c : X ⟶ Y` be a stable model
over `b`. At a field-valued point `P` of the base of `X`, for presentations `V` of the fibre of
`X` and `W` of the fibre of `Y` over the image of `P`, the induced morphism `V ⟶ W` satisfies the
conditions of Stacks 0E7Q. -/
theorem IsStableModel.isStableContraction_of_presentation {g : ℕ} {X Y : CurveFamily B hZ}
    {b : X.base ⟶ Y.base} {c : X.total ⟶ Y.total} (h : IsStableModel B hZ g b c)
    (P : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj)
    {V W : BigFppfOver B integerBase hZ} (v : V ⟶ P.siteObject) (w : W ⟶ P.siteObject)
    (q : yoneda.obj V ⟶ X.total.obj) (r : yoneda.obj W ⟶ Y.total.obj) (m : V ⟶ W)
    (hq : IsPullback q (yoneda.map v) X.toBase.hom (yonedaEquiv.symm P.value))
    (hr : IsPullback r (yoneda.map w) Y.toBase.hom (yonedaEquiv.symm (P.value ≫ b)))
    (hmw : m ≫ w = v) (hmr : yoneda.map m ≫ r = q ≫ c.hom) :
    Stacks.Curves.StableModel.IsStableContraction
      ((BigFppfOver.toScheme B integerBase hZ).map v)
      ((BigFppfOver.toScheme B integerBase hZ).map w)
      ((BigFppfOver.toScheme B integerBase hZ).map m) := by
  have := h.isIso_base
  let P' := Space.FieldValuedPoint.map B integerBase hZ _ (schemeSpaceMap b).hom P
  let pv : P.siteObject ⟶ X.base := P.value
  have hq0 : IsPullback q (yoneda.map v) X.toBase.hom (yoneda.map pv) := by
    rwa [yonedaEquiv_symm_value] at hq
  have h₁ : IsPullback (yoneda.map pv) (𝟙 _) (yoneda.map b) (yoneda.map (pv ≫ b)) :=
    IsPullback.of_vert_isIso ⟨by rw [Category.id_comp, Functor.map_comp]⟩
  have h₂ := hq0.paste_vert h₁
  rw [Category.comp_id] at h₂
  have hq' : IsPullback q (yoneda.map v) (c ≫ Y.toBase).hom (yonedaEquiv.symm P'.value) := by
    rwa [h.comp_toBase]
  exact (h.fibrewiseStable P').2 v w q r m hq' hr hmw hmr

/-- **Two stable models of a prestable family contract its fibres alike** (the hypothesis of
Stacks 0E89 at every point). At a field-valued point, the two morphisms of fibres are stable
contractions of the fibre of `X`, a proper nodal curve of dimension one with `H⁰ = K`
(`AlgebraicGeometry.C1590Private.fibre_properties_of_isPrestableCurveFamily`) and of genus
`g ≥ 2`, so they differ by an isomorphism of targets under it (Stacks 0E7Q), which lies over the
point because a stable contraction is an epimorphism onto separated targets. -/
theorem fibresContractedAlike_of_isStableModel {g : ℕ} {X Y₁ Y₂ : CurveFamily B hZ}
    (hX : IsPrestableCurveFamily B hZ X) (hg : 2 ≤ g) {b₁ : X.base ⟶ Y₁.base}
    {c₁ : X.total ⟶ Y₁.total} {b₂ : X.base ⟶ Y₂.base} {c₂ : X.total ⟶ Y₂.total}
    (h₁ : IsStableModel B hZ g b₁ c₁) (h₂ : IsStableModel B hZ g b₂ c₂)
    (s : (BigFppfOver.toScheme B integerBase hZ).obj X.base) :
    FibresContractedAlike b₁ b₂ c₁ c₂ s := by
  intro P _ V W₁ W₂ v w₁ w₂ q r₁ r₂ m₁ m₂ hq hr₁ hr₂ hm₁w hm₁r hm₂w hm₂r
  let T := BigFppfOver.toScheme B integerBase hZ
  have hc₁ := h₁.isStableContraction_of_presentation P v w₁ q r₁ m₁ hq hr₁ hm₁w hm₁r
  have hc₂ := h₂.isStableContraction_of_presentation P v w₂ q r₂ m₂ hq hr₂ hm₂w hm₂r
  obtain ⟨hprop, hdim, hH0, hnodal⟩ := fibre_properties_of_isPrestableCurveFamily hX P v q hq
  have := hprop
  have := hH0
  have hgW : genus (T.map w₁) = g :=
    (h₁.hasFibresOfGenus (Space.FieldValuedPoint.map B integerBase hZ _
      (schemeSpaceMap b₁).hom P)).genus_eq w₁ r₁ hr₁
  have hgV : 2 ≤ genus (T.map v) := by
    rwa [← IsStableContraction.genus_eq hc₁ hdim, hgW]
  obtain ⟨-, huniq⟩ :=
    Stacks.Curves.StableModel.existsUnique_isStableContraction (T.map v) hdim hgV hnodal
  obtain ⟨e, he, -⟩ := huniq _ _ _ _ _ _ hc₁ hc₂
  let ε : W₁ ≅ W₂ :=
    { hom := homOfToScheme e.hom
      inv := homOfToScheme e.inv
      hom_inv_id := hom_ext_of_toScheme (by
        rw [Functor.map_comp, CategoryTheory.Functor.map_id]; exact e.hom_inv_id)
      inv_hom_id := hom_ext_of_toScheme (by
        rw [Functor.map_comp, CategoryTheory.Functor.map_id]; exact e.inv_hom_id) }
  refine ⟨⟨ε, T.map_injective ?_, T.map_injective ?_⟩, hdim.le,
    hc₁.isIso_unitToPushforwardObjUnit, hc₁.isZero_rightDerived_one⟩
  · rw [Functor.map_comp, toScheme_map_homOfToScheme]
    refine hc₁.ext (gY' := 𝟙 (Spec (.of P.carrier))) ?_
    rw [← Category.assoc, he, ← Functor.map_comp, hm₂w, ← Functor.map_comp, hm₁w]
  · rwa [Functor.map_comp, toScheme_map_homOfToScheme]

end AlgebraicGeometry.C1590Private

end
