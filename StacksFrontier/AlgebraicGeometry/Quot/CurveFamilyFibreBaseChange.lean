module

public import StacksFrontier.AlgebraicGeometry.Quot.ContractionEtaleData

/-!
# Fibres of families of curves over points with values in fields

For a family of curves `F` over a scheme `S` of the site and a point `c : Spec K ⟶ S` with values
in a field, the fibre of `F` over `c` is a proper scheme over `K`
(`AlgebraicGeometry.CurveFamily.exists_fibre`, from Stacks 0ADD in the form
`AlgebraicGeometry.CurveFamily.exists_iso_curveFamilyOfScheme_of_base_eq`). Fibres are unique up
to a unique isomorphism over `K` (`AlgebraicGeometry.CurveFamily.fibreIso`), and the base change
of a fibre along an extension of fields is the fibre of the base change
(`AlgebraicGeometry.CurveFamily.exists_fibre_baseChange`).

## Main results

* `AlgebraicGeometry.CurveFamily.exists_fibre`.
* `AlgebraicGeometry.CurveFamily.fibreIso`.
* `AlgebraicGeometry.CurveFamily.exists_fibre_baseChange`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace CurveFamily

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- A cartesian square of schemes of the site is a cartesian square of representable
presheaves. -/
theorem isPullback_yoneda_integerSiteMap {P Q R W : Scheme.{u}} {hP : B.Contains P}
    {hQ : B.Contains Q} {hR : B.Contains R} {hW : B.Contains W} {a : P ⟶ Q} {b : P ⟶ R}
    {c : Q ⟶ W} {d : R ⟶ W} (h : IsPullback a b c d) :
    IsPullback (yoneda.map (integerSiteMap B hZ hP hQ a)) (yoneda.map (integerSiteMap B hZ hP hR b))
      (yoneda.map (integerSiteMap B hZ hQ hW c)) (yoneda.map (integerSiteMap B hZ hR hW d)) :=
  AlgebraicSpaces.isPullback_hom B integerBase hZ (isPullback_schemeSpaceMap_integerSiteMap h)

/-- **The fibre of a family of curves over a point with values in a field is a proper scheme.** -/
theorem exists_fibre {V : BigFppfOver B integerBase hZ} (F : CurveFamily B hZ)
    (hF : F.base = V) {K : Type u} [Field K]
    (hK : B.Contains (Spec (.of K))) (c : integerSiteObject B hZ hK ⟶ V) :
    ∃ (X : Over (Spec (.of K))) (_ : IsProper X.hom) (hX : B.Contains X.left)
      (ι : yoneda.obj (integerSiteObject B hZ hX) ⟶ F.total.obj),
      topologicalKrullDim X.left ≤ 1 ∧
      IsPullback ι (yoneda.map (integerSiteMap B hZ hX hK X.hom)) (F.toBaseYonedaOfEq hF)
        (yoneda.map c) := by
  let Fc := (F.ofBaseEq hF).pullback c
  have sq := F.isPullback_pullbackHom_yoneda hF c
  obtain ⟨X, hXp, hdim, ⟨φ⟩⟩ := exists_iso_curveFamilyOfScheme_of_base_eq hK Fc rfl
  have := hXp
  have hX : B.Contains X.left := Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact X.hom hK
  let βi : integerSiteObject B hZ hK ≅ integerSiteObject B hZ hK :=
    { hom := φ.inv.baseMap
      inv := φ.hom.baseMap
      hom_inv_id := (comp_baseMap φ.inv φ.hom).symm.trans
        ((congrArg Hom.baseMap φ.inv_hom_id).trans (id_baseMap _))
      inv_hom_id := (comp_baseMap φ.hom φ.inv).symm.trans
        ((congrArg Hom.baseMap φ.hom_inv_id).trans (id_baseMap _)) }
  have hcart : IsPullback φ.inv.totalMap.hom (curveFamilyOfScheme X B hZ hK hdim).toBaseYoneda
      Fc.toBaseYoneda (yoneda.map βi.hom) :=
    AlgebraicSpaces.isPullback_hom B integerBase hZ φ.inv.cartesian
  let βs := (BigFppfOver.toScheme B integerBase hZ).mapIso βi
  let β : Spec (.of K) ⟶ Spec (.of K) := βs.hom
  have hβ : IsIso β := Iso.isIso_hom βs
  have hiso : ∀ {P X Y Y' Z : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u} {fst : P ⟶ X}
      {snd : P ⟶ Y'} {f : X ⟶ Z} {g : Y' ⟶ Z}, IsPullback fst snd f g → ∀ e : Y ≅ Y',
        IsPullback fst (snd ≫ e.inv) f (e.hom ≫ g) := fun h e =>
    h.of_iso (Iso.refl _) (Iso.refl _) e.symm (Iso.refl _) (by simp) (by simp) (by simp)
      (by simp)
  let X' : Over (Spec (.of K)) := Over.mk (X.hom ≫ β)
  have e_snd : (curveFamilyOfScheme X B hZ hK hdim).toBaseYoneda ≫ yoneda.map βi.hom =
      yoneda.map (integerSiteMap B hZ hX hK X'.hom) := by
    refine (yoneda.map_comp _ _).symm.trans (congrArg yoneda.map ?_)
    change integerSiteMap B hZ hX hK X.hom ≫ βi.hom = integerSiteMap B hZ hX hK (X.hom ≫ β)
    rw [← integerSiteMap_comp]
    exact congrArg _ (integerSiteMap_toScheme_map βi.hom).symm
  have e_bot : (yoneda.mapIso βi).symm.hom ≫ yoneda.map βi.hom ≫
      yoneda.map c = yoneda.map c := by
    simp
  refine ⟨X', inferInstanceAs (IsProper (X.hom ≫ β)), hX, φ.inv.totalMap.hom ≫
    ((F.ofBaseEq hF).pullbackHom c).totalMap.hom, hdim, ?_⟩
  rw [← e_snd, ← e_bot]
  exact hiso (hcart.paste_horiz sq) (yoneda.mapIso βi).symm

/-- **Fibres are unique up to isomorphism over the field.** -/
theorem fibreIso {K : Type u} [Field K] {hK : B.Contains (Spec (.of K))}
    {P Q : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u} (t : P ⟶ Q)
    {c : yoneda.obj (integerSiteObject B hZ hK) ⟶ Q} {X X' : Scheme.{u}}
    {hX : B.Contains X} {hX' : B.Contains X'} {pX : X ⟶ Spec (.of K)} {pX' : X' ⟶ Spec (.of K)}
    {ι : yoneda.obj (integerSiteObject B hZ hX) ⟶ P}
    {ι' : yoneda.obj (integerSiteObject B hZ hX') ⟶ P}
    (h : IsPullback ι (yoneda.map (integerSiteMap B hZ hX hK pX)) t c)
    (h' : IsPullback ι' (yoneda.map (integerSiteMap B hZ hX' hK pX')) t c) :
    ∃ e : X ≅ X', e.hom ≫ pX' = pX ∧
      yoneda.map (integerSiteMap B hZ hX hX' e.hom) ≫ ι' = ι := by
  let i := h.isoIsPullback _ _ h'
  let i' := Yoneda.fullyFaithful.preimageIso i
  let e := (BigFppfOver.toScheme B integerBase hZ).mapIso i'
  have hi : yoneda.map i'.hom = i.hom := Yoneda.fullyFaithful.map_preimage _
  have he : integerSiteMap B hZ hX hX' e.hom = i'.hom := integerSiteMap_toScheme_map i'.hom
  refine ⟨e, ?_, ?_⟩
  · have h2 := h.isoIsPullback_hom_snd _ _ h'
    rw [← hi] at h2
    have h3 := congrArg (fun f => (BigFppfOver.toScheme B integerBase hZ).map
      (Yoneda.fullyFaithful.preimage f)) h2
    simp only [Functor.FullyFaithful.preimage_map] at h3
    simp only [← Functor.map_comp, Functor.FullyFaithful.preimage_map] at h3
    exact h3
  · rw [he, hi]
    exact h.isoIsPullback_hom_fst _ _ h'

/-- **The base change of a fibre is the fibre of the base change.** Let `F'` over `S'` be a base
change of `F` over `S` along `w` (the cartesian square `e`), `X` the fibre of `F` over a point
`c : Spec K ⟶ S`, and `k : Spec K' ⟶ Spec K` lie under a point `c'` of `S'` over `c`. Then
`X ×_K K'` is the fibre of `F'` over `c'`. -/
theorem exists_fibre_baseChange {P P' : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u}
    {V V' : BigFppfOver B integerBase hZ} {e : P' ⟶ P} {t' : P' ⟶ yoneda.obj V'}
    {t : P ⟶ yoneda.obj V} {w : V' ⟶ V} (sq : IsPullback e t' t (yoneda.map w))
    {K K' : Type u} [Field K] [Field K'] {hK : B.Contains (Spec (.of K))}
    {hK' : B.Contains (Spec (.of K'))} {c : integerSiteObject B hZ hK ⟶ V}
    {c' : integerSiteObject B hZ hK' ⟶ V'} (k : Spec (.of K') ⟶ Spec (.of K))
    (hc : c' ≫ w = integerSiteMap B hZ hK' hK k ≫ c) {X : Scheme.{u}}
    {hX : B.Contains X} {pX : X ⟶ Spec (.of K)} {ι : yoneda.obj (integerSiteObject B hZ hX) ⟶ P}
    (h : IsPullback ι (yoneda.map (integerSiteMap B hZ hX hK pX)) t (yoneda.map c))
    {X' : Scheme.{u}} (hX' : B.Contains X') {fst' : X' ⟶ X} {snd' : X' ⟶ Spec (.of K')}
    (hsq : IsPullback fst' snd' pX k) :
    ∃ ι' : yoneda.obj (integerSiteObject B hZ hX') ⟶ P',
      ι' ≫ e = yoneda.map (integerSiteMap B hZ hX' hX fst') ≫ ι ∧
      IsPullback ι' (yoneda.map (integerSiteMap B hZ hX' hK' snd')) t'
        (yoneda.map c') := by
  have h1 := (isPullback_yoneda_integerSiteMap (hP := hX') (hQ := hX) (hR := hK') (hW := hK)
    hsq).paste_horiz h
  have e1 : yoneda.map (integerSiteMap B hZ hK' hK k) ≫ yoneda.map c =
      yoneda.map c' ≫ yoneda.map w := by
    rw [← yoneda.map_comp, ← yoneda.map_comp, hc]
  rw [e1] at h1
  exact ⟨_, sq.lift_fst _ _ _, h1.of_right' sq⟩

end CurveFamily

end AlgebraicGeometry

end
