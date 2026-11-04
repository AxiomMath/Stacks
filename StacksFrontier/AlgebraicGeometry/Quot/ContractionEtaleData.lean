module

public import StacksFrontier.AlgebraicGeometry.Quot.ContractionExistenceEtale

/-!
# The conclusion of Stacks 0E7C, as a predicate

Let `F` be a family of curves over a scheme `S` of the site, `s : Spec K ⟶ S` a point of `S` with
values in a field `K`, `X₀` the fibre of `F` over `s` (through the cartesian square `ι`), and
`h₀ : X₀ ⟶ Y₀` a morphism over `K`. The conclusion of Stacks 0E7C for these data is recorded here
as `AlgebraicGeometry.CurveFamily.HasEtaleContraction`: there are an étale morphism `e : U ⟶ S`,
a lift `t : Spec K ⟶ U` of `s`, a family of curves `G` over `U` and a morphism `h` from the base
change `F_U` of `F` to `G` over `U`, such that `X₀` and `Y₀` are the fibres of `F_U` and `G` over
`t` and `h` restricts to `h₀` on them.

This file proves it over an affine Noetherian base whose local ring at the point is a G-ring, from
`AlgebraicGeometry.CurveFamily.exists_contraction_of_isGRing_localization`.

## Main definitions

* `AlgebraicGeometry.CurveFamily.HasEtaleContraction`.

## Main results

* `AlgebraicGeometry.CurveFamily.hasEtaleContraction_of_isGRing_localization`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace AlgebraicGeometry

namespace CurveFamily

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- **The conclusion of Stacks 0E7C.** For a family of curves `F` over `S`, a point
`s : Spec K ⟶ S`, the fibre `X₀` of `F` over `s` (with `ι` its map to the total space of `F`) and
a morphism `h₀ : X₀ ⟶ Y₀` over `K`: there are an étale `e : U ⟶ S`, a lift `t : Spec K ⟶ U` of
`s`, a family of curves `G` over `U` and a morphism `h` over `U` from the total space of the base
change `F_U` of `F` to that of `G`, with `X₀` and `Y₀` the fibres of `F_U` and of `G` over `t`
(the first compatibly with `ι`) and `h` restricting to `h₀`. -/
def HasEtaleContraction {S : Scheme.{u}} (hS : B.Contains S) (F : CurveFamily B hZ)
    (hF : F.base = integerSiteObject B hZ hS) {K : Type u} [Field K]
    (hK : B.Contains (Spec (.of K))) (s : Spec (.of K) ⟶ S) {X₀ : Scheme.{u}}
    (hX₀ : B.Contains X₀) (pX₀ : X₀ ⟶ Spec (.of K))
    (ι : yoneda.obj (integerSiteObject B hZ hX₀) ⟶ F.total.obj) {Y₀ : Scheme.{u}}
    (hY₀ : B.Contains Y₀) (pY₀ : Y₀ ⟶ Spec (.of K)) (h₀ : X₀ ⟶ Y₀) : Prop :=
  ∃ (U : Scheme.{u}) (hU : B.Contains U) (e : U ⟶ S) (_ : Etale e) (t : Spec (.of K) ⟶ U),
    t ≫ e = s ∧
    ∃ (G : CurveFamily B hZ) (hG : G.base = integerSiteObject B hZ hU)
      (h : ((F.ofBaseEq hF).pullback (integerSiteMap B hZ hU hS e)).total.obj ⟶ G.total.obj),
      h ≫ G.toBaseYonedaOfEq hG =
        ((F.ofBaseEq hF).pullback (integerSiteMap B hZ hU hS e)).toBaseYoneda ∧
      ∃ ιU : yoneda.obj (integerSiteObject B hZ hX₀) ⟶
          ((F.ofBaseEq hF).pullback (integerSiteMap B hZ hU hS e)).total.obj,
        ιU ≫ ((F.ofBaseEq hF).pullbackHom (integerSiteMap B hZ hU hS e)).totalMap.hom = ι ∧
        IsPullback ιU (yoneda.map (integerSiteMap B hZ hX₀ hK pX₀))
          ((F.ofBaseEq hF).pullback (integerSiteMap B hZ hU hS e)).toBaseYoneda
          (yoneda.map (integerSiteMap B hZ hK hU t)) ∧
        ∃ j : yoneda.obj (integerSiteObject B hZ hY₀) ⟶ G.total.obj,
          IsPullback j (yoneda.map (integerSiteMap B hZ hY₀ hK pY₀)) (G.toBaseYonedaOfEq hG)
            (yoneda.map (integerSiteMap B hZ hK hU t)) ∧
          ιU ≫ h = yoneda.map (integerSiteMap B hZ hX₀ hY₀ h₀) ≫ j

/-- **Stacks 0E7C over an affine Noetherian base whose local ring at the point is a G-ring**, in
the form `AlgebraicGeometry.CurveFamily.HasEtaleContraction`. -/
theorem hasEtaleContraction_of_isGRing_localization
    {R : Type u} [CommRing R] [IsNoetherianRing R] (p : Ideal R) [p.IsPrime]
    (hGR : IsGRing (Localization.AtPrime p))
    (hR : B.Contains (Spec (.of R))) (hκ : B.Contains (Spec (.of p.ResidueField)))
    (F : CurveFamily B hZ) (hF : F.base = integerSiteObject B hZ hR)
    {X₀ : Scheme.{u}} (hX₀ : B.Contains X₀) (pX₀ : X₀ ⟶ Spec (.of p.ResidueField))
    (ι : yoneda.obj (integerSiteObject B hZ hX₀) ⟶ F.total.obj)
    (hι : IsPullback ι (yoneda.map (integerSiteMap B hZ hX₀ hκ pX₀)) (F.toBaseYonedaOfEq hF)
      (yoneda.map (integerSiteMap B hZ hκ hR
        (Spec.map (CommRingCat.ofHom (algebraMap R p.ResidueField))))))
    {Y₀ : Scheme.{u}} (hY₀ : B.Contains Y₀) (pY₀ : Y₀ ⟶ Spec (.of p.ResidueField))
    [IsProper pY₀] (h₀ : X₀ ⟶ Y₀) (hh₀ : h₀ ≫ pY₀ = pX₀)
    (h0 : IsIso (C := Y₀.Modules) (Scheme.Modules.unitToPushforwardUnit h₀))
    (hR1 : IsZero (((Scheme.Modules.pushforward h₀).rightDerived 1).obj
      (SheafOfModules.unit X₀.ringCatSheaf))) :
    HasEtaleContraction hR F hF hκ (Spec.map (CommRingCat.ofHom (algebraMap R p.ResidueField)))
      hX₀ pX₀ ι hY₀ pY₀ h₀ := by
  obtain ⟨D, _, _, _, pD, _, hpD, -, hD, θ, ht, G, hG, h, hh, ιD, hιDe, hιD, j, hj, hιj⟩ :=
    exists_contraction_of_isGRing_localization p hGR hR hκ F hF hX₀ pX₀ ι hι hY₀ pY₀ h₀ hh₀
      h0 hR1
  have : Etale (Spec.map (CommRingCat.ofHom (algebraMap R D))) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr (RingHom.etale_algebraMap.mpr inferInstance)
  exact ⟨Spec (.of D), hD, Spec.map (CommRingCat.ofHom (algebraMap R D)), inferInstance,
    Spec.map (CommRingCat.ofHom θ) ≫ Spec.map (CommRingCat.ofHom (algebraMap D pD.ResidueField)),
    ht, G, hG, h, hh, ιD, hιDe, hιD, j, hj, hιj⟩

/-- **Base change of the conclusion of Stacks 0E7C.** Let `F` over `S` be a base change of `F₀`
over `S₀` along `a : S ⟶ S₀` (through `φ`, compatible with the structure maps), let
`k : Spec K ⟶ Spec K₀` cover `a` on the points, and let `X₀ ⟶ X₁`, `Y₀ ⟶ Y₁` be compatible with
`ι`, `ι₁`, `h₀`, `h₁`, the second exhibiting `Y₀` as the base change of `Y₁` along `k`. If the
conclusion of Stacks 0E7C holds for `F₀`, `X₁`, `h₁`, then it holds for `F`, `X₀`, `h₀`: base
change the étale neighbourhood, the family and the morphism along `a`. -/
theorem HasEtaleContraction.baseChange {S₀ S : Scheme.{u}} {hS₀ : B.Contains S₀}
    {hS : B.Contains S} (a : S ⟶ S₀) {F₀ F : CurveFamily B hZ}
    {hF₀ : F₀.base = integerSiteObject B hZ hS₀} {hF : F.base = integerSiteObject B hZ hS}
    (φ : F.total.obj ⟶ F₀.total.obj)
    (hφ : φ ≫ F₀.toBaseYonedaOfEq hF₀ =
      F.toBaseYonedaOfEq hF ≫ yoneda.map (integerSiteMap B hZ hS hS₀ a))
    {K₀ K : Type u} [Field K₀] [Field K] {hK₀ : B.Contains (Spec (.of K₀))}
    {hK : B.Contains (Spec (.of K))} {s₀ : Spec (.of K₀) ⟶ S₀} {s : Spec (.of K) ⟶ S}
    (k : Spec (.of K) ⟶ Spec (.of K₀)) (hk : s ≫ a = k ≫ s₀)
    {X₁ : Scheme.{u}} {hX₁ : B.Contains X₁} {pX₁ : X₁ ⟶ Spec (.of K₀)}
    {ι₁ : yoneda.obj (integerSiteObject B hZ hX₁) ⟶ F₀.total.obj} {Y₁ : Scheme.{u}}
    {hY₁ : B.Contains Y₁} {pY₁ : Y₁ ⟶ Spec (.of K₀)} {h₁ : X₁ ⟶ Y₁}
    (H : HasEtaleContraction hS₀ F₀ hF₀ hK₀ s₀ hX₁ pX₁ ι₁ hY₁ pY₁ h₁)
    {X₀ : Scheme.{u}} (hX₀ : B.Contains X₀) (pX₀ : X₀ ⟶ Spec (.of K))
    (ι : yoneda.obj (integerSiteObject B hZ hX₀) ⟶ F.total.obj)
    (hι : IsPullback ι (yoneda.map (integerSiteMap B hZ hX₀ hK pX₀)) (F.toBaseYonedaOfEq hF)
      (yoneda.map (integerSiteMap B hZ hK hS s)))
    (x : X₀ ⟶ X₁) (hx : x ≫ pX₁ = pX₀ ≫ k)
    (hιx : ι ≫ φ = yoneda.map (integerSiteMap B hZ hX₀ hX₁ x) ≫ ι₁)
    {Y₀ : Scheme.{u}} (hY₀ : B.Contains Y₀) (pY₀ : Y₀ ⟶ Spec (.of K)) (y₀ : Y₀ ⟶ Y₁)
    (hy : IsPullback y₀ pY₀ pY₁ k) (h₀ : X₀ ⟶ Y₀) (hh₀ : h₀ ≫ pY₀ = pX₀)
    (hhx : h₀ ≫ y₀ = x ≫ h₁) :
    HasEtaleContraction hS F hF hK s hX₀ pX₀ ι hY₀ pY₀ h₀ := by
  obtain ⟨U₀, hU₀, e₀, _, t₀, ht₀, G₀, hG₀, hU0, hhU0, ιU₀, hιU₀e, hιU₀, j₀, hj₀, hιj₀⟩ := H
  have fibre : ∀ {P X Y Z D V : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u} {c₁ : X ⟶ Z}
      {c₂ : X ⟶ Y} {f : Z ⟶ D} {g : Y ⟶ D} {ι : P ⟶ Z} {q : P ⟶ V} {s : V ⟶ D} {t : V ⟶ Y},
      IsPullback c₁ c₂ f g → IsPullback ι q f s → t ≫ g = s →
        ∃ ιU : P ⟶ X, ιU ≫ c₁ = ι ∧ IsPullback ιU q c₂ t := by
    intro P X Y Z D V c₁ c₂ f g ι q s t sq hbig hts
    subst hts
    exact ⟨_, sq.lift_fst _ _ _, IsPullback.of_right' hbig sq⟩
  have hU : B.Contains (Limits.pullback e₀ a) := Scheme.size_pullback_lt e₀ a hU₀ hS
  let t : Spec (.of K) ⟶ Limits.pullback e₀ a := Limits.pullback.lift (k ≫ t₀) s (by
    rw [Category.assoc, ht₀, hk])
  have ht : t ≫ Limits.pullback.snd e₀ a = s := Limits.pullback.lift_snd _ _ _
  have htf : t ≫ Limits.pullback.fst e₀ a = k ≫ t₀ := Limits.pullback.lift_fst _ _ _
  -- the family `G` and the base change of `F₀` to `U₀`
  let G := (G₀.ofBaseEq hG₀).pullback (integerSiteMap B hZ hU hU₀ (Limits.pullback.fst e₀ a))
  have hG : G.base = integerSiteObject B hZ hU := rfl
  have eG : G.toBaseYonedaOfEq hG = G.toBaseYoneda := toBaseYonedaOfEq_rfl' G
  have sqG :=
    G₀.isPullback_pullbackHom_yoneda hG₀ (integerSiteMap B hZ hU hU₀ (Limits.pullback.fst e₀ a))
  let FU := (F.ofBaseEq hF).pullback (integerSiteMap B hZ hU hS (Limits.pullback.snd e₀ a))
  have sqFU :=
    F.isPullback_pullbackHom_yoneda hF (integerSiteMap B hZ hU hS (Limits.pullback.snd e₀ a))
  have sqF0 := F₀.isPullback_pullbackHom_yoneda hF₀ (integerSiteMap B hZ hU₀ hS₀ e₀)
  have hcond : yoneda.map (integerSiteMap B hZ hU hU₀ (Limits.pullback.fst e₀ a)) ≫
      yoneda.map (integerSiteMap B hZ hU₀ hS₀ e₀) =
      yoneda.map (integerSiteMap B hZ hU hS (Limits.pullback.snd e₀ a)) ≫
        yoneda.map (integerSiteMap B hZ hS hS₀ a) := by
    rw [yoneda_map_integerSiteMap_comp, yoneda_map_integerSiteMap_comp, Limits.pullback.condition]
  let mU := sqF0.lift
    (((F.ofBaseEq hF).pullbackHom
      (integerSiteMap B hZ hU hS (Limits.pullback.snd e₀ a))).totalMap.hom ≫ φ)
    (FU.toBaseYoneda ≫ yoneda.map (integerSiteMap B hZ hU hU₀ (Limits.pullback.fst e₀ a)))
    (by rw [Category.assoc, hφ, reassoc_of% sqFU.w, Category.assoc, hcond])
  have hmU1 : mU ≫ ((F₀.ofBaseEq hF₀).pullbackHom (integerSiteMap B hZ hU₀ hS₀ e₀)).totalMap.hom =
      ((F.ofBaseEq hF).pullbackHom
        (integerSiteMap B hZ hU hS (Limits.pullback.snd e₀ a))).totalMap.hom ≫ φ :=
    sqF0.lift_fst _ _ _
  have hmU2 : mU ≫ ((F₀.ofBaseEq hF₀).pullback (integerSiteMap B hZ hU₀ hS₀ e₀)).toBaseYoneda =
      FU.toBaseYoneda ≫ yoneda.map (integerSiteMap B hZ hU hU₀ (Limits.pullback.fst e₀ a)) :=
    sqF0.lift_snd _ _ _
  let h := sqG.lift (mU ≫ hU0) FU.toBaseYoneda (by rw [Category.assoc, hhU0, hmU2])
  have hlift1 := sqG.lift_fst (mU ≫ hU0) FU.toBaseYoneda (by rw [Category.assoc, hhU0, hmU2])
  have hlift2 := sqG.lift_snd (mU ≫ hU0) FU.toBaseYoneda (by rw [Category.assoc, hhU0, hmU2])
  -- the fibre of `F_U` over `t`
  have es : yoneda.map (integerSiteMap B hZ hK hU t) ≫
        yoneda.map (integerSiteMap B hZ hU hS (Limits.pullback.snd e₀ a)) =
      yoneda.map (integerSiteMap B hZ hK hS s) :=
    (yoneda_map_integerSiteMap_comp _ _).trans
      (congrArg (fun f => yoneda.map (integerSiteMap B hZ hK hS f)) ht)
  obtain ⟨ιU, hιUe, hιU⟩ := fibre sqFU hι es
  -- the fibre of `G` over `t`
  have hyy := AlgebraicSpaces.isPullback_hom B integerBase hZ
    (isPullback_schemeSpaceMap_integerSiteMap (hP := hY₀) (hQ := hY₁) (hR := hK) (hW := hK₀) hy)
  have hJ := (show IsPullback (yoneda.map (integerSiteMap B hZ hY₀ hY₁ y₀))
      (yoneda.map (integerSiteMap B hZ hY₀ hK pY₀)) (yoneda.map (integerSiteMap B hZ hY₁ hK₀ pY₁))
      (yoneda.map (integerSiteMap B hZ hK hK₀ k)) from hyy).paste_horiz hj₀
  have etk : yoneda.map (integerSiteMap B hZ hK hU t) ≫
        yoneda.map (integerSiteMap B hZ hU hU₀ (Limits.pullback.fst e₀ a)) =
      yoneda.map (integerSiteMap B hZ hK hK₀ k) ≫
        yoneda.map (integerSiteMap B hZ hK₀ hU₀ t₀) := by
    rw [yoneda_map_integerSiteMap_comp, yoneda_map_integerSiteMap_comp, htf]
  obtain ⟨j, hjf, hj⟩ := fibre sqG hJ etk
  -- compatibility of `ιU` with the fibre of `F₀` over `t₀`
  have hιmU : ιU ≫ mU = yoneda.map (integerSiteMap B hZ hX₀ hX₁ x) ≫ ιU₀ := by
    apply sqF0.hom_ext
    · rw [Category.assoc, hmU1, reassoc_of% hιUe, hιx, Category.assoc, hιU₀e]
    · rw [Category.assoc, hmU2, reassoc_of% hιU.w, Category.assoc, etk, hιU₀.w,
        ← Category.assoc, ← Category.assoc, yoneda_map_integerSiteMap_comp pX₀ k,
        yoneda_map_integerSiteMap_comp x pX₁, hx]
  refine ⟨Limits.pullback e₀ a, hU, Limits.pullback.snd e₀ a, inferInstance, t, ht, G, hG, h,
    by rw [eG]; exact hlift2, ιU, hιUe, hιU, j, by rw [eG]; exact hj, ?_⟩
  apply sqG.hom_ext
  · rw [Category.assoc, Category.assoc, hjf, hlift1, reassoc_of% hιmU, hιj₀, ← Category.assoc,
      ← Category.assoc, yoneda_map_integerSiteMap_comp, yoneda_map_integerSiteMap_comp, hhx]
  · rw [Category.assoc, Category.assoc, hlift2, hj.w, hιU.w, ← yoneda.map_comp_assoc,
      integerSiteMap_comp, hh₀]

end CurveFamily

end AlgebraicGeometry

end
