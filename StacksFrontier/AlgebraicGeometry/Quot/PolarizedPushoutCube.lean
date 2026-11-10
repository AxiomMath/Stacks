module

public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedFamiliesTransport
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushoutCartesianSpans
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushoutModuleGluing

/-!
# The canonical cube of a polarized family over a pushout along a thickening

Let `T ⟶ T'` be a thickening of schemes of the big fppf site, `T ⟶ S` an affine morphism, and
`S'` a pushout of the two, identified with Mathlib's canonical pushout `P` by an isomorphism
`e : P ≅ S'`. A polarized family `x` over `S'` (Stacks 0D1M) restricts along `S ⟶ S'`,
`T' ⟶ S'` and `T ⟶ S'` to three polarized families, whose total spaces are the three base changes
`V = S ×_P X`, `U' = T' ×_P X` and `U = T ×_P X` of [Stacks Project, Tag 08KU] for the morphism
`X ⟶ P` read through `e`; together with the morphisms between them they form a commutative cube
of polarized families lying over the square of bases. This file builds that cube and proves that
**morphisms out of `x` glue along it** (Tags 07RX and 08KU): two morphisms out of the restrictions
to `S` and to `T'`, lying over the two maps to the base of the target and agreeing on the
restriction to `T`, are the restrictions of a unique morphism out of `x` over the identity.

## Main definitions

* `AlgebraicGeometry.PolarizedFamily.cubeTarget`, `cubeAmbient`, `cubeCommon`: the restrictions
  of `x` to `S`, to `T'` and to `T`.
* `AlgebraicGeometry.PolarizedFamily.cubeTargetHom`, `cubeAmbientHom`, `cubeCommonToTarget`,
  `cubeCommonToAmbient`: the four morphisms of the cube.

## Main results

* `AlgebraicGeometry.PolarizedFamily.cubeCommonToTarget_comp_cubeTargetHom`: the cube commutes.
* `AlgebraicGeometry.PolarizedFamily.existsUnique_glue_hom`: morphisms out of `x` glue.

## References

* [Stacks Project, Tag 07RX](https://stacks.math.columbia.edu/tag/07RX)
* [Stacks Project, Tag 08KU](https://stacks.math.columbia.edu/tag/08KU)
* [Stacks Project, Tag 0D44](https://stacks.math.columbia.edu/tag/0D44)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Pushout Stacks.Thickenings

namespace AlgebraicGeometry.PolarizedFamily

universe u

variable {B : BigFppfSite.{u}}

section Cube

variable {T T' S : B.Schemes} (i : T ⟶ T') (f : T ⟶ S)
  [HasPushout (B.inclusion.map i) (B.inclusion.map f)]
  (x : PolarizedFamily B) (g : T' ⟶ x.base) (h : S ⟶ x.base)
  (e : pushout (B.inclusion.map i) (B.inclusion.map f) ≅ B.inclusion.obj x.base)
  (q : x.total ⟶ pushout (B.inclusion.map i) (B.inclusion.map f))

/-- The pullback of `q` along a map `p` into `P` is a base change of `q ≫ e.hom` along `p ≫ e.hom`
for any isomorphism `e` out of `P`. -/
private theorem isPullback_pullback_snd_of_iso {C : Type*} [Category C] {A P X Y : C}
    (p : A ⟶ P) (q : X ⟶ P) [HasPullback p q] (e : P ≅ Y) {a : A ⟶ Y} {b : X ⟶ Y}
    (hp : p ≫ e.hom = a) (hq : q ≫ e.hom = b) :
    IsPullback (pullback.snd p q) (pullback.fst p q) b a :=
  (IsPullback.of_hasPullback p q).flip.of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) e (by simp) (by simp) (by simpa using hq)
    (by simpa using hp)

/-- A pullback square over `d` stays a pullback after transporting its base along `e.inv`. -/
private theorem isPullback_comp_inv_of_hom_eq {C : Type*} [Category C] {W Z V Y P : C}
    {fst : W ⟶ Z} {snd : W ⟶ V} {c : Z ⟶ Y} {d : V ⟶ Y} (H : IsPullback fst snd c d)
    (e : P ≅ Y) {p : V ⟶ P} (hp : p ≫ e.hom = d) : IsPullback fst snd (c ≫ e.inv) p :=
  H.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) e.symm (by simp) (by simp) (by simp)
    (by simp [← hp])

/-- The restriction of the total space to `S` is a base change of the family along `S ⟶ S'`. -/
theorem isPullback_targetRestriction
    (hh : pushout.inr (B.inclusion.map i) (B.inclusion.map f) ≫ e.hom = B.inclusion.map h)
    (hq : q ≫ e.hom = x.toBase) :
    IsPullback (targetRestriction (B.inclusion.map i) (B.inclusion.map f) q)
      (targetBase (B.inclusion.map i) (B.inclusion.map f) q) x.toBase (B.inclusion.map h) :=
  isPullback_pullback_snd_of_iso _ _ e hh hq

/-- The restriction of the total space to `T'` is a base change of the family along
`T' ⟶ S'`. -/
theorem isPullback_ambientRestriction
    (hg : pushout.inl (B.inclusion.map i) (B.inclusion.map f) ≫ e.hom = B.inclusion.map g)
    (hq : q ≫ e.hom = x.toBase) :
    IsPullback (ambientRestriction (B.inclusion.map i) (B.inclusion.map f) q)
      (ambientBase (B.inclusion.map i) (B.inclusion.map f) q) x.toBase (B.inclusion.map g) :=
  isPullback_pullback_snd_of_iso _ _ e hg hq

/-- The restriction of the total space to `T` is a base change of the family along `T ⟶ S'`. -/
theorem isPullback_commonRestriction
    (hg : pushout.inl (B.inclusion.map i) (B.inclusion.map f) ≫ e.hom = B.inclusion.map g)
    (hq : q ≫ e.hom = x.toBase) :
    IsPullback (commonRestriction (B.inclusion.map i) (B.inclusion.map f) q)
      (pullback.fst (B.inclusion.map i ≫ pushout.inl _ _) q) x.toBase
      (B.inclusion.map (i ≫ g)) :=
  isPullback_pullback_snd_of_iso _ _ e (by rw [Category.assoc, hg, Functor.map_comp]) hq

/-- The restriction to `T` maps to the restriction to `S` along a cartesian square over
`T ⟶ S`. -/
theorem isPullback_commonToTarget (hsq : f ≫ h = i ≫ g)
    (hg : pushout.inl (B.inclusion.map i) (B.inclusion.map f) ≫ e.hom = B.inclusion.map g)
    (hh : pushout.inr (B.inclusion.map i) (B.inclusion.map f) ≫ e.hom = B.inclusion.map h)
    (hq : q ≫ e.hom = x.toBase) :
    IsPullback (commonToTarget (B.inclusion.map i) (B.inclusion.map f) q)
      (pullback.fst (B.inclusion.map i ≫ pushout.inl _ _) q)
      (targetBase (B.inclusion.map i) (B.inclusion.map f) q) (B.inclusion.map f) := by
  have hbig := isPullback_commonRestriction i f x g e q hg hq
  rw [← commonToTarget_comp_restriction, ← hsq, Functor.map_comp] at hbig
  exact IsPullback.of_right hbig (pullback.lift_fst _ _ _)
    (isPullback_targetRestriction i f x h e q hh hq)

/-- The restriction to `T` maps to the restriction to `T'` along a cartesian square over
`T ⟶ T'`. -/
theorem isPullback_commonToAmbient
    (hg : pushout.inl (B.inclusion.map i) (B.inclusion.map f) ≫ e.hom = B.inclusion.map g)
    (hq : q ≫ e.hom = x.toBase) :
    IsPullback (commonToAmbient (B.inclusion.map i) (B.inclusion.map f) q)
      (pullback.fst (B.inclusion.map i ≫ pushout.inl _ _) q)
      (ambientBase (B.inclusion.map i) (B.inclusion.map f) q) (B.inclusion.map i) := by
  have hbig := isPullback_commonRestriction i f x g e q hg hq
  rw [← commonToAmbient_comp_restriction, Functor.map_comp] at hbig
  exact IsPullback.of_right hbig (pullback.lift_fst _ _ _)
    (isPullback_ambientRestriction i f x g e q hg hq)

variable (hsq : f ≫ h = i ≫ g)
  (hg : pushout.inl (B.inclusion.map i) (B.inclusion.map f) ≫ e.hom = B.inclusion.map g)
  (hh : pushout.inr (B.inclusion.map i) (B.inclusion.map f) ≫ e.hom = B.inclusion.map h)
  (hq : q ≫ e.hom = x.toBase)

/-- The restriction of `x` to `S`, with total space `V = S ×_P X`. -/
abbrev cubeTarget : PolarizedFamily B :=
  x.ofIsPullback h (isPullback_targetRestriction i f x h e q hh hq)

/-- The morphism from the restriction of `x` to `S` to `x`. -/
abbrev cubeTargetHom : cubeTarget i f x h e q hh hq ⟶ x :=
  x.ofIsPullbackHom h (isPullback_targetRestriction i f x h e q hh hq)

/-- The restriction of `x` to `T'`, with total space `U' = T' ×_P X`. -/
abbrev cubeAmbient : PolarizedFamily B :=
  x.ofIsPullback g (isPullback_ambientRestriction i f x g e q hg hq)

/-- The morphism from the restriction of `x` to `T'` to `x`. -/
abbrev cubeAmbientHom : cubeAmbient i f x g e q hg hq ⟶ x :=
  x.ofIsPullbackHom g (isPullback_ambientRestriction i f x g e q hg hq)

/-- The restriction of `x` to `T`, with total space `U = T ×_P X`, read as the restriction of
`cubeTarget` along `T ⟶ S`. -/
abbrev cubeCommon : PolarizedFamily B :=
  (cubeTarget i f x h e q hh hq).ofIsPullback f
    (isPullback_commonToTarget i f x g h e q hsq hg hh hq)

/-- The morphism from the restriction to `T` to the restriction to `S`. -/
abbrev cubeCommonToTarget :
    cubeCommon i f x g h e q hsq hg hh hq ⟶ cubeTarget i f x h e q hh hq :=
  (cubeTarget i f x h e q hh hq).ofIsPullbackHom f
    (isPullback_commonToTarget i f x g h e q hsq hg hh hq)

/-- The morphism from the restriction to `T` to the restriction to `T'`: the restriction map of
total spaces over `T ⟶ T'`, with the canonical identification of the two restrictions of the
polarization to `U` of [Stacks Project, Tag 08KU]. -/
abbrev cubeCommonToAmbient :
    cubeCommon i f x g h e q hsq hg hh hq ⟶ cubeAmbient i f x g e q hg hq where
  baseMap := i
  totalMap := commonToAmbient (B.inclusion.map i) (B.inclusion.map f) q
  cartesian := isPullback_commonToAmbient i f x g e q hg hq
  lineBundleIso :=
    ((overlapComparison (B.inclusion.map i) (B.inclusion.map f) q).app x.lineBundle).symm

/-- The comparison of polarizations of the morphism from the restriction to `T` to the restriction
to `T'` is the inverse of the overlap comparison. -/
@[simp]
theorem cubeCommonToAmbient_lineBundleIso :
    (cubeCommonToAmbient i f x g h e q hsq hg hh hq).lineBundleIso =
      ((overlapComparison (B.inclusion.map i) (B.inclusion.map f) q).app x.lineBundle).symm :=
  rfl

/-- The map of total spaces of the morphism from the restriction to `T` to the restriction to `T'`
is the restriction map `U ⟶ U'`. -/
@[simp]
theorem cubeCommonToAmbient_totalMap :
    (cubeCommonToAmbient i f x g h e q hsq hg hh hq).totalMap =
      commonToAmbient (B.inclusion.map i) (B.inclusion.map f) q :=
  rfl

/-- **The cube commutes.** -/
theorem cubeCommonToTarget_comp_cubeTargetHom :
    cubeCommonToTarget i f x g h e q hsq hg hh hq ≫ cubeTargetHom i f x h e q hh hq =
      cubeCommonToAmbient i f x g h e q hsq hg hh hq ≫ cubeAmbientHom i f x g e q hg hq := by
  have ht : commonToTarget (B.inclusion.map i) (B.inclusion.map f) q ≫
      targetRestriction (B.inclusion.map i) (B.inclusion.map f) q =
      commonToAmbient (B.inclusion.map i) (B.inclusion.map f) q ≫
      ambientRestriction (B.inclusion.map i) (B.inclusion.map f) q :=
    commonToTarget_comp_targetRestriction _ _ q
  refine Hom.ext hsq ht ?_
  have hobj : (Scheme.Modules.pullback (commonToTarget (B.inclusion.map i) (B.inclusion.map f) q ≫
      targetRestriction (B.inclusion.map i) (B.inclusion.map f) q)).obj x.lineBundle =
      (Scheme.Modules.pullback (commonToAmbient (B.inclusion.map i) (B.inclusion.map f) q ≫
        ambientRestriction (B.inclusion.map i) (B.inclusion.map f) q)).obj x.lineBundle := by
    rw [ht]
  have key : Hom.lineBundleIso (cubeCommonToTarget i f x g h e q hsq hg hh hq ≫
      cubeTargetHom i f x h e q hh hq) = eqToIso hobj ≪≫ Hom.lineBundleIso
        (cubeCommonToAmbient i f x g h e q hsq hg hh hq ≫ cubeAmbientHom i f x g e q hg hq) := by
    refine Iso.ext ?_
    change (Scheme.Modules.pullbackComp _ _).inv.app x.lineBundle ≫
        (Scheme.Modules.pullback _).map (𝟙 _) ≫ 𝟙 _ =
      eqToHom hobj ≫ (Scheme.Modules.pullbackComp _ _).inv.app x.lineBundle ≫
        (Scheme.Modules.pullback _).map (𝟙 _) ≫
        ((overlapComparison (B.inclusion.map i) (B.inclusion.map f) q).app x.lineBundle).inv
    simp [overlapComparison, Scheme.Modules.pullbackCongr]
  exact (heq_of_eq key).trans (eqToIso_trans_heq hobj _)

/-- Equal morphisms of polarized families have comparisons of polarizations that agree up to the
transport between the two pullbacks of the polarization. -/
theorem Hom.lineBundleIso_eq_of_eq {z y : PolarizedFamily B} {φ ψ : z ⟶ y} (hφψ : φ = ψ) :
    φ.lineBundleIso = eqToIso (congrArg (fun k : z ⟶ y ↦
      (Scheme.Modules.pullback k.totalMap).obj y.lineBundle) hφψ) ≪≫ ψ.lineBundleIso := by
  subst hφψ
  simp

include hsq in
/-- **Morphisms out of a polarized family glue along its cube** (Tags 07RX and 08KU). Let `y` be
a polarized family over the same base as `x`, and let `α` and `β` be morphisms to `y` from the
restrictions of `x` to `S` and to `T'`, lying over `S ⟶ S'` and `T' ⟶ S'` and agreeing on the
restriction to `T`. Then there is a unique morphism `x ⟶ y` over the identity of the base whose
restrictions are `α` and `β`. -/
theorem existsUnique_glue_hom (hi : IsThickening (B.inclusion.map i))
    [IsAffineHom (B.inclusion.map f)] {y : PolarizedFamily B} (hy : y.base = x.base)
    (α : cubeTarget i f x h e q hh hq ⟶ y) (β : cubeAmbient i f x g e q hg hq ⟶ y)
    (hα : α.baseMap = h ≫ eqToHom hy.symm) (hβ : β.baseMap = g ≫ eqToHom hy.symm)
    (hαβ : cubeCommonToTarget i f x g h e q hsq hg hh hq ≫ α =
      cubeCommonToAmbient i f x g h e q hsq hg hh hq ≫ β) :
    ∃! φ : x ⟶ y, φ.baseMap = eqToHom hy.symm ∧ cubeTargetHom i f x h e q hh hq ≫ φ = α ∧
      cubeAmbientHom i f x g e q hg hq ≫ φ = β := by
  obtain ⟨yb, yt, ytb, yp, yfl, yfp, yl, yi, ya⟩ := y
  change yb = x.base at hy
  subst hy
  obtain ⟨ab, αt, ac, al⟩ := α
  obtain ⟨bb, βt, bc, bl⟩ := β
  change ab = h ≫ 𝟙 _ at hα
  change bb = g ≫ 𝟙 _ at hβ
  rw [Category.comp_id] at hα hβ
  subst ab bb
  have hqe : q = x.toBase ≫ e.inv := by
    rw [← hq, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have : Flat x.toBase := x.flat
  have hqf : Flat q := by rw [hqe]; infer_instance
  have hyf : Flat (ytb ≫ e.inv) := by have : Flat ytb := yfl; infer_instance
  have hcy : IsPullback αt (targetBase (B.inclusion.map i) (B.inclusion.map f) q) (ytb ≫ e.inv)
      (pushout.inr (B.inclusion.map i) (B.inclusion.map f)) :=
    isPullback_comp_inv_of_hom_eq ac e hh
  have hdy : IsPullback βt (ambientBase (B.inclusion.map i) (B.inclusion.map f) q) (ytb ≫ e.inv)
      (pushout.inl (B.inclusion.map i) (B.inclusion.map f)) :=
    isPullback_comp_inv_of_hom_eq bc e hg
  have huvt : commonToTarget (B.inclusion.map i) (B.inclusion.map f) q ≫ αt =
      commonToAmbient (B.inclusion.map i) (B.inclusion.map f) q ≫ βt :=
    congrArg Hom.totalMap hαβ
  have hcube := isPullback_commonToTarget i f x g h e q hsq hg hh hq
  have hvi : commonToAmbient (B.inclusion.map i) (B.inclusion.map f) q ≫
      ambientBase (B.inclusion.map i) (B.inclusion.map f) q =
      pullback.fst ((B.inclusion.map i) ≫ pushout.inl (B.inclusion.map i) (B.inclusion.map f)) q ≫
        (B.inclusion.map i) :=
    pullback.lift_fst _ _ _
  have hPx : IsPushout (commonToTarget (B.inclusion.map i) (B.inclusion.map f) q)
      (commonToAmbient (B.inclusion.map i) (B.inclusion.map f) q)
      (targetRestriction (B.inclusion.map i) (B.inclusion.map f) q)
      (ambientRestriction (B.inclusion.map i) (B.inclusion.map f) q) :=
    isPushout_of_cartesianCube (B.inclusion.map i) (B.inclusion.map f) hi q hqf
      (IsPullback.of_hasPullback _ q).flip (IsPullback.of_hasPullback _ q).flip hcube hvi
      (commonToTarget_comp_targetRestriction _ _ q)
  have hPy : IsPushout (commonToTarget (B.inclusion.map i) (B.inclusion.map f) q)
      (commonToAmbient (B.inclusion.map i) (B.inclusion.map f) q) αt βt :=
    isPushout_of_cartesianCube (B.inclusion.map i) (B.inclusion.map f) hi (ytb ≫ e.inv) hyf hcy hdy
      hcube hvi huvt
  obtain ⟨t, ht₁, ht₂⟩ : ∃ t, targetRestriction (B.inclusion.map i) (B.inclusion.map f) q ≫ t = αt ∧
      ambientRestriction (B.inclusion.map i) (B.inclusion.map f) q ≫ t = βt :=
    ⟨hPx.desc αt βt huvt, hPx.inl_desc _ _ _, hPx.inr_desc _ _ _⟩
  subst ht₁ ht₂
  have htiso : IsIso t := by
    have : t = (hPx.isoIsPushout _ _ hPy).hom :=
      hPx.hom_ext (IsPushout.inl_isoIsPushout_hom _ _ hPx hPy).symm
        (IsPushout.inr_isoIsPushout_hom _ _ hPx hPy).symm
    rw [this]
    exact Iso.isIso_hom _
  have htb : t ≫ ytb = x.toBase := by
    apply hPx.hom_ext
    · exact (Category.assoc _ _ _).symm.trans
        (ac.w.trans (isPullback_targetRestriction i f x h e q hh hq).w.symm)
    · exact (Category.assoc _ _ _).symm.trans
        (bc.w.trans (isPullback_ambientRestriction i f x g e q hg hq).w.symm)
  have hcart : IsPullback t x.toBase ytb (B.inclusion.map (𝟙 x.base)) := by
    have : IsIso (B.inclusion.map (𝟙 x.base)) := by
      rw [CategoryTheory.Functor.map_id]; infer_instance
    exact IsPullback.of_horiz_isIso ⟨by rw [htb, CategoryTheory.Functor.map_id, Category.comp_id]⟩
  have hobj : (Scheme.Modules.pullback (commonToTarget (B.inclusion.map i) (B.inclusion.map f) q ≫
      targetRestriction (B.inclusion.map i) (B.inclusion.map f) q ≫ t)).obj yl =
      (Scheme.Modules.pullback (commonToAmbient (B.inclusion.map i) (B.inclusion.map f) q ≫
        ambientRestriction (B.inclusion.map i) (B.inclusion.map f) q ≫ t)).obj yl := by
    rw [huvt]
  have key := congrArg Iso.hom (Hom.lineBundleIso_eq_of_eq hαβ)
  simp only [Iso.trans_hom, comp_lineBundleIso_hom, Iso.symm_hom, eqToIso.hom] at key
  dsimp only [comp_totalMap] at key
  have hστ := compatible_of_overlapComparison (B.inclusion.map i) (B.inclusion.map f) q t yl
    x.lineBundle al.hom bl.hom hobj key
  have := x.invertible
  have : AlgebraicGeometry.SheafOfModules.IsInvertible yt.presheaf yt.ringCatSheaf.2 yl := yi
  have hM : FlatQuasicoherent q ((Scheme.Modules.pullback t).obj yl) := by
    have : AlgebraicGeometry.SheafOfModules.IsInvertible x.total.presheaf x.total.ringCatSheaf.2
        ((Scheme.Modules.pullback t).obj yl) :=
      Stacks.RingedSpace.algebraicGeometryIsInvertible_modulePullback t.toLRSHom.toShHom yl
    exact flatQuasicoherent_of_isInvertible q _
  have hN : FlatQuasicoherent q x.lineBundle := flatQuasicoherent_of_isInvertible q x.lineBundle
  obtain ⟨ℓ, hℓ₁, hℓ₂⟩ := exists_iso_of_compatible (B.inclusion.map i) (B.inclusion.map f) hi q
    hM hN ((Scheme.Modules.pullbackComp _ t).app yl ≪≫ al)
    ((Scheme.Modules.pullbackComp _ t).app yl ≪≫ bl) hστ
  refine ⟨⟨𝟙 x.base, t, hcart, ℓ⟩, ⟨rfl, ?_, ?_⟩, ?_⟩
  on_goal 3 =>
    rintro ⟨b', t', c', l'⟩ ⟨hb', h₁, h₂⟩
    change b' = 𝟙 _ at hb'
    subst hb'
    have ht' : t' = t := hPx.hom_ext (congrArg Hom.totalMap h₁) (congrArg Hom.totalMap h₂)
    subst ht'
    have e₁ := congrArg Iso.hom (Hom.lineBundleIso_eq_of_eq h₁)
    have e₂ := congrArg Iso.hom (Hom.lineBundleIso_eq_of_eq h₂)
    simp only [Iso.trans_hom, eqToIso.hom, comp_lineBundleIso_hom] at e₁ e₂
    dsimp only [comp_totalMap] at e₁ e₂
    simp only [Iso.refl_hom, Category.comp_id] at e₁ e₂
    have hl₁ : (Scheme.Modules.pullback (targetRestriction (B.inclusion.map i)
        (B.inclusion.map f) q)).map l'.hom = (Scheme.Modules.pullback _).map ℓ.hom := by
      rw [hℓ₁, Iso.trans_hom, Iso.app_hom, ← e₁.trans (Category.id_comp al.hom),
        Iso.hom_inv_id_app_assoc]
    have hl₂ : (Scheme.Modules.pullback (ambientRestriction (B.inclusion.map i)
        (B.inclusion.map f) q)).map l'.hom = (Scheme.Modules.pullback _).map ℓ.hom := by
      rw [hℓ₂, Iso.trans_hom, Iso.app_hom, ← e₂.trans (Category.id_comp bl.hom),
        Iso.hom_inv_id_app_assoc]
    obtain ⟨_, -, huniq⟩ := existsUnique_hom_of_compatible (B.inclusion.map i)
      (B.inclusion.map f) hi q hM hN _ _
      ((overlapComparison (B.inclusion.map i) (B.inclusion.map f) q).hom.naturality ℓ.hom)
    have hl : l' = ℓ := Iso.ext ((huniq _ ⟨hl₁, hl₂⟩).trans (huniq _ ⟨rfl, rfl⟩).symm)
    subst hl
    rfl
  all_goals
    refine Hom.ext (Category.comp_id _) rfl (heq_of_eq (Iso.ext ?_))
    rw [comp_lineBundleIso_hom]
    change _ ≫ _ ≫ 𝟙 _ = _
    rw [Category.comp_id]
    change _ ≫ (Scheme.Modules.pullback _).map ℓ.hom = _
    first | rw [hℓ₁] | rw [hℓ₂]
    simp

end Cube

end AlgebraicGeometry.PolarizedFamily

end
