module

public import StacksFrontier.CategoryTheory.FiberedCategory.FiberSquareRestrictionEquivalence
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedPushoutCube
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushoutInvertible
public import StacksFrontier.AlgebraicGeometry.AmpleThickeningAscent.Basic

/-!
# The stack of polarized schemes satisfies the pushout condition (Stacks 0D44)

Let

```
T  --i-->  T'
|          |
f          g
|          |
v          v
S  --h-->  S'
```

be a pushout in the category of schemes, with `i` a thickening and `f` affine, all four schemes in
the big fppf site. [Stacks Project, Tag 0D44] asserts that the comparison functor
`AlgebraicGeometry.polarizedPushoutRestriction`

`𝒫olarized_{S'} ⟶ 𝒫olarized_S ×_{𝒫olarized_T} 𝒫olarized_{T'}`

on fibre categories of the stack of polarized schemes (Stacks 0D1M) is an equivalence. This file
proves it, following the source.

* **Gluing of objects** (`AlgebraicGeometry.PolarizedFamily.exists_glue_family`). Given polarized
  families over `S` and `T'` with an identification of their restrictions to `T`, the total
  spaces glue to a scheme `X'` flat and locally of finite presentation over `S'` (Tag 07RX), which
  is proper over `S'` because its restriction to the thickening `S ⊆ S'` is (the map from the
  restriction is a surjective closed immersion, across which universal closedness and
  separatedness descend). The polarizations glue to a quasi-coherent module flat over `S'`
  (Tag 08KU), of finite presentation by the finite presentation clause of Tag 08KU, invertible by
  `Stacks.Pushout.isInvertible_of_isInvertible_pullback_snd` (the small point of the source,
  through Tag 080Q), and relatively ample by Tag 0D2R.
* **Gluing of morphisms** (`AlgebraicGeometry.PolarizedFamily.existsUnique_glue_hom`): the
  restriction of the total space to `S` and `T'` exhibits it as the pushout (Tag 07RX), and
  isomorphisms of invertible modules glue (Tag 08KU).
* **The equivalence** (`AlgebraicGeometry.isEquivalence_polarizedPushoutRestriction`): both
  feed the general criterion
  `CategoryTheory.Functor.isEquivalence_fiberSquareRestriction`.

The pushout of the statement is an arbitrary pushout square in `Scheme`; it is compared with
Mathlib's canonical pushout `CategoryTheory.Limits.pushout`, on which Tags 07RV, 07RX and 08KU are
stated, by the canonical isomorphism of the two.

## Main results

* `AlgebraicGeometry.isEquivalence_polarizedPushoutRestriction`: **Stacks 0D44**.

## References

* [Stacks Project, Tag 0D44](https://stacks.math.columbia.edu/tag/0D44)
* [Stacks Project, Tag 07RT](https://stacks.math.columbia.edu/tag/07RT)
* [Stacks Project, Tag 07RX](https://stacks.math.columbia.edu/tag/07RX)
* [Stacks Project, Tag 08KU](https://stacks.math.columbia.edu/tag/08KU)
* [Stacks Project, Tag 080Q](https://stacks.math.columbia.edu/tag/080Q)
* [Stacks Project, Tag 0D2R](https://stacks.math.columbia.edu/tag/0D2R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Pushout Stacks.Thickenings

namespace AlgebraicGeometry.PolarizedFamily

universe u

variable {B : BigFppfSite.{u}}

/-- **Polarized families glue across a pushout along a thickening** (Tags 07RX, 08KU, 080Q and
0D2R). Let `xS`, `xT'` and `xT` be polarized families over `S`, `T'` and `T`, with morphisms
`xT ⟶ xS` over `f` and `xT ⟶ xT'` over `i`. Then there is a polarized family over the pushout
`S'` with morphisms from `xS` over `h` and from `xT'` over `g` making the square commute. -/
theorem exists_glue_family {xS xT' xT : PolarizedFamily B} {S' : B.Schemes}
    (i : xT.base ⟶ xT'.base) (f : xT.base ⟶ xS.base) (g : xT'.base ⟶ S') (h : xS.base ⟶ S')
    (hsq : f ≫ h = i ≫ g) [HasPushout (B.inclusion.map i) (B.inclusion.map f)]
    (hi : IsThickening (B.inclusion.map i)) [IsAffineHom (B.inclusion.map f)]
    (e : pushout (B.inclusion.map i) (B.inclusion.map f) ≅ B.inclusion.obj S')
    (hg : pushout.inl (B.inclusion.map i) (B.inclusion.map f) ≫ e.hom = B.inclusion.map g)
    (hh : pushout.inr (B.inclusion.map i) (B.inclusion.map f) ≫ e.hom = B.inclusion.map h)
    (u : xT ⟶ xS) (v : xT ⟶ xT') (hu : u.baseMap = f) (hv : v.baseMap = i) :
    ∃ (a : PolarizedFamily B) (ha : a.base = S') (μ : xS ⟶ a) (ν : xT' ⟶ a),
      μ.baseMap = h ≫ eqToHom ha.symm ∧ ν.baseMap = g ≫ eqToHom ha.symm ∧ u ≫ μ = v ≫ ν := by
  obtain ⟨ub, ut, uc, ul⟩ := u
  obtain ⟨vb, vt, vc, vl⟩ := v
  change ub = f at hu
  change vb = i at hv
  subst ub vb
  obtain ⟨Z, q, c, d, hc, hd, hP, hcth, hfl, hlfp⟩ :=
    exists_glue_of_cartesianSpan (B.inclusion.map i) (B.inclusion.map f) hi uc vc
  have : Flat q := hfl xS.flat xT'.flat
  have : LocallyOfFinitePresentation q :=
    hlfp xS.flat xS.finitePresentation.1 xT'.flat xT'.finitePresentation.1
  have : IsProper xS.toBase := xS.proper
  have : IsProper q := isProper_of_isPullback_inr _ _ hi hc
  -- the total spaces of the three families are the three canonical base changes of `Z`
  let ξS := hc.flip.isoPullback
  let ξT' := hd.flip.isoPullback
  have hTc : IsPullback (vt ≫ d) xT.toBase q (B.inclusion.map i ≫ pushout.inl _ _) :=
    vc.paste_horiz hd
  let ξT := hTc.flip.isoPullback
  let yS := xS.transportTotal ξS
  let yT' := xT'.transportTotal ξT'
  let yT := xT.transportTotal ξT
  let u0 : yT ⟶ yS := xT.transportTotalInv ξT ≫ ⟨f, ut, uc, ul⟩ ≫ xS.transportTotalHom ξS
  let v0 : yT ⟶ yT' := xT.transportTotalInv ξT ≫ ⟨i, vt, vc, vl⟩ ≫ xT'.transportTotalHom ξT'
  have hu0t : u0.totalMap = commonToTarget (B.inclusion.map i) (B.inclusion.map f) q := by
    apply pullback.hom_ext
    · change (ξT.inv ≫ ut ≫ ξS.hom) ≫ _ = _
      rw [commonToTarget, pullback.lift_fst, Category.assoc, Category.assoc,
        IsPullback.isoPullback_hom_fst, uc.w, ← Category.assoc, IsPullback.isoPullback_inv_fst]
    · change (ξT.inv ≫ ut ≫ ξS.hom) ≫ _ = _
      rw [commonToTarget, pullback.lift_snd, Category.assoc, Category.assoc,
        IsPullback.isoPullback_hom_snd, hP.w, IsPullback.isoPullback_inv_snd]
  have hv0t : v0.totalMap = commonToAmbient (B.inclusion.map i) (B.inclusion.map f) q := by
    apply pullback.hom_ext
    · change (ξT.inv ≫ vt ≫ ξT'.hom) ≫ _ = _
      rw [commonToAmbient, pullback.lift_fst, Category.assoc, Category.assoc,
        IsPullback.isoPullback_hom_fst, vc.w, ← Category.assoc, IsPullback.isoPullback_inv_fst]
    · change (ξT.inv ≫ vt ≫ ξT'.hom) ≫ _ = _
      rw [commonToAmbient, pullback.lift_snd, Category.assoc, Category.assoc,
        IsPullback.isoPullback_hom_snd, IsPullback.isoPullback_inv_snd]
  have hu0b : u0.baseMap = f := by
    change 𝟙 _ ≫ f ≫ 𝟙 _ = f
    rw [Category.id_comp, Category.comp_id]
  have hv0b : v0.baseMap = i := by
    change 𝟙 _ ≫ i ≫ 𝟙 _ = i
    rw [Category.id_comp, Category.comp_id]
  have hxu : xT.transportTotalHom ξT ≫ u0 = (⟨f, ut, uc, ul⟩ : xT ⟶ xS) ≫
      xS.transportTotalHom ξS := by
    simp only [u0, ← Category.assoc, transportTotalHom_comp_transportTotalInv, Category.id_comp]
  have hxv : xT.transportTotalHom ξT ≫ v0 = (⟨i, vt, vc, vl⟩ : xT ⟶ xT') ≫
      xT'.transportTotalHom ξT' := by
    simp only [v0, ← Category.assoc, transportTotalHom_comp_transportTotalInv, Category.id_comp]
  clear_value u0 v0
  obtain ⟨u0b, u0t, u0c, u0l⟩ := u0
  obtain ⟨v0b, v0t, v0c, v0l⟩ := v0
  change u0t = _ at hu0t
  change v0t = _ at hv0t
  change u0b = f at hu0b
  change v0b = i at hv0b
  subst u0t v0t u0b v0b
  -- the polarizations glue (Tag 08KU)
  have hyS : yS.toBase = targetBase (B.inclusion.map i) (B.inclusion.map f) q :=
    IsPullback.isoPullback_inv_fst hc.flip
  have hyT' : yT'.toBase = ambientBase (B.inclusion.map i) (B.inclusion.map f) q :=
    IsPullback.isoPullback_inv_fst hd.flip
  have := yS.invertible
  have := yT'.invertible
  have hA : FlatQuasicoherent (targetBase (B.inclusion.map i) (B.inclusion.map f) q)
      yS.lineBundle := by
    have : Flat (targetBase (B.inclusion.map i) (B.inclusion.map f) q) := by
      rw [← hyS]
      exact yS.flat
    exact flatQuasicoherent_of_isInvertible _ _
  have hA' : FlatQuasicoherent (ambientBase (B.inclusion.map i) (B.inclusion.map f) q)
      yT'.lineBundle := by
    have : Flat (ambientBase (B.inclusion.map i) (B.inclusion.map f) q) := by
      rw [← hyT']
      exact yT'.flat
    exact flatQuasicoherent_of_isInvertible _ _
  obtain ⟨M, μl, νl, hM, hcomm⟩ := exists_glue_of_compatible (B.inclusion.map i)
    (B.inclusion.map f) hi q yS.lineBundle yT'.lineBundle (u0l ≪≫ v0l.symm) hA hA'
  -- the glued module is invertible (Tag 080Q)
  have : Stacks.SheafOfModules.IsInvertible
      ((sheafToPresheaf _ _).obj
        (Limits.pullback (pushout.inr (B.inclusion.map i) (B.inclusion.map f)) q).sheaf)
      (Limits.pullback (pushout.inr (B.inclusion.map i) (B.inclusion.map f)) q).ringCatSheaf.2
      yS.lineBundle := yS.invertible
  have : Stacks.SheafOfModules.IsInvertible
      ((sheafToPresheaf _ _).obj
        (Limits.pullback (pushout.inl (B.inclusion.map i) (B.inclusion.map f)) q).sheaf)
      (Limits.pullback (pushout.inl (B.inclusion.map i) (B.inclusion.map f)) q).ringCatSheaf.2
      yT'.lineBundle := yT'.invertible
  have hVinv : AlgebraicGeometry.SheafOfModules.IsInvertible
      (Limits.pullback (pushout.inr (B.inclusion.map i) (B.inclusion.map f)) q).presheaf
      (Limits.pullback (pushout.inr (B.inclusion.map i) (B.inclusion.map f)) q).ringCatSheaf.2
      ((Scheme.Modules.pullback (targetRestriction (B.inclusion.map i) (B.inclusion.map f)
        q)).obj M) := Stacks.SheafOfModules.isInvertible_of_iso _ _ μl.symm
  have hUinv : AlgebraicGeometry.SheafOfModules.IsInvertible
      (Limits.pullback (pushout.inl (B.inclusion.map i) (B.inclusion.map f)) q).presheaf
      (Limits.pullback (pushout.inl (B.inclusion.map i) (B.inclusion.map f)) q).ringCatSheaf.2
      ((Scheme.Modules.pullback (ambientRestriction (B.inclusion.map i) (B.inclusion.map f)
        q)).obj M) := Stacks.SheafOfModules.isInvertible_of_iso _ _ νl.symm
  have hMfp : M.IsFinitePresentation :=
    (isFinitePresentation_iff_baseChangeTripleFunctor_obj (B.inclusion.map i) (B.inclusion.map f)
      hi q inferInstance ⟨M, hM⟩).mpr
      ⟨isFinitePresentation_of_isInvertible ((Scheme.Modules.pullback
          (targetRestriction (B.inclusion.map i) (B.inclusion.map f) q)).obj M),
        isFinitePresentation_of_isInvertible ((Scheme.Modules.pullback
          (ambientRestriction (B.inclusion.map i) (B.inclusion.map f) q)).obj M)⟩
  have hinr := pushout_inr_isThickening forall_isAffine_of_isThickening
    (B.inclusion.map i) (B.inclusion.map f) hi
  have : IsClosedImmersion (pushout.inr (B.inclusion.map i) (B.inclusion.map f)) := hinr.1
  have hMinv := isInvertible_of_isInvertible_pullback_snd
    (pushout.inr (B.inclusion.map i) (B.inclusion.map f)) hinr.2 q M hM.2
  -- the glued polarization is relatively ample (Tag 0D2R)
  have htR : IsThickening (targetRestriction (B.inclusion.map i) (B.inclusion.map f) q) :=
    isThickening_of_isPullback (IsPullback.of_hasPullback _ q).flip hinr
  have hhth : IsThickening (B.inclusion.map h) := by
    rw [← hh]
    exact ⟨inferInstance, e.hom.surjective.comp hinr.2⟩
  have hsqA : targetRestriction (B.inclusion.map i) (B.inclusion.map f) q ≫ (q ≫ e.hom) =
      targetBase (B.inclusion.map i) (B.inclusion.map f) q ≫ B.inclusion.map h := by
    rw [← hh, ← Category.assoc, ← pullback.condition, Category.assoc]
  have : Stacks.Ample.IsInvertibleModule Z M := hMinv
  have : Stacks.Ample.IsInvertibleModule _ yS.lineBundle := yS.invertible
  have : Stacks.Ample.IsInvertibleModule _ (Stacks.AmpleLocallyClosed.pullbackModule
      (targetRestriction (B.inclusion.map i) (B.inclusion.map f) q) M) := hVinv
  have hamp : Stacks.RelativeAmple.IsRelativelyAmple (q ≫ e.hom) M := by
    refine (Stacks.AmpleThickeningAscent.isRelativelyAmple_iff htR hhth hsqA M).mpr ?_
    refine (Stacks.RelativeVeryAmple.isRelativelyAmple_congr _ _ _ μl).mpr ?_
    rw [← hyS]
    exact yS.relativelyAmple
  let a : PolarizedFamily B :=
    { base := S'
      total := Z
      toBase := q ≫ e.hom
      proper := inferInstance
      flat := inferInstance
      finitePresentation := ⟨inferInstance, inferInstance, inferInstance⟩
      lineBundle := M
      invertible := hMinv
      relativelyAmple := hamp }
  let μ0 : yS ⟶ a :=
    { baseMap := h
      totalMap := targetRestriction (B.inclusion.map i) (B.inclusion.map f) q
      cartesian := by
        rw [hyS]
        exact isPullback_targetRestriction i f a h e q hh rfl
      lineBundleIso := μl }
  let ν0 : yT' ⟶ a :=
    { baseMap := g
      totalMap := ambientRestriction (B.inclusion.map i) (B.inclusion.map f) q
      cartesian := by
        rw [hyT']
        exact isPullback_ambientRestriction i f a g e q hg rfl
      lineBundleIso := νl }
  have key : (⟨f, _, u0c, u0l⟩ : yT ⟶ yS) ≫ μ0 = (⟨i, _, v0c, v0l⟩ : yT ⟶ yT') ≫ ν0 := by
    refine Hom.ext_of_lineBundleIso_hom hsq (commonToTarget_comp_targetRestriction _ _ q) ?_
    rw [comp_lineBundleIso_hom, comp_lineBundleIso_hom]
    exact pullbackComp_inv_comp_eq_of_compatible _ _ q M μl νl u0l v0l hcomm
  refine ⟨a, rfl, xS.transportTotalHom ξS ≫ μ0, xT'.transportTotalHom ξT' ≫ ν0,
    (Category.id_comp _).trans (Category.comp_id _).symm,
    (Category.id_comp _).trans (Category.comp_id _).symm, ?_⟩
  rw [← Category.assoc, ← hxu, Category.assoc, key, ← Category.assoc, hxv, Category.assoc]

end AlgebraicGeometry.PolarizedFamily

namespace AlgebraicGeometry

open PolarizedFamily

universe u

variable (B : BigFppfSite.{u})

/-- **Stacks 0D44.** Let

```
T  --i-->  T'
|          |
f          g
|          |
v          v
S  --h-->  S'
```

be a pushout in the category of schemes, of schemes of the big fppf site, where `T ⟶ T'` is a
thickening and `T ⟶ S` is affine. Then the functor on fibre categories of the stack of polarized
schemes

`𝒫olarized_{S'} ⟶ 𝒫olarized_S ×_{𝒫olarized_T} 𝒫olarized_{T'}`

is an equivalence. (The source states the lemma "in Situation 08KB"; that situation fixes data
which the statement does not use.) -/
@[stacks 0D44 "the comparison functor `polarizedPushoutRestriction` of a pushout square of \
schemes with `T ⟶ T'` a thickening and `T ⟶ S` affine is an equivalence"]
theorem isEquivalence_polarizedPushoutRestriction {T T' S S' : B.Schemes} (i : T ⟶ T')
    (f : T ⟶ S) (g : T' ⟶ S') (h : S ⟶ S') (hsq : f ≫ h = i ≫ g)
    (hpush : IsPushout (B.inclusion.map f) (B.inclusion.map i) (B.inclusion.map h)
      (B.inclusion.map g))
    (hi : IsThickening (B.inclusion.map i)) [IsAffineHom (B.inclusion.map f)] :
    (polarizedPushoutRestriction B i f g h hsq).IsEquivalence := by
  have := hasPushout_of_isThickening (B.inclusion.map i) (B.inclusion.map f) hi
  let e := hpush.flip.isoPushout.symm
  have hg : pushout.inl (B.inclusion.map i) (B.inclusion.map f) ≫ e.hom = B.inclusion.map g :=
    hpush.flip.inl_isoPushout_inv
  have hh : pushout.inr (B.inclusion.map i) (B.inclusion.map f) ≫ e.hom = B.inclusion.map h :=
    hpush.flip.inr_isoPushout_inv
  have hcart : ∀ {x y : PolarizedFamily B} {k : x.base ⟶ y.base} (φ : x ⟶ y),
      φ.baseMap = k → (polarizedProjection B).IsCartesian k φ := by
    intro x y k φ hk
    subst hk
    have : (polarizedProjection B).IsHomLift φ.baseMap φ :=
      IsHomLift.map (polarizedProjection B) φ
    have := polarizedProjection_isFiberedInGroupoids_unconditional.isStronglyCartesian_homLift
      (p := polarizedProjection B) φ.baseMap φ
    infer_instance
  have hbase : ∀ {x y : PolarizedFamily B} {k : x.base ⟶ y.base} {φ : x ⟶ y},
      (polarizedProjection B).IsHomLift k φ → φ.baseMap = k := by
    intro x y k φ hφ
    have h₀ := IsHomLift.fac' (polarizedProjection B) k φ
    change φ.baseMap = eqToHom rfl ≫ k ≫ eqToHom rfl at h₀
    simpa using h₀
  refine Functor.isEquivalence_fiberSquareRestriction (polarizedProjection B) i f g h hsq ?_ ?_
  · rintro ⟨x, hx⟩
    change x.base = S' at hx
    subst hx
    have hq : (x.toBase ≫ e.inv) ≫ e.hom = x.toBase := by
      rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    refine ⟨cubeTarget i f x h e _ hh hq, cubeAmbient i f x g e _ hg hq,
      cubeCommon i f x g h e _ hsq hg hh hq, cubeTargetHom i f x h e _ hh hq,
      cubeAmbientHom i f x g e _ hg hq, cubeCommonToTarget i f x g h e _ hsq hg hh hq,
      cubeCommonToAmbient i f x g h e _ hsq hg hh hq, hcart _ rfl, hcart _ rfl,
      IsHomLift.map (polarizedProjection B) (cubeCommonToTarget i f x g h e _ hsq hg hh hq),
      IsHomLift.map (polarizedProjection B) (cubeCommonToAmbient i f x g h e _ hsq hg hh hq),
      cubeCommonToTarget_comp_cubeTargetHom i f x g h e _ hsq hg hh hq, ?_⟩
    rintro ⟨⟨yb, yt, ytb, yp, yfl, yfp, yl, yi, ya⟩, hy⟩ α β hα hβ hαβ
    change yb = x.base at hy
    subst hy
    let y : PolarizedFamily B := ⟨x.base, yt, ytb, yp, yfl, yfp, yl, yi, ya⟩
    have hαb : α.baseMap = h ≫ eqToHom rfl := by simpa using hbase hα
    have hβb : β.baseMap = g ≫ eqToHom rfl := by simpa using hbase hβ
    obtain ⟨φ, ⟨hφb, hφ₁, hφ₂⟩, huniq⟩ :=
      existsUnique_glue_hom i f x g h e _ hsq hg hh hq hi (y := y) rfl α β hαb hβb hαβ
    rw [eqToHom_refl] at hφb
    refine ⟨⟨φ, (hcart φ hφb).toIsHomLift⟩, ⟨hφ₁, hφ₂⟩, ?_⟩
    rintro ⟨ψ, hψ⟩ ⟨hψ₁, hψ₂⟩
    have hψb : ψ.baseMap = eqToHom rfl := by simpa using hbase hψ
    have := huniq ψ ⟨hψb, hψ₁, hψ₂⟩
    subst this
    rfl
  · rintro ⟨xS, hS⟩ ⟨xT', hT'⟩ xT u v hu hv
    change xS.base = S at hS
    change xT'.base = T' at hT'
    subst hS hT'
    have : (polarizedProjection B).IsHomLift f u := hu.toIsHomLift
    have : (polarizedProjection B).IsHomLift i v := hv.toIsHomLift
    have hT : xT.base = T := IsHomLift.domain_eq (polarizedProjection B) f u
    subst hT
    have hub : u.baseMap = f := hbase hu.toIsHomLift
    have hvb : v.baseMap = i := hbase hv.toIsHomLift
    obtain ⟨⟨ab, at', atb, ap, afl, afp, al, ai, aa⟩, ha, μ, ν, hμ, hν, huv⟩ :=
      exists_glue_family i f g h hsq hi e hg hh u v hub hvb
    change ab = S' at ha
    subst ha
    rw [eqToHom_refl, Category.comp_id] at hμ hν
    exact ⟨⟨_, rfl⟩, μ, ν, hcart μ hμ, hcart ν hν, huv⟩

end AlgebraicGeometry

end
