module

public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomDescentCocycle
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiAffineFlatBaseChange

/-!
# Descent of the affine hull of a quasi-affine descent datum

Let `Q : Sc ⟶ Sa` be a flat surjection of affine schemes and let `w : Sv ⟶ Sc` be a *quasi-affine*
morphism carrying a descent datum relative to `Q`. This file descends the datum on global
sections: there is a ring `C` under `Γ(Sa)` and inside `Γ(Sv)` with `Γ(Sv)` the pushout of
`Γ(Sc) ← Γ(Sa) → C`, that is, `Spec Γ(Sv) = Sc ×_{Sa} Spec C`. In words, the affine hull of the
datum descends, and `Spec C` is the affine hull of the object which the datum would descend to.

## Main results

* `AlgebraicGeometry.exists_descentPushout_of_isQuasiAffineHom`: **the affine hull of a
  quasi-affine descent datum descends.** A descent datum of quasi-affine schemes along a flat
  surjection of affine schemes, presented by its action and the cocycle identity, produces a ring
  `C` under `Γ(Sa)` and injectively over `Γ(Sv)` with `Γ(Sv) = Γ(Sc) ⊗_{Γ(Sa)} C`, whose elements
  are invariant under the datum.
* `AlgebraicGeometry.Space.exists_descentSquares_of_presheaf`: the representing object of a
  representable morphism and the two fibre products of its descent datum, for an *arbitrary*
  property `P` of morphisms of schemes.
* `AlgebraicGeometry.Space.exists_descentHullPushout_of_isPullback`: a Cartesian square of
  presheaves whose base change along an affine chart of an affine base object is representable by
  a quasi-affine morphism produces the representing object `v` over `c`, the datum's action on it,
  and the descended algebra `C` over `Γ(a)` with `Γ(v) = Γ(c) ⊗_{Γ(a)} C` invariant under that
  action.

## References

* [Stacks Project, Tag 0245](https://stacks.math.columbia.edu/tag/0245)
* [Stacks Project, Tag 0247](https://stacks.math.columbia.edu/tag/0247)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 01SM](https://stacks.math.columbia.edu/tag/01SM)
-/


@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CommRingCat

namespace AlgebraicGeometry

/-! ### The descended algebra of a quasi-affine datum -/

/-- **A descent datum of quasi-affine schemes along a flat surjection of affine schemes descends
on global sections.** Let `Q : Sc ⟶ Sa` be a flat surjection of affine schemes, let `w : Sv ⟶ Sc`
be quasi-affine, let `P₁` present `Sv ×_{Sa} Sc`, let `P₂` present `Sc ×_{Sa} Sv` and let `W`
present `Sc ×_{Sa} P₂`. Suppose given the descent datum in the form of its action `s : P₂ ⟶ Sv`
over the first projection, the isomorphism `φ : P₁ ≅ P₂` it induces, and the two morphisms
`l, l' : W ⟶ P₂` of the cocycle condition, which `s` carries to the same morphism `W ⟶ Sv`. Then
there is a ring `C` under `Γ(Sa)` and injectively over `Γ(Sv)`, with `Γ(Sv)` the pushout of
`Γ(Sc) ← Γ(Sa) → C`, i.e. `Spec Γ(Sv) = Sc ×_{Sa} Spec C`, and the image of `C` in `Γ(Sv)` is
invariant under the datum: the action `s` and the projection `ρ₂` restrict to the same map on
it. -/
theorem exists_descentPushout_of_isQuasiAffineHom
    {Sa Sc Sv P₁ P₂ W : Scheme.{u}} [IsAffine Sa] [IsAffine Sc]
    {Q : Sc ⟶ Sa} {w : Sv ⟶ Sc} (hQs : Surjective Q) (hQf : Flat Q)
    (hw : IsQuasiAffineHom w)
    {π₁ : P₁ ⟶ Sv} {π₂ : P₁ ⟶ Sc} (sq₁ : IsPullback π₁ π₂ (w ≫ Q) Q)
    {ρ₁ : P₂ ⟶ Sc} {ρ₂ : P₂ ⟶ Sv} (sq₂ : IsPullback ρ₁ ρ₂ Q (w ≫ Q))
    {ω₁ : W ⟶ Sc} {ω₂ : W ⟶ P₂} (sq₃ : IsPullback ω₁ ω₂ Q (ρ₁ ≫ Q))
    {s : P₂ ⟶ Sv} {φ : P₁ ≅ P₂}
    (hs₁ : s ≫ w = ρ₁) (hφ₁ : φ.inv ≫ π₁ = s) (hφ₂ : φ.inv ≫ π₂ = ρ₂ ≫ w)
    {l l' : W ⟶ P₂}
    (hl₁ : l ≫ ρ₁ = ω₁) (hl₂ : l ≫ ρ₂ = ω₂ ≫ s)
    (hl₁' : l' ≫ ρ₁ = ω₁) (hl₂' : l' ≫ ρ₂ = ω₂ ≫ ρ₂)
    (hcoc : l ≫ s = l' ≫ s) :
    ∃ (C : CommRingCat.{u}) (k : Γ(Sa, ⊤) ⟶ C) (p : C ⟶ Γ(Sv, ⊤)),
      Function.Injective p.hom ∧ IsPushout Q.appTop k w.appTop p ∧
        p ≫ s.appTop = p ≫ ρ₂.appTop := by
  have := hQf
  have := hw
  have hSv : Scheme.IsQuasiAffine Sv := (isQuasiAffineHom_iff_isQuasiAffine w).1 hw
  have : CompactSpace Sv := inferInstance
  have : QuasiSeparatedSpace Sv := inferInstance
  have hQqa : IsQuasiAffineHom Q :=
    isQuasiAffineHom_of_isQuasiAffine Q inferInstance inferInstance
  have hρ₁ : IsQuasiAffineHom ρ₁ :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback sq₂.flip
      (MorphismProperty.comp_mem (@IsQuasiAffineHom) w Q hw hQqa)
  have hP₂ : Scheme.IsQuasiAffine P₂ := (isQuasiAffineHom_iff_isQuasiAffine ρ₁).1 hρ₁
  have : CompactSpace P₂ := inferInstance
  have : QuasiSeparatedSpace P₂ := inferInstance
  let _ : Algebra ↥Γ(Sa, ⊤) ↥Γ(Sc, ⊤) := Q.appTop.hom.toAlgebra
  let _ : Algebra ↥Γ(Sc, ⊤) ↥Γ(Sv, ⊤) := w.appTop.hom.toAlgebra
  let _ : Algebra ↥Γ(Sa, ⊤) ↥Γ(Sv, ⊤) := (w ≫ Q).appTop.hom.toAlgebra
  have : IsScalarTower ↥Γ(Sa, ⊤) ↥Γ(Sc, ⊤) ↥Γ(Sv, ⊤) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hQ' : (ofHom (algebraMap ↥Γ(Sa, ⊤) ↥Γ(Sc, ⊤)) : Γ(Sa, ⊤) ⟶ Γ(Sc, ⊤)) = Q.appTop := rfl
  have hW' : (ofHom (algebraMap ↥Γ(Sc, ⊤) ↥Γ(Sv, ⊤)) : Γ(Sc, ⊤) ⟶ Γ(Sv, ⊤)) = w.appTop := rfl
  have hWQ' : (ofHom (algebraMap ↥Γ(Sa, ⊤) ↥Γ(Sv, ⊤)) : Γ(Sa, ⊤) ⟶ Γ(Sv, ⊤))
      = (w ≫ Q).appTop := rfl
  have po₁ := isPushout_appTop_of_flat sq₁
  have po₂ := (isPushout_appTop_of_flat sq₂.flip).flip
  have po₃ := (isPushout_appTop_of_flat sq₃.flip).flip
  rw [← hWQ', ← hQ'] at po₁
  rw [← hWQ', ← hQ'] at po₂
  rw [Scheme.Hom.comp_appTop, ← hQ'] at po₃
  have happIso : (Scheme.appTopIso φ).hom = φ.inv.appTop := rfl
  have hsapp : π₁.appTop ≫ φ.inv.appTop = s.appTop := by
    rw [← Scheme.Hom.comp_appTop, hφ₁]
  have h1 : (ofHom (algebraMap ↥Γ(Sc, ⊤) ↥Γ(Sv, ⊤)) : Γ(Sc, ⊤) ⟶ Γ(Sv, ⊤)) ≫
      π₁.appTop ≫ (Scheme.appTopIso φ).hom = ρ₁.appTop := by
    rw [hW', happIso, hsapp, ← Scheme.Hom.comp_appTop, hs₁]
  have h2 : π₂.appTop ≫ (Scheme.appTopIso φ).hom
      = (ofHom (algebraMap ↥Γ(Sc, ⊤) ↥Γ(Sv, ⊤)) : Γ(Sc, ⊤) ⟶ Γ(Sv, ⊤)) ≫ ρ₂.appTop := by
    rw [hW', happIso, ← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, hφ₂]
  have hΛ₁ : ρ₁.appTop ≫ l.appTop = ω₁.appTop := by
    rw [← Scheme.Hom.comp_appTop, hl₁]
  have hΛ₂ : ρ₂.appTop ≫ l.appTop = (π₁.appTop ≫ (Scheme.appTopIso φ).hom) ≫ ω₂.appTop := by
    rw [happIso, hsapp, ← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, hl₂]
  have hΛ₁' : ρ₁.appTop ≫ l'.appTop = ω₁.appTop := by
    rw [← Scheme.Hom.comp_appTop, hl₁']
  have hΛ₂' : ρ₂.appTop ≫ l'.appTop = ρ₂.appTop ≫ ω₂.appTop := by
    rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, hl₂']
  have hcocr : (π₁.appTop ≫ (Scheme.appTopIso φ).hom) ≫ l.appTop
      = (π₁.appTop ≫ (Scheme.appTopIso φ).hom) ≫ l'.appTop := by
    rw [happIso, hsapp, ← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, hcoc]
  obtain ⟨τ, hτ, hinv, hkey⟩ := exists_transition_unitCoassoc_of_isPushout po₁ po₂ po₃
    (Scheme.appTopIso φ) h1 h2 hΛ₁ hΛ₂ hΛ₁' hΛ₂' hcocr
  have hff : Module.FaithfullyFlat ↥Γ(Sa, ⊤) ↥Γ(Sc, ⊤) :=
    RingHom.faithfullyFlat_algebraMap_iff.1 (faithfullyFlat_appTop_of_flat_of_surjective Q)
  have hbij := ModuleCat.bijective_productMap_descentInvariants_of_unitCoassoc
    ↥Γ(Sa, ⊤) ↥Γ(Sc, ⊤) ↥Γ(Sv, ⊤) τ hτ hkey
  refine ⟨CommRingCat.of ↥(ModuleCat.descentInvariants ↥Γ(Sa, ⊤) ↥Γ(Sc, ⊤) ↥Γ(Sv, ⊤) τ),
    ofHom (algebraMap ↥Γ(Sa, ⊤)
      ↥(ModuleCat.descentInvariants ↥Γ(Sa, ⊤) ↥Γ(Sc, ⊤) ↥Γ(Sv, ⊤) τ)),
    ofHom (ModuleCat.descentInvariants ↥Γ(Sa, ⊤) ↥Γ(Sc, ⊤) ↥Γ(Sv, ⊤) τ).val.toRingHom,
    Subtype.val_injective, ?_, ?_⟩
  · refine (CommRingCat.isPushout_tensorProduct ↥Γ(Sa, ⊤) ↥Γ(Sc, ⊤)
        ↥(ModuleCat.descentInvariants ↥Γ(Sa, ⊤) ↥Γ(Sc, ⊤) ↥Γ(Sv, ⊤) τ)).of_iso
      (Iso.refl _) (Iso.refl _) (Iso.refl _)
      ((AlgEquiv.ofBijective _ hbij).toRingEquiv.toCommRingCatIso) ?_ ?_ ?_ ?_
    · rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp, hQ']
    · simp
    · rw [Iso.refl_hom, Category.id_comp, ← hW']
      ext x
      change (AlgEquiv.ofBijective _ hbij) (x ⊗ₜ[↥Γ(Sa, ⊤)] (1 : _)) = _
      change Algebra.TensorProduct.productMap _ _ (x ⊗ₜ[↥Γ(Sa, ⊤)] (1 : _)) = _
      rw [Algebra.TensorProduct.productMap_apply_tmul, map_one, mul_one]
      rfl
    · rw [Iso.refl_hom, Category.id_comp]
      ext x
      change Algebra.TensorProduct.productMap _ _ ((1 : ↥Γ(Sc, ⊤)) ⊗ₜ[↥Γ(Sa, ⊤)] x) = _
      rw [Algebra.TensorProduct.productMap_apply_tmul, map_one, one_mul]
      rfl
  · have hsχ : π₁.appTop ≫ (Scheme.appTopIso φ).hom = s.appTop := by
      rw [happIso, hsapp]
    ext x
    have hx := hinv x.val x.2
    rw [hsχ] at hx
    exact hx

namespace Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}
    {a c : BigFppfOver B S hS} {h : yoneda.obj a ⟶ Y} {q : c ⟶ a}
    {A₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {m : A₀ ⟶ X} {r : A₀ ⟶ yoneda.obj c}

/-! ### The fibre products of a representable morphism's descent datum -/

/-- **The two fibre products of a representable morphism's descent datum, from representability
alone.** Let `r : A₀ ⟶ yoneda.obj c` be representable with all of its represented base changes
carrying a property `P` of morphisms of schemes. Then there are an object `v` of the site, a
morphism `w : v ⟶ c` carrying `P`, an isomorphism `A₀ ≅ yoneda.obj v` identifying `r` with `w`,
and objects `P₁` and `P₂` presenting the fibre products `v ×_a c` and `c ×_a v`. -/
theorem exists_descentSquares_of_presheaf {P : MorphismProperty Scheme.{u}}
    (hr : (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf r) :
    ∃ (v : BigFppfOver B S hS) (w : v ⟶ c) (e : A₀ ≅ yoneda.obj v),
      P ((BigFppfOver.toScheme B S hS).map w) ∧
      e.hom ≫ yoneda.map w = r ∧
      ∃ (P₁ P₂ : BigFppfOver B S hS) (π₁ : P₁ ⟶ v) (π₂ : P₁ ⟶ c)
        (ρ₁ : P₂ ⟶ c) (ρ₂ : P₂ ⟶ v),
        IsPullback π₁ π₂ (w ≫ q) q ∧ IsPullback ρ₁ ρ₂ q (w ≫ q) := by
  have hrep := hr.rep
  have hsq : IsPullback (pullback.fst q q) (pullback.snd q q) q q := IsPullback.of_hasPullback q q
  have b₁ := isPullback_descentBaseChange hrep (pullback.fst q q)
  have b₂ := isPullback_descentBaseChange hrep (pullback.snd q q)
  exact ⟨_, hrep.snd (𝟙 (yoneda.obj c)), descentObjIso hrep,
    hr.property_snd (𝟙 (yoneda.obj c)), descentObjIso_hom_comp hrep, _, _, _, _, _, _,
    (b₁.flip.paste_horiz hsq.flip).flip, b₂.flip.paste_horiz hsq⟩

/-! ### The descended affine hull over an affine chart -/

/-- **Descent of the affine hull of a quasi-affine datum over an affine chart.** Let
`f : X ⟶ Y` be a morphism of presheaves on the big fppf site of `S`, let `h : yoneda.obj a ⟶ Y`
with `a` affine, let `q : c ⟶ a` be a flat surjection of the site with `c` affine, and let `m, r`
present `A₀` as the base change of `f` along `yoneda.map q ≫ h`, with `r` representable by a
quasi-affine morphism. Then `A₀` is represented by an object `v` quasi-affine over `c`, the datum
has an action `s : c ×_a v ⟶ v` over the first projection whose composite to `X` agrees with that
of the second projection `ρ₂`, and there is a ring `C` under `Γ(a)` and injectively over `Γ(v)`
with `Γ(v)` the pushout of `Γ(c) ← Γ(a) → C`, that is, `Spec Γ(v) = c ×_a Spec C`, on which `s`
and `ρ₂` induce the same map. -/
theorem exists_descentHullPushout_of_isPullback
    (sq : IsPullback m r f (yoneda.map q ≫ h))
    (hr : (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsQuasiAffineHom.{u})
      (BigFppfOver.toScheme B S hS)).presheaf r)
    (ha : IsAffine ((BigFppfOver.toScheme B S hS).obj a))
    (hc : IsAffine ((BigFppfOver.toScheme B S hS).obj c))
    (hqs : Surjective ((BigFppfOver.toScheme B S hS).map q))
    (hqf : Flat ((BigFppfOver.toScheme B S hS).map q)) :
    ∃ (v : BigFppfOver B S hS) (w : v ⟶ c) (e : A₀ ≅ yoneda.obj v),
      _root_.AlgebraicGeometry.IsQuasiAffineHom ((BigFppfOver.toScheme B S hS).map w) ∧
      e.hom ≫ yoneda.map w = r ∧
      ∃ (P : BigFppfOver B S hS) (ρ₁ : P ⟶ c) (ρ₂ s : P ⟶ v),
        IsPullback ρ₁ ρ₂ q (w ≫ q) ∧ s ≫ w = ρ₁ ∧
        yoneda.map s ≫ e.inv ≫ m = yoneda.map ρ₂ ≫ e.inv ≫ m ∧
        ∃ (C : CommRingCat.{u}) (k : Γ((BigFppfOver.toScheme B S hS).obj a, ⊤) ⟶ C)
          (p : C ⟶ Γ((BigFppfOver.toScheme B S hS).obj v, ⊤)),
          Function.Injective p.hom ∧
          IsPushout ((BigFppfOver.toScheme B S hS).map q).appTop k
            ((BigFppfOver.toScheme B S hS).map w).appTop p ∧
          p ≫ ((BigFppfOver.toScheme B S hS).map s).appTop
            = p ≫ ((BigFppfOver.toScheme B S hS).map ρ₂).appTop := by
  obtain ⟨v, w, e, hwqa, hew, P₁, P₂, π₁, π₂, ρ₁, ρ₂, s, φ, sq₁, sq₂, hs₁, hs₂, hφ₁, hφ₂⟩ :=
    exists_descentAction_of_isPullback sq hr
  refine ⟨v, w, e, hwqa, hew, P₂, ρ₁, ρ₂, s, sq₂, hs₁, hs₂, ?_⟩
  have vsq : IsPullback (e.inv ≫ m) (yoneda.map w) f (yoneda.map q ≫ h) := by
    refine sq.of_iso e (Iso.refl X) (Iso.refl (yoneda.obj c)) (Iso.refl Y) ?_ ?_ ?_ ?_
    · rw [Iso.refl_hom, Category.comp_id, Iso.hom_inv_id_assoc]
    · rw [Iso.refl_hom, Category.comp_id, hew]
    · simp
    · simp
  obtain ⟨T₀, ω₁, ω₂, sq₃⟩ : ∃ (T₀ : BigFppfOver B S hS) (ω₁ : T₀ ⟶ c) (ω₂ : T₀ ⟶ P₂),
      IsPullback ω₁ ω₂ q (ρ₁ ≫ q) := ⟨_, _, _, IsPullback.of_hasPullback _ _⟩
  have hlift : ∀ t : T₀ ⟶ v, ω₁ ≫ q = t ≫ w ≫ q →
      ∃ l : T₀ ⟶ P₂, l ≫ ρ₁ = ω₁ ∧ l ≫ ρ₂ = t := fun t cond =>
    ⟨sq₂.lift _ _ cond, sq₂.lift_fst _ _ cond, sq₂.lift_snd _ _ cond⟩
  obtain ⟨l, hl₁, hl₂⟩ := hlift (ω₂ ≫ s)
    (by rw [Category.assoc, ← Category.assoc s, hs₁]; exact sq₃.w)
  obtain ⟨l', hl₁', hl₂'⟩ := hlift (ω₂ ≫ ρ₂) (by rw [Category.assoc, ← sq₂.w]; exact sq₃.w)
  have hcoc : l ≫ s = l' ≫ s :=
    descentAction_assoc vsq hs₁ hs₂ hl₁ hl₂ hl₁' hl₂'
  have hav := ha
  have hcv := hc
  set F := BigFppfOver.toScheme B S hS with hF
  have mhφ₁ : (F.mapIso φ).inv ≫ F.map π₁ = F.map s := by simpa using congrArg F.map hφ₁
  have mhφ₂ : (F.mapIso φ).inv ≫ F.map π₂ = F.map ρ₂ ≫ F.map w := by
    simpa using congrArg F.map hφ₂
  exact exists_descentPushout_of_isQuasiAffineHom hqs hqf hwqa (by simpa using sq₁.map F)
    (by simpa using sq₂.map F) (by simpa using sq₃.map F) (by simpa using congrArg F.map hs₁)
    mhφ₁ mhφ₂ (by simpa using congrArg F.map hl₁) (by simpa using congrArg F.map hl₂)
    (by simpa using congrArg F.map hl₁') (by simpa using congrArg F.map hl₂')
    (by simpa using congrArg F.map hcoc)

end Space

end AlgebraicGeometry

end
