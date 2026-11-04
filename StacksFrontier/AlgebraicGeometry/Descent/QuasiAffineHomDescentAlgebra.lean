module

public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomDescentCocycle
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiAffineFlatBaseChange

/-!
# The descended algebra of a quasi-affine descent datum

A descent datum of *affine* schemes along a faithfully flat morphism of affine schemes descends
to a ring: `AlgebraicGeometry.exists_descentPushout_of_isPullback` produces, from the datum
`w : Sv ⟶ Sc` over `Q : Sc ⟶ Sa` together with its groupoid action, a ring `C` under `Γ(Sa)` and
inside `Γ(Sv)` with `Γ(Sv) = Γ(Sc) ⊗_{Γ(Sa)} C`.

That argument asks of `Sv` only that `Γ` turn the three Cartesian squares of the datum into
pushouts of rings, which is flat base change for the sections of the structure sheaf
(`AlgebraicGeometry.isPushout_appTop_of_flat`) and holds for any quasi-compact quasi-separated
`Sv`. This file reads the result on the site: the datum of a *quasi-affine* morphism over an
affine chart descends to a ring `C` under `Γ(a)` and inside `Γ(v)`, presenting `Γ(v)` as
`Γ(c) ⊗_{Γ(a)} C`.

Geometrically `Spec C` is the base of the affine hull: `Spec Γ(v) = c ×_a Spec C`, and the
quasi-affine `v` sits inside `Spec Γ(v)` as a quasi-compact open, by Stacks 01SM part (4). That
is the first step of the proof of Stacks 0247 — the descent of the quasi-coherent algebra
`π_*𝒪_V` — and the open subscheme of `Spec C` which `v` cuts out is the second, carried out in
`StacksFrontier.AlgebraicGeometry.Descent.QuasiAffineHomEffectiveDescent`.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Space.exists_descentDatumAction_of_isPullback`: the descent datum of a
  representable morphism of presheaves together with its groupoid action, for an *arbitrary*
  property of morphisms of schemes. This is
  `AlgebraicGeometry.Space.exists_affineDescentAction_of_isPullback` with its affineness
  hypotheses dropped: neither the comparison isomorphism nor the action uses them. The datum
  alone is `AlgebraicGeometry.Space.exists_descentDatum_of_isPullback`, which this consumes.
* `AlgebraicGeometry.Space.exists_descentPushout_appTop_of_isQuasiAffineHom`: **the descended
  algebra of a quasi-affine descent datum over an affine chart.** A Cartesian square of
  presheaves whose base change along an affine chart is representable by a quasi-affine morphism
  produces the descended algebra `C` over `Γ(a)` with `Γ(v) = Γ(c) ⊗_{Γ(a)} C`, together with
  the action `s` and the equation saying that the action is a morphism over `Spec C`.

## Implementation notes

The three pushout presentations are read off from the three Cartesian squares of the datum in the
orientation in which flat base change applies: the flat affine side is always the chart
`Q : Sc ⟶ Sa`, so the squares `Sc ×_{Sa} Sv` and `Sc ×_{Sa} (Sc ×_{Sa} Sv)` are flipped before
`AlgebraicGeometry.isPushout_appTop_of_flat` is applied and flipped back afterwards.

`Sc ×_{Sa} Sv` is quasi-compact and quasi-separated because its projection to `Sv` is a base
change of the affine morphism `Q`, hence quasi-compact and quasi-separated, and `Sv` is. In the
affine case that object was affine, which is how the earlier argument got the third pushout.

The generality of `AlgebraicGeometry.Space.exists_descentDatumAction_of_isPullback` costs
nothing: `AlgebraicGeometry.Space.exists_descentIso_of_isPullback` and
`AlgebraicGeometry.Space.exists_descentAction` use only the Cartesian square presenting the
datum, so the property carried by the datum is simply transported.

## References

* [Stacks Project, Tag 0245](https://stacks.math.columbia.edu/tag/0245)
* [Stacks Project, Tag 0247](https://stacks.math.columbia.edu/tag/0247)
* [Stacks Project, Tag 01SM](https://stacks.math.columbia.edu/tag/01SM)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CommRingCat

namespace AlgebraicGeometry

/-! ### The descent datum and its action, for an arbitrary property -/

namespace Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}
    {a c : BigFppfOver B S hS} {h : yoneda.obj a ⟶ Y} {q : c ⟶ a}
    {A₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {m : A₀ ⟶ X} {r : A₀ ⟶ yoneda.obj c}

/-- Transport a Cartesian square along an isomorphism `e` with `e.hom ≫ yoneda.map w = r`. -/
private theorem isPullback_inv_comp_of_comp_eq {v : BigFppfOver B S hS} {w : v ⟶ c}
    (sq : IsPullback m r f (yoneda.map q ≫ h)) (e : A₀ ≅ yoneda.obj v)
    (hew : e.hom ≫ yoneda.map w = r) :
    IsPullback (e.inv ≫ m) (yoneda.map w) f (yoneda.map q ≫ h) :=
  sq.of_iso e (Iso.refl X) (Iso.refl (yoneda.obj c)) (Iso.refl Y)
    (by simp) (by simp [hew]) (by simp) (by simp)

/-- **The descent datum of a representable morphism of presheaves, together with its action.**
This is `AlgebraicGeometry.Space.exists_descentDatum_of_isPullback` with the comparison
isomorphism `φ` replaced by the data it comes from: the action `s : P₂ ⟶ v` of the groupoid
`c ×_a c` on `v`, which lies over the first projection `ρ₁` and agrees with the second projection
`ρ₂` over `X`, together with the two triangles identifying `φ.inv` with the pair `(s, ρ₂ ≫ w)`.

This is `AlgebraicGeometry.Space.exists_affineDescentAction_of_isPullback` without its affineness
hypotheses and for an arbitrary `P`. The equation
`yoneda.map s ≫ e.inv ≫ m = yoneda.map ρ₂ ≫ e.inv ≫ m` is what makes the cocycle condition
available through `AlgebraicGeometry.Space.descentAction_assoc`. -/
theorem exists_descentDatumAction_of_isPullback {P : MorphismProperty Scheme.{u}}
    (sq : IsPullback m r f (yoneda.map q ≫ h))
    (hr : (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf r) :
    ∃ (v : BigFppfOver B S hS) (w : v ⟶ c) (e : A₀ ≅ yoneda.obj v),
      P ((BigFppfOver.toScheme B S hS).map w) ∧
      e.hom ≫ yoneda.map w = r ∧
      ∃ (P₁ P₂ : BigFppfOver B S hS) (π₁ : P₁ ⟶ v) (π₂ : P₁ ⟶ c)
        (ρ₁ : P₂ ⟶ c) (ρ₂ s : P₂ ⟶ v) (φ : P₁ ≅ P₂),
        IsPullback π₁ π₂ (w ≫ q) q ∧ IsPullback ρ₁ ρ₂ q (w ≫ q) ∧
        s ≫ w = ρ₁ ∧
        yoneda.map s ≫ e.inv ≫ m = yoneda.map ρ₂ ≫ e.inv ≫ m ∧
        φ.inv ≫ π₁ = s ∧ φ.inv ≫ π₂ = ρ₂ ≫ w := by
  obtain ⟨v, w, e, hwP, hew, P₁, P₂, π₁, π₂, ρ₁, ρ₂, -, sq₁, sq₂, -, -⟩ :=
    exists_descentDatum_of_isPullback sq hr
  have vsq := isPullback_inv_comp_of_comp_eq sq e hew
  obtain ⟨s, hs₁, hs₂⟩ := exists_descentAction vsq ρ₁ ρ₂ sq₂.w
  obtain ⟨s', hs₁', hs₂'⟩ := exists_descentAction vsq π₂ π₁ sq₁.w.symm
  have hcondh : (π₁ ≫ w) ≫ q = s' ≫ w ≫ q := by
    rw [← Category.assoc, hs₁', Category.assoc]
    exact sq₁.w
  have hcondi : s ≫ w ≫ q = (ρ₂ ≫ w) ≫ q := by
    rw [← Category.assoc, hs₁, Category.assoc]
    exact sq₂.w
  have hΦ₁ : sq₂.lift (π₁ ≫ w) s' hcondh ≫ ρ₁ = π₁ ≫ w := sq₂.lift_fst _ _ hcondh
  have hΦ₂ : sq₂.lift (π₁ ≫ w) s' hcondh ≫ ρ₂ = s' := sq₂.lift_snd _ _ hcondh
  have hΦ₃ : sq₁.lift s (ρ₂ ≫ w) hcondi ≫ π₁ = s := sq₁.lift_fst _ _ hcondi
  have hΦ₄ : sq₁.lift s (ρ₂ ≫ w) hcondi ≫ π₂ = ρ₂ ≫ w := sq₁.lift_snd _ _ hcondi
  have hA : sq₂.lift (π₁ ≫ w) s' hcondh ≫ s = π₁ := by
    refine descentAction_unique vsq ?_ ?_
    · rw [Category.assoc, hs₁, hΦ₁]
    · rw [Functor.map_comp, Category.assoc, hs₂, ← Category.assoc, ← Functor.map_comp, hΦ₂, hs₂']
  have hBb : sq₁.lift s (ρ₂ ≫ w) hcondi ≫ s' = ρ₂ := by
    refine descentAction_unique vsq ?_ ?_
    · rw [Category.assoc, hs₁', hΦ₄]
    · rw [Functor.map_comp, Category.assoc, hs₂', ← Category.assoc, ← Functor.map_comp, hΦ₃, hs₂]
  refine ⟨v, w, e, hwP, hew, P₁, P₂, π₁, π₂, ρ₁, ρ₂, s,
    ⟨sq₂.lift (π₁ ≫ w) s' hcondh, sq₁.lift s (ρ₂ ≫ w) hcondi, ?_, ?_⟩, sq₁, sq₂,
    hs₁, hs₂, hΦ₃, hΦ₄⟩
  · refine sq₁.hom_ext ?_ ?_
    · rw [Category.assoc, hΦ₃, hA, Category.id_comp]
    · rw [Category.assoc, hΦ₄, ← Category.assoc, hΦ₂, hs₁', Category.id_comp]
  · refine sq₂.hom_ext ?_ ?_
    · rw [Category.assoc, hΦ₁, ← Category.assoc, hΦ₃, hs₁, Category.id_comp]
    · rw [Category.assoc, hΦ₂, hBb, Category.id_comp]

end Space

/-! ### The descended algebra of a quasi-affine datum on the site -/

namespace Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}
    {a c : BigFppfOver B S hS} {h : yoneda.obj a ⟶ Y} {q : c ⟶ a}
    {A₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {m : A₀ ⟶ X} {r : A₀ ⟶ yoneda.obj c}

/-- **The descended algebra of a quasi-affine descent datum over an affine chart.** Let
`f : X ⟶ Y` be a morphism of presheaves on the big fppf site of `S`, let `h : yoneda.obj a ⟶ Y`
with `a` affine, let `q : c ⟶ a` be a flat surjection of the site with `c` affine, and let `m, r`
present `A₀` as the base change of `f` along `yoneda.map q ≫ h`, with `r` representable by a
quasi-affine morphism. Then the representing object `v` of `A₀` is quasi-affine over `c`, and
there is a ring `C` under `Γ(a)` and inside `Γ(v)` with `Γ(v)` the pushout of
`Γ(c) ← Γ(a) → C`, that is, `Spec Γ(v) = c ×_a Spec C`.

The action `s : P₂ ⟶ v` of the groupoid `c ×_a c` on `v` is returned alongside, with the two
properties that characterise it and with the equation `p ≫ s.appTop = p ≫ ρ₂.appTop` saying that
the action is a morphism over `Spec C`.

This is the quasi-coherent-algebra step of the proof of Stacks 0247: the algebra `π_*𝒪_V` of the
datum, which over an affine chart is the ring `Γ(v)`, descends. The open subscheme of `Spec C`
which `v` cuts out is then cut out in
`StacksFrontier.AlgebraicGeometry.Descent.QuasiAffineHomEffectiveDescent`. -/
theorem exists_descentPushout_appTop_of_isQuasiAffineHom
    (sq : IsPullback m r f (yoneda.map q ≫ h))
    (hr : (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsQuasiAffineHom.{u})
      (BigFppfOver.toScheme B S hS)).presheaf r)
    (ha : IsAffine ((BigFppfOver.toScheme B S hS).obj a))
    (hc : IsAffine ((BigFppfOver.toScheme B S hS).obj c))
    (hqs : Surjective ((BigFppfOver.toScheme B S hS).map q))
    (hqf : Flat ((BigFppfOver.toScheme B S hS).map q)) :
    ∃ (v : BigFppfOver B S hS) (w : v ⟶ c) (e : A₀ ≅ yoneda.obj v),
      Scheme.IsQuasiAffine ((BigFppfOver.toScheme B S hS).obj v) ∧
      _root_.AlgebraicGeometry.IsQuasiAffineHom ((BigFppfOver.toScheme B S hS).map w) ∧
      e.hom ≫ yoneda.map w = r ∧
      ∃ (P₂ : BigFppfOver B S hS) (ρ₁ : P₂ ⟶ c) (ρ₂ s : P₂ ⟶ v),
        IsPullback ρ₁ ρ₂ q (w ≫ q) ∧ s ≫ w = ρ₁ ∧
        yoneda.map s ≫ e.inv ≫ m = yoneda.map ρ₂ ≫ e.inv ≫ m ∧
      ∃ (C : CommRingCat.{u}) (k : Γ((BigFppfOver.toScheme B S hS).obj a, ⊤) ⟶ C)
        (p : C ⟶ Γ((BigFppfOver.toScheme B S hS).obj v, ⊤)),
        Function.Injective p.hom ∧
        p ≫ ((BigFppfOver.toScheme B S hS).map s).appTop =
          p ≫ ((BigFppfOver.toScheme B S hS).map ρ₂).appTop ∧
        IsPushout ((BigFppfOver.toScheme B S hS).map q).appTop k
          ((BigFppfOver.toScheme B S hS).map w).appTop p := by
  obtain ⟨v, w, e, hwqa, hew, P₁, P₂, π₁, π₂, ρ₁, ρ₂, s, φ, sq₁, sq₂,
    hs₁, hs₂, hφ₁, hφ₂⟩ := exists_descentDatumAction_of_isPullback sq hr
  have hvqa : Scheme.IsQuasiAffine ((BigFppfOver.toScheme B S hS).obj v) :=
    (isQuasiAffineHom_iff_isQuasiAffine ((BigFppfOver.toScheme B S hS).map w)).1 hwqa
  refine ⟨v, w, e, hvqa, hwqa, hew, P₂, ρ₁, ρ₂, s, sq₂, hs₁, hs₂, ?_⟩
  have vsq := isPullback_inv_comp_of_comp_eq sq e hew
  obtain ⟨T₀, ω₁, ω₂, sq₃⟩ : ∃ (T₀ : BigFppfOver B S hS) (ω₁ : T₀ ⟶ c) (ω₂ : T₀ ⟶ P₂),
      IsPullback ω₁ ω₂ q (ρ₁ ≫ q) := ⟨_, _, _, IsPullback.of_hasPullback _ _⟩
  have lift : ∀ x : T₀ ⟶ v, ω₁ ≫ q = x ≫ w ≫ q →
      ∃ l : T₀ ⟶ P₂, l ≫ ρ₁ = ω₁ ∧ l ≫ ρ₂ = x :=
    fun x cond => ⟨sq₂.lift _ _ cond, sq₂.lift_fst _ _ cond, sq₂.lift_snd _ _ cond⟩
  obtain ⟨l, hl₁, hl₂⟩ := lift (ω₂ ≫ s) (by
    rw [Category.assoc, ← Category.assoc s, hs₁]
    exact sq₃.w)
  obtain ⟨l', hl₁', hl₂'⟩ := lift (ω₂ ≫ ρ₂) (by
    rw [Category.assoc, ← sq₂.w]
    exact sq₃.w)
  have : CompactSpace ((BigFppfOver.toScheme B S hS).obj v) := hvqa.toCompactSpace
  set F := BigFppfOver.toScheme B S hS
  have msq₁ : IsPullback (F.map π₁) (F.map π₂) (F.map w ≫ F.map q) (F.map q) := by
    rw [← Functor.map_comp]
    exact sq₁.map F
  have msq₂ : IsPullback (F.map ρ₁) (F.map ρ₂) (F.map q) (F.map w ≫ F.map q) := by
    rw [← Functor.map_comp]
    exact sq₂.map F
  have msq₃ : IsPullback (F.map ω₁) (F.map ω₂) (F.map q) (F.map ρ₁ ≫ F.map q) := by
    rw [← Functor.map_comp]
    exact sq₃.map F
  have mhs₁ : F.map s ≫ F.map w = F.map ρ₁ := by rw [← Functor.map_comp, hs₁]
  have mhφ₁ : (F.mapIso φ).inv ≫ F.map π₁ = F.map s := by
    rw [Functor.mapIso_inv, ← Functor.map_comp, hφ₁]
  have mhφ₂ : (F.mapIso φ).inv ≫ F.map π₂ = F.map ρ₂ ≫ F.map w := by
    rw [Functor.mapIso_inv, ← Functor.map_comp, ← Functor.map_comp, hφ₂]
  have mhl₁ : F.map l ≫ F.map ρ₁ = F.map ω₁ := by rw [← Functor.map_comp, hl₁]
  have mhl₂ : F.map l ≫ F.map ρ₂ = F.map ω₂ ≫ F.map s := by
    rw [← Functor.map_comp, ← Functor.map_comp, hl₂]
  have mhl₁' : F.map l' ≫ F.map ρ₁ = F.map ω₁ := by rw [← Functor.map_comp, hl₁']
  have mhl₂' : F.map l' ≫ F.map ρ₂ = F.map ω₂ ≫ F.map ρ₂ := by
    rw [← Functor.map_comp, ← Functor.map_comp, hl₂']
  have mhcoc : F.map l ≫ F.map s = F.map l' ≫ F.map s := by
    rw [← Functor.map_comp, ← Functor.map_comp,
      descentAction_assoc vsq hs₁ hs₂ hl₁ hl₂ hl₁' hl₂']
  exact exists_descentPushout_of_isPullback hqs hqf msq₁ msq₂ msq₃ mhs₁
    mhφ₁ mhφ₂ mhl₁ mhl₂ mhl₁' mhl₂' mhcoc

end Space

end AlgebraicGeometry

end
