module

public import StacksFrontier.AlgebraicGeometry.Descent.DescendedObjectEffectiveDescent
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcQuasiAffine
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiAffineEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiAffineHomDescentAlgebra
public import StacksFrontier.AlgebraicGeometry.Size.FlatSurjective

/-!
# Effective descent for quasi-affine morphisms along a surjective étale chart

`AlgebraicGeometry.Space.IsEffectiveDescentAlongSurjectiveEtale B S hS P` is the one geometric
hypothesis of Stacks 03I2: morphisms of schemes with property `P` descend *effectively* along a
surjective étale morphism of the big fppf site of `S`. **This file discharges it for
`P = AlgebraicGeometry.IsQuasiAffineHom`, outright and with no further hypothesis**, by the
argument of Stacks 0247.

The route is the one of the source. Over an affine chart `q : c ⟶ a` the datum is presented by an
object `v` of the site, quasi-affine over `c`, and `v` sits inside its affine hull `Spec Γ(v)` as
a quasi-compact open, by Stacks 01SM part (4). The algebra `Γ(v)` descends to a ring `C` under
`Γ(a)`, which presents `Spec Γ(v)` as the base change `c ×_a Spec C`; this is descent for
quasi-coherent algebras, and it is
`AlgebraicGeometry.Space.exists_descentPushout_appTop_of_isQuasiAffineHom`. `Spec C` is an object
`o` of the site, affine over `a`. The open subset of `c ×_a o` which is the image of `v` is then
*invariant* under the groupoid of the chart, so its image `V` in `o` is open — the projection
`c ×_a o ⟶ o` is surjective étale, hence an open map — and its preimage is the open again. The
open subscheme `b` of `o` on `V` is the descended object: `v = c ×_a b`, because the two open
immersions `v ⟶ c ×_a o` and `c ×_a b ⟶ c ×_a o` have the same range.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Space.exists_affineHullSiteObject_of_isPushout_appTop`: **the descended
  algebra is an object of the site, and the affine hull of `v` is its base change.** A pushout
  square of rings presenting `Γ(v)` as `Γ(c) ⊗_{Γ(a)} C`, with `C` a subring of `Γ(v)`, comes
  from an object `o` of the site, affine and affine over `a`, with `Spec Γ(v) = c ×_a o` and a
  morphism `t : v ⟶ o` of the site through which `v` maps to its affine hull. The last clause
  records `t` in the one form in which it is used: two morphisms into `v` whose actions on global
  sections agree on `C` agree after `t`.
* `AlgebraicGeometry.Space.exists_affineHullSiteObject_of_isQuasiAffineHom`: the same for a
  quasi-affine descent datum, with the compatibility of the groupoid action with `o`.
* `AlgebraicGeometry.preimage_image_range_eq_range_of_action`: **a subobject of a descent datum
  invariant under the action is saturated.** This is the step of Stacks 0247 which says that the
  quasi-compact open `V ⊆ X ×_S U'` is stable under the datum, so that membership in it depends
  only on the `U'`-coordinate. It is stated for schemes and uses no quasi-affineness.
* `AlgebraicGeometry.Space.presheaf_pullback_snd_isQuasiAffineHom_of_isPullback`: effective
  descent for a quasi-affine datum over an affine chart. This is the geometric content the file
  contributes; the global statement it feeds,
  `AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isQuasiAffineHom`, is proved
  once and for all in `StacksFrontier.AlgebraicGeometry.Descent.QuasiAffineEtaleDescent`, and the
  four equivalent conditions of Stacks 03WM which it unlocks,
  `AlgebraicGeometry.Space.isQuasiAffineHom_tfae_of_isAlgebraicSpace`, in
  `StacksFrontier.AlgebraicGeometry.Spaces.QuasiAffineTfaeComplete`.

## Implementation notes

The size bound putting `Spec C` in the site is Stacks 000R (9), but not in the shape used for an
affine datum: there `Γ(v)` is bounded by `size v` because `⊤` is an affine open, whereas a
quasi-affine `v` is only quasi-compact, and
`AlgebraicGeometry.Scheme.mk_sections_le_two_pow_size` bounds its global sections by
`2 ^ size v`. One power is therefore lost, and it is absorbed by the cutoff being a strong
prelimit: `size v < κ` gives `2 ^ size v < κ`, and `size (Spec C) = max {ℵ₀, #C} < κ`.

The Cartesian square presenting the affine hull is the image under `Spec` of the pushout square
of rings, transported along the canonical isomorphisms of the two *affine* schemes `c` and `a`
with the spectra of their rings of global sections. Unlike the affine case no isomorphism is
needed at the upper-left corner: that corner is `Spec Γ(v)`, and `v` itself is not affine. The
structure morphism of that corner over `c` is `AlgebraicGeometry.specΓToBase`, through which
`v ⟶ c` factors by `AlgebraicGeometry.toSpecΓ_specΓToBase`.

*The invariance step carries no points.* The translate of a point of `Spec Γ(v) ×_o v` is the
morphism to `v` obtained by comparing that fibre product with the groupoid `c ×_a v` — which is
possible exactly because `Spec Γ(v)` is `c ×_a o` — and then applying the action. It lies over
the same point of `o`, because the action is a morphism over `o`, and over the same point of `c`,
because it lies over the first projection; so the two morphisms into `Spec Γ(v)` agree by the
universal property of that fibre product, and the range of `v` already contains the preimage of
its image. The compatibility of the action with `o` is spent here and nowhere else.

*Why `b` is quasi-affine over `a`.* It is an open subscheme of the affine `o`, so it suffices
that it be quasi-compact, and it is the image of the quasi-compact `v` under the surjection
`v ⟶ b` which the Cartesian square `v = c ×_a b` produces from the surjectivity of the chart.

*No tag is carried here.* Stacks 0247 sits on
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isQuasiAffineHom`, the global
statement in `StacksFrontier.AlgebraicGeometry.Descent.QuasiAffineEtaleDescent`; what this file
proves is the affine-chart step of that argument, which is not the tag's assertion.

## References

* [Stacks Project, Tag 0247](https://stacks.math.columbia.edu/tag/0247)
* [Stacks Project, Tag 0245](https://stacks.math.columbia.edu/tag/0245)
* [Stacks Project, Tag 01SM](https://stacks.math.columbia.edu/tag/01SM)
* [Stacks Project, Tag 02W3](https://stacks.math.columbia.edu/tag/02W3)
* [Stacks Project, Tag 02W8](https://stacks.math.columbia.edu/tag/02W8)
* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
* [Stacks Project, Tag 03WL](https://stacks.math.columbia.edu/tag/03WL)
* [Stacks Project, Tag 03WM](https://stacks.math.columbia.edu/tag/03WM)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Cardinal

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}
    {a c v : BigFppfOver B S hS} {h : yoneda.obj a ⟶ Y} {q : c ⟶ a} {w : v ⟶ c}

/-- **The descended algebra is an object of the site, and the affine hull of `v` is its base
change.** Let `q : c ⟶ a` and `w : v ⟶ c` be morphisms of the big fppf site of `S` with `a` and
`c` affine, and let `C` be a ring under `Γ(a)` and inside `Γ(v)` presenting `Γ(v)` as the pushout
`Γ(c) ⊗_{Γ(a)} C`. Then `Spec C` carries an object `o` of the site, affine and affine over `a`
through a morphism `n`, the affine hull `Spec Γ(v)` of `v` is the base change `c ×_a o` through a
morphism `τ`, and `v` maps to `o` through a morphism `t` of the site whose underlying morphism of
schemes is `v ⟶ Spec Γ(v) ⟶ o`.

Moreover `t` is `Spec` of the inclusion `C ⟶ Γ(v)`, in the only form in which that is used: two
morphisms `g₁, g₂ : Z ⟶ v` of the site whose actions on global sections agree on `C` agree after
`t`.

This is `AlgebraicGeometry.Space.exists_site_object_of_isPushout_appTop` with the affineness of
`v` removed; the corner of the Cartesian square becomes the affine hull of `v` rather than `v`
itself, and the size bound passes through
`AlgebraicGeometry.Scheme.mk_sections_le_two_pow_size`. -/
theorem exists_affineHullSiteObject_of_isPushout_appTop
    (ha : IsAffine ((BigFppfOver.toScheme B S hS).obj a))
    (hc : IsAffine ((BigFppfOver.toScheme B S hS).obj c))
    {C : CommRingCat.{u}} {k : Γ((BigFppfOver.toScheme B S hS).obj a, ⊤) ⟶ C}
    {p : C ⟶ Γ((BigFppfOver.toScheme B S hS).obj v, ⊤)}
    (hpinj : Function.Injective p.hom)
    (hpo : IsPushout ((BigFppfOver.toScheme B S hS).map q).appTop k
      ((BigFppfOver.toScheme B S hS).map w).appTop p) :
    ∃ (o : BigFppfOver B S hS) (n : o ⟶ a) (t : v ⟶ o)
      (τ : Spec Γ((BigFppfOver.toScheme B S hS).obj v, ⊤) ⟶
        (BigFppfOver.toScheme B S hS).obj o),
      IsAffine ((BigFppfOver.toScheme B S hS).obj o) ∧
      _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map n) ∧
      IsPullback (specΓToBase ((BigFppfOver.toScheme B S hS).map w)) τ
        ((BigFppfOver.toScheme B S hS).map q) ((BigFppfOver.toScheme B S hS).map n) ∧
      ((BigFppfOver.toScheme B S hS).obj v).toSpecΓ ≫ τ =
        (BigFppfOver.toScheme B S hS).map t ∧
      ∀ {Z : BigFppfOver B S hS} (g₁ g₂ : Z ⟶ v),
        p ≫ ((BigFppfOver.toScheme B S hS).map g₁).appTop =
          p ≫ ((BigFppfOver.toScheme B S hS).map g₂).appTop → g₁ ≫ t = g₂ ≫ t := by
  have := ha; have := hc
  have hmk : Cardinal.mk C ≤ 2 ^ ((BigFppfOver.toScheme B S hS).obj v).size :=
    (Cardinal.mk_le_of_injective hpinj).trans
      (Scheme.mk_sections_le_two_pow_size ((BigFppfOver.toScheme B S hS).obj v) ⊤)
  have hCsize : B.Contains (Spec C) :=
    (Scheme.size_Spec C).trans_lt
      (max_lt B.aleph0_lt_cutoff (hmk.trans_lt (B.cutoff_isStrongPrelimit v.left.2)))
  have hsep : ∀ {Z : BigFppfOver B S hS} (g₁ g₂ : Z ⟶ v),
      p ≫ ((BigFppfOver.toScheme B S hS).map g₁).appTop =
        p ≫ ((BigFppfOver.toScheme B S hS).map g₂).appTop →
      (BigFppfOver.toScheme B S hS).map g₁ ≫
          (((BigFppfOver.toScheme B S hS).obj v).toSpecΓ ≫ Spec.map p) =
        (BigFppfOver.toScheme B S hS).map g₂ ≫
          (((BigFppfOver.toScheme B S hS).obj v).toSpecΓ ≫ Spec.map p) := by
    intro Z g₁ g₂ hg
    rw [Scheme.toSpecΓ_naturality_assoc, Scheme.toSpecΓ_naturality_assoc,
      ← Spec.map_comp, ← Spec.map_comp, hg]
  have sqSpec : IsPullback (specΓToBase ((BigFppfOver.toScheme B S hS).map w)) (Spec.map p)
      ((BigFppfOver.toScheme B S hS).map q)
      (Spec.map k ≫ ((BigFppfOver.toScheme B S hS).obj a).isoSpec.inv) := by
    refine (hpo.op.map Scheme.Spec).flip.of_iso'
      (Iso.refl (Spec Γ((BigFppfOver.toScheme B S hS).obj v, ⊤)))
      ((BigFppfOver.toScheme B S hS).obj c).isoSpec (Iso.refl (Spec C))
      ((BigFppfOver.toScheme B S hS).obj a).isoSpec ?_ ?_
      (Scheme.isoSpec_hom_naturality ((BigFppfOver.toScheme B S hS).map q)) ?_
    · rw [Iso.refl_hom, Category.id_comp, specΓToBase, Category.assoc, Iso.inv_hom_id,
        Category.comp_id]
      rfl
    · rw [Iso.refl_hom, Iso.refl_hom, Category.id_comp, Category.comp_id]
      rfl
    · rw [Iso.refl_hom, Category.id_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]
      rfl
  obtain ⟨n, hn⟩ := BigFppfOver.exists_hom_of_comp_eq B S hS
    (X := BigFppfOver.mk B S hS hCsize
      ((Spec.map k ≫ ((BigFppfOver.toScheme B S hS).obj a).isoSpec.inv) ≫
        B.inclusion.map a.hom))
    (Y := a) (Spec.map k ≫ ((BigFppfOver.toScheme B S hS).obj a).isoSpec.inv) rfl
  have hwt : (((BigFppfOver.toScheme B S hS).obj v).toSpecΓ ≫ Spec.map p) ≫
      ((Spec.map k ≫ ((BigFppfOver.toScheme B S hS).obj a).isoSpec.inv) ≫
        B.inclusion.map a.hom) = B.inclusion.map v.hom := by
    rw [Category.assoc, ← Category.assoc (Spec.map p), ← sqSpec.w, Category.assoc,
      BigFppfOver.toScheme_map_comp_hom q, ← Category.assoc,
      toSpecΓ_specΓToBase ((BigFppfOver.toScheme B S hS).map w),
      BigFppfOver.toScheme_map_comp_hom w]
  have hoaff : IsAffine ((BigFppfOver.toScheme B S hS).obj (BigFppfOver.mk B S hS hCsize
      ((Spec.map k ≫ ((BigFppfOver.toScheme B S hS).obj a).isoSpec.inv) ≫
        B.inclusion.map a.hom))) := inferInstanceAs (IsAffine (Spec C))
  refine ⟨_, n, BigFppfOver.homMk B S hS hCsize _
    (((BigFppfOver.toScheme B S hS).obj v).toSpecΓ ≫ Spec.map p) hwt, Spec.map p,
    hoaff, ?_, ?_, ?_, ?_⟩
  · rw [hn]
    exact _root_.AlgebraicGeometry.isAffineHom_of_isAffine _
  · rw [hn]
    exact sqSpec
  · exact (BigFppfOver.toScheme_map_homMk B S hS hCsize _ _ hwt).symm
  · intro Z g₁ g₂ hg
    refine (BigFppfOver.toScheme B S hS).map_injective ?_
    rw [Functor.map_comp, Functor.map_comp, BigFppfOver.toScheme_map_homMk]
    exact hsep g₁ g₂ hg

variable {A₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {m : A₀ ⟶ X} {r : A₀ ⟶ yoneda.obj c}

/-- **The descended affine hull of a quasi-affine descent datum over an affine chart.** Let
`f : X ⟶ Y` be a morphism of presheaves on the big fppf site of `S`, let `h : yoneda.obj a ⟶ Y`
with `a` affine, let `q : c ⟶ a` be a flat surjection of the site with `c` affine, and let `m, r`
present `A₀` as the base change of `f` along `yoneda.map q ≫ h`, with `r` representable by a
quasi-affine morphism.

Then the datum is presented by an object `v` of the site, quasi-affine over `c`, and there is an
object `o` of the site, affine over `a` through `n`, such that the affine hull `Spec Γ(v)` of `v`
is the base change `c ×_a o` and the morphism `v ⟶ Spec Γ(v) ⟶ o` is a morphism `t` of the site
over which the groupoid action `s` of the chart on `v` is a morphism, that is, `s ≫ t = ρ₂ ≫ t`.

This is the whole input which the proof of Stacks 0247 takes from descent for quasi-coherent
algebras: the base `o` of the relative spectrum of the algebra of the datum descends, and the
action acts trivially on it. What remains of 0247 is the open subscheme of `o` cut out by the
quasi-compact open immersion `v ⟶ Spec Γ(v)` of Stacks 01SM part (4). -/
theorem exists_affineHullSiteObject_of_isQuasiAffineHom
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
      ∃ (o : BigFppfOver B S hS) (n : o ⟶ a) (t : v ⟶ o)
        (τ : Spec Γ((BigFppfOver.toScheme B S hS).obj v, ⊤) ⟶
          (BigFppfOver.toScheme B S hS).obj o),
        IsAffine ((BigFppfOver.toScheme B S hS).obj o) ∧
        _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map n) ∧
        IsPullback (specΓToBase ((BigFppfOver.toScheme B S hS).map w)) τ
          ((BigFppfOver.toScheme B S hS).map q) ((BigFppfOver.toScheme B S hS).map n) ∧
        ((BigFppfOver.toScheme B S hS).obj v).toSpecΓ ≫ τ =
          (BigFppfOver.toScheme B S hS).map t ∧
        ∃ (P₂ : BigFppfOver B S hS) (ρ₁ : P₂ ⟶ c) (ρ₂ s : P₂ ⟶ v),
          IsPullback ρ₁ ρ₂ q (w ≫ q) ∧ s ≫ w = ρ₁ ∧
          yoneda.map s ≫ e.inv ≫ m = yoneda.map ρ₂ ≫ e.inv ≫ m ∧
          s ≫ t = ρ₂ ≫ t := by
  obtain ⟨v, w, e, hvqa, hwqa, hew, P₂, ρ₁, ρ₂, s, sq₂, hs₁, hs₂, C, k, p, hpinj, hpact,
    hpo⟩ := exists_descentPushout_appTop_of_isQuasiAffineHom sq hr ha hc hqs hqf
  obtain ⟨o, n, t, τ, hoaff, hnaff, sqτ, hτt, hsept⟩ :=
    exists_affineHullSiteObject_of_isPushout_appTop ha hc hpinj hpo
  exact ⟨v, w, e, hvqa, hwqa, hew, o, n, t, τ, hoaff, hnaff, sqτ, hτt,
    P₂, ρ₁, ρ₂, s, sq₂, hs₁, hs₂, hsept s ρ₂ hpact⟩

end AlgebraicGeometry.Space

namespace AlgebraicGeometry

/-! ### The open subscheme of the descended object cut out by the datum -/

/-- **A subobject of a descent datum which is invariant under the action is saturated.** Let
```
  Zh --τc--> Zc
  |τ          |mq
  Zo --mn-->  Za
```
be a Cartesian square of schemes, let `σ : Zv ⟶ Zh` be a morphism whose composites with `τc` and
`τ` are `mw : Zv ⟶ Zc` and `mt : Zv ⟶ Zo`, and let `ms : W ⟶ Zv` be an action of the groupoid
`W = Zc ×_{Za} Zv` on `Zv` — a morphism lying over the first projection `mρ₁` which agrees with
the second projection `mρ₂` after `mt`. Then the range of `σ` is saturated for `τ`: the preimage
under `τ` of its image is itself.

This is the invariance step of the proof of Stacks 0247. The translate of a point of
`Zh ×_{Zo} Zv` is the morphism to `Zv` obtained by comparing that fibre product with
`W = Zc ×_{Za} Zv` — which is possible because `Zh` is `Zc ×_{Za} Zo` — and then applying the
action; it lands in the fibre of `τ` over the given point of `Zo`, because the action is a
morphism over `Zo`, and over the given point of `Zc`, because it lies over the first projection.
The two morphisms into `Zh` are then identified by the universal property of the Cartesian
square, so the range of `σ` already contains the preimage. -/
theorem preimage_image_range_eq_range_of_action
    {Za Zc Zv Zo Zh W : Scheme.{u}} {mq : Zc ⟶ Za} {mw : Zv ⟶ Zc} {mn : Zo ⟶ Za} {mt : Zv ⟶ Zo}
    {σ : Zv ⟶ Zh} {τc : Zh ⟶ Zc} {τ : Zh ⟶ Zo}
    (sqτ : IsPullback τc τ mq mn) (hσc : σ ≫ τc = mw) (hστ : σ ≫ τ = mt)
    {mρ₁ : W ⟶ Zc} {mρ₂ ms : W ⟶ Zv}
    (sq₂ : IsPullback mρ₁ mρ₂ mq (mw ≫ mq))
    (hs₁ : ms ≫ mw = mρ₁) (hst : ms ≫ mt = mρ₂ ≫ mt) :
    τ.base ⁻¹' (τ.base '' Set.range σ.base) = Set.range σ.base := by
  -- the image of `Zv` in `Zo` is the range of `mt`
  have himg : τ.base '' Set.range σ.base = Set.range mt.base := by
    rw [← hστ, ← Set.range_comp]
    rfl
  -- the preimage of that image is the range of the projection of `Zh ×_{Zo} Zv`
  have hkcond : pullback.fst τ mt ≫ τ = pullback.snd τ mt ≫ mt := pullback.condition
  have hK : τ.base ⁻¹' Set.range mt.base = Set.range (pullback.fst τ mt).base :=
    (AlgebraicGeometry.range_snd_of_isPullback (IsPullback.of_hasPullback τ mt).flip).symm
  -- the comparison of `Zh ×_{Zo} Zv` with the groupoid `Zc ×_{Za} Zv`
  have hmw : mt ≫ mn = mw ≫ mq := by
    rw [← hσc, ← hστ, Category.assoc, Category.assoc, sqτ.w]
  have cond : (pullback.fst τ mt ≫ τc) ≫ mq = pullback.snd τ mt ≫ (mw ≫ mq) := by
    simp only [Category.assoc, sqτ.w, reassoc_of% hkcond, hmw]
  set ν := sq₂.lift (pullback.fst τ mt ≫ τc) (pullback.snd τ mt) cond
  have hν₁ : ν ≫ mρ₁ = pullback.fst τ mt ≫ τc := sq₂.lift_fst _ _ cond
  have hν₂ : ν ≫ mρ₂ = pullback.snd τ mt := sq₂.lift_snd _ _ cond
  -- the translate lands in the range of `σ`
  have hμ : (ν ≫ ms) ≫ σ = pullback.fst τ mt :=
    sqτ.hom_ext (by simp only [Category.assoc, hσc, hs₁, hν₁])
      (by simp only [Category.assoc, hστ, hst, reassoc_of% hν₂, hkcond])
  refine Set.Subset.antisymm ?_ (Set.subset_preimage_image τ.base _)
  rw [himg, hK, ← hμ]
  rintro _ ⟨x, rfl⟩
  exact ⟨(ν ≫ ms).base x, by simp⟩

end AlgebraicGeometry

namespace AlgebraicGeometry.Space

/-! ### Effective descent for quasi-affine morphisms -/

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}
    {a c : BigFppfOver B S hS} {h : yoneda.obj a ⟶ Y} {q : c ⟶ a}

/-- **Effective descent for quasi-affine morphisms over an affine base, at one datum.** Let
`f : X ⟶ Y` be a morphism of sheaves on the big fppf site of `S`, let `h : yoneda.obj a ⟶ Y` with
`a` affine, let `q : c ⟶ a` be a surjective étale morphism of the site with `c` affine, and let
`m, r` present `A₀` as the base change of `f` along `yoneda.map q ≫ h`, with `r` representable by
a quasi-affine morphism. Then the base change of `f` along `h` is itself representable by a
quasi-affine morphism.

This is the argument of Stacks 0247 after its reduction to a single flat surjection of affines.
The algebra of the datum descends to a ring `C`, by
`AlgebraicGeometry.Space.exists_affineHullSiteObject_of_isQuasiAffineHom`, which presents the
affine hull of `v` as `c ×_a o` for `o = Spec C` an object of the site; the object `v` of the
datum is a quasi-compact open of that affine hull, by Stacks 01SM part (4), and its image `V` in
`o` is open because the projection `c ×_a o ⟶ o` is surjective étale. The image is saturated, by
`AlgebraicGeometry.preimage_image_range_eq_range_of_action`, so the base change to `c` of the
open subscheme `b` of `o` on `V` is again the open of the affine hull whose image is `v` — the
two are open immersions into `c ×_a o` with the same range, hence isomorphic over it, which is
the Cartesian square `v = c ×_a b`. `b` is then the descended object, and
`AlgebraicGeometry.Space.presheaf_pullback_snd_of_descendedObject` concludes. Its structure
morphism to `a` is quasi-affine because `b` is a quasi-compact open subscheme of the affine `o`,
quasi-compactness coming from the surjectivity of `v ⟶ b`. -/
theorem presheaf_pullback_snd_isQuasiAffineHom_of_isPullback
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    (hY : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y)
    (ha : IsAffine ((BigFppfOver.toScheme B S hS).obj a))
    (hc : IsAffine ((BigFppfOver.toScheme B S hS).obj c))
    (hqs : Surjective ((BigFppfOver.toScheme B S hS).map q))
    (hqe : Etale ((BigFppfOver.toScheme B S hS).map q))
    {A₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {m : A₀ ⟶ X} {r : A₀ ⟶ yoneda.obj c}
    (sq : IsPullback m r f (yoneda.map q ≫ h))
    (hr : (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsQuasiAffineHom.{u})
      (BigFppfOver.toScheme B S hS)).presheaf r) :
    (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsQuasiAffineHom.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f h) := by
  obtain ⟨hqf, -, -⟩ := Etale.iff_flat_and_formallyUnramified.1 hqe
  obtain ⟨v, w, e, hvqa, hwqa, hew, o, n, t, τ, hoaff, hnaff, sqτ, hτt,
    P₂, ρ₁, ρ₂, s, sq₂, hs₁, hs₂, hst⟩ :=
    exists_affineHullSiteObject_of_isQuasiAffineHom sq hr ha hc hqs hqf
  have _ := ha; have _ := hc; have _ := hvqa; have _ := hoaff; have _ := hqe
  -- the open subset of the affine hull of `v` which is the image of `v` is saturated for `τ`
  have msq₂ : IsPullback ((BigFppfOver.toScheme B S hS).map ρ₁)
      ((BigFppfOver.toScheme B S hS).map ρ₂) ((BigFppfOver.toScheme B S hS).map q)
      ((BigFppfOver.toScheme B S hS).map w ≫ (BigFppfOver.toScheme B S hS).map q) := by
    rw [← Functor.map_comp]
    exact sq₂.map (BigFppfOver.toScheme B S hS)
  have mhs₁ : (BigFppfOver.toScheme B S hS).map s ≫ (BigFppfOver.toScheme B S hS).map w =
      (BigFppfOver.toScheme B S hS).map ρ₁ := by rw [← Functor.map_comp, hs₁]
  have mhst : (BigFppfOver.toScheme B S hS).map s ≫ (BigFppfOver.toScheme B S hS).map t =
      (BigFppfOver.toScheme B S hS).map ρ₂ ≫ (BigFppfOver.toScheme B S hS).map t := by
    rw [← Functor.map_comp, ← Functor.map_comp, hst]
  have hsat := preimage_image_range_eq_range_of_action sqτ
    (toSpecΓ_specΓToBase ((BigFppfOver.toScheme B S hS).map w)) hτt msq₂ mhs₁ mhst
  -- the image is open, and carries an open subscheme `b` of `o`
  have hτe : Etale τ := MorphismProperty.of_isPullback sqτ hqe
  have _ := hτe
  have hVopen : IsOpen (τ.base ''
      Set.range ((BigFppfOver.toScheme B S hS).obj v).toSpecΓ.base) :=
    τ.isOpenMap _ (IsOpenImmersion.isOpen_range _)
  obtain ⟨b, i, hioi, hirange, -⟩ := exists_restrict_bigFppfOver o ⟨_, hVopen⟩
  have _ := hioi
  -- the base change of `b` to the affine hull of `v` is the image of `v`
  have hj₁oi : _root_.AlgebraicGeometry.IsOpenImmersion
      (pullback.fst τ ((BigFppfOver.toScheme B S hS).map i)) :=
    MorphismProperty.of_isPullback
      (IsPullback.of_hasPullback τ ((BigFppfOver.toScheme B S hS).map i)).flip hioi
  have _ := hj₁oi
  have hj₁range : Set.range ((BigFppfOver.toScheme B S hS).obj v).toSpecΓ.base =
      Set.range (pullback.fst τ ((BigFppfOver.toScheme B S hS).map i)).base := by
    rw [AlgebraicGeometry.range_snd_of_isPullback (IsPullback.of_hasPullback τ
      ((BigFppfOver.toScheme B S hS).map i)).flip, show
        Set.range ((BigFppfOver.toScheme B S hS).map i).base =
          τ.base '' Set.range ((BigFppfOver.toScheme B S hS).obj v).toSpecΓ.base from hirange]
    exact hsat.symm
  set ε := IsOpenImmersion.isoOfRangeEq ((BigFppfOver.toScheme B S hS).obj v).toSpecΓ
    (pullback.fst τ ((BigFppfOver.toScheme B S hS).map i)) hj₁range with hε
  have hεfac : ε.hom ≫ pullback.fst τ ((BigFppfOver.toScheme B S hS).map i) =
      ((BigFppfOver.toScheme B S hS).obj v).toSpecΓ :=
    IsOpenImmersion.isoOfRangeEq_hom_fac _ _ hj₁range
  have hεt : (ε.hom ≫ pullback.snd τ ((BigFppfOver.toScheme B S hS).map i)) ≫
      (BigFppfOver.toScheme B S hS).map i = (BigFppfOver.toScheme B S hS).map t := by
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, hεfac, hτt]
  -- the comparison is a morphism of the site
  obtain ⟨t', ht'⟩ := BigFppfOver.exists_hom_of_comp_eq B S hS
    (ε.hom ≫ pullback.snd τ ((BigFppfOver.toScheme B S hS).map i))
    (by rw [← BigFppfOver.toScheme_map_comp_hom i, ← Category.assoc, hεt,
      BigFppfOver.toScheme_map_comp_hom t])
  -- the Cartesian square `v = c ×_a b`
  have sqb : IsPullback ((BigFppfOver.toScheme B S hS).map w)
      ((BigFppfOver.toScheme B S hS).map t') ((BigFppfOver.toScheme B S hS).map q)
      ((BigFppfOver.toScheme B S hS).map (i ≫ n)) := by
    refine ((IsPullback.of_hasPullback τ ((BigFppfOver.toScheme B S hS).map i)).paste_horiz
      sqτ).of_iso' ε (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · rw [Iso.refl_hom, Category.comp_id, ← Category.assoc, hεfac,
        toSpecΓ_specΓToBase ((BigFppfOver.toScheme B S hS).map w)]
    · rw [Iso.refl_hom, Category.comp_id, ht']
    · rw [Iso.refl_hom, Iso.refl_hom, Category.id_comp, Category.comp_id]
    · rw [Iso.refl_hom, Iso.refl_hom, Category.id_comp, Category.comp_id, Functor.map_comp]
  -- `b` is quasi-compact, being the image of `v`
  have ht'surj : Surjective ((BigFppfOver.toScheme B S hS).map t') :=
    MorphismProperty.of_isPullback sqb hqs
  have _ := ht'surj
  have hbcpt : CompactSpace ((BigFppfOver.toScheme B S hS).obj b) := by
    refine ⟨?_⟩
    have hcpt := isCompact_range ((BigFppfOver.toScheme B S hS).map t').base.hom.continuous
    rwa [(Surjective.surj (f := (BigFppfOver.toScheme B S hS).map t')).range_eq] at hcpt
  have _ := hbcpt
  have hinqa : _root_.AlgebraicGeometry.IsQuasiAffineHom
      ((BigFppfOver.toScheme B S hS).map (i ≫ n)) :=
    (isQuasiAffineHom_iff_isQuasiAffine _).2
      (Scheme.IsQuasiAffine.of_isImmersion ((BigFppfOver.toScheme B S hS).map i))
  -- the action is a morphism over `b`
  have hmonoi : Mono i := (BigFppfOver.toScheme B S hS).mono_of_mono_map
    (inferInstanceAs (Mono ((BigFppfOver.toScheme B S hS).map i)))
  have ht'i : t' ≫ i = t :=
    (BigFppfOver.toScheme B S hS).map_injective (by rw [Functor.map_comp, ht', hεt])
  have hst' : s ≫ t' = ρ₂ ≫ t' := by
    refine (cancel_mono i).1 ?_
    rw [Category.assoc, Category.assoc, ht'i, hst]
  exact presheaf_pullback_snd_of_descendedObject
    inferInstance hX hY hqs hqe sq e hew sq₂ hs₁ hs₂ sqb hst' hinqa

end AlgebraicGeometry.Space

end
