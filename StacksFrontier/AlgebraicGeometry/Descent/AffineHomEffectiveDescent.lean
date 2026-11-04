module

public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomDescentCocycle
public import StacksFrontier.AlgebraicGeometry.Descent.AffineSourceEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Descent.FiniteDescentFromAffine
public import StacksFrontier.AlgebraicGeometry.Descent.OpenImmersionEtaleDescent
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Effective descent of affine morphisms along a surjective étale chart

`AlgebraicGeometry.Space.exists_descentPushout_appTop_of_isPullback` descends the datum of an
affine morphism over an affine chart to a ring `C` under `Γ(a)` and inside `Γ(v)`, exhibiting
`v` as `c ×_a Spec C`, and returns alongside it the action `s` of the groupoid `c ×_a c` on `v`
together with the equation saying that the action is a morphism *over* `Spec C`. **This file
carries the datum back to the site and concludes that affine morphisms descend effectively
along the surjective étale morphisms of the big fppf site of `S`**, with no hypothesis left.

Three things are needed, and they are the three sections below.

*The compatibility of the descended section.* The equation saying that the action is a morphism
over `Spec C` says exactly that the section of the descended sheaf carried by `v` is compatible
with the covering `v ⟶ Spec C`, in the precise form
`CategoryTheory.Presieve.isSheafFor_singleton` asks for. That form quantifies over an arbitrary
pair of morphisms into `v` agreeing over `Spec C` rather than over the two projections of
`v ×_{Spec C} v`, so no triple identification of fibre products is needed: the pair is
translated into the groupoid by the universal property of `v = c ×_a Spec C`, and the action
moves one member of the pair onto the other.

*The descended object inside the site.* `C` is a subring of `Γ(v)`, so the size of `Spec C` is
bounded by the size of `v` and `Spec C` carries an object of the site, by
`AlgebraicGeometry.Scheme.size_Spec_lt_of_mk_le`; it lies over `S` through `Spec Γ(a)` and `a`,
and `Spec` turns the pushout square of rings into the Cartesian square `v = c ×_a Spec C` of the
site. The projection `v ⟶ Spec C` is then a base change of the chart `q`, hence a surjective
étale covering of `Spec C`.

*The comparison with the fibre product of presheaves.* The section carried by `v` amalgamates,
over that covering, to a section of `X ×[Y] yoneda.obj a` over `Spec C`, i.e. to a morphism
`ℓ : yoneda.obj (Spec C) ⟶ X ×[Y] yoneda.obj a`. It lies over `Spec C ⟶ a` because
`yoneda.obj a` is separated for the covering, it is locally surjective because every section of
the fibre product is, after one base change of the chart, a section of the descent datum, and it
is locally injective because a morphism into `v = c ×_a Spec C` is determined by its two
components. Two locally bijective morphisms of sheaves being isomorphic, the projection
`X ×[Y] yoneda.obj a ⟶ yoneda.obj a` is the representable morphism `Spec C ⟶ a`, which is affine
because both schemes are.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Space.comp_eq_of_comp_descentAction_eq`: the action `s` carries a morphism
  into `c ×_a v` to the unique morphism into `v` which lies over the first projection and agrees
  with the second projection over the descended object.
* `AlgebraicGeometry.Space.descentSection_eq_of_comp_eq`: **the compatibility of the descended
  section.** Two morphisms `p₁, p₂ : Z ⟶ v` of the site which agree after `v ⟶ Spec C` have the
  same composite with the leg of the descent datum to the source of the morphism being
  descended.
* `AlgebraicGeometry.Space.exists_site_object_of_isPushout_appTop`: **the descended ring is an
  object of the site.** A pushout square of rings presenting `Γ(v)` as `Γ(c) ⊗_{Γ(a)} C`, with
  `C` a subring of `Γ(v)`, comes from a Cartesian square `v = c ×_a o` of the site with `o`
  affine over `a`.
* `AlgebraicGeometry.Space.exists_affineHull_site_object_of_isPushout_appTop`: the same
  statement with the affineness of `v` dropped, concluding about the *affine hull*
  `Spec Γ(v, ⊤)` of `v` instead of about `v`. This is what the quasi-affine descent of
  `StacksFrontier.AlgebraicGeometry.Descent.QuasiAffineHomEffectiveDescent` cuts its descended open
  out of.
* `AlgebraicGeometry.Space.exists_isIso_comparison_of_descentAction`: **the comparison of the
  descended object with the fibre product of presheaves is an isomorphism.** This is the
  property-agnostic core of the argument — no property of the descended object is used, only the
  Cartesian square presenting `v` as `c ×_a o` and the compatibility of the action with
  `t : v ⟶ o` — and it is what the quasi-affine descent reuses.
* `AlgebraicGeometry.Space.presheaf_pullback_snd_isAffineHom_of_isPullback`: the base change of
  `f` along a morphism from an affine object of the site is representable by an affine morphism
  as soon as its further base change along an affine surjective étale chart is.
* `AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isAffineHom`: **affine
  morphisms of schemes descend effectively along the surjective étale morphisms of the big fppf
  site of `S`**, outright. This discharges the hypothesis of every statement in this development
  which assumes `AlgebraicGeometry.Space.IsEffectiveDescentAlongSurjectiveEtale` at
  `AlgebraicGeometry.IsAffineHom`, or at a property contained in it.

## Implementation notes

The compatibility statements take the Cartesian square `v = c ×_a Spec C` as a square of
*schemes* rather than of objects of the site, because that is the form in which it comes out of
the pushout square of rings; the morphisms `t : v ⟶ Spec C` and `n : Spec C ⟶ a` are morphisms of
the site, and faithfulness of `AlgebraicGeometry.BigFppfOver.toScheme` is what passes between the
two. Nothing else about `Spec C` is used there — in particular neither affineness nor the ring
`C` itself — so the object is written as an arbitrary object `o` of the site.

The agreement over `X` of the action with the second projection, `hs₂`, is the output of
`AlgebraicGeometry.Space.exists_descentAction_of_isPullback`; the agreement over `o`,
`hst`, is the output of
`AlgebraicGeometry.Space.exists_descentPushout_appTop_of_isPullback` transported from global
sections by the last clause of
`AlgebraicGeometry.Space.exists_site_object_of_isPushout_appTop`, which records that `t` is
`Spec` of the inclusion `C ⟶ Γ(v)` and therefore separates morphisms into `v` that agree on `C`.
Neither the cocycle condition nor the comparison isomorphism `φ` appears: both have already been
spent in producing `C`.

The reduction to an affine base and an affine source is
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_of_affineBase_affineSource`, step
1 of Stacks 02W8, and it is the only reason the quasi-compactness of the chart is available and
unused here: the affine case needs no glueing, so steps 2 to 5 of Stacks 02W8 — and with them
Stacks 02LR and Stacks 0247 — are not entered at all. That is the whole point of descending
affine morphisms separately from quasi-affine ones.

*No tag is carried.* Stacks 0245 quantifies over arbitrary fpqc coverings of an arbitrary scheme
and Stacks 023T is the statement for quasi-coherent sheaves, whereas
`AlgebraicGeometry.Space.IsEffectiveDescentAlongSurjectiveEtale` quantifies over the surjective
étale morphisms of one big fppf site; it is a predicate of this development and not a Stacks
lemma. This is the position already taken for open immersions by
`isEffectiveDescentAlongSurjectiveEtale_isOpenImmersion` of
`StacksFrontier.AlgebraicGeometry.Descent.OpenImmersionEtaleDescent`.

## References

* [Stacks Project, Tag 0245](https://stacks.math.columbia.edu/tag/0245)
* [Stacks Project, Tag 023W](https://stacks.math.columbia.edu/tag/023W)
* [Stacks Project, Tag 02W8](https://stacks.math.columbia.edu/tag/02W8)
* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
* [Stacks Project, Tag 03I2](https://stacks.math.columbia.edu/tag/03I2)
-/
@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

/-! ### The compatibility of the descended section with its covering -/

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}
    {a c v o : BigFppfOver B S hS} {h : yoneda.obj a ⟶ Y} {q : c ⟶ a} {w : v ⟶ c}
    {n : o ⟶ a} {t : v ⟶ o} {Fst : yoneda.obj v ⟶ X}
    {P₂ : BigFppfOver B S hS} {ρ₁ : P₂ ⟶ c} {ρ₂ s : P₂ ⟶ v}

/-- The square presenting `v` as `c ×_a o`, read in the site rather than in schemes: the
commuting triangle it contains is an equation of morphisms of the site, because
`AlgebraicGeometry.BigFppfOver.toScheme` is faithful. -/
theorem comp_eq_comp_of_isPullback_map
    (sqv : IsPullback ((BigFppfOver.toScheme B S hS).map w)
      ((BigFppfOver.toScheme B S hS).map t) ((BigFppfOver.toScheme B S hS).map q)
      ((BigFppfOver.toScheme B S hS).map n)) :
    w ≫ q = t ≫ n :=
  (BigFppfOver.toScheme B S hS).map_injective (by
    rw [Functor.map_comp, Functor.map_comp]; exact sqv.w)

/-- **The action translates a pair of morphisms agreeing over the descended object.** Let `v` be
`c ×_a o`, let `s : P₂ ⟶ v` be the action of the groupoid `P₂ = c ×_a v` on `v`, lying over the
first projection and a morphism over `o`, and let `χ : Z ⟶ P₂` have first component `p₁ ≫ w` and
second component `p₂`, for a pair `p₁, p₂ : Z ⟶ v` agreeing after `t`. Then `χ ≫ s = p₁`.

Both sides lie over the same morphism to `c` — that is `hs₁` and the first component of `χ` —
and over the same morphism to `o`, because the action is a morphism over `o` and `p₁` and `p₂`
agree there. The universal property of `v = c ×_a o` then identifies them. -/
theorem comp_eq_of_comp_descentAction_eq
    (sqv : IsPullback ((BigFppfOver.toScheme B S hS).map w)
      ((BigFppfOver.toScheme B S hS).map t) ((BigFppfOver.toScheme B S hS).map q)
      ((BigFppfOver.toScheme B S hS).map n))
    (sq₂ : IsPullback ρ₁ ρ₂ q (w ≫ q)) (hs₁ : s ≫ w = ρ₁) (hst : s ≫ t = ρ₂ ≫ t)
    {Z : BigFppfOver B S hS} {p₁ p₂ : Z ⟶ v} (hp : p₁ ≫ t = p₂ ≫ t)
    (cond : (p₁ ≫ w) ≫ q = p₂ ≫ w ≫ q) :
    sq₂.lift (p₁ ≫ w) p₂ cond ≫ s = p₁ := by
  have hχ₁ : sq₂.lift (p₁ ≫ w) p₂ cond ≫ ρ₁ = p₁ ≫ w := sq₂.lift_fst _ _ cond
  have hχ₂ : sq₂.lift (p₁ ≫ w) p₂ cond ≫ ρ₂ = p₂ := sq₂.lift_snd _ _ cond
  refine (BigFppfOver.toScheme B S hS).map_injective (sqv.hom_ext ?_ ?_)
  · rw [← Functor.map_comp, ← Functor.map_comp, Category.assoc, hs₁, hχ₁]
  · rw [← Functor.map_comp, ← Functor.map_comp]
    refine congrArg (BigFppfOver.toScheme B S hS).map ?_
    rw [Category.assoc, hst, ← Category.assoc, hχ₂, hp]

/-- **The descended section is compatible with its covering.** Let `v` present the base change
of `f` along `yoneda.map q ≫ h`, with leg `Fst` to `X`, let `v` be `c ×_a o`, and let
`s : P₂ ⟶ v` be the action of the groupoid `P₂ = c ×_a v` on `v`: a morphism over the first
projection which agrees with the second projection over `X` and over `o`. Then any two
morphisms `p₁, p₂ : Z ⟶ v` of the site agreeing after `t : v ⟶ o` have the same composite with
`Fst`.

This is exactly the compatibility condition of `CategoryTheory.Presieve.isSheafFor_singleton`
for the section of the base change of `f` along `h` carried by `v`, relative to the one-element
covering `{t}` of `o`. The pair `(p₁ ≫ w, p₂)` defines a morphism `χ : Z ⟶ P₂`; the action
moves it to `p₁` by `AlgebraicGeometry.Space.comp_eq_of_comp_descentAction_eq`, and it agrees
with `p₂` over `X` by `hs₂`. -/
theorem descentSection_eq_of_comp_eq
    (sqv : IsPullback ((BigFppfOver.toScheme B S hS).map w)
      ((BigFppfOver.toScheme B S hS).map t) ((BigFppfOver.toScheme B S hS).map q)
      ((BigFppfOver.toScheme B S hS).map n))
    (sq₂ : IsPullback ρ₁ ρ₂ q (w ≫ q)) (hs₁ : s ≫ w = ρ₁)
    (hs₂ : yoneda.map s ≫ Fst = yoneda.map ρ₂ ≫ Fst) (hst : s ≫ t = ρ₂ ≫ t)
    {Z : BigFppfOver B S hS} {p₁ p₂ : Z ⟶ v} (hp : p₁ ≫ t = p₂ ≫ t) :
    yoneda.map p₁ ≫ Fst = yoneda.map p₂ ≫ Fst := by
  have hwq : w ≫ q = t ≫ n := comp_eq_comp_of_isPullback_map sqv
  have cond : (p₁ ≫ w) ≫ q = p₂ ≫ w ≫ q := by
    rw [Category.assoc, hwq, ← Category.assoc, hp, Category.assoc]
  have key := comp_eq_of_comp_descentAction_eq sqv sq₂ hs₁ hst hp cond
  have hχ₂ : sq₂.lift (p₁ ≫ w) p₂ cond ≫ ρ₂ = p₂ := sq₂.lift_snd _ _ cond
  rw [← key, Functor.map_comp, Category.assoc, hs₂, ← Category.assoc, ← Functor.map_comp, hχ₂]

/-! ### The descended ring as an object of the site -/

/-- Morphisms into `v` which agree on global sections after `p` agree after
`toSpecΓ ≫ Spec.map p`. -/
private theorem comp_toSpecΓ_comp_eq_of_appTop_comp_eq {C : CommRingCat.{u}}
    {p : C ⟶ Γ((BigFppfOver.toScheme B S hS).obj v, ⊤)} {Z : BigFppfOver B S hS}
    (g₁ g₂ : Z ⟶ v)
    (hg : p ≫ ((BigFppfOver.toScheme B S hS).map g₁).appTop =
      p ≫ ((BigFppfOver.toScheme B S hS).map g₂).appTop) :
    (BigFppfOver.toScheme B S hS).map g₁ ≫
        (((BigFppfOver.toScheme B S hS).obj v).toSpecΓ ≫ Spec.map p) =
      (BigFppfOver.toScheme B S hS).map g₂ ≫
        (((BigFppfOver.toScheme B S hS).obj v).toSpecΓ ≫ Spec.map p) := by
  rw [Scheme.toSpecΓ_naturality_assoc, Scheme.toSpecΓ_naturality_assoc,
    ← Spec.map_comp, ← Spec.map_comp, hg]

/-- **The descended ring is an object of the site, and `v` is its base change.** Let `q : c ⟶ a`
and `w : v ⟶ c` be morphisms of the big fppf site of `S` with `a`, `c` and `v` affine, and let
`C` be a ring under `Γ(a)` and inside `Γ(v)` presenting `Γ(v)` as the pushout
`Γ(c) ⊗_{Γ(a)} C`. Then `Spec C` carries an object `o` of the site, affine and affine over `a`
through a morphism `n`, and `v` is the base change `c ×_a o`, through a morphism `t : v ⟶ o`.

Moreover `t` is `Spec` of the inclusion `C ⟶ Γ(v)`, in the only form in which that is used: two
morphisms `g₁, g₂ : Z ⟶ v` of the site whose actions on global sections agree on `C` agree after
`t`. This is what transports an identity of ring maps out of `C` into an identity of morphisms
over `o`, and is what
`AlgebraicGeometry.Space.descentSection_eq_of_comp_eq` consumes as its hypothesis `hst`.

The size bound putting `Spec C` in the site is Stacks 000R (9): `C` injects into
`Γ(v)`, whose cardinality is bounded by the size of `v` because `v` is affine, so
`AlgebraicGeometry.Scheme.size_Spec_lt_of_mk_le` applies. The Cartesian square is the image under
`Spec` of the pushout square of rings, transported along the canonical isomorphisms of the three
affine schemes with the spectra of their rings of global sections. -/
theorem exists_site_object_of_isPushout_appTop
    (ha : IsAffine ((BigFppfOver.toScheme B S hS).obj a))
    (hc : IsAffine ((BigFppfOver.toScheme B S hS).obj c))
    (hv : IsAffine ((BigFppfOver.toScheme B S hS).obj v))
    {C : CommRingCat.{u}} {k : Γ((BigFppfOver.toScheme B S hS).obj a, ⊤) ⟶ C}
    {p : C ⟶ Γ((BigFppfOver.toScheme B S hS).obj v, ⊤)}
    (hpinj : Function.Injective p.hom)
    (hpo : IsPushout ((BigFppfOver.toScheme B S hS).map q).appTop k
      ((BigFppfOver.toScheme B S hS).map w).appTop p) :
    ∃ (o : BigFppfOver B S hS) (n : o ⟶ a) (t : v ⟶ o),
      IsAffine ((BigFppfOver.toScheme B S hS).obj o) ∧
      _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map n) ∧
      IsPullback ((BigFppfOver.toScheme B S hS).map w) ((BigFppfOver.toScheme B S hS).map t)
        ((BigFppfOver.toScheme B S hS).map q) ((BigFppfOver.toScheme B S hS).map n) ∧
      ∀ {Z : BigFppfOver B S hS} (g₁ g₂ : Z ⟶ v),
        p ≫ ((BigFppfOver.toScheme B S hS).map g₁).appTop =
          p ≫ ((BigFppfOver.toScheme B S hS).map g₂).appTop → g₁ ≫ t = g₂ ≫ t := by
  have := ha; have := hc; have := hv
  have hmk : Cardinal.mk C ≤ ((BigFppfOver.toScheme B S hS).obj v).size ^ Cardinal.aleph0 :=
    ((Cardinal.mk_le_of_injective hpinj).trans
      (Scheme.mk_sections_le_size ((BigFppfOver.toScheme B S hS).obj v)
        ⟨⊤, isAffineOpen_top _⟩)).trans (Cardinal.self_le_power _ Cardinal.one_le_aleph0)
  have hCsize : B.Contains (Spec C) :=
    Scheme.size_Spec_lt_of_mk_le B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit C v.left.2 hmk
  have sqSpec : IsPullback ((BigFppfOver.toScheme B S hS).map w)
      (((BigFppfOver.toScheme B S hS).obj v).toSpecΓ ≫ Spec.map p)
      ((BigFppfOver.toScheme B S hS).map q)
      (Spec.map k ≫ ((BigFppfOver.toScheme B S hS).obj a).isoSpec.inv) := by
    refine (hpo.op.map Scheme.Spec).flip.of_iso'
      ((BigFppfOver.toScheme B S hS).obj v).isoSpec
      ((BigFppfOver.toScheme B S hS).obj c).isoSpec (Iso.refl (Spec C))
      ((BigFppfOver.toScheme B S hS).obj a).isoSpec
      (Scheme.isoSpec_hom_naturality ((BigFppfOver.toScheme B S hS).map w)) ?_
      (Scheme.isoSpec_hom_naturality ((BigFppfOver.toScheme B S hS).map q)) ?_
    · rw [Iso.refl_hom, Category.comp_id]; rfl
    · rw [Iso.refl_hom, Category.id_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]; rfl
  obtain ⟨n, hn⟩ := BigFppfOver.exists_hom_of_comp_eq B S hS
    (X := BigFppfOver.mk B S hS hCsize
      ((Spec.map k ≫ ((BigFppfOver.toScheme B S hS).obj a).isoSpec.inv) ≫
        B.inclusion.map a.hom))
    (Y := a) (Spec.map k ≫ ((BigFppfOver.toScheme B S hS).obj a).isoSpec.inv) rfl
  have hwt : (((BigFppfOver.toScheme B S hS).obj v).toSpecΓ ≫ Spec.map p) ≫
      ((Spec.map k ≫ ((BigFppfOver.toScheme B S hS).obj a).isoSpec.inv) ≫
        B.inclusion.map a.hom) = B.inclusion.map v.hom := by
    rw [← Category.assoc, ← sqSpec.w, Category.assoc,
      BigFppfOver.toScheme_map_comp_hom q, BigFppfOver.toScheme_map_comp_hom w]
  have hoaff : IsAffine ((BigFppfOver.toScheme B S hS).obj (BigFppfOver.mk B S hS hCsize
      ((Spec.map k ≫ ((BigFppfOver.toScheme B S hS).obj a).isoSpec.inv) ≫
        B.inclusion.map a.hom))) := inferInstanceAs (IsAffine (Spec C))
  refine ⟨_, n, BigFppfOver.homMk B S hS hCsize _
    (((BigFppfOver.toScheme B S hS).obj v).toSpecΓ ≫ Spec.map p) hwt, hoaff, ?_, ?_, ?_⟩
  · rw [hn]; exact _root_.AlgebraicGeometry.isAffineHom_of_isAffine _
  · rw [hn, BigFppfOver.toScheme_map_homMk]; exact sqSpec
  · intro Z g₁ g₂ hg
    refine (BigFppfOver.toScheme B S hS).map_injective ?_
    rw [Functor.map_comp, Functor.map_comp, BigFppfOver.toScheme_map_homMk]
    exact comp_toSpecΓ_comp_eq_of_appTop_comp_eq g₁ g₂ hg

/-- **The descended ring of a quasi-affine datum is an object of the site, and the *affine hull*
of `v` is its base change.** Let `q : c ⟶ a` and `w : v ⟶ c` be morphisms of the big fppf site of
`S` with `a` and `c` affine — but `v` *arbitrary* — and let `C` be a ring under `Γ(a)` and inside
`Γ(v)` presenting `Γ(v)` as the pushout `Γ(c) ⊗_{Γ(a)} C`. Then `Spec C` carries an object `o` of
the site, affine and affine over `a` through a morphism `n`, and the affine hull
`Spec Γ(v, ⊤)` of `v` is the base change `c ×_a o`, through morphisms `Υ` to `c` and `Λ` to `o`
which the canonical morphism `v ⟶ Spec Γ(v, ⊤)` carries to `w` and to a morphism `t : v ⟶ o` of
the site.

This is `AlgebraicGeometry.Space.exists_site_object_of_isPushout_appTop` with the affineness of
`v` dropped: for affine `v` the canonical morphism `v ⟶ Spec Γ(v, ⊤)` is an isomorphism and the
Cartesian square may be read on `v` itself, whereas in general it can only be read on the hull.
The last clause is unchanged — `t` is `Spec` of the inclusion `C ⟶ Γ(v)` precomposed with the
canonical morphism, so it separates morphisms into `v` which agree on `C`.

The one step of the proof which does not carry over is the size bound putting `Spec C` in the
site. `AlgebraicGeometry.Scheme.size_Spec_lt_of_mk_le` wants `#C ≤ (size v) ^ ℵ₀`, which for
affine `v` follows from `AlgebraicGeometry.Scheme.mk_sections_le_size`; for arbitrary `v` only
`#Γ(v, ⊤) ≤ 2 ^ size v` is available, by
`AlgebraicGeometry.Scheme.mk_sections_le_two_pow_size`, and one power is genuinely lost there.
The bound is therefore taken through `AlgebraicGeometry.Scheme.size_Spec` — the size of a
spectrum is `max {ℵ₀, #C}` — and the powerset-closure of the cutoff,
`AlgebraicGeometry.BigFppfSite.cutoff_isStrongPrelimit`, which absorbs the lost power. -/
theorem exists_affineHull_site_object_of_isPushout_appTop
    (ha : IsAffine ((BigFppfOver.toScheme B S hS).obj a))
    (hc : IsAffine ((BigFppfOver.toScheme B S hS).obj c))
    {C : CommRingCat.{u}} {k : Γ((BigFppfOver.toScheme B S hS).obj a, ⊤) ⟶ C}
    {p : C ⟶ Γ((BigFppfOver.toScheme B S hS).obj v, ⊤)}
    (hpinj : Function.Injective p.hom)
    (hpo : IsPushout ((BigFppfOver.toScheme B S hS).map q).appTop k
      ((BigFppfOver.toScheme B S hS).map w).appTop p) :
    ∃ (o : BigFppfOver B S hS) (n : o ⟶ a) (t : v ⟶ o)
      (Υ : Spec Γ((BigFppfOver.toScheme B S hS).obj v, ⊤) ⟶
        (BigFppfOver.toScheme B S hS).obj c)
      (Λ : Spec Γ((BigFppfOver.toScheme B S hS).obj v, ⊤) ⟶
        (BigFppfOver.toScheme B S hS).obj o),
      IsAffine ((BigFppfOver.toScheme B S hS).obj o) ∧
      _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map n) ∧
      ((BigFppfOver.toScheme B S hS).obj v).toSpecΓ ≫ Υ =
        (BigFppfOver.toScheme B S hS).map w ∧
      ((BigFppfOver.toScheme B S hS).obj v).toSpecΓ ≫ Λ =
        (BigFppfOver.toScheme B S hS).map t ∧
      IsPullback Υ Λ ((BigFppfOver.toScheme B S hS).map q)
        ((BigFppfOver.toScheme B S hS).map n) ∧
      ∀ {Z : BigFppfOver B S hS} (g₁ g₂ : Z ⟶ v),
        p ≫ ((BigFppfOver.toScheme B S hS).map g₁).appTop =
          p ≫ ((BigFppfOver.toScheme B S hS).map g₂).appTop → g₁ ≫ t = g₂ ≫ t := by
  have := ha; have := hc
  have hvlt : ((BigFppfOver.toScheme B S hS).obj v).size < B.cutoff := v.left.2
  have hmk : Cardinal.mk C ≤ 2 ^ ((BigFppfOver.toScheme B S hS).obj v).size :=
    (Cardinal.mk_le_of_injective hpinj).trans
      (Scheme.mk_sections_le_two_pow_size ((BigFppfOver.toScheme B S hS).obj v) ⊤)
  have hCsize : B.Contains (Spec C) :=
    (Scheme.size_Spec C).trans_lt
      (max_lt B.aleph0_lt_cutoff (hmk.trans_lt (B.cutoff_isStrongPrelimit hvlt)))
  have sqSpec : IsPullback (specΓToBase ((BigFppfOver.toScheme B S hS).map w)) (Spec.map p)
      ((BigFppfOver.toScheme B S hS).map q)
      (Spec.map k ≫ ((BigFppfOver.toScheme B S hS).obj a).isoSpec.inv) := by
    refine (hpo.op.map Scheme.Spec).flip.of_iso' (Iso.refl _)
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
  have hwq : (((BigFppfOver.toScheme B S hS).obj v).toSpecΓ ≫ Spec.map p) ≫
      (Spec.map k ≫ ((BigFppfOver.toScheme B S hS).obj a).isoSpec.inv) =
      (BigFppfOver.toScheme B S hS).map w ≫ (BigFppfOver.toScheme B S hS).map q := by
    rw [Category.assoc, ← sqSpec.w, toSpecΓ_specΓToBase_assoc]
  have hwt : (((BigFppfOver.toScheme B S hS).obj v).toSpecΓ ≫ Spec.map p) ≫
      ((Spec.map k ≫ ((BigFppfOver.toScheme B S hS).obj a).isoSpec.inv) ≫
        B.inclusion.map a.hom) = B.inclusion.map v.hom := by
    rw [← Category.assoc, hwq, Category.assoc,
      BigFppfOver.toScheme_map_comp_hom q, BigFppfOver.toScheme_map_comp_hom w]
  have hoaff : IsAffine ((BigFppfOver.toScheme B S hS).obj (BigFppfOver.mk B S hS hCsize
      ((Spec.map k ≫ ((BigFppfOver.toScheme B S hS).obj a).isoSpec.inv) ≫
        B.inclusion.map a.hom))) := inferInstanceAs (IsAffine (Spec C))
  refine ⟨_, n, BigFppfOver.homMk B S hS hCsize _
      (((BigFppfOver.toScheme B S hS).obj v).toSpecΓ ≫ Spec.map p) hwt,
    specΓToBase ((BigFppfOver.toScheme B S hS).map w), Spec.map p, hoaff, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hn]; exact _root_.AlgebraicGeometry.isAffineHom_of_isAffine _
  · exact toSpecΓ_specΓToBase _
  · rfl
  · rw [hn]; exact sqSpec
  · intro Z g₁ g₂ hg
    refine (BigFppfOver.toScheme B S hS).map_injective ?_
    rw [Functor.map_comp, Functor.map_comp, BigFppfOver.toScheme_map_homMk]
    exact comp_toSpecΓ_comp_eq_of_appTop_comp_eq g₁ g₂ hg

/-! ### Effective descent for affine morphisms -/

/-- A presheaf of types on the big fppf site of `S` which is a sheaf is a sheaf for the
one-element presieve of a surjective flat morphism of the site locally of finite
presentation. -/
private theorem isSheafFor_singleton_of_isSheaf
    {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hP : Presheaf.IsSheaf (BigFppfOver.topology B S hS) P)
    {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
    (hgs : Surjective ((BigFppfOver.toScheme B S hS).map g))
    (hgf : Flat ((BigFppfOver.toScheme B S hS).map g))
    (hgp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map g)) :
    Presieve.IsSheafFor P (Presieve.singleton g) :=
  ((isSheaf_iff_isSheaf_of_type _ _).1 hP).isSheafFor _
    (sieve_generate_singleton_mem_topology_over_of_flat B S hS g hgs hgf hgp)

/-- The first projection of the pullback of a surjective flat morphism of the site locally of
finite presentation along any morphism is a covering. -/
private theorem generate_singleton_pullback_fst_mem_topology {U T T' : BigFppfOver B S hS}
    (u : U ⟶ T) (g : T' ⟶ T) (hgs : Surjective ((BigFppfOver.toScheme B S hS).map g))
    (hgf : Flat ((BigFppfOver.toScheme B S hS).map g))
    (hgp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map g)) :
    Sieve.generate (Presieve.singleton (pullback.fst u g)) ∈ BigFppfOver.topology B S hS U :=
  have sq := (IsPullback.of_hasPullback u g).map (BigFppfOver.toScheme B S hS)
  sieve_generate_singleton_mem_topology_over_of_flat B S hS _
    (MorphismProperty.of_isPullback sq.flip hgs) (MorphismProperty.of_isPullback sq.flip hgf)
    (MorphismProperty.of_isPullback sq.flip hgp)

/-- **The comparison of the descended object with the fibre product of presheaves is an
isomorphism.** This is the property-agnostic core of the descent argument. Let `f : X ⟶ Y` be a
morphism of sheaves on the big fppf site of `S`, let `q : c ⟶ a` be a surjective flat morphism of
the site locally of finite presentation, and let `m, r` present `A₀` as the base change of `f`
along `yoneda.map q ≫ h`, with `A₀` represented by `v` over `c` through `e`. Suppose given the
action `s : P₂ ⟶ v` of the groupoid `P₂ = c ×_a v` on `v` — a morphism over the first projection
agreeing with the second over `X` — an object `o` of the site over `a` through `n : o ⟶ a`, and
a morphism `t : v ⟶ o` presenting `v` as `c ×_a o` and equalizing the action with the second
projection. Then `yoneda.obj o` *is* the fibre product `X ×[Y] yoneda.obj a`, compatibly with
`n`.

No property of `n`, of `w` or of `t` is used, and neither affineness nor the descended ring is
mentioned: the whole input is the Cartesian square `sqv` presenting `v` as `c ×_a o` and the
compatibility `hst` of the action with `t`. The section of `X ×[Y] yoneda.obj a` carried by `v`
amalgamates over the covering `t`, by
`AlgebraicGeometry.Space.descentSection_eq_of_comp_eq`; the amalgamation lies over `n` because
`yoneda.obj a` is separated for that covering; it is locally surjective because every section of
the fibre product is, after one base change of the chart, a section of the descent datum; and it
is locally injective because a morphism into `v = c ×_a o` is determined by its two components.
Two locally bijective morphisms of sheaves are isomorphic,
`CategoryTheory.Sheaf.isLocallyBijective_iff_isIso`.

`AlgebraicGeometry.Space.presheaf_pullback_snd_isAffineHom_of_isPullback` is this statement with
`o` produced by `AlgebraicGeometry.Space.exists_site_object_of_isPushout_appTop`, where `n` is
affine; for a quasi-affine datum the same core is fed an `o` cut out of the affine hull. -/
@[sga "3 IV 4.6.8" "special case"]
theorem exists_isIso_comparison_of_descentAction
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    (hY : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y)
    (hqs : Surjective ((BigFppfOver.toScheme B S hS).map q))
    (hqf : Flat ((BigFppfOver.toScheme B S hS).map q))
    (hqp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map q))
    {A₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {m : A₀ ⟶ X} {r : A₀ ⟶ yoneda.obj c}
    (sq : IsPullback m r f (yoneda.map q ≫ h))
    {e : A₀ ≅ yoneda.obj v} (hew : e.hom ≫ yoneda.map w = r)
    (sq₂ : IsPullback ρ₁ ρ₂ q (w ≫ q)) (hs₁ : s ≫ w = ρ₁)
    (hs₂ : yoneda.map s ≫ e.inv ≫ m = yoneda.map ρ₂ ≫ e.inv ≫ m)
    (sqv : IsPullback ((BigFppfOver.toScheme B S hS).map w)
      ((BigFppfOver.toScheme B S hS).map t) ((BigFppfOver.toScheme B S hS).map q)
      ((BigFppfOver.toScheme B S hS).map n))
    (hst : s ≫ t = ρ₂ ≫ t) :
    ∃ ι : yoneda.obj o ≅ pullback f h, ι.hom ≫ pullback.snd f h = yoneda.map n := by
  have vsq : IsPullback (e.inv ≫ m) (yoneda.map w) f (yoneda.map q ≫ h) := by
    refine sq.of_iso e (Iso.refl X) (Iso.refl (yoneda.obj c)) (Iso.refl Y) ?_ ?_ ?_ ?_
    · rw [Iso.refl_hom, Category.comp_id, Iso.hom_inv_id_assoc]
    · rw [Iso.refl_hom, Category.comp_id, hew]
    · simp
    · simp
  have hwq : w ≫ q = t ≫ n := comp_eq_comp_of_isPullback_map sqv
  obtain ⟨σ, hσ₁, hσ₂⟩ : ∃ σ : yoneda.obj v ⟶ pullback f h,
      σ ≫ pullback.fst f h = e.inv ≫ m ∧ σ ≫ pullback.snd f h = yoneda.map (w ≫ q) :=
    ⟨pullback.lift (e.inv ≫ m) (yoneda.map (w ≫ q))
      (by rw [vsq.w, Functor.map_comp, Category.assoc]),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  -- the section carried by `v` is compatible with the covering `t`
  have hcompat : ∀ {Z : BigFppfOver B S hS} (p₁ p₂ : Z ⟶ v), p₁ ≫ t = p₂ ≫ t →
      yoneda.map p₁ ≫ σ = yoneda.map p₂ ≫ σ := by
    intro Z p₁ p₂ hp
    refine pullback.hom_ext ?_ ?_
    · simp only [Category.assoc, hσ₁]
      exact descentSection_eq_of_comp_eq sqv sq₂ hs₁ hs₂ hst hp
    · simp only [Category.assoc, hσ₂, ← Functor.map_comp]
      refine congrArg yoneda.map ?_
      rw [hwq, ← Category.assoc, hp, Category.assoc]
  have hts : Surjective ((BigFppfOver.toScheme B S hS).map t) :=
    MorphismProperty.of_isPullback sqv hqs
  have htf : Flat ((BigFppfOver.toScheme B S hS).map t) :=
    MorphismProperty.of_isPullback sqv hqf
  have htp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map t) :=
    MorphismProperty.of_isPullback sqv hqp
  have hFsheaf : Presheaf.IsSheaf (BigFppfOver.topology B S hS) (pullback f h) :=
    BigFppfOver.isSheaf_pullback_yoneda_obj f h hX hY
  obtain ⟨ℓ₀, hℓ₀, -⟩ := (Presieve.isSheafFor_singleton (P := pullback f h)).1
    (isSheafFor_singleton_of_isSheaf hFsheaf t hts htf htp) (yonedaEquiv σ) (by
      intro Z p₁ p₂ hp
      rw [yonedaEquiv_naturality, yonedaEquiv_naturality]
      exact congrArg yonedaEquiv (hcompat p₁ p₂ hp))
  have htl : yoneda.map t ≫ yonedaEquiv.symm ℓ₀ = σ := by
    apply yonedaEquiv.injective
    rw [← yonedaEquiv_naturality, Equiv.apply_symm_apply, hℓ₀]
  -- the amalgamation lies over `n`
  have hln : yonedaEquiv.symm ℓ₀ ≫ pullback.snd f h = yoneda.map n := by
    have hsep : Function.Injective ((yoneda.obj a).map t.op) :=
      Presieve.isSeparatedFor_singleton.1
        (isSheafFor_singleton_of_isSheaf (BigFppfOver.isSheaf_yoneda_obj B S hS a) t
          hts htf htp).isSeparatedFor
    refine yonedaEquiv.injective (hsep ?_)
    rw [yonedaEquiv_naturality, yonedaEquiv_naturality]
    refine congrArg yonedaEquiv ?_
    rw [← Category.assoc, htl, hσ₂, ← Functor.map_comp, hwq]
  -- the amalgamation is locally surjective
  have hls : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
      (yonedaEquiv.symm ℓ₀) := by
    constructor
    intro T z
    obtain ⟨g, hg⟩ : ∃ g : T ⟶ a, (pullback.snd f h).app (Opposite.op T) z = g := ⟨_, rfl⟩
    have hz : yonedaEquiv.symm z ≫ pullback.snd f h = yoneda.map g := by
      rw [yonedaEquiv_symm_comp_pullback_snd, hg]
    obtain ⟨α, hα₁, hα₂⟩ := exists_lift_of_descentDatum sq (yonedaEquiv.symm z) hz
      (pullback.fst g q) (pullback.snd g q) pullback.condition
    obtain ⟨β, hβ⟩ : ∃ β : Limits.pullback g q ⟶ v, yoneda.map β = α ≫ e.hom :=
      ⟨yoneda.preimage (α ≫ e.hom), Functor.map_preimage _ _⟩
    have hβw : β ≫ w = pullback.snd g q := by
      refine yoneda.map_injective ?_
      rw [Functor.map_comp, hβ, Category.assoc, hew, hα₂]
    have hβσ : yoneda.map β ≫ σ = yoneda.map (pullback.fst g q) ≫ yonedaEquiv.symm z := by
      refine pullback.hom_ext ?_ ?_
      · simpa only [Category.assoc, hσ₁, hβ, Iso.hom_inv_id_assoc] using hα₁
      · simp only [Category.assoc, hσ₂, hz, ← Functor.map_comp]
        refine congrArg yoneda.map ?_
        rw [← Category.assoc, hβw]
        exact pullback.condition.symm
    refine (BigFppfOver.topology B S hS).superset_covering ?_
      (generate_singleton_pullback_fst_mem_topology g q hqs hqf hqp)
    rintro Z κ ⟨Z', u, bb, hbb, hfac⟩
    cases hbb
    refine ⟨u ≫ β ≫ t, ?_⟩
    have key : yoneda.map (u ≫ β ≫ t) ≫ yonedaEquiv.symm ℓ₀ =
        yoneda.map κ ≫ yonedaEquiv.symm z := by
      rw [← hfac]
      simp only [Functor.map_comp, Category.assoc, htl, hβσ]
    calc (yonedaEquiv.symm ℓ₀).app (Opposite.op Z) (u ≫ β ≫ t)
        = yonedaEquiv (yoneda.map (u ≫ β ≫ t) ≫ yonedaEquiv.symm ℓ₀) := by
          rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map]
      _ = yonedaEquiv (yoneda.map κ ≫ yonedaEquiv.symm z) := by rw [key]
      _ = (pullback f h).map κ.op z := by
          rw [← yonedaEquiv_naturality, Equiv.apply_symm_apply]
  -- the amalgamation is locally injective
  have hli : Presheaf.IsLocallyInjective (BigFppfOver.topology B S hS)
      (yonedaEquiv.symm ℓ₀) := by
    constructor
    intro T x y hxy
    have hxyl : yoneda.map x ≫ yonedaEquiv.symm ℓ₀ = yoneda.map y ≫ yonedaEquiv.symm ℓ₀ := by
      apply yonedaEquiv.injective
      rwa [yonedaEquiv_comp, yonedaEquiv_comp, yonedaEquiv_yoneda_map, yonedaEquiv_yoneda_map]
    have hxn : x ≫ n = y ≫ n := by
      refine yoneda.map_injective ?_
      rw [Functor.map_comp, Functor.map_comp, ← hln, ← Category.assoc, ← Category.assoc, hxyl]
    -- the translate of the second projection by the other section of `o`
    have hcond : ((BigFppfOver.toScheme B S hS).map (pullback.snd x t ≫ w)) ≫
        (BigFppfOver.toScheme B S hS).map q =
        ((BigFppfOver.toScheme B S hS).map (pullback.fst x t ≫ y)) ≫
          (BigFppfOver.toScheme B S hS).map n := by
      rw [← Functor.map_comp, ← Functor.map_comp]
      refine congrArg (BigFppfOver.toScheme B S hS).map ?_
      simp only [Category.assoc]
      rw [hwq, ← Category.assoc, ← pullback.condition, Category.assoc, hxn]
    have hβ₂cond : (sqv.lift ((BigFppfOver.toScheme B S hS).map (pullback.snd x t ≫ w))
          ((BigFppfOver.toScheme B S hS).map (pullback.fst x t ≫ y)) hcond) ≫
          B.inclusion.map v.hom = B.inclusion.map (Limits.pullback x t).hom := by
      rw [← BigFppfOver.toScheme_map_comp_hom w, ← Category.assoc, sqv.lift_fst,
        Functor.map_comp, Category.assoc, BigFppfOver.toScheme_map_comp_hom w,
        BigFppfOver.toScheme_map_comp_hom (pullback.snd x t)]
    obtain ⟨β₂, hβ₂⟩ := BigFppfOver.exists_hom_of_comp_eq B S hS _ hβ₂cond
    have hβ₂w : β₂ ≫ w = pullback.snd x t ≫ w := by
      refine (BigFppfOver.toScheme B S hS).map_injective ?_
      rw [Functor.map_comp, hβ₂, sqv.lift_fst]
    have hβ₂t : β₂ ≫ t = pullback.fst x t ≫ y := by
      refine (BigFppfOver.toScheme B S hS).map_injective ?_
      rw [Functor.map_comp, hβ₂, sqv.lift_snd]
    have e1 : yoneda.map (pullback.snd x t) ≫ σ =
        yoneda.map (pullback.fst x t) ≫ yoneda.map x ≫ yonedaEquiv.symm ℓ₀ := by
      rw [← htl, ← Category.assoc, ← Functor.map_comp, ← pullback.condition,
        Functor.map_comp, Category.assoc]
    have e2 : yoneda.map β₂ ≫ σ =
        yoneda.map (pullback.fst x t) ≫ yoneda.map y ≫ yonedaEquiv.symm ℓ₀ := by
      rw [← htl, ← Category.assoc, ← Functor.map_comp, hβ₂t, Functor.map_comp, Category.assoc]
    have hβ₂eq : pullback.snd x t = β₂ := by
      refine descentAction_unique vsq hβ₂w.symm ?_
      have h2 := congrArg (fun κ => κ ≫ pullback.fst f h) (e1.trans (hxyl ▸ e2.symm))
      simpa only [Category.assoc, hσ₁] using h2
    have hxy' : pullback.fst x t ≫ x = pullback.fst x t ≫ y := by
      rw [pullback.condition, hβ₂eq, hβ₂t]
    refine (BigFppfOver.topology B S hS).superset_covering ?_
      (generate_singleton_pullback_fst_mem_topology x t hts htf htp)
    rintro Z κ ⟨Z', u, bb, hbb, hfac⟩
    cases hbb
    show κ ≫ x = κ ≫ y
    rw [← hfac, Category.assoc, Category.assoc, hxy']
  -- two locally bijective sheaves are isomorphic, and `n` is affine
  have hosheaf : Presheaf.IsSheaf (BigFppfOver.topology B S hS) (yoneda.obj o) :=
    BigFppfOver.isSheaf_yoneda_obj B S hS o
  have hliso : IsIso (yonedaEquiv.symm ℓ₀) := by
    have hsh : IsIso ((⟨yonedaEquiv.symm ℓ₀⟩ :
        (⟨yoneda.obj o, hosheaf⟩ : Sheaf (BigFppfOver.topology B S hS) (Type u)) ⟶
          ⟨pullback f h, hFsheaf⟩)) :=
      (Sheaf.isLocallyBijective_iff_isIso _).1 ⟨hli, hls⟩
    exact inferInstanceAs (IsIso ((sheafToPresheaf (BigFppfOver.topology B S hS) (Type u)).map
      ((⟨yonedaEquiv.symm ℓ₀⟩ :
        (⟨yoneda.obj o, hosheaf⟩ : Sheaf (BigFppfOver.topology B S hS) (Type u)) ⟶
          ⟨pullback f h, hFsheaf⟩))))
  exact ⟨asIso (yonedaEquiv.symm ℓ₀), hln⟩


/-- **Effective descent for affine morphisms over an affine base, at one datum.** Let
`f : X ⟶ Y` be a morphism of sheaves on the big fppf site of `S`, let `h : yoneda.obj a ⟶ Y` with
`a` affine, let `q : c ⟶ a` be a surjective flat morphism of the site locally of finite
presentation with `c` affine, and let
`m, r` present `A₀` as the base change of `f` along `yoneda.map q ≫ h`, with `r` representable by
an affine morphism. Then the base change of `f` along `h` is itself representable by an affine
morphism.

The descended object is `Spec C` for the ring `C` of
`AlgebraicGeometry.Space.exists_descentPushout_appTop_of_isPullback`, placed in the site by
`AlgebraicGeometry.Space.exists_site_object_of_isPushout_appTop`. The comparison with
`X ×[Y] yoneda.obj a` is an isomorphism because it is locally injective and locally surjective
between two sheaves, as in
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isOpenImmersion`; the section it
amalgamates is the one carried by `v`, and its compatibility with the covering `v ⟶ Spec C` is
`AlgebraicGeometry.Space.descentSection_eq_of_comp_eq`. -/
theorem presheaf_pullback_snd_isAffineHom_of_isPullback
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    (hY : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y)
    (ha : IsAffine ((BigFppfOver.toScheme B S hS).obj a))
    (hc : IsAffine ((BigFppfOver.toScheme B S hS).obj c))
    (hqs : Surjective ((BigFppfOver.toScheme B S hS).map q))
    (hqf : Flat ((BigFppfOver.toScheme B S hS).map q))
    (hqp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map q))
    {A₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {m : A₀ ⟶ X} {r : A₀ ⟶ yoneda.obj c}
    (sq : IsPullback m r f (yoneda.map q ≫ h))
    (hr : (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsAffineHom.{u})
      (BigFppfOver.toScheme B S hS)).presheaf r) :
    (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsAffineHom.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f h) := by
  have hPqc : (@_root_.AlgebraicGeometry.IsAffineHom.{u} : MorphismProperty Scheme.{u}) ≤
      (@QuasiCompact.{u} : MorphismProperty Scheme.{u}) :=
    fun _ _ g hg => by have := hg; exact (inferInstance : QuasiCompact g)
  have hPqs : (@_root_.AlgebraicGeometry.IsAffineHom.{u} : MorphismProperty Scheme.{u}) ≤
      (@QuasiSeparated.{u} : MorphismProperty Scheme.{u}) :=
    fun _ _ g hg => by have := hg; exact (inferInstance : QuasiSeparated g)
  obtain ⟨v, w, e, hwaff, hew, P₂, ρ₁, ρ₂, s, sq₂, hs₁, hs₂, C, k, p, hpinj,
    hpact, hpo⟩ := exists_descentPushout_appTop_of_isPullback hPqc hPqs sq hr ha hc hqs hqf
  have _ := hc
  have _ := hwaff
  have hvaff : IsAffine ((BigFppfOver.toScheme B S hS).obj v) :=
    isAffine_of_isAffineHom ((BigFppfOver.toScheme B S hS).map w)
  obtain ⟨o, n, t, hoaff, hnaff, sqv, hsept⟩ :=
    exists_site_object_of_isPushout_appTop ha hc hvaff hpinj hpo
  obtain ⟨ι, hι⟩ := exists_isIso_comparison_of_descentAction hX hY hqs hqf hqp sq hew sq₂
    hs₁ hs₂ sqv (hsept s ρ₂ hpact)
  have hpn : (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsAffineHom.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map n) :=
    presheaf_yoneda_map_of_inverseImage B S hS inferInstance n hnaff
  have hRI : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsAffineHom.{u})
      (BigFppfOver.toScheme B S hS))).RespectsIso :=
    (MorphismProperty.relative_isStableUnderBaseChange (F := yoneda) _).respectsIso
  have hfinal : pullback.snd f h = ι.inv ≫ yoneda.map n := by
    rw [← hι, Iso.inv_hom_id_assoc]
  rw [hfinal]
  exact MorphismProperty.RespectsIso.precomp _ ι.inv _ hpn

/-- **Affine morphisms of schemes descend effectively along the surjective étale morphisms of
the big fppf site of `S`**, outright. Whenever a morphism `f : X ⟶ Y` of sheaves becomes
representable by an affine morphism after base change along a surjective étale morphism
`q : c ⟶ a` of the site, its base change along `h : yoneda.obj a ⟶ Y` is already representable by
an affine morphism.

This discharges the hypothesis `hdesc` of every statement which takes
`AlgebraicGeometry.Space.IsEffectiveDescentAlongSurjectiveEtale` at
`AlgebraicGeometry.IsAffineHom`, and — through
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isIntegralHom_of_isAffineHom` and
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isFinite_of_isAffineHom` — at the
integral and the finite morphisms.

Only the affine case of a descent datum is needed:
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_of_affineBase_affineSource`
reduces an arbitrary datum to one whose base and covering objects are affine, and over an affine
base the datum is an algebra descent datum along a faithfully flat ring map, which is effective
with no glueing. See the implementation notes of this file for why no Stacks tag is carried. -/
@[ega "III 1.4.16" "sufficiency direction",
  sga "1 VIII 5.6" "sufficiency",
  sga "3 X 1.6" "more general",
  sga "3 XVIII 3.13" "(iv), special case"]
theorem isEffectiveDescentAlongSurjectiveEtale_isAffineHom
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    IsEffectiveDescentAlongSurjectiveEtale B S hS
      (@_root_.AlgebraicGeometry.IsAffineHom.{u}) := by
  have _hri : MorphismProperty.RespectsIso (@_root_.AlgebraicGeometry.IsAffineHom.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have _hzl : IsZariskiLocalAtTarget (@_root_.AlgebraicGeometry.IsAffineHom.{u}) :=
    @HasAffineProperty.instIsZariskiLocalAtTarget _ _ instHasAffinePropertyIsAffineHomIsAffine
  have _hd : MorphismProperty.DescendsAlong (@_root_.AlgebraicGeometry.IsAffineHom.{u})
      (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) :=
    descendsAlong_fppf_of _
  refine isEffectiveDescentAlongSurjectiveEtale_of_affineBase_affineSource ?_
  intro X Y f hX hY a c h q ha hc hqs hqe _ A₀ m r sq hr
  obtain ⟨hqf, -, hqp⟩ := Etale.iff_flat_and_formallyUnramified.1 hqe
  exact presheaf_pullback_snd_isAffineHom_of_isPullback hX hY ha hc hqs hqf hqp sq hr


end AlgebraicGeometry.Space

end
