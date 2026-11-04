module

public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomDescentCocycle
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcAffineChart

/-!
# The descended affine object of a flat affine chart, as a Cartesian square of the site

`AlgebraicGeometry.Space.exists_descentPushout_appTop_of_isPullback` descends the datum of an
affine morphism along a flat surjective chart `q : c ⟶ a` of affine objects of the big fppf site
of `S`, but it delivers the descended object as a *ring*: a `Γ(a)`-algebra `C` inside `Γ(v)` with
`Γ(v)` the pushout of `Γ(c) ← Γ(a) → C`. Two things were still owed before that output is a
candidate for the descended object in the sense of
`AlgebraicGeometry.Space.presheaf_pullback_snd_of_isPullback_of_invariant`: that `Spec C` be an
object of the site, and that the pushout of rings be read back as a Cartesian square of the site.
The first is `AlgebraicGeometry.exists_bigFppfOver_Spec_of_injective_appTop`. This file supplies
the second, and assembles the two into the candidate.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Space.exists_affineCandidate_of_isPullback`: **the candidate.** Let
  `f : X ⟶ Y` be a morphism of presheaves on the big fppf site of `S`, let `h : yoneda.obj a ⟶ Y`
  with `a` affine, let `q : c ⟶ a` be a surjective flat morphism of the site with `c` affine, and
  let `(m, r)` present `A₀` as the base change of `f` along `yoneda.map q ≫ h`, with `r`
  representable by an affine morphism. Then there are an object `bb` of the site and an affine
  morphism `i : bb ⟶ a` whose base change along `q` *is* the datum: a Cartesian square
  `IsPullback k w i q` of the site, an isomorphism `e : A₀ ≅ yoneda.obj v` over `yoneda.obj c`,
  and the invariance of `k`.

## Implementation notes

*Why no fpqc input appears here.* The chart is only flat, not étale, so the datum's covering is
not an fppf covering of the site and the sheaf-theoretic comparison of the descended fibre
product with `yoneda.obj bb` is *not* available — that comparison is
`AlgebraicGeometry.Space.presheaf_pullback_snd_of_isPullback_of_invariant`, which asks for an
étale chart, and its fpqc analogue needs the fpqc sheaf condition of Stacks 0APL. Nothing below
performs that comparison: the conclusion is the *candidate*, i.e. exactly the data that
comparison consumes, and every step used to produce it is algebra over the
descent of `Γ` proved in the library.

*How the Cartesian square is read off.* `AlgebraicGeometry.isPullback_SpecMap_of_isPushout` turns
the pushout of rings into a Cartesian square of affine spectra, and the four objects of that
square are the spectra of the sections of `v`, `c`, `a` and of the descended ring, all four
affine. Transporting along `AlgebraicGeometry.Scheme.isoSpec` for the first three and along the
isomorphism with `Spec C` for the fourth — the comparisons being natural by
`AlgebraicGeometry.Scheme.isoSpec_inv_naturality` — gives a Cartesian square of the *underlying
schemes* whose only new morphism is `κ`, the composite
`v ≅ Spec Γ(v) ⟶ Spec C ≅ bb`. That `κ` lifts to the site because the square commutes: its
composite to `a` is the one `w ≫ q` already has, so its composite to `S` is the structure
morphism of `v`. The square then lifts with it, the canonical functor to schemes being faithful
and reflecting fibre products.

*Where the invariance comes from.* It is needed for arbitrary `ζ₁, ζ₂ : W ⟶ v`, but it reduces
to the single equation `s ≫ k = ρ₂ ≫ k` for the action `s` and the second projection `ρ₂` of the
groupoid of the chart: given `ζ₁` and `ζ₂` agreeing over `a`, the pair `(ζ₁ ≫ w, ζ₂)` names a
morphism `θ : W ⟶ P` into the groupoid, and `θ ≫ ρ₂ = ζ₂` while `θ ≫ s = ζ₁` by the uniqueness
of the action, `AlgebraicGeometry.Space.descentAction_unique` — which is where the agreement over
`X` is used. The single equation is in turn the invariance of the descended ring under the
action, `p ≫ (G.map s).appTop = p ≫ (G.map ρ₂).appTop`, read through
`AlgebraicGeometry.Scheme.toSpecΓ_naturality`; no affineness of `P` is needed for that, because
`toSpecΓ` is defined for every scheme.

*What the conclusion is.* Stacks 0245 asserts effectivity of descent for an arbitrary fpqc
covering of an arbitrary scheme. What is reached here is the candidate for the descended object
at one chart of the site: exactly the data that the sheaf-theoretic comparison
`AlgebraicGeometry.Space.presheaf_pullback_snd_of_isPullback_of_invariant` consumes.

## References

* [Stacks Project, Tag 0245](https://stacks.math.columbia.edu/tag/0245)
* [Stacks Project, Tag 02W8](https://stacks.math.columbia.edu/tag/02W8)
* [Stacks Project, Tag 041Z](https://stacks.math.columbia.edu/tag/041Z)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}
  {a c : BigFppfOver B S hS} {h : yoneda.obj a ⟶ Y} {q : c ⟶ a}
  {A₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {m : A₀ ⟶ X} {r : A₀ ⟶ yoneda.obj c}

/-- **The candidate for the descended object of a flat affine chart.** Let `f : X ⟶ Y` be a
morphism of presheaves on the big fppf site of `S`, let `h : yoneda.obj a ⟶ Y` with the scheme
underlying `a` affine, let `q : c ⟶ a` be a morphism of the site whose underlying morphism of
schemes is surjective and flat and whose source has affine underlying scheme, and let `m, r`
present `A₀` as the base change of `f` along `yoneda.map q ≫ h`, with `r` representable by an
affine morphism.

Then the datum has a candidate for its descended object: there are objects `bb` and `v` of the
site, an affine morphism `i : bb ⟶ a`, a Cartesian square `IsPullback k w i q` exhibiting `v` as
the base change of `i` along `q`, and an isomorphism `e : A₀ ≅ yoneda.obj v` over `yoneda.obj c`
whose `k` is invariant: two morphisms into `v` which agree over `X` and over `a` agree after `k`.

This is `AlgebraicGeometry.Space.exists_descentPushout_appTop_of_isPullback` with its descended
ring turned back into an object of the site by
`AlgebraicGeometry.exists_bigFppfOver_Spec_of_injective_appTop` and its pushout of rings read
back as a Cartesian square of the site. It is exactly the hypothesis `H` of
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_of_exists_isPullback_of_invariant`
at `AlgebraicGeometry.IsAffineHom`, but for a chart which is only flat; the step which consumes a
candidate is stated for an étale chart and its flat analogue needs Stacks 0APL. -/
theorem exists_affineCandidate_of_isPullback
    (sq : IsPullback m r f (yoneda.map q ≫ h))
    (hr : (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsAffineHom.{u})
      (BigFppfOver.toScheme B S hS)).presheaf r)
    (ha : IsAffine ((BigFppfOver.toScheme B S hS).obj a))
    (hc : IsAffine ((BigFppfOver.toScheme B S hS).obj c))
    (hqs : Surjective ((BigFppfOver.toScheme B S hS).map q))
    (hqf : Flat ((BigFppfOver.toScheme B S hS).map q)) :
    ∃ (bb v : BigFppfOver B S hS) (i : bb ⟶ a) (k : v ⟶ bb) (w : v ⟶ c),
      _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map i) ∧
      IsPullback k w i q ∧
      ∃ e : A₀ ≅ yoneda.obj v, e.hom ≫ yoneda.map w = r ∧
        ∀ ⦃W : BigFppfOver B S hS⦄ (ζ₁ ζ₂ : W ⟶ v),
          yoneda.map ζ₁ ≫ e.inv ≫ m = yoneda.map ζ₂ ≫ e.inv ≫ m →
          ζ₁ ≫ w ≫ q = ζ₂ ≫ w ≫ q → ζ₁ ≫ k = ζ₂ ≫ k := by
  have hPqc : (@_root_.AlgebraicGeometry.IsAffineHom.{u} : MorphismProperty Scheme.{u}) ≤
      (@_root_.AlgebraicGeometry.QuasiCompact.{u} : MorphismProperty Scheme.{u}) := by
    intro _ _ g hg
    have : _root_.AlgebraicGeometry.IsAffineHom g := hg
    infer_instance
  have hPqs : (@_root_.AlgebraicGeometry.IsAffineHom.{u} : MorphismProperty Scheme.{u}) ≤
      (@_root_.AlgebraicGeometry.QuasiSeparated.{u} : MorphismProperty Scheme.{u}) := by
    intro _ _ g hg
    have : _root_.AlgebraicGeometry.IsAffineHom g := hg
    have : _root_.AlgebraicGeometry.IsSeparated g := inferInstance
    infer_instance
  obtain ⟨v, w, e, hwaff, hew, P, ρ₁, ρ₂, s, sq₂, hs₁, hs₂, Cr, k₀, pr,
    hpinj, hinvp, hpo⟩ :=
    exists_descentPushout_appTop_of_isPullback hPqc hPqs sq hr ha hc hqs hqf
  have _ := ha
  have _ := hc
  have hvaff : IsAffine ((BigFppfOver.toScheme B S hS).obj v) :=
    have := hwaff
    isAffine_of_isAffineHom ((BigFppfOver.toScheme B S hS).map w)
  obtain ⟨bb, i, ε, hε⟩ := exists_bigFppfOver_Spec_of_injective_appTop ha hvaff k₀ hpinj
  have _ := hvaff
  have hbb : IsAffine ((BigFppfOver.toScheme B S hS).obj bb) := IsAffine.of_isIso ε.hom
  -- the comparison morphism of underlying schemes, and the Cartesian square carrying it
  have hsq : IsPullback
      (((BigFppfOver.toScheme B S hS).obj v).isoSpec.hom ≫ Spec.map pr ≫ ε.inv)
      ((BigFppfOver.toScheme B S hS).map w) ((BigFppfOver.toScheme B S hS).map i)
      ((BigFppfOver.toScheme B S hS).map q) := by
    refine (isPullback_SpecMap_of_isPushout _ _ _ _ hpo).flip.of_iso
      (((BigFppfOver.toScheme B S hS).obj v).isoSpec.symm) ε.symm
      (((BigFppfOver.toScheme B S hS).obj c).isoSpec.symm)
      (((BigFppfOver.toScheme B S hS).obj a).isoSpec.symm) ?_ ?_ ?_ ?_
    · simp only [Iso.symm_hom]
      rw [Iso.inv_hom_id_assoc]
    · simpa only [Iso.symm_hom] using
        Scheme.isoSpec_inv_naturality ((BigFppfOver.toScheme B S hS).map w)
    · simp only [Iso.symm_hom]
      rw [← hε, Iso.inv_hom_id_assoc]
    · simpa only [Iso.symm_hom] using
        Scheme.isoSpec_inv_naturality ((BigFppfOver.toScheme B S hS).map q)
  -- the comparison morphism lifts to the site, because the square commutes over `a`
  let k : v ⟶ bb := Over.homMk (ObjectProperty.homMk
      (((BigFppfOver.toScheme B S hS).obj v).isoSpec.hom ≫ Spec.map pr ≫ ε.inv)) (by
    apply ObjectProperty.hom_ext
    show ((BigFppfOver.toScheme B S hS).obj v).isoSpec.hom ≫ Spec.map pr ≫ ε.inv ≫ bb.hom.hom
      = v.hom.hom
    rw [← Over.w i, ← Over.w w, ← Over.w q]
    show ((BigFppfOver.toScheme B S hS).obj v).isoSpec.hom ≫ Spec.map pr ≫ ε.inv ≫
        ((BigFppfOver.toScheme B S hS).map i ≫ a.hom.hom)
      = (BigFppfOver.toScheme B S hS).map w ≫
        (BigFppfOver.toScheme B S hS).map q ≫ a.hom.hom
    simp only [← Category.assoc]
    congr 1
    simpa only [Category.assoc] using hsq.w)
  have hGk : (BigFppfOver.toScheme B S hS).map k =
      ((BigFppfOver.toScheme B S hS).obj v).isoSpec.hom ≫ Spec.map pr ≫ ε.inv := rfl
  -- the invariance, which reduces to a single equation about the action
  have hsk : s ≫ k = ρ₂ ≫ k := by
    refine (BigFppfOver.toScheme B S hS).map_injective ?_
    rw [Functor.map_comp, Functor.map_comp, hGk]
    have key : ∀ t : P ⟶ v, (BigFppfOver.toScheme B S hS).map t ≫
        ((BigFppfOver.toScheme B S hS).obj v).isoSpec.hom ≫ Spec.map pr
        = ((BigFppfOver.toScheme B S hS).obj P).toSpecΓ ≫
          Spec.map (pr ≫ ((BigFppfOver.toScheme B S hS).map t).appTop) := by
      intro t
      rw [Scheme.isoSpec_hom, ← Category.assoc,
        Scheme.toSpecΓ_naturality ((BigFppfOver.toScheme B S hS).map t), Category.assoc,
        Spec.map_comp]
    rw [← Category.assoc, ← Category.assoc, ← Category.assoc, ← Category.assoc,
      Category.assoc ((BigFppfOver.toScheme B S hS).map s),
      Category.assoc ((BigFppfOver.toScheme B S hS).map ρ₂), key s, key ρ₂, hinvp]
  refine ⟨bb, v, i, k, w, inferInstance, ?_, e, hew, ?_⟩
  · refine IsPullback.of_map_of_faithful (BigFppfOver.toScheme B S hS) ?_
    rw [hGk]
    exact hsq
  · intro W ζ₁ ζ₂ hX ha'
    have vsq : IsPullback (e.inv ≫ m) (yoneda.map w) f (yoneda.map q ≫ h) := by
      refine sq.of_iso e (Iso.refl X) (Iso.refl (yoneda.obj c)) (Iso.refl Y) ?_ ?_ ?_ ?_
      · rw [Iso.refl_hom, Category.comp_id, Iso.hom_inv_id_assoc]
      · rw [Iso.refl_hom, Category.comp_id, hew]
      · simp
      · simp
    have hcond : (ζ₁ ≫ w) ≫ q = ζ₂ ≫ w ≫ q := by rw [Category.assoc]; exact ha'
    set θ := sq₂.lift (ζ₁ ≫ w) ζ₂ hcond with hθ
    have hθ₁ : θ ≫ ρ₁ = ζ₁ ≫ w := sq₂.lift_fst _ _ hcond
    have hθ₂ : θ ≫ ρ₂ = ζ₂ := sq₂.lift_snd _ _ hcond
    have hθs : θ ≫ s = ζ₁ := by
      refine descentAction_unique vsq ?_ ?_
      · rw [Category.assoc, hs₁, hθ₁]
      · rw [Functor.map_comp, Category.assoc, hs₂, ← Category.assoc, ← Functor.map_comp, hθ₂]
        exact hX.symm
    rw [← hθs, ← hθ₂, Category.assoc, Category.assoc, hsk]

end AlgebraicGeometry.Space

end
