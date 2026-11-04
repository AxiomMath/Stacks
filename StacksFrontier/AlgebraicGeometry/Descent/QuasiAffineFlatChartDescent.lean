module

public import StacksFrontier.AlgebraicGeometry.Descent.CoveringSieveQuasiAffineDescent
public import StacksFrontier.AlgebraicGeometry.Descent.OpenImmersionFlatChartDescent
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiAffineEtaleDescent
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Effective descent of quasi-affine morphisms along a surjective flat chart, and Stacks 0265

`AlgebraicGeometry.Space.presheaf_pullback_snd_isQuasiAffineHom_of_affineBase` is Stacks 0247
over an affine base with an affine chart source, for a chart which is surjective *étale*. The
fourth step of Stacks 02W8 consumes the tag along a chart which is only surjective, flat and
locally of finite presentation — that is what step 1 of Descent, Lemma 02W3 produces from a
covering sieve — and this file proves that form and runs out its consequences, up to **Stacks
0265**: the quotient sheaf of an étale equivalence relation on an affine object of the big fppf
site of `S` is an algebraic space over `S`, with surjective étale quotient map, unconditionally.

The proof of the flat form is the proof of the étale form verbatim, with its two uses of
étaleness replaced:
`AlgebraicGeometry.Space.isLocallySurjective_datumToPullback_of_flat` for the local surjectivity
of the canonical morphism out of the datum, and
`AlgebraicGeometry.Space.presheaf_pullback_snd_isOpenImmersion_of_flatChart` for the descent of
the open subset of `Spec C` which cuts out the descended object. Neither needs a new idea: a
surjective flat morphism locally of finite presentation generates a one-element covering of the
site just as an étale one does.

## Main results

* `AlgebraicGeometry.Space.isLocallySurjective_datumToPullback_of_flat`: the datum covers the
  descended fibre product, for a flat chart.
* `AlgebraicGeometry.Space.presheaf_pullback_snd_isQuasiAffineHom_of_flatChart`: **Stacks 0247
  over an affine base with an affine chart, for a surjective flat chart of finite presentation.**
  This is the form in which the fourth step of Stacks 02W8 consumes the tag.
* `AlgebraicGeometry.Space.isRepresentable_openSubspaceOfPoints_of_affineFlatChart`: the third
  and fourth steps of Stacks 02W8 at one piece of the covering, unconditionally — this is
  `AlgebraicGeometry.Space.isRepresentable_openSubspaceOfPoints_of_flatChart` with its
  hypothesis `h0247` discharged, over an affine base.
* `AlgebraicGeometry.Space.isEffectiveDescentAlongCoveringSieve_monomorphisms_inf_lft`:
  **effective descent along the covering sieves of the site at the monomorphisms locally of
  finite type**, unconditionally. This is the descent hypothesis of the diagonal half of Stacks
  0265.
* `AlgebraicGeometry.Space.isAlgebraicSpace_quotientSheaf_of_affineBase_unconditional`,
  `AlgebraicGeometry.Space.surjective_toQuotientSheaf_of_affineBase_unconditional` and
  `AlgebraicGeometry.Space.etale_toQuotientSheaf_of_affineBase_unconditional` are **Stacks
  0265**, unconditionally.

## Implementation notes

*Why only an affine base object is needed here.* "Base object" means the base object of a
covering sieve, not the base scheme `S` and not the chart `U`: `S` carries no hypothesis
anywhere in this file. The `[IsAffine …]` binder on `U` further down is the affineness
hypothesis of Stacks 0265 itself ("Assume that `U` is affine", Lemma 65.10.4); the three Stacks
0265 statements omit it, since their proofs do not use it. The general form, with `U`
arbitrary, is Stacks 02WW and is proved and tagged in
`StacksFrontier/AlgebraicGeometry/Spaces/QuotientSheafPresentationUnconditional.lean`.
The covering-sieve predicate at the quasi-affine
morphisms is *not* proved — see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Descent.QuasiAffineEtaleDescent` for the obstruction — and it is
not needed. `AlgebraicGeometry.Space.isRepresentable_openSubspaceOfPoints_of_flatChart` consumes
it only through `AlgebraicGeometry.Space.presheaf_of_surjectiveFlatChart_of_coveringSieveDescent`
and only to conclude that one presheaf is representable; and at the one call site, inside the
hypothesis of `AlgebraicGeometry.Space.coveringSieveBody_affineBase_of_representable`, the base
object and the chart source are both affine. So the base change along the *identity* of the base,
at an affine base, is all that is asked of the tag, and that is what is proved here. The
difference matters: the covering-sieve predicate quantifies over arbitrary base objects, and
gluing the descended pieces over a non-quasi-compact base would need a uniform size bound on
them, which quasi-affineness does not give.

*No cardinal input.* `Cardinal.IsRegular` is used nowhere, and the only facts about the site's
cutoff used anywhere in the chain are
`AlgebraicGeometry.BigFppfSite.aleph0_lt_cutoff` and
`AlgebraicGeometry.BigFppfSite.cutoff_isStrongPrelimit`.

## References

* [Stacks Project, Tag 0247](https://stacks.math.columbia.edu/tag/0247)
* [Stacks Project, Tag 0265](https://stacks.math.columbia.edu/tag/0265)
* [Stacks Project, Tag 02W8](https://stacks.math.columbia.edu/tag/02W8)
* [Stacks Project, Tag 02W3](https://stacks.math.columbia.edu/tag/02W3)
* [Stacks Project, Tag 02LR](https://stacks.math.columbia.edu/tag/02LR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}
    {a c : BigFppfOver B S hS} {h : yoneda.obj a ⟶ Y} {q : c ⟶ a}
    {A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {m : A ⟶ X} {r : A ⟶ yoneda.obj c}

/-! ### The datum covers the descended fibre product, for a flat chart -/

/-- A property respecting isomorphisms holds for `g` once it holds for its base change along the
identity. -/
private theorem morphismProperty_of_pullback_snd_id {C : Type*} [Category C]
    {P : MorphismProperty C} [P.RespectsIso] {X T : C} (g : X ⟶ T) [HasPullback g (𝟙 T)]
    (hg : P (pullback.snd g (𝟙 T))) : P g := by
  rw [← ((IsPullback.id_horiz g).isoIsPullback_hom_snd _ _
    (IsPullback.of_hasPullback g (𝟙 T)))]
  exact MorphismProperty.RespectsIso.precomp _ _ _ hg

/-- **The datum covers the descended fibre product, for a flat chart.** Let `(m, r)` present `A`
as the base change of `f` along `yoneda.map q ≫ h`, with `q` surjective, flat and locally of
finite presentation. Then the canonical morphism from `A` to `X ×[Y] yoneda.obj a` — the one
whose components are `m` and `r ≫ yoneda.map q` — is locally surjective for the fppf topology of
the site.

This is `AlgebraicGeometry.Space.isLocallySurjective_datumToPullback` with étaleness of the chart
replaced by flatness together with local finite presentation: the covering on which a section
lifts is the one generated by the base change of the chart, a one-element covering of the site by
`AlgebraicGeometry.Space.sieve_generate_singleton_mem_topology_over_of_flat`. -/
theorem isLocallySurjective_datumToPullback_of_flat (sq : IsPullback m r f (yoneda.map q ≫ h))
    (hqs : Surjective ((BigFppfOver.toScheme B S hS).map q))
    (hqf : Flat ((BigFppfOver.toScheme B S hS).map q))
    (hqp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map q)) :
    Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
      ((IsPullback.of_hasPullback f h).lift m (r ≫ yoneda.map q)
        (by rw [sq.w, Category.assoc])) := by
  refine ⟨fun {T} x => ?_⟩
  obtain ⟨s, hs⟩ : ∃ s : T ⟶ a, (pullback.snd f h).app (op T) x = s := ⟨_, rfl⟩
  have hx : yonedaEquiv.symm x ≫ pullback.snd f h = yoneda.map s := by
    rw [yonedaEquiv_symm_comp_pullback_snd, hs]
  obtain ⟨α, hα1, hα2⟩ := exists_lift_of_descentDatum sq (yonedaEquiv.symm x) hx
    (pullback.fst s q) (pullback.snd s q) pullback.condition
  have hακ : α ≫ (IsPullback.of_hasPullback f h).lift m (r ≫ yoneda.map q)
      (by rw [sq.w, Category.assoc])
      = yoneda.map (pullback.fst s q) ≫ yonedaEquiv.symm x := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, (IsPullback.of_hasPullback f h).lift_fst, hα1, Category.assoc]
    · rw [Category.assoc, (IsPullback.of_hasPullback f h).lift_snd, ← Category.assoc, hα2,
        Category.assoc, hx, ← Functor.map_comp, ← Functor.map_comp, pullback.condition]
  have sqS : IsPullback ((BigFppfOver.toScheme B S hS).map (pullback.fst s q))
      ((BigFppfOver.toScheme B S hS).map (pullback.snd s q))
      ((BigFppfOver.toScheme B S hS).map s) ((BigFppfOver.toScheme B S hS).map q) :=
    (IsPullback.of_hasPullback s q).map (BigFppfOver.toScheme B S hS)
  refine (BigFppfOver.topology B S hS).superset_covering ?_
    (sieve_generate_singleton_mem_topology_over_of_flat B S hS (pullback.fst s q)
      (MorphismProperty.of_isPullback sqS.flip hqs)
      (MorphismProperty.of_isPullback sqS.flip hqf)
      (MorphismProperty.of_isPullback sqS.flip hqp))
  rintro Z k₀ ⟨Z', u, bb, hbb, hfac⟩
  cases hbb
  refine ⟨yonedaEquiv (yoneda.map u ≫ α), ?_⟩
  rw [← yonedaEquiv_comp, Category.assoc, hακ, ← Category.assoc, ← Functor.map_comp, hfac]
  exact (map_op_eq_yonedaEquiv (F := pullback f h) x _).symm

/-! ### Stacks 0247 over an affine base, for a flat chart -/

/-- **Stacks 0247 over an affine base with an affine chart, for a surjective flat chart locally
of finite presentation.** Let `f : X ⟶ Y` be a morphism of sheaves on the big fppf site of `S`,
let `h : yoneda.obj a ⟶ Y` with `a` affine, let `q : c ⟶ a` be a surjective, flat morphism of
the site locally of finite presentation with `c` affine, and let `(m, r)` present `A` as the base
change of `f` along `yoneda.map q ≫ h`, with `r` representable by quasi-affine morphisms. Then
`X ×[Y] yoneda.obj a ⟶ yoneda.obj a` is representable by quasi-affine morphisms.

This is `AlgebraicGeometry.Space.presheaf_pullback_snd_isQuasiAffineHom_of_affineBase` with
étaleness of the chart replaced by flatness together with local finite presentation, and it is
the form in which the fourth step of Stacks 02W8 consumes Stacks 0247. The proof is the same: the
datum descends on global sections to a ring `C` with `Spec Γ(v, ⊤) = c ×_a Spec C`, the invariance
of `C` gives a morphism of presheaves to `yoneda.obj (Spec C)`, and the descended object is cut
out of `Spec C` by an open subset, which descends by
`AlgebraicGeometry.Space.presheaf_pullback_snd_isOpenImmersion_of_flatChart`. -/
theorem presheaf_pullback_snd_isQuasiAffineHom_of_flatChart
    (hXs : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    (hYs : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y)
    (ha : IsAffine ((BigFppfOver.toScheme B S hS).obj a))
    (hc : IsAffine ((BigFppfOver.toScheme B S hS).obj c))
    (hqs : Surjective ((BigFppfOver.toScheme B S hS).map q))
    (hqf : Flat ((BigFppfOver.toScheme B S hS).map q))
    (hqp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map q))
    (sq : IsPullback m r f (yoneda.map q ≫ h))
    (hr : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsQuasiAffineHom.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf r) :
    (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsQuasiAffineHom.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f h) := by
  have _ha := ha
  have _hc := hc
  have _hrioi : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsOpenImmersion.{u})
      (BigFppfOver.toScheme B S hS))).RespectsIso :=
    (MorphismProperty.relative_isStableUnderBaseChange (F := yoneda) _).respectsIso
  -- the datum, its action, and the ring the datum descends to on global sections
  obtain ⟨v, w, e, hwqa, hew, P₂, ρ₁, ρ₂, s, sq₂, hs₁, hs₂, Cr, kR, pR, hpinj, po, hinvR⟩ :=
    exists_descentHullPushout_of_isPullback sq hr ha hc hqs hqf
  have vsq : IsPullback (e.inv ≫ m) (yoneda.map w) f (yoneda.map q ≫ h) := by
    refine sq.of_iso e (Iso.refl X) (Iso.refl (yoneda.obj c)) (Iso.refl Y) ?_ ?_ ?_ ?_
    · rw [Iso.refl_hom, Category.comp_id, Iso.hom_inv_id_assoc]
    · rw [Iso.refl_hom, Category.comp_id, hew]
    · simp
    · simp
  have hvqa : Scheme.IsQuasiAffine ((BigFppfOver.toScheme B S hS).obj v) :=
    (isQuasiAffineHom_iff_isQuasiAffine _).1 hwqa
  have _hvc : CompactSpace ((BigFppfOver.toScheme B S hS).obj v) := inferInstance
  obtain ⟨hvoi, hvqc⟩ :=
    (isQuasiAffineHom_iff_toSpecΓ ((BigFppfOver.toScheme B S hS).map w)).1 hwqa
  -- `Spec C` as an object of the site over `a`, with the invariant morphism out of `v`
  obtain ⟨T, i, kT, pT, hTaff, hki, hsk, hFkT, hspec⟩ :=
    exists_candidate_object_of_isPushout w q s ρ₂ ha hc hpinj po hinvR
  have _hTaff := hTaff
  -- the invariance in the form the comparison morphism consumes
  have hinv : ∀ ⦃W : BigFppfOver B S hS⦄ (ζ₁ ζ₂ : W ⟶ v),
      yoneda.map ζ₁ ≫ e.inv ≫ m = yoneda.map ζ₂ ≫ e.inv ≫ m →
      ζ₁ ≫ w ≫ q = ζ₂ ≫ w ≫ q → ζ₁ ≫ kT = ζ₂ ≫ kT := by
    intro W ζ₁ ζ₂ hmζ hqζ
    have cond : (ζ₁ ≫ w) ≫ q = ζ₂ ≫ w ≫ q := by rwa [Category.assoc]
    have hu₁ : sq₂.lift (ζ₁ ≫ w) ζ₂ cond ≫ ρ₁ = ζ₁ ≫ w := sq₂.lift_fst _ _ cond
    have hu₂ : sq₂.lift (ζ₁ ≫ w) ζ₂ cond ≫ ρ₂ = ζ₂ := sq₂.lift_snd _ _ cond
    have hus : sq₂.lift (ζ₁ ≫ w) ζ₂ cond ≫ s = ζ₁ := by
      refine descentAction_unique vsq ?_ ?_
      · rw [Category.assoc, hs₁, hu₁]
      · rw [Functor.map_comp, Category.assoc, hs₂, ← Category.assoc, ← Functor.map_comp, hu₂,
          hmζ]
    rw [← hus, Category.assoc, hsk, ← Category.assoc, hu₂]
  -- the canonical morphism from the datum to the descended fibre product
  obtain ⟨κ, hκ1, hκ2, sqκ, hκls⟩ : ∃ κ : A ⟶ pullback f h, κ ≫ pullback.fst f h = m ∧
      κ ≫ pullback.snd f h = r ≫ yoneda.map q ∧
      IsPullback κ r (pullback.snd f h) (yoneda.map q) ∧
      Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) κ :=
    ⟨_, (IsPullback.of_hasPullback f h).lift_fst m (r ≫ yoneda.map q)
        (by rw [sq.w, Category.assoc]),
      (IsPullback.of_hasPullback f h).lift_snd m (r ≫ yoneda.map q)
        (by rw [sq.w, Category.assoc]),
      sq.of_right' (IsPullback.of_hasPullback f h),
      isLocallySurjective_datumToPullback_of_flat sq hqs hqf hqp⟩
  -- the comparison morphism to `T = Spec C`
  obtain ⟨g, hgκ, hgfac⟩ := exists_comparison_of_invariant hκ1 hκ2 hκls hki e hew hinv
  -- the chart of `T` obtained by base change, and the datum read over it
  have csq : IsPullback (pullback.fst q i) (pullback.snd q i) q i := IsPullback.of_hasPullback q i
  have hq's : Surjective ((BigFppfOver.toScheme B S hS).map (pullback.snd q i)) :=
    MorphismProperty.of_isPullback (csq.map (BigFppfOver.toScheme B S hS)) hqs
  have hq'f : Flat ((BigFppfOver.toScheme B S hS).map (pullback.snd q i)) :=
    MorphismProperty.of_isPullback (csq.map (BigFppfOver.toScheme B S hS)) hqf
  have hq'p : LocallyOfFinitePresentation
      ((BigFppfOver.toScheme B S hS).map (pullback.snd q i)) :=
    MorphismProperty.of_isPullback (csq.map (BigFppfOver.toScheme B S hS)) hqp
  obtain ⟨θ, hθ₁, hθ₂⟩ : ∃ θ : v ⟶ pullback q i, θ ≫ pullback.fst q i = w ∧
      θ ≫ pullback.snd q i = kT :=
    ⟨csq.lift w kT hki.symm, csq.lift_fst _ _ hki.symm, csq.lift_snd _ _ hki.symm⟩
  have sq' : IsPullback κ (e.hom ≫ yoneda.map θ) g (yoneda.map (pullback.snd q i)) := by
    refine IsPullback.of_bot ?_ ?_ ((csq.map yoneda).flip)
    · rw [Category.assoc, ← Functor.map_comp, hθ₁, hew, hgfac]
      exact sqκ
    · rw [hgκ, Category.assoc, ← Functor.map_comp, hθ₂]
  -- the datum's object is a quasi-compact open subscheme of `c ×_a T`
  have hθoi : _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map θ) := by
    have hcomp : (BigFppfOver.toScheme B S hS).map θ
        = ((BigFppfOver.toScheme B S hS).obj v).toSpecΓ
          ≫ (hspec.isoIsPullback _ _ (csq.map (BigFppfOver.toScheme B S hS))).hom := by
      refine (csq.map (BigFppfOver.toScheme B S hS)).hom_ext ?_ ?_
      · rw [← Functor.map_comp, hθ₁, Category.assoc, hspec.isoIsPullback_hom_fst,
          ← Scheme.toSpecΓ_naturality_assoc, Scheme.toSpecΓ_isoSpec_inv, Category.comp_id]
      · rw [← Functor.map_comp, hθ₂, Category.assoc, hspec.isoIsPullback_hom_snd, hFkT]
    rw [hcomp]
    have _ := hvoi
    exact inferInstance
  have hr'oi : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsOpenImmersion.{u}) (BigFppfOver.toScheme B S hS)))
      (e.hom ≫ yoneda.map θ) :=
    MorphismProperty.RespectsIso.precomp _ e.hom _
      ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ θ).2 hθoi)
  -- the open subset of `T` descends
  have hgp : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsOpenImmersion.{u}) (BigFppfOver.toScheme B S hS))) g := by
    have hpred := presheaf_pullback_snd_isOpenImmersion_of_flatChart
      (BigFppfOver.isSheaf_pullback_yoneda_obj f h hXs hYs)
      (BigFppfOver.isSheaf_yoneda_obj B S hS T)
      (h := 𝟙 (yoneda.obj T)) (m := κ) (r := e.hom ≫ yoneda.map θ)
      (by rwa [Category.comp_id]) hq's hq'f hq'p hr'oi
    exact morphismProperty_of_pullback_snd_id g hpred
  obtain ⟨b, i₀, hi₀oi, j, hj⟩ : ∃ (b : BigFppfOver B S hS) (i₀ : b ⟶ T),
      _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map i₀) ∧
      ∃ j : pullback f h ≅ yoneda.obj b, j.hom ≫ yoneda.map i₀ = g :=
    ⟨_, _, hgp.property_snd (𝟙 (yoneda.obj T)), descentObjIso hgp.rep,
      descentObjIso_hom_comp hgp.rep⟩
  -- the descended object is quasi-compact, being covered by the datum's object
  obtain ⟨ψ, hψ⟩ : ∃ ψ : v ⟶ b, yoneda.map ψ = e.inv ≫ κ ≫ j.hom :=
    ⟨yoneda.preimage _, Functor.map_preimage _ _⟩
  have sqψ : IsPullback (yoneda.map ψ) (yoneda.map θ) (yoneda.map i₀)
      (yoneda.map (pullback.snd q i)) := by
    refine sq'.of_iso e j (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · rw [hψ, Iso.hom_inv_id_assoc]
    · rw [Iso.refl_hom, Category.comp_id]
    · rw [Iso.refl_hom, Category.comp_id, hj]
    · simp
  have hψs : Surjective ((BigFppfOver.toScheme B S hS).map ψ) :=
    MorphismProperty.of_isPullback
      (((IsPullback.of_map_of_faithful yoneda sqψ).map
        (BigFppfOver.toScheme B S hS)).flip) hq's
  have _hbc : CompactSpace ((BigFppfOver.toScheme B S hS).obj b) := by
    refine ⟨?_⟩
    rw [← Set.range_eq_univ.2 hψs.surj]
    exact isCompact_range (Scheme.Hom.continuous _)
  -- the descended morphism is quasi-affine
  have _hi₀ := hi₀oi
  have hbqa : Scheme.IsQuasiAffine ((BigFppfOver.toScheme B S hS).obj b) :=
    Scheme.IsQuasiAffine.of_isImmersion ((BigFppfOver.toScheme B S hS).map i₀)
  have hfinqa : _root_.AlgebraicGeometry.IsQuasiAffineHom
      ((BigFppfOver.toScheme B S hS).map (i₀ ≫ i)) :=
    isQuasiAffineHom_of_isQuasiAffine _ hbqa ha
  have sqfin : IsPullback (j.inv ≫ pullback.fst f h) (yoneda.map (i₀ ≫ i)) f h := by
    refine (IsPullback.of_hasPullback f h).of_iso j (Iso.refl X)
      (Iso.refl (yoneda.obj a)) (Iso.refl Y) ?_ ?_ ?_ ?_
    · rw [Iso.refl_hom, Category.comp_id, Iso.hom_inv_id_assoc]
    · rw [Iso.refl_hom, Category.comp_id, Functor.map_comp, ← Category.assoc, hj, hgfac]
    · simp
    · simp
  exact presheaf_pullback_snd_of_isPullback sqfin hfinqa


/-! ### The third and fourth steps of Stacks 02W8, unconditionally -/

/-- **The third and fourth steps of Stacks 02W8 at one piece of the covering, over an affine
base, unconditionally.** This is
`AlgebraicGeometry.Space.isRepresentable_openSubspaceOfPoints_of_flatChart` with its hypothesis
`h0247` discharged, at the cost of the affineness of the base object `a` — which is present at
the one call site, inside the hypothesis of
`AlgebraicGeometry.Space.coveringSieveBody_affineBase_of_representable`.

The third step is Stacks 02LR applied to `i ≫ ρ₀`, which is separated, locally quasi-finite and
locally of finite type because `ρ₀` is and `i` is an open immersion, and quasi-compact because
`b` is a quasi-compact scheme and the affine `c` is a quasi-separated space. The fourth step is
Stacks 0247 along a flat chart,
`AlgebraicGeometry.Space.presheaf_pullback_snd_isQuasiAffineHom_of_flatChart`: the Cartesian
square obtained by pasting `hsqb` onto the presentation of the chart exhibits `yoneda.obj b` as
the base change of `openSubspaceOfPoints B S hS G W ⟶ yoneda.obj a` along `yoneda.map p`, so that
morphism is representable, and its target is representable. -/
@[sga "3 X 5.4" "partial, special case"]
theorem isRepresentable_openSubspaceOfPoints_of_affineFlatChart
    {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hG : Presheaf.IsSheaf (BigFppfOver.topology B S hS) G)
    {a c : BigFppfOver B S hS} (π : G ⟶ yoneda.obj a) (p : c ⟶ a)
    (ha : IsAffine ((BigFppfOver.toScheme B S hS).obj a))
    (hc : IsAffine ((BigFppfOver.toScheme B S hS).obj c))
    (hps : Surjective ((BigFppfOver.toScheme B S hS).map p))
    (hpf : Flat ((BigFppfOver.toScheme B S hS).map p))
    (hpp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map p))
    {U : BigFppfOver B S hS} {g : yoneda.obj U ⟶ G} {ρ : yoneda.obj U ⟶ yoneda.obj c}
    (sqg : IsPullback g ρ π (yoneda.map p))
    (hρ : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsSeparated.{u} ⊓ @LocallyQuasiFinite ⊓ @LocallyOfFiniteType :
        MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf ρ)
    {W : Set (points B S hS G)} {b : BigFppfOver B S hS} {i : b ⟶ U}
    (hi : _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map i))
    (hbqc : IsCompact (Set.range ((BigFppfOver.toScheme B S hS).map i)))
    {k : yoneda.obj b ⟶ (openSubspaceOfPoints B S hS G W).toFunctor}
    (hsqb : IsPullback k (yoneda.map i) (openSubspaceOfPoints B S hS G W).ι g) :
    (openSubspaceOfPoints B S hS G W).toFunctor.IsRepresentable := by
  have _hc := hc
  have _hi := hi
  have _hqari := isQuasiAffineHom_respectsIso.{u}
  have _hsepbc :=
    isSeparated_inf_locallyQuasiFinite_inf_locallyOfFiniteType_isStableUnderBaseChange.{u}
  have _hripre : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsQuasiAffineHom.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).RespectsIso :=
    (MorphismProperty.relative_isStableUnderBaseChange (F := yoneda) _).respectsIso
  -- the morphism of the site underlying `ρ`, and the property it carries
  set ρ₀ : U ⟶ c := yoneda.preimage ρ
  have hρmap : yoneda.map ρ₀ = ρ := Functor.map_preimage _ _
  obtain ⟨⟨hsep, hqf⟩, hft⟩ :
      (@_root_.AlgebraicGeometry.IsSeparated.{u} ⊓ @LocallyQuasiFinite ⊓ @LocallyOfFiniteType :
        MorphismProperty Scheme.{u}) ((BigFppfOver.toScheme B S hS).map ρ₀) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ ρ₀).1 (hρmap ▸ hρ)
  have _hsep := hsep
  have _hqf := hqf
  have _hft := hft
  -- the open `b` is a quasi-compact scheme, so `i ≫ ρ₀` is a quasi-compact morphism
  have _hcs : CompactSpace ((BigFppfOver.toScheme B S hS).obj b) :=
    ⟨hi.base_open.isEmbedding.isCompact_iff.2 (by rwa [Set.image_univ])⟩
  have _hqsp : QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj c) :=
    quasiSeparatedSpace_of_isAffine _
  -- the third step: Stacks 02LR applied to `i ≫ ρ₀`
  have hQA : _root_.AlgebraicGeometry.IsQuasiAffineHom
      ((BigFppfOver.toScheme B S hS).map (i ≫ ρ₀)) := by
    rw [Functor.map_comp]
    exact isSeparated_inf_quasiFinite_le_isQuasiAffineHom _
      ⟨⟨⟨inferInstance, inferInstance⟩, inferInstance⟩, inferInstance⟩
  have hQAp : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsQuasiAffineHom.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map i ≫ ρ) := by
    rw [← hρmap, ← Functor.map_comp]
    exact (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ (i ≫ ρ₀)).2 hQA
  -- the fourth step: the pasted square is the datum of the open subfunctor over `yoneda.obj a`
  have sqF : IsPullback k (yoneda.map i ≫ ρ)
      ((openSubspaceOfPoints B S hS G W).ι ≫ π) (yoneda.map p) := hsqb.paste_vert sqg
  have hpres := presheaf_pullback_snd_isQuasiAffineHom_of_flatChart
    (isSheaf_openSubspaceOfPoints B S hS hG W) (BigFppfOver.isSheaf_yoneda_obj B S hS a)
    ha hc hps hpf hpp (h := 𝟙 (yoneda.obj a)) (m := k) (r := yoneda.map i ≫ ρ)
    (by rwa [Category.comp_id]) hQAp
  exact Functor.isRepresentable_of_relativelyRepresentable_of_target_isRepresentable _
    (morphismProperty_of_pullback_snd_id _ hpres).rep

/-! ### The covering-sieve predicate at the monomorphisms locally of finite type -/

/-- **The affine-base body of the covering-sieve predicate at the monomorphisms locally of finite
type, unconditionally.** This is
`AlgebraicGeometry.Space.coveringSieveBody_affineBase_monomorphisms_inf_locallyOfFiniteType` with
its hypothesis `h0247` discharged: steps 1, 2 and 5 of Stacks 02W8 are
`AlgebraicGeometry.Space.coveringSieveBody_affineBase_of_representable`, and steps 3 and 4 are
`AlgebraicGeometry.Space.isRepresentable_openSubspaceOfPoints_of_affineFlatChart`. -/
theorem coveringSieveBody_affineBase_monomorphisms_inf_lft :
    ∀ ⦃X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u⦄ (f : X ⟶ Y),
      Presheaf.IsSheaf (BigFppfOver.topology B S hS) X →
      Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y →
      ∀ ⦃a : BigFppfOver B S hS⦄ (h : yoneda.obj a ⟶ Y) (T : Sieve a),
        IsAffine ((BigFppfOver.toScheme B S hS).obj a) →
        T ∈ BigFppfOver.topology B S hS a →
        (∀ ⦃b : BigFppfOver B S hS⦄ (q : b ⟶ a), T q →
          ((MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType).inverseImage
            (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f (yoneda.map q ≫ h))) →
        ((MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType).inverseImage
          (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f h) := by
  have _h1 := monomorphisms_inf_locallyOfFiniteType_isZariskiLocalAtTarget.{u}
  have _h2 := monomorphisms_inf_locallyOfFiniteType_descendsAlong_fppf.{u}
  refine coveringSieveBody_affineBase_of_representable ?_
  intro G hG a c π p ha hc hps hpf hpp U g ρ sqg hρ W b i k hi hbqc hsqb
  exact isRepresentable_openSubspaceOfPoints_of_affineFlatChart hG π p ha hc hps hpf hpp sqg
    (MorphismProperty.relative_monotone
      (MorphismProperty.monotone_inverseImage (BigFppfOver.toScheme B S hS)
        monomorphisms_inf_locallyOfFiniteType_le_stacks02W8) _ hρ)
    hi hbqc hsqb

/-! ### The covering-sieve predicate at the property of Stacks 02W8 -/

/-- **The affine-base body of the covering-sieve predicate at the property of Stacks 02W8,
unconditionally.** Over an affine base object of the big fppf site of `S`, a descent datum along a
covering sieve for a morphism which is separated, locally quasi-finite and locally of finite type
after every represented base change is effective.

This is Stacks 02W8 at its own property in the *covering-sieve* shape — descent along an fppf
covering, which is the shape the source states — with all five of its steps discharged: steps 1,
2 and 5 are `AlgebraicGeometry.Space.coveringSieveBody_affineBase_of_representable` and steps 3
and 4 are `AlgebraicGeometry.Space.isRepresentable_openSubspaceOfPoints_of_affineFlatChart`.
Unlike `AlgebraicGeometry.Space.coveringSieveBody_affineBase_monomorphisms_inf_lft` no transfer
along `≤` is needed, the chart's leg carrying exactly the property being descended. -/
theorem coveringSieveBody_affineBase_isSeparated_inf_locallyQuasiFinite_inf_lft :
    ∀ ⦃X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u⦄ (f : X ⟶ Y),
      Presheaf.IsSheaf (BigFppfOver.topology B S hS) X →
      Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y →
      ∀ ⦃a : BigFppfOver B S hS⦄ (h : yoneda.obj a ⟶ Y) (T : Sieve a),
        IsAffine ((BigFppfOver.toScheme B S hS).obj a) →
        T ∈ BigFppfOver.topology B S hS a →
        (∀ ⦃b : BigFppfOver B S hS⦄ (q : b ⟶ a), T q →
          ((@_root_.AlgebraicGeometry.IsSeparated.{u} ⊓ @LocallyQuasiFinite ⊓
              @LocallyOfFiniteType : MorphismProperty Scheme.{u}).inverseImage
            (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f (yoneda.map q ≫ h))) →
        ((@_root_.AlgebraicGeometry.IsSeparated.{u} ⊓ @LocallyQuasiFinite ⊓
            @LocallyOfFiniteType : MorphismProperty Scheme.{u}).inverseImage
          (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f h) := by
  have _h1 :=
    isSeparated_inf_locallyQuasiFinite_inf_locallyOfFiniteType_isZariskiLocalAtTarget.{u}
  have _h2 := isSeparated_inf_locallyQuasiFinite_inf_locallyOfFiniteType_descendsAlong_fppf.{u}
  refine coveringSieveBody_affineBase_of_representable ?_
  intro G hG a c π p ha hc hps hpf hpp U g ρ sqg hρ W b i k hi hbqc hsqb
  exact isRepresentable_openSubspaceOfPoints_of_affineFlatChart hG π p ha hc hps hpf hpp sqg hρ
    hi hbqc hsqb

/-- **Effective descent along the covering sieves of the big fppf site of `S` at the property of
Stacks 02W8, for a site whose cutoff is a regular cardinal.** A descent datum along an fppf
covering for a separated, locally quasi-finite morphism locally of finite type is effective.

The cardinal hypothesis is not an artefact of this proof and cannot be removed by working harder
at the geometry: the geometry is complete, in
`AlgebraicGeometry.Space.coveringSieveBody_affineBase_isSeparated_inf_locallyQuasiFinite_inf_lft`,
and what `hreg` pays for is the passage from an affine base object to an arbitrary one. That
passage glues the descended pieces over the affine opens of the base, and so needs one cardinal
below the cutoff bounding them all. The two other ways the library has of paying — a size bound
on the property, `…_of_affineBase_of_size_le`, or containment in the monomorphisms,
`…_of_affineBase_of_le_monomorphisms` — are both unavailable here, since `∐_{i < κ} Spec A ⟶
Spec A` has the property of Stacks 02W8 for every `κ`. -/
theorem isEffectiveDescentAlongCoveringSieve_isSeparated_inf_lqf_inf_lft_of_isRegular
    (hreg : B.cutoff.IsRegular) :
    IsEffectiveDescentAlongCoveringSieve B S hS
      (@_root_.AlgebraicGeometry.IsSeparated.{u} ⊓ @LocallyQuasiFinite ⊓ @LocallyOfFiniteType :
        MorphismProperty Scheme.{u}) := by
  have _h1 :=
    isSeparated_inf_locallyQuasiFinite_inf_locallyOfFiniteType_isZariskiLocalAtTarget.{u}
  have _h2 := isSeparated_inf_locallyQuasiFinite_inf_locallyOfFiniteType_descendsAlong_fppf.{u}
  exact isEffectiveDescentAlongCoveringSieve_of_affineBase_of_isRegular hreg
    coveringSieveBody_affineBase_isSeparated_inf_locallyQuasiFinite_inf_lft

/-! ### Stacks 0265 -/

section Stacks0265

open Stacks.Groupoids

variable (B) (S) (hS) (U : BigFppfOver B S hS)
  [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  {R : Over S}
  (j : PreRelation R ((Over.post B.inclusion).obj U))
  [IsEtaleEquivalenceRelation j]

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  [HasSheafify (BigFppfOver.topology B S hS) (Type u)] in
/-- **Effective descent along the covering sieves of the big fppf site of `S` at the
monomorphisms locally of finite type**, unconditionally. This is
`isEffectiveDescentAlongCoveringSieve_monomorphisms_inf_lft_of_isQuasiAffineHom`
with its hypothesis discharged, and it is the descent hypothesis which the diagonal of a quotient
sheaf consumes. (The name of that conditional statement is too long to cite on one line here;
it lives in `StacksFrontier.AlgebraicGeometry.Descent.CoveringSieveQuasiAffineDescent`.)

No cardinal hypothesis and no hypothesis on the site's cutoff is used: the passage from affine to
arbitrary base objects is paid for by `AlgebraicGeometry.Scheme.size_le_of_mono`, available
because the property lies below the monomorphisms. -/
@[stacks 02W8 "effective descent along the covering sieves of the site, at the monomorphisms \
locally of finite type"]
theorem isEffectiveDescentAlongCoveringSieve_monomorphisms_inf_lft :
    IsEffectiveDescentAlongCoveringSieve B S hS
      (MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType) :=
  isEffectiveDescentAlongCoveringSieve_monomorphisms_inf_locallyOfFiniteType_of_affineBase
    B S hS coveringSieveBody_affineBase_monomorphisms_inf_lft

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj U)] in
/-- **Stacks 0265, the algebraic-space property.** The quotient sheaf of an étale equivalence
relation on an object of the big fppf site of `S` is an algebraic space over `S`. Stacks 0265
assumes the underlying scheme of `U` affine; the proof does not use it.

This is `AlgebraicGeometry.Space.isAlgebraicSpace_quotientSheaf_of_quasiAffineDescent` with its
hypothesis `h0247` discharged. -/
@[stacks 0265 "the quotient sheaf is an algebraic space"]
theorem isAlgebraicSpace_quotientSheaf_of_affineBase_unconditional :
    IsAlgebraicSpace B S hS
      (quotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion) j).obj :=
  isAlgebraicSpace_quotientSheaf_of_diagDescent B S hS U j
    (isEffectiveDescentAlongCoveringSieve_monomorphisms_inf_lft B S hS)

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj U)] in
/-- **Stacks 0265, surjectivity of the quotient map.** This is
`AlgebraicGeometry.Space.surjective_toQuotientSheaf_of_quasiAffineDescent` with its hypothesis
`h0247` discharged. -/
@[stacks 0265 "the quotient map is surjective"]
theorem surjective_toQuotientSheaf_of_affineBase_unconditional :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)))
      (yonedaEquiv.symm
        ((toQuotientSheaf (BigFppfOver.topology B S hS)
          (Over.post B.inclusion) j).app (Opposite.op U)
          (𝟙 ((Over.post B.inclusion).obj U)))) :=
  surjective_toQuotientSheaf_of_diagDescent B S hS U j
    (isEffectiveDescentAlongCoveringSieve_monomorphisms_inf_lft B S hS)

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj U)] in
/-- **Stacks 0265, étaleness of the quotient map.** This is
`AlgebraicGeometry.Space.etale_toQuotientSheaf_of_quasiAffineDescent` with its hypothesis `h0247`
discharged. -/
@[stacks 0265 "the quotient map is étale"]
theorem etale_toQuotientSheaf_of_affineBase_unconditional :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)))
      (yonedaEquiv.symm
        ((toQuotientSheaf (BigFppfOver.topology B S hS)
          (Over.post B.inclusion) j).app (Opposite.op U)
          (𝟙 ((Over.post B.inclusion).obj U)))) :=
  etale_toQuotientSheaf_of_diagDescent B S hS U j
    (isEffectiveDescentAlongCoveringSieve_monomorphisms_inf_lft B S hS)

end Stacks0265

end AlgebraicGeometry.Space

end
