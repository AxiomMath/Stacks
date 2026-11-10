module

public import StacksFrontier.AlgebraicGeometry.Descent.AffineFpqcChartDescent
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcQuasiAffine
public import StacksFrontier.AlgebraicGeometry.Descent.IndQuasiAffineFpqcSheaf
public import StacksFrontier.AlgebraicGeometry.Descent.InvariantOpenAlongFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiAffineFlatChartDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentabilityCriteria
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Effective descent of quasi-affine morphisms along a flat quasi-compact chart

`AlgebraicGeometry.Space.isQuasiAffineHom_isLocalAtTarget_fpqc` of
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentabilityCriteria.lean` proves the conclusion of
**Stacks 0423** — quasi-affineness of morphisms of algebraic spaces over `S` is fpqc local on the
base — from one named hypothesis,
`AlgebraicGeometry.Space.IsEffectiveQuasiAffineDescentAlongFpqc`, described there as *Stacks 0247
together with Stacks 02L7, 0APL and 041Y*. This file discharges that hypothesis from **Stacks
0APL alone**, so Stacks 0423 holds outright.

The route is the one
`StacksFrontier/AlgebraicGeometry/Descent/AffineFpqcChartDescent.lean` takes for
affine morphisms: the finite fpqc covering of an affine object of the site is replaced by the
single surjective flat quasi-compact morphism out of its coproduct, the per-member data is glued
over that coproduct by Zariski descent, and the descended object is produced over the resulting
chart. For quasi-affine morphisms the descended object is not produced in one step, because it is
only an open piece of the affine hull of the datum, so the chart form of Stacks 0247 is proved
here rather than reduced to the generic descent step from a candidate.

## Main results

* `AlgebraicGeometry.Space.isLocallyInjective_pullback_snd_of_fpqc` and
  `AlgebraicGeometry.Space.presheaf_pullback_snd_isOpenImmersion_of_fpqcChart`: the two statements
  of `StacksFrontier/AlgebraicGeometry/Descent/OpenImmersionFlatChartDescent.lean` with
  `AlgebraicGeometry.LocallyOfFinitePresentation` on the chart replaced by
  `AlgebraicGeometry.QuasiCompact`.
* `AlgebraicGeometry.Space.presheaf_pullback_snd_isQuasiAffineHom_of_fpqcChart`: **Stacks 0247
  over an affine base with an affine chart, for a surjective flat quasi-compact chart.**
* `AlgebraicGeometry.Space.isEffectiveQuasiAffineDescentAlongFpqc_of_isSheaf_fpqc`:
  `AlgebraicGeometry.Space.IsEffectiveQuasiAffineDescentAlongFpqc` from Stacks 0APL.
* `AlgebraicGeometry.Space.isLocalAtTarget_isQuasiAffineHom_fpqc`: **Stacks 0423**, Lemma
  74.11.20 of *Descent and Algebraic Spaces*: quasi-affineness of morphisms of algebraic spaces
  over `S` is fpqc local on the base in the sense of Definition 74.10.1 (Stacks 03YH).

## Implementation notes

*Where local finite presentation of the chart was used, and what replaces it.* In the
flat-chart descent of open immersions it is consumed twice. Once to generate a one-element
covering of the site, and there
`AlgebraicGeometry.Space.sieve_generate_singleton_mem_fpqcTopology_over` serves instead, which is
why every topology in this file is the fpqc one and why the sheaf conditions are the fpqc sheaf
conditions — for an algebraic space that is Stacks 0APL. Once to see the chart as an open map,
`AlgebraicGeometry.UniversallyOpen.of_flat`, which is Stacks 01UA and genuinely needs local
finite presentation; a surjective flat quasi-compact morphism need not be open. What replaces it
is Stacks 03N0, `AlgebraicGeometry.existsUnique_opens_preimage_eq`: the open piece cut out on the
chart is invariant under the datum, by
`AlgebraicGeometry.Space.preimage_range_eq_preimage_range`, so it is the inverse image of a
unique open of the base, which is the open subscheme the descended object is cut out of. Its
underlying set is the image of the open piece, by surjectivity of the chart, so the rest of the
argument — the stability of the open piece and the identification of the descended fibre product
with the open subscheme it produces — is unchanged.

*Why the generic descent step from a candidate is not used.*
`AlgebraicGeometry.Space.presheaf_pullback_snd_of_isPullback_of_invariant_of_fpqc` is generic in
the property, and the quasi-affine candidate's two ingredients,
`AlgebraicGeometry.Space.exists_descentHullPushout_of_isPullback` and
`AlgebraicGeometry.Space.exists_candidate_object_of_isPushout`, ask nothing of the chart beyond
surjectivity and flatness. The candidate they produce is the affine hull `Spec C`, not the
descended object: the latter is an open subscheme of `Spec C`, and exhibiting it as one is
exactly the open-immersion descent proved here. So the chart form of Stacks 0247 is assembled
directly, as
`AlgebraicGeometry.Space.presheaf_pullback_snd_isQuasiAffineHom_of_flatChart` assembles it for a
chart of finite presentation.

*Which private helper is duplicated.*
`AlgebraicGeometry.Space.map_op_eq_yonedaEquiv` restates a section of a presheaf as a
morphism out of a representable presheaf. The same statement is private in
`StacksFrontier/AlgebraicGeometry/Descent/OpenImmersionFlatChartDescent.lean` and in
`StacksFrontier/AlgebraicGeometry/Descent/AffineFpqcChartDescent.lean`, so it is restated here
rather than reused.

## References

* [Stacks Project, Tag 0247](https://stacks.math.columbia.edu/tag/0247)
* [Stacks Project, Tag 02L7](https://stacks.math.columbia.edu/tag/02L7)
* [Stacks Project, Tag 03N0](https://stacks.math.columbia.edu/tag/03N0)
* [Stacks Project, Tag 0423](https://stacks.math.columbia.edu/tag/0423)
* [Stacks Project, Tag 0APL](https://stacks.math.columbia.edu/tag/0APL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}
    {a c : BigFppfOver B S hS} {h : yoneda.obj a ⟶ Y} {q : c ⟶ a}
    {A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {m : A ⟶ X} {r : A ⟶ yoneda.obj c}

/-- A sieve containing every morphism that factors through the base change of a surjective flat
quasi-compact `q` along some `s` is a covering sieve for the fpqc topology. -/
private theorem mem_fpqcTopology_of_forall_factor_pullback_fst {T : BigFppfOver B S hS}
    (s : T ⟶ a) (hqs : Surjective ((BigFppfOver.toScheme B S hS).map q))
    (hqf : Flat ((BigFppfOver.toScheme B S hS).map q))
    (hqc : QuasiCompact ((BigFppfOver.toScheme B S hS).map q)) (R : Sieve T)
    (hR : ∀ ⦃Z : BigFppfOver B S hS⦄ (k : Z ⟶ T) (u : Z ⟶ pullback s q),
      u ≫ pullback.fst s q = k → R k) :
    R ∈ (Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS)).toGrothendieck T := by
  have sqS : IsPullback ((BigFppfOver.toScheme B S hS).map (pullback.fst s q))
      ((BigFppfOver.toScheme B S hS).map (pullback.snd s q))
      ((BigFppfOver.toScheme B S hS).map s) ((BigFppfOver.toScheme B S hS).map q) :=
    (IsPullback.of_hasPullback s q).map (BigFppfOver.toScheme B S hS)
  refine (Scheme.fpqcPrecoverage.comap
      (BigFppfOver.toScheme B S hS)).toGrothendieck.superset_covering ?_
    (sieve_generate_singleton_mem_fpqcTopology_over B S hS (pullback.fst s q)
      (MorphismProperty.of_isPullback sqS.flip hqs)
      (MorphismProperty.of_isPullback sqS.flip hqf)
      (MorphismProperty.of_isPullback sqS.flip hqc))
  rintro Z k ⟨Z', u, bb, hbb, hfac⟩
  cases hbb
  exact hR k u hfac

/-- The base change of an isomorphic cone is a pullback square: replacing the apex along `j`
and the second leg by `p₂'` with `j.hom ≫ p₂' = p₂`. -/
private theorem isPullback_inv_comp_of_hom_comp_eq {C : Type*} [Category C]
    {P P' X Y Z : C} {p₁ : P ⟶ X} {p₂ : P ⟶ Y} {p₂' : P' ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (sq : IsPullback p₁ p₂ f g) (j : P ≅ P') (hj : j.hom ≫ p₂' = p₂) :
    IsPullback (j.inv ≫ p₁) p₂' f g :=
  sq.of_iso j (Iso.refl X) (Iso.refl Y) (Iso.refl Z) (by simp) (by simp [hj]) (by simp) (by simp)

/-- **The descended morphism is locally injective, for a flat quasi-compact chart.** If the
descent datum `r` is a monomorphism, then the projection `X ×[Y] yoneda.obj a ⟶ yoneda.obj a` is
locally injective for the fpqc topology: two sections with the same image agree after the base
change of the chart, because they then define the same section of `A`.

This is `AlgebraicGeometry.Space.isLocallyInjective_pullback_snd_of_flat` with local finite
presentation of the chart replaced by quasi-compactness; the covering on which the two sections
are compared is the one generated by the base change of the chart, which is an fpqc covering of
the site by `AlgebraicGeometry.Space.sieve_generate_singleton_mem_fpqcTopology_over`. -/
theorem isLocallyInjective_pullback_snd_of_fpqc (sq : IsPullback m r f (yoneda.map q ≫ h))
    (hrmono : Mono r) (hqs : Surjective ((BigFppfOver.toScheme B S hS).map q))
    (hqf : Flat ((BigFppfOver.toScheme B S hS).map q))
    (hqc : QuasiCompact ((BigFppfOver.toScheme B S hS).map q)) :
    Presheaf.IsLocallyInjective
      (Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS)).toGrothendieck
      (pullback.snd f h) := by
  constructor
  intro T x y hxy
  obtain ⟨s, hs⟩ : ∃ s : T.unop ⟶ a, (pullback.snd f h).app T x = s := ⟨_, rfl⟩
  have hx : yonedaEquiv.symm x ≫ pullback.snd f h = yoneda.map s := by
    rw [yonedaEquiv_symm_comp_pullback_snd, hs]
  have hy : yonedaEquiv.symm y ≫ pullback.snd f h = yoneda.map s := by
    rw [yonedaEquiv_symm_comp_pullback_snd, ← hxy, hs]
  obtain ⟨α, hα1, hα2⟩ := exists_lift_of_descentDatum sq (yonedaEquiv.symm x) hx
    (pullback.fst s q) (pullback.snd s q) pullback.condition
  obtain ⟨α', hα1', hα2'⟩ := exists_lift_of_descentDatum sq (yonedaEquiv.symm y) hy
    (pullback.fst s q) (pullback.snd s q) pullback.condition
  have hαα : α = α' := (cancel_mono r).1 (hα2.trans hα2'.symm)
  have key : yoneda.map (pullback.fst s q) ≫ yonedaEquiv.symm x =
      yoneda.map (pullback.fst s q) ≫ yonedaEquiv.symm y := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, ← hα1, ← hα1', hαα]
    · rw [Category.assoc, Category.assoc, hx, hy]
  have h1 : (pullback f h).map (pullback.fst s q).op x =
      (pullback f h).map (pullback.fst s q).op y :=
    calc (pullback f h).map (pullback.fst s q).op x
        = yonedaEquiv (yoneda.map (pullback.fst s q) ≫ yonedaEquiv.symm x) :=
          map_op_eq_yonedaEquiv (F := pullback f h) x _
      _ = yonedaEquiv (yoneda.map (pullback.fst s q) ≫ yonedaEquiv.symm y) := by rw [key]
      _ = (pullback f h).map (pullback.fst s q).op y :=
          (map_op_eq_yonedaEquiv (F := pullback f h) y _).symm
  refine mem_fpqcTopology_of_forall_factor_pullback_fst s hqs hqf hqc _ ?_
  intro Z k u hfac
  change (pullback f h).map k.op x = (pullback f h).map k.op y
  rw [← hfac, op_comp, Functor.map_comp_apply, Functor.map_comp_apply, h1]

/-- An open with the same inverse image under both projections of one pullback square of
`φ` along itself has the same inverse image under both projections of the chosen pullback. -/
private theorem pullback_fst_preimage_eq_snd_preimage_of_isPullback {X' Y' P : Scheme.{u}}
    {φ : X' ⟶ Y'} {p₁ p₂ : P ⟶ X'} (sqD : IsPullback p₁ p₂ φ φ) {V : X'.Opens}
    (hV : p₁ ⁻¹ᵁ V = p₂ ⁻¹ᵁ V) :
    Limits.pullback.fst φ φ ⁻¹ᵁ V = Limits.pullback.snd φ φ ⁻¹ᵁ V :=
  calc Limits.pullback.fst φ φ ⁻¹ᵁ V
      = (((IsPullback.of_hasPullback φ φ).isoIsPullback _ _ sqD).hom ≫ p₁) ⁻¹ᵁ V := by
        rw [(IsPullback.of_hasPullback φ φ).isoIsPullback_hom_fst _ _ sqD]
    _ = (((IsPullback.of_hasPullback φ φ).isoIsPullback _ _ sqD).hom ≫ p₂) ⁻¹ᵁ V := by
        rw [Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage, hV]
    _ = Limits.pullback.snd φ φ ⁻¹ᵁ V := by
        rw [(IsPullback.of_hasPullback φ φ).isoIsPullback_hom_snd _ _ sqD]

/-- **The descended open is reached locally.** If `r` is representable by open immersions and the
base change of `f` along `h` factors through `yoneda.map i` via `l`, where the inverse image along
`q` of the range of `i` lies in the open piece cut out on `c`, then `l` is locally surjective for
the fpqc topology. -/
private theorem isLocallySurjective_of_comp_yoneda_map_eq_pullback_snd
    (sq : IsPullback m r f (yoneda.map q ≫ h))
    (hqs : Surjective ((BigFppfOver.toScheme B S hS).map q))
    (hqf : Flat ((BigFppfOver.toScheme B S hS).map q))
    (hqc : QuasiCompact ((BigFppfOver.toScheme B S hS).map q))
    (hr : (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsOpenImmersion.{u})
      (BigFppfOver.toScheme B S hS)).presheaf r)
    {b : BigFppfOver B S hS} {i : b ⟶ a} [Mono i] {l : pullback f h ⟶ yoneda.obj b}
    (hl : l ≫ yoneda.map i = pullback.snd f h)
    (hrange : ((BigFppfOver.toScheme B S hS).map q).base ⁻¹'
        Set.range ((BigFppfOver.toScheme B S hS).map i).base ⊆
      Set.range ((BigFppfOver.toScheme B S hS).map (hr.rep.snd (𝟙 (yoneda.obj c)))).base) :
    Presheaf.IsLocallySurjective
      (Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS)).toGrothendieck l := by
  constructor
  intro T w
  refine mem_fpqcTopology_of_forall_factor_pullback_fst (w ≫ i) hqs hqf hqc _ ?_
  intro Z k u hfac
  have heq : (u ≫ pullback.snd (w ≫ i) q) ≫ q = (k ≫ w) ≫ i := by
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, hfac, Category.assoc]
  have hrangesub : Set.range ((BigFppfOver.toScheme B S hS).map
      (u ≫ pullback.snd (w ≫ i) q)).base ⊆
        Set.range ((BigFppfOver.toScheme B S hS).map (hr.rep.snd (𝟙 (yoneda.obj c)))).base := by
    rintro z ⟨z0, rfl⟩
    refine hrange ?_
    rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, ← Functor.map_comp, heq,
      Functor.map_comp, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  obtain ⟨vv, hvv⟩ := exists_comp_eq_of_isOpenImmersion (hr.rep.snd (𝟙 (yoneda.obj c)))
    (hr.property_snd (𝟙 (yoneda.obj c))) (u ≫ pullback.snd (w ≫ i) q) hrangesub
  have hw0 : hr.rep.fst (𝟙 (yoneda.obj c)) ≫ r =
      yoneda.map (hr.rep.snd (𝟙 (yoneda.obj c))) := by
    simpa only [Category.comp_id] using hr.rep.w (𝟙 (yoneda.obj c))
  have hsqw : m ≫ f = (r ≫ yoneda.map q) ≫ h := by rw [sq.w, Category.assoc]
  have hxisnd : (yoneda.map vv ≫ hr.rep.fst (𝟙 (yoneda.obj c)) ≫
        pullback.lift m (r ≫ yoneda.map q) hsqw) ≫ pullback.snd f h =
      yoneda.map ((k ≫ w) ≫ i) := by
    calc (yoneda.map vv ≫ hr.rep.fst (𝟙 (yoneda.obj c)) ≫
          pullback.lift m (r ≫ yoneda.map q) hsqw) ≫ pullback.snd f h
        = yoneda.map vv ≫ (hr.rep.fst (𝟙 (yoneda.obj c)) ≫ r) ≫ yoneda.map q := by
          simp only [Category.assoc]
          rw [pullback.lift_snd]
      _ = yoneda.map ((vv ≫ hr.rep.snd (𝟙 (yoneda.obj c))) ≫ q) := by
          rw [hw0, Functor.map_comp, Functor.map_comp, Category.assoc]
      _ = yoneda.map ((k ≫ w) ≫ i) := by rw [hvv, heq]
  have hxil : (yoneda.map vv ≫ hr.rep.fst (𝟙 (yoneda.obj c)) ≫
      pullback.lift m (r ≫ yoneda.map q) hsqw) ≫ l = yoneda.map (k ≫ w) := by
    rw [← cancel_mono (yoneda.map i), Category.assoc, hl, hxisnd, ← Functor.map_comp]
  refine ⟨yonedaEquiv (yoneda.map vv ≫ hr.rep.fst (𝟙 (yoneda.obj c)) ≫
    pullback.lift m (r ≫ yoneda.map q) hsqw), ?_⟩
  rw [← yonedaEquiv_comp, hxil, yonedaEquiv_yoneda_map]
  rfl

/-- The image of an open under a surjective morphism of schemes is open, as soon as the open is
the inverse image of an open of the target. -/
private theorem isOpen_image_of_surjective_of_preimage_eq {X' Y' : Scheme.{u}} {φ : X' ⟶ Y'}
    (hφ : Surjective φ) {V : X'.Opens} {W : Y'.Opens} (hW : φ ⁻¹ᵁ W = V) :
    IsOpen (φ.base '' V) := by
  have himg : φ.base '' V = (W : Set Y') := by
    refine Set.eq_of_subset_of_subset ?_ ?_
    · rintro z ⟨z0, hz0, rfl⟩
      have hz0' : z0 ∈ φ ⁻¹ᵁ W := by rw [hW]; exact hz0
      exact hz0'
    · intro z hz
      obtain ⟨z0, rfl⟩ := hφ.surj z
      refine ⟨z0, ?_, rfl⟩
      have hz0' : z0 ∈ φ ⁻¹ᵁ W := hz
      rw [hW] at hz0'
      exact hz0'
  rw [himg]
  exact W.isOpen

/-- A locally injective and locally surjective morphism of fpqc sheaves on the big fppf site of
`S` is an isomorphism. -/
private theorem isIso_of_isLocallyInjective_of_isLocallySurjective_fpqc
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {l : F ⟶ G}
    (hF : Presheaf.IsSheaf
      (Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS)).toGrothendieck F)
    (hG : Presheaf.IsSheaf
      (Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS)).toGrothendieck G)
    (hli : Presheaf.IsLocallyInjective
      (Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS)).toGrothendieck l)
    (hls : Presheaf.IsLocallySurjective
      (Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS)).toGrothendieck l) :
    IsIso l := by
  have hsh : IsIso ((⟨l⟩ :
      (⟨F, hF⟩ : Sheaf
        (Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS)).toGrothendieck
          (Type u)) ⟶ ⟨G, hG⟩)) :=
    (Sheaf.isLocallyBijective_iff_isIso _).1 ⟨hli, hls⟩
  exact inferInstanceAs (IsIso ((sheafToPresheaf
    (Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS)).toGrothendieck
      (Type u)).map
    ((⟨l⟩ : (⟨F, hF⟩ : Sheaf
      (Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS)).toGrothendieck
        (Type u)) ⟶ ⟨G, hG⟩))))

/-- **Effective descent of open immersions along a surjective flat quasi-compact chart.**
Whenever a morphism `f : X ⟶ Y` of fpqc sheaves on the big fppf site of `S` becomes representable
by an open immersion after base change along a morphism `q : c ⟶ a` of the site which is
surjective, flat and quasi-compact, its base change along `h : yoneda.obj a ⟶ Y` is already
representable by an open immersion.

This is `AlgebraicGeometry.Space.presheaf_pullback_snd_isOpenImmersion_of_flatChart` with local
finite presentation of the chart replaced by quasi-compactness. The descended object is the open
subscheme of `a` whose inverse image along `q` is the open piece `V` cut out on `c`: that open of
`a` exists and is unique by Stacks 03N0, the invariance of `V` which 03N0 asks for being
`AlgebraicGeometry.Space.preimage_range_eq_preimage_range`, and its underlying set is the image
of `V` because `q` is surjective. -/
@[ega "IV 2.7.1" "(x)"]
theorem presheaf_pullback_snd_isOpenImmersion_of_fpqcChart
    (hX : Presheaf.IsSheaf
      (Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS)).toGrothendieck X)
    (hY : Presheaf.IsSheaf
      (Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS)).toGrothendieck Y)
    (sq : IsPullback m r f (yoneda.map q ≫ h))
    (hqs : Surjective ((BigFppfOver.toScheme B S hS).map q))
    (hqf : Flat ((BigFppfOver.toScheme B S hS).map q))
    (hqc : QuasiCompact ((BigFppfOver.toScheme B S hS).map q))
    (hr : (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsOpenImmersion.{u})
      (BigFppfOver.toScheme B S hS)).presheaf r) :
    (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsOpenImmersion.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f h) := by
  have hRIoi : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsOpenImmersion.{u})
      (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  have hRIpre : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsOpenImmersion.{u})
      (BigFppfOver.toScheme B S hS))).RespectsIso :=
    (MorphismProperty.relative_isStableUnderBaseChange (F := yoneda) _).respectsIso
  have hmono : (@_root_.AlgebraicGeometry.IsOpenImmersion.{u}) ≤
      MorphismProperty.monomorphisms Scheme.{u} := fun _ _ g hg => by
    have := hg; exact (inferInstance : Mono g)
  have hrmono : Mono r := mono_of_presheaf hmono hr
  have hr'oi : _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (hr.rep.snd (𝟙 (yoneda.obj c)))) :=
    hr.property_snd (𝟙 (yoneda.obj c))
  obtain ⟨Vc, hVcdef⟩ : ∃ Vc : Set ((BigFppfOver.toScheme B S hS).obj c),
      Set.range ((BigFppfOver.toScheme B S hS).map
        (hr.rep.snd (𝟙 (yoneda.obj c)))).base = Vc := ⟨_, rfl⟩
  have hVcopen : IsOpen Vc := by
    rw [← hVcdef]
    exact IsOpenImmersion.isOpen_range _
  have hkey := preimage_range_eq_preimage_range sq hr.rep
  rw [hVcdef] at hkey
  have sqD : IsPullback ((BigFppfOver.toScheme B S hS).map (pullback.fst q q))
      ((BigFppfOver.toScheme B S hS).map (pullback.snd q q))
      ((BigFppfOver.toScheme B S hS).map q) ((BigFppfOver.toScheme B S hS).map q) :=
    (IsPullback.of_hasPullback q q).map (BigFppfOver.toScheme B S hS)
  have hstab : ((BigFppfOver.toScheme B S hS).map q).base ⁻¹'
      (((BigFppfOver.toScheme B S hS).map q).base '' Vc) ⊆ Vc := by
    have h1 := Scheme.image_preimage_eq_of_isPullback sqD Vc
    rw [hkey] at h1
    rw [← h1]
    exact Set.image_preimage_subset _ _
  have hinvS := pullback_fst_preimage_eq_snd_preimage_of_isPullback sqD (V := ⟨Vc, hVcopen⟩)
    (TopologicalSpace.Opens.ext hkey)
  obtain ⟨W, hW, -⟩ := existsUnique_opens_preimage_eq ((BigFppfOver.toScheme B S hS).map q)
    ⟨Vc, hVcopen⟩ hinvS
  have hVopen : IsOpen (((BigFppfOver.toScheme B S hS).map q).base '' Vc) :=
    isOpen_image_of_surjective_of_preimage_eq hqs hW
  obtain ⟨b, i, hioi, hirange, hiuniv⟩ := exists_restrict_bigFppfOver a
    ⟨((BigFppfOver.toScheme B S hS).map q).base '' Vc, hVopen⟩
  have hirange' : Set.range ((BigFppfOver.toScheme B S hS).map i).base =
      ((BigFppfOver.toScheme B S hS).map q).base '' Vc := hirange
  have hmonoi : Mono i := (BigFppfOver.toScheme B S hS).mono_of_mono_map
    (inferInstance : Mono ((BigFppfOver.toScheme B S hS).map i))
  have hlr : Subfunctor.range (pullback.snd f h) ≤ Subfunctor.range (yoneda.map i) := by
    rintro T _ ⟨x, rfl⟩
    have hsub := range_subset_image_range sq hr.rep hqs (yonedaEquiv.symm x)
      (yonedaEquiv_symm_comp_pullback_snd x)
    rw [hVcdef] at hsub
    obtain ⟨g, hg⟩ := hiuniv ((pullback.snd f h).app T x) hsub
    exact ⟨g, hg⟩
  obtain ⟨l, hlfac⟩ : ∃ l : pullback f h ⟶ yoneda.obj b,
      l ≫ yoneda.map i = pullback.snd f h := by
    have h1 : inv (Subfunctor.toRange (yoneda.map i)) ≫ yoneda.map i =
        (Subfunctor.range (yoneda.map i)).ι :=
      (IsIso.inv_comp_eq _).2 (Subfunctor.toRange_ι (yoneda.map i)).symm
    refine ⟨Subfunctor.lift (pullback.snd f h) hlr ≫
      inv (Subfunctor.toRange (yoneda.map i)), ?_⟩
    rw [Category.assoc, h1, Subfunctor.lift_ι]
  have hli : Presheaf.IsLocallyInjective
      (Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS)).toGrothendieck l :=
    have := isLocallyInjective_pullback_snd_of_fpqc sq hrmono hqs hqf hqc
    Presheaf.isLocallyInjective_of_isLocallyInjective_fac _ hlfac
  have hls := isLocallySurjective_of_comp_yoneda_map_eq_pullback_snd sq hqs hqf hqc hr hlfac
    (by rw [hirange', hVcdef]; exact hstab)
  have hliso : IsIso l := isIso_of_isLocallyInjective_of_isLocallySurjective_fpqc
    (BigFppfOver.isSheaf_fpqc_pullback_yoneda_obj f h hX hY)
    (BigFppfOver.isSheaf_fpqc_yoneda_obj B S hS b) hli hls
  have hpi : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsOpenImmersion.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map i) :=
    presheaf_yoneda_map_of_inverseImage B S hS inferInstance i hioi
  rw [← hlfac]
  exact MorphismProperty.RespectsIso.precomp _ l _ hpi

/-- **Stacks 0247 over an affine base with an affine chart, for a surjective flat quasi-compact
chart.** Let `f : X ⟶ Y` be a morphism of fpqc sheaves on the big fppf site of `S`, let
`h : yoneda.obj a ⟶ Y` with `a` affine, let `q : c ⟶ a` be a surjective, flat, quasi-compact
morphism of the site with `c` affine, and let `(m, r)` present `A` as the base change of `f`
along `yoneda.map q ≫ h`, with `r` representable by quasi-affine morphisms. Then
`X ×[Y] yoneda.obj a ⟶ yoneda.obj a` is representable by quasi-affine morphisms.

This is `AlgebraicGeometry.Space.presheaf_pullback_snd_isQuasiAffineHom_of_flatChart` with local
finite presentation of the chart replaced by quasi-compactness, and it is the form in which the
fpqc locality of quasi-affineness consumes Stacks 0247. The proof is the same: the datum descends
on global sections to a ring `C` with `Spec Γ(v, ⊤) = c ×_a Spec C`, the invariance of `C` gives a
morphism of presheaves to `yoneda.obj (Spec C)`, and the descended object is cut out of `Spec C`
by an open subset, which descends by
`AlgebraicGeometry.Space.presheaf_pullback_snd_isOpenImmersion_of_fpqcChart`. -/
@[ega "IV 2.7.1" "(xiv), special case"]
theorem presheaf_pullback_snd_isQuasiAffineHom_of_fpqcChart
    (hXs : Presheaf.IsSheaf
      (Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS)).toGrothendieck X)
    (hYs : Presheaf.IsSheaf
      (Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS)).toGrothendieck Y)
    (ha : IsAffine ((BigFppfOver.toScheme B S hS).obj a))
    (hc : IsAffine ((BigFppfOver.toScheme B S hS).obj c))
    (hqs : Surjective ((BigFppfOver.toScheme B S hS).map q))
    (hqf : Flat ((BigFppfOver.toScheme B S hS).map q))
    (hqc : QuasiCompact ((BigFppfOver.toScheme B S hS).map q))
    (sq : IsPullback m r f (yoneda.map q ≫ h))
    (hr : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsQuasiAffineHom.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf r) :
    (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsQuasiAffineHom.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f h) := by
  have _hrioi : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsOpenImmersion.{u})
      (BigFppfOver.toScheme B S hS))).RespectsIso :=
    (MorphismProperty.relative_isStableUnderBaseChange (F := yoneda) _).respectsIso
  -- the datum, its action, and the ring the datum descends to on global sections
  obtain ⟨v, w, e, hwqa, hew, P₂, ρ₁, ρ₂, s, sq₂, hs₁, hs₂, Cr, kR, pR, hpinj, po, hinvR⟩ :=
    exists_descentHullPushout_of_isPullback sq hr ha hc hqs hqf
  have vsq : IsPullback (e.inv ≫ m) (yoneda.map w) f (yoneda.map q ≫ h) :=
    isPullback_inv_comp_of_hom_comp_eq sq e hew
  have hvqa : Scheme.IsQuasiAffine ((BigFppfOver.toScheme B S hS).obj v) :=
    (isQuasiAffineHom_iff_isQuasiAffine _).1 hwqa
  obtain ⟨hvoi, hvqc⟩ :=
    (isQuasiAffineHom_iff_toSpecΓ ((BigFppfOver.toScheme B S hS).map w)).1 hwqa
  -- `Spec C` as an object of the site over `a`, with the invariant morphism out of `v`
  obtain ⟨T, i, kT, pT, hTaff, hki, hsk, hFkT, hspec⟩ :=
    exists_candidate_object_of_isPushout w q s ρ₂ ha hc hpinj po hinvR
  -- the invariance in the form the comparison morphism consumes
  have hinv : ∀ ⦃W : BigFppfOver B S hS⦄ (ζ₁ ζ₂ : W ⟶ v),
      yoneda.map ζ₁ ≫ e.inv ≫ m = yoneda.map ζ₂ ≫ e.inv ≫ m →
      ζ₁ ≫ w ≫ q = ζ₂ ≫ w ≫ q → ζ₁ ≫ kT = ζ₂ ≫ kT := by
    intro W ζ₁ ζ₂ hmζ hqζ
    have cond : (ζ₁ ≫ w) ≫ q = ζ₂ ≫ w ≫ q := (Category.assoc _ _ _).trans hqζ
    have hu₂ : sq₂.lift (ζ₁ ≫ w) ζ₂ cond ≫ ρ₂ = ζ₂ := sq₂.lift_snd _ _ cond
    have hus : sq₂.lift (ζ₁ ≫ w) ζ₂ cond ≫ s = ζ₁ := by
      refine descentAction_unique vsq ?_ ?_
      · rw [Category.assoc, hs₁, sq₂.lift_fst]
      · rw [Functor.map_comp, Category.assoc, hs₂, ← Category.assoc, ← Functor.map_comp, hu₂,
          hmζ]
    calc ζ₁ ≫ kT = (sq₂.lift (ζ₁ ≫ w) ζ₂ cond ≫ s) ≫ kT := by rw [hus]
      _ = (sq₂.lift (ζ₁ ≫ w) ζ₂ cond ≫ ρ₂) ≫ kT := by
          rw [Category.assoc, Category.assoc, hsk]
      _ = ζ₂ ≫ kT := by rw [hu₂]
  -- the canonical morphism from the datum to the descended fibre product
  obtain ⟨κ, hκ1, hκ2, sqκ, hκls⟩ : ∃ κ : A ⟶ pullback f h, κ ≫ pullback.fst f h = m ∧
      κ ≫ pullback.snd f h = r ≫ yoneda.map q ∧
      IsPullback κ r (pullback.snd f h) (yoneda.map q) ∧
      Presheaf.IsLocallySurjective
        (Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS)).toGrothendieck κ :=
    ⟨_, (IsPullback.of_hasPullback f h).lift_fst m (r ≫ yoneda.map q)
        (by rw [sq.w, Category.assoc]),
      (IsPullback.of_hasPullback f h).lift_snd m (r ≫ yoneda.map q)
        (by rw [sq.w, Category.assoc]),
      sq.of_right' (IsPullback.of_hasPullback f h),
      isLocallySurjective_datumToPullback_of_fpqc sq hqs hqf hqc⟩
  -- the comparison morphism to `T = Spec C`
  obtain ⟨g, hgκ, hgfac⟩ := exists_comparison_of_invariant_of_isSheaf
    (Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS)).toGrothendieck
    hκ1 hκ2 hκls (BigFppfOver.isSheaf_fpqc_yoneda_obj B S hS T)
    (BigFppfOver.isSheaf_fpqc_yoneda_obj B S hS a) hki e hew hinv
  -- the chart of `T` obtained by base change, and the datum read over it
  have csq : IsPullback (pullback.fst q i) (pullback.snd q i) q i := IsPullback.of_hasPullback q i
  have hq's : Surjective ((BigFppfOver.toScheme B S hS).map (pullback.snd q i)) :=
    MorphismProperty.of_isPullback (csq.map (BigFppfOver.toScheme B S hS)) hqs
  have hq'f : Flat ((BigFppfOver.toScheme B S hS).map (pullback.snd q i)) :=
    MorphismProperty.of_isPullback (csq.map (BigFppfOver.toScheme B S hS)) hqf
  have hq'c : QuasiCompact ((BigFppfOver.toScheme B S hS).map (pullback.snd q i)) :=
    MorphismProperty.of_isPullback (csq.map (BigFppfOver.toScheme B S hS)) hqc
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
    exact inferInstance
  have hr'oi : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsOpenImmersion.{u}) (BigFppfOver.toScheme B S hS)))
      (e.hom ≫ yoneda.map θ) :=
    MorphismProperty.RespectsIso.precomp _ e.hom _
      ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ θ).2 hθoi)
  -- the open subset of `T` descends
  have hgp : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsOpenImmersion.{u}) (BigFppfOver.toScheme B S hS))) g := by
    have hpred := presheaf_pullback_snd_isOpenImmersion_of_fpqcChart
      (BigFppfOver.isSheaf_fpqc_pullback_yoneda_obj f h hXs hYs)
      (BigFppfOver.isSheaf_fpqc_yoneda_obj B S hS T)
      (h := 𝟙 (yoneda.obj T)) (m := κ) (r := e.hom ≫ yoneda.map θ)
      (by simpa only [Category.comp_id] using sq') hq's hq'f hq'c hr'oi
    rw [← (IsPullback.id_horiz g).isoIsPullback_hom_snd _ _
      (IsPullback.of_hasPullback g (𝟙 (yoneda.obj T)))]
    exact MorphismProperty.RespectsIso.precomp _ _ _ hpred
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
  have hbqa : Scheme.IsQuasiAffine ((BigFppfOver.toScheme B S hS).obj b) :=
    Scheme.IsQuasiAffine.of_isImmersion ((BigFppfOver.toScheme B S hS).map i₀)
  have hfinqa : _root_.AlgebraicGeometry.IsQuasiAffineHom
      ((BigFppfOver.toScheme B S hS).map (i₀ ≫ i)) :=
    isQuasiAffineHom_of_isQuasiAffine _ hbqa ha
  have sqfin : IsPullback (j.inv ≫ pullback.fst f h) (yoneda.map (i₀ ≫ i)) f h :=
    isPullback_inv_comp_of_hom_comp_eq (IsPullback.of_hasPullback f h) j
      (by rw [Functor.map_comp, ← Category.assoc, hj, hgfac])
  exact presheaf_pullback_snd_of_isPullback sqfin hfinqa

/-- **`AlgebraicGeometry.Space.IsEffectiveQuasiAffineDescentAlongFpqc` follows from Stacks
0APL.** If every algebraic space over `S` is a sheaf for the fpqc topology of the big fppf site
of `S` — which is Stacks 0APL — then effective descent for quasi-affine morphisms along a finite
fpqc covering of an affine object of the site holds, and hence, through
`AlgebraicGeometry.Space.isQuasiAffineHom_isLocalAtTarget_fpqc`, so does Stacks 0423.

The proof is the composition of the pieces the affine case composes:
`AlgebraicGeometry.BigFppfOver.exists_affine_chart_of_finite_fpqc` replaces the finite family by
the single surjective flat quasi-compact morphism out of its coproduct,
`AlgebraicGeometry.Space.presheaf_pullback_snd_cofanDesc_of_finite` glues the per-member data
over that coproduct by Zariski descent, and
`AlgebraicGeometry.Space.presheaf_pullback_snd_isQuasiAffineHom_of_fpqcChart` descends along the
chart. The conclusion is read back as a Cartesian square over the affine base through the
representing object of the base change along the identity, which is quasi-affine over an affine
object and hence quasi-affine. -/
theorem isEffectiveQuasiAffineDescentAlongFpqc_of_isSheaf_fpqc
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hAPL : ∀ {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}, IsAlgebraicSpace B S hS F →
      Presheaf.IsSheaf
        (Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS)).toGrothendieck F) :
    IsEffectiveQuasiAffineDescentAlongFpqc B S hS := by
  have hRIpre : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsQuasiAffineHom.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).RespectsIso :=
    (MorphismProperty.relative_isStableUnderBaseChange (F := yoneda) _).respectsIso
  have _hzar : IsZariskiLocalAtTarget
      (@_root_.AlgebraicGeometry.IsQuasiAffineHom.{u} : MorphismProperty Scheme.{u}) :=
    _root_.AlgebraicGeometry.isQuasiAffineHom_isZariskiLocalAtTarget.{u}
  have _hfppf : MorphismProperty.DescendsAlong
      (@_root_.AlgebraicGeometry.IsQuasiAffineHom.{u} : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) :=
    _root_.AlgebraicGeometry.descendsAlong_fppf_of_descendsAlong_fpqc _
  intro Z 𝒰 hfin hmem F G hF hG f k hall
  have _hZaff : IsAffine ((BigFppfOver.toScheme B S hS).obj
    ((BigAffineFppf.inclusion B S hS).obj Z)) := Z.property
  have hmem' : Presieve.ofArrows (fun j ↦ (BigAffineFppf.inclusion B S hS).obj (𝒰.X j))
      (fun j ↦ (BigAffineFppf.inclusion B S hS).map (𝒰.f j)) ∈
      (Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS)).coverings
        ((BigAffineFppf.inclusion B S hS).obj Z) := by
    rw [Precoverage.mem_comap_iff, Presieve.map_ofArrows]
    rwa [PreZeroHypercover.presieve₀, Presieve.map_ofArrows] at hmem
  obtain ⟨c, inj, q, ⟨hcol⟩, hcaff, hqs, hqf, hqc, hq⟩ :=
    BigFppfOver.exists_affine_chart_of_finite_fpqc (Z := (BigAffineFppf.inclusion B S hS).obj Z)
      Z.property (fun j ↦ (BigAffineFppf.inclusion B S hS).obj (𝒰.X j))
      (fun j ↦ (BigAffineFppf.inclusion B S hS).map (𝒰.f j))
      (fun j ↦ (𝒰.X j).property) hmem'
  have hall' : ∀ j, (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsQuasiAffineHom.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf
      (pullback.snd f (yoneda.map ((BigAffineFppf.inclusion B S hS).map (𝒰.f j)) ≫ k)) := by
    intro j
    obtain ⟨W, p, qq, hWqa, hpb⟩ := hall j
    have hXaff : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((BigAffineFppf.inclusion B S hS).obj (𝒰.X j))) := (𝒰.X j).property
    have hqq : (@_root_.AlgebraicGeometry.IsQuasiAffineHom.{u} : MorphismProperty Scheme.{u})
        ((BigFppfOver.toScheme B S hS).map qq) :=
      (isQuasiAffineHom_iff_isQuasiAffine ((BigFppfOver.toScheme B S hS).map qq)).2 hWqa
    exact presheaf_pullback_snd_of_isPullback hpb hqq
  have hr := presheaf_pullback_snd_cofanDesc_of_finite f hF.isSheaf hG.isSheaf k
    (fun j ↦ (BigAffineFppf.inclusion B S hS).obj (𝒰.X j))
    (fun j ↦ (BigAffineFppf.inclusion B S hS).map (𝒰.f j)) hcol q hq hall'
  have hfinal := presheaf_pullback_snd_isQuasiAffineHom_of_fpqcChart (hAPL hF) (hAPL hG)
    Z.property hcaff hqs hqf hqc (IsPullback.of_hasPullback f (yoneda.map q ≫ k)) hr
  -- read the conclusion back as a Cartesian square over the affine base
  have hi₀ : (@_root_.AlgebraicGeometry.IsQuasiAffineHom.{u} : MorphismProperty Scheme.{u})
      ((BigFppfOver.toScheme B S hS).map
        (hfinal.rep.snd (𝟙 (yoneda.obj ((BigAffineFppf.inclusion B S hS).obj Z))))) :=
    hfinal.property_snd (𝟙 _)
  refine ⟨_, (descentObjIso hfinal.rep).inv ≫ pullback.fst f k,
    hfinal.rep.snd (𝟙 (yoneda.obj ((BigAffineFppf.inclusion B S hS).obj Z))),
    (isQuasiAffineHom_iff_isQuasiAffine _).1 hi₀, ?_⟩
  exact isPullback_inv_comp_of_hom_comp_eq (IsPullback.of_hasPullback f k)
    (descentObjIso hfinal.rep) (descentObjIso_hom_comp hfinal.rep)

/-- **Stacks 0423** (Lemma 74.11.20 of Chapter 74, *Descent and Algebraic Spaces*). The
property "`f` is quasi-affine" of morphisms of algebraic spaces over `S` is fpqc local on the
base, in the sense of Definition 74.10.1 (Stacks 03YH): for every fpqc covering
`{Yᵢ ⟶ Y}` of algebraic spaces over `S` (Stacks 03MQ) and every morphism of algebraic spaces
`f : X ⟶ Y`, the morphism `f` is quasi-affine if and only if each base change
`Yᵢ ×_Y X ⟶ Yᵢ` is quasi-affine.

The setting is that of the conventions of Chapter 74 (Stacks 041I): `S` is a scheme of the big
fppf site `B`, algebraic spaces over `S` are sheaves on the big fppf site of `S`, and
quasi-affineness is the notion of Stacks 03WL, `AlgebraicGeometry.Space.IsQuasiAffineHom`:
every base change to an affine scheme is represented by a quasi-affine scheme. Locality on the
base is `CategoryTheory.MorphismProperty.IsLocalAtTarget` for the fpqc precoverage
`AlgebraicGeometry.Space.Topology.precoverage .fpqc` of the category of algebraic spaces over
`S`, whose covering presieves are those generated by the fpqc coverings, with index sets in any
universe. -/
@[stacks 0423, ega "IV 2.7.1" "more general", sga "4 IV 8.5.5" "more general"]
theorem isLocalAtTarget_isQuasiAffineHom_fpqc (B : BigFppfSite.{u}) (S : Scheme.{u})
    (contains : B.Contains S) :
    MorphismProperty.IsLocalAtTarget
      (fun {X Y : AlgebraicSpaces B S contains} (g : X ⟶ Y) ↦
          IsQuasiAffineHom B S contains g.hom :
        MorphismProperty (AlgebraicSpaces B S contains))
      (Topology.fpqc.precoverage.{u, v} B S contains) :=
  isQuasiAffineHom_isLocalAtTarget_fpqc B S contains
    (isEffectiveQuasiAffineDescentAlongFpqc_of_isSheaf_fpqc B S contains
      fun hF ↦ hF.isSheaf_fpqc)

end AlgebraicGeometry.Space

end
