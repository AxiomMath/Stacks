module

import StacksFrontier.AlgebraicGeometry.RelativeAmple.RestrictBase
import StacksFrontier.AlgebraicGeometry.Spaces.AffineBaseChangeLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmpleBaseChangeCriteria
import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmpleEtaleSourceScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmpleOverScheme
import StacksFrontier.AlgebraicGeometry.Spaces.SchematicLocusRelative

/-!
# Relative ampleness tested on scheme base changes: the full equivalence

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site and let
`L` be an invertible `𝒪_X`-module. [Stacks, Tag 0D36] says that the following are equivalent:

1. `L` is ample on `X/Y`;
2. for every scheme `Z` and every morphism `Z ⟶ Y` the algebraic space `X_Z = Z ×_Y X` is a
   scheme and the pullback `L_Z` is ample on `X_Z/Z`;
3. the same for every affine scheme `Z`;
4. there are a scheme `V` and a surjective étale morphism `V ⟶ Y` such that `X_V` is a scheme
   and `L_V` is ample on `X_V/V`.

This file proves it at exactly those hypotheses, with the four clauses spelled as in
`StacksFrontier/AlgebraicGeometry/Spaces/RelativeAmpleBaseChangeCriteria.lean`, through
`AlgebraicGeometry.Space.IsAmpleOnBaseChange`.

## Main results

* `AlgebraicGeometry.Space.isAmpleOnBaseChange_of_forall_affine`: clause (3) implies clause (2).
* `AlgebraicGeometry.Space.isAmpleOnBaseChange_of_exists_etaleChart`: clause (4) implies clause
  (3).
* `AlgebraicGeometry.Space.isRelativelyAmple_tfae_of_isInvertible`: **Stacks 0D36**, the four
  clauses are equivalent.

## The proof

Clauses (1) and (2) are equivalent by definition, (2) implies (3) trivially, and (1) implies (4)
by choosing an atlas of `Y`; those are
`AlgebraicGeometry.Space.isRelativelyAmple_iff_forall_isAmpleOnBaseChange` and
`AlgebraicGeometry.Space.exists_etaleChart_isAmpleOnBaseChange_of_isRelativelyAmple`.

**(3) implies (2).** Let `T ⟶ Y` be a morphism from a scheme and `U = X_T`. That `U` is a scheme
is [Stacks, Tag 03JH], in the form
`AlgebraicGeometry.Space.relativelyRepresentable_of_forall_affine_isAmpleOnBaseChange`. The
pullback `L_U` is invertible by
`AlgebraicGeometry.Space.isInvertibleModule_baseChangeModule`, and `U ⟶ T` is quasi-compact
because quasi-compactness is local on the target and holds over every affine of the site. For
an affine open `W ⊆ T`, which is an object of the site, clause (3) gives the ampleness of the
pullback of `L` to `X_W`; the comparison of the chart reading with base change,
`AlgebraicGeometry.Space.nonempty_baseChangeModule_baseChange_of_isInvertible`, and the
base-change invariance of relative ampleness, [Stacks, Tag 0893], identify that with ampleness of
`L_U` restricted over `W`. So `L_U` is ample over the members of an open covering of `T`, hence
over `T` by [Stacks, Tag 01VJ], clause (2) implies clause (1).

**(4) implies (3).** Let `V ⟶ Y` be the given chart and `Z ⟶ Y` a morphism from an affine scheme.
The base change `V ×_Y Z ⟶ Z` is a surjective étale morphism of schemes and `Z` is quasi-compact,
so finitely many affine opens of `V ×_Y Z` already surject onto `Z`; their disjoint union `V'` is
an affine scheme of the site, surjective étale over `Z`
(`AlgebraicGeometry.BigFppfOver.exists_affine_comp_etale_surjective`). Over `V'`, which maps to
`V`, the pullback of `L` is ample by [Stacks, Tag 0D33], and [Stacks, Tag 0D35] for the surjective
étale morphism `V' ⟶ Z` of affine schemes then makes `L_Z` ample on `X_Z/Z`, with `X_Z` a scheme.

The passage between ampleness of `L_Z` on the algebraic space `X_Z` over `Z` in the sense of
[Stacks, Tag 0D31] and the clause `AlgebraicGeometry.Space.IsAmpleOnBaseChange` at `Z ⟶ Y` is
`AlgebraicGeometry.Space.isRelativelyAmple_of_isAmpleOnBaseChange` and
`AlgebraicGeometry.Space.isAmpleOnBaseChange_of_isRelativelyAmple_of_isPullback`, through
[Stacks, Tag 0D32].

## References

* [Stacks Project, Tag 0D36](https://stacks.math.columbia.edu/tag/0D36)
* [Stacks Project, Tag 0D35](https://stacks.math.columbia.edu/tag/0D35)
* [Stacks Project, Tag 0D33](https://stacks.math.columbia.edu/tag/0D33)
* [Stacks Project, Tag 0D32](https://stacks.math.columbia.edu/tag/0D32)
* [Stacks Project, Tag 01VJ](https://stacks.math.columbia.edu/tag/01VJ)
* [Stacks Project, Tag 03JH](https://stacks.math.columbia.edu/tag/03JH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.AmpleLocallyClosed (pullbackModule)

universe u

namespace AlgebraicGeometry

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### An affine surjective étale refinement over a quasi-compact base -/

/-- **A surjective étale morphism onto a quasi-compact scheme is refined by one from an affine
scheme.** If `b : U ⟶ Z` is a morphism of the big fppf site of `S` whose underlying morphism of
schemes is surjective and étale and `Z` is quasi-compact, then there are an object `V` of the site
with affine underlying scheme and a morphism `c : V ⟶ U` such that `c ≫ b` is still surjective
and étale.

The images of the affine opens of `U` are open, `b` being étale, and cover `Z`, `b` being
surjective; finitely many of them suffice, and `V` is the disjoint union of the corresponding
affine opens, which lies in the site and is affine. -/
theorem BigFppfOver.exists_affine_comp_etale_surjective {U Z : BigFppfOver B S hS} (b : U ⟶ Z)
    [Etale ((BigFppfOver.toScheme B S hS).map b)]
    [Surjective ((BigFppfOver.toScheme B S hS).map b)]
    [CompactSpace ((BigFppfOver.toScheme B S hS).obj Z)] :
    ∃ (V : BigFppfOver B S hS) (c : V ⟶ U),
      IsAffine ((BigFppfOver.toScheme B S hS).obj V) ∧
      Etale ((BigFppfOver.toScheme B S hS).map (c ≫ b)) ∧
      Surjective ((BigFppfOver.toScheme B S hS).map (c ≫ b)) := by
  classical
  have hA : ∀ x : (BigFppfOver.toScheme B S hS).obj U,
      ∃ A : ((BigFppfOver.toScheme B S hS).obj U).affineOpens,
        x ∈ (A : ((BigFppfOver.toScheme B S hS).obj U).Opens) := by
    intro x
    obtain ⟨_, ⟨A, hA, rfl⟩, hxA, -⟩ :=
      ((BigFppfOver.toScheme B S hS).obj U).isBasis_affineOpens.exists_subset_of_mem_open
        (Set.mem_univ x) isOpen_univ
    exact ⟨⟨A, hA⟩, hxA⟩
  choose A hxA using hA
  have hopen : ∀ x, IsOpen ((BigFppfOver.toScheme B S hS).map b ''
      ((A x : ((BigFppfOver.toScheme B S hS).obj U).Opens) :
        Set ((BigFppfOver.toScheme B S hS).obj U))) :=
    fun x => ((BigFppfOver.toScheme B S hS).map b).isOpenMap _
      (A x : ((BigFppfOver.toScheme B S hS).obj U).Opens).isOpen
  have hcov : (Set.univ : Set ((BigFppfOver.toScheme B S hS).obj Z)) ⊆
      ⋃ x, (BigFppfOver.toScheme B S hS).map b ''
        ((A x : ((BigFppfOver.toScheme B S hS).obj U).Opens) :
          Set ((BigFppfOver.toScheme B S hS).obj U)) := by
    intro z _
    obtain ⟨x, rfl⟩ := ((BigFppfOver.toScheme B S hS).map b).surjective z
    exact Set.mem_iUnion.2 ⟨x, x, hxA x, rfl⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover _ hopen hcov
  choose W j hj hjrange hWaff using fun a : {x // x ∈ t} =>
    BigFppfOver.exists_affineOpen_restrict B S hS U (A a.1)
  obtain ⟨V, cι, e, hce, huniv⟩ :=
    BigFppfOver.exists_coproduct_of_mk_le_aleph0 (B := B) (S := S) (hS := hS)
      (σ := {x // x ∈ t}) Cardinal.mk_le_aleph0 W
  obtain ⟨d, hd⟩ := huniv j
  have hWa : ∀ a : {x // x ∈ t}, IsAffine ((BigFppfOver.toScheme B S hS).obj (W a)) := hWaff
  have hVaff : IsAffine ((BigFppfOver.toScheme B S hS).obj V) := IsAffine.of_isIso e.inv
  have hdesc : e.hom ≫ (BigFppfOver.toScheme B S hS).map d =
      Sigma.desc fun a : {x // x ∈ t} => (BigFppfOver.toScheme B S hS).map (j a) := by
    refine Sigma.hom_ext _ _ fun a => ?_
    rw [← Category.assoc, hce a, Sigma.ι_desc, ← Functor.map_comp, hd a]
  have hEt : ∀ a : {x // x ∈ t}, Etale ((BigFppfOver.toScheme B S hS).map (j a)) := by
    intro a
    have := hj a
    infer_instance
  have _ : IsZariskiLocalAtSource @Etale :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale) (Q := RingHom.Etale)
  have hdE : Etale ((BigFppfOver.toScheme B S hS).map d) := by
    have hdescE : Etale (Sigma.desc fun a : {x // x ∈ t} =>
        (BigFppfOver.toScheme B S hS).map (j a)) :=
      IsZariskiLocalAtSource.sigmaDesc fun a => hEt a
    have hrw : (BigFppfOver.toScheme B S hS).map d =
        e.inv ≫ Sigma.desc fun a : {x // x ∈ t} => (BigFppfOver.toScheme B S hS).map (j a) := by
      rw [← hdesc, Iso.inv_hom_id_assoc]
    rw [hrw]
    infer_instance
  refine ⟨V, d, hVaff, ?_, ⟨fun z => ?_⟩⟩
  · rw [Functor.map_comp]
    infer_instance
  · obtain ⟨x, hxt, y, hyA, rfl⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ z))
    have hy : y ∈ Set.range ((BigFppfOver.toScheme B S hS).map (j ⟨x, hxt⟩)) := by
      rw [hjrange]
      exact hyA
    obtain ⟨w, rfl⟩ := hy
    refine ⟨(BigFppfOver.toScheme B S hS).map (cι ⟨x, hxt⟩) w, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Functor.map_comp, ← Category.assoc, hd ⟨x, hxt⟩,
      Functor.map_comp, Scheme.Hom.comp_apply]

/-- A cartesian square over `g` factors through a cartesian square over `g` by one over the
identity. -/
private theorem exists_isPullback_id_of_isPullback {C : Type*} [Category C]
    {X Y XT T U : C} {f : X ⟶ Y} {g : T ⟶ Y} {pr : XT ⟶ X} {fT : XT ⟶ T} {p : U ⟶ X} {q : U ⟶ T}
    (hsq : IsPullback pr fT f g) (hUp : IsPullback p q f g) :
    ∃ p₀ : U ⟶ XT, p₀ ≫ pr = p ∧ p₀ ≫ fT = q ∧ IsPullback p₀ q fT (𝟙 T) := by
  have hq₀ : hsq.lift p q hUp.w ≫ fT = q := hsq.lift_snd _ _ _
  refine ⟨hsq.lift p q hUp.w, hsq.lift_fst _ _ _, hq₀, ?_⟩
  refine IsPullback.of_right ?_ (hq₀.trans (Category.comp_id _).symm) hsq
  rw [hsq.lift_fst]
  exact (congrArg (IsPullback p q f) (Category.id_comp g)).mpr hUp

namespace Space

/-! ### The clause of Stacks 0D36 at one base change, read on the base-changed space -/

/-- **The clause of Stacks 0D36 at a base change is relative ampleness of the base change.**
Let `T` be a scheme of the site, `g : T ⟶ Y`, and let `pr : X_T ⟶ X`, `f_T : X_T ⟶ T` present
`X_T` as `T ×_Y X`. If the clause `AlgebraicGeometry.Space.IsAmpleOnBaseChange` holds at `g` for
an invertible `𝒪_X`-module `L`, then the pullback of `L` to `X_T` is ample on `X_T/T` in the sense
of Stacks 0D31.

The clause makes `X_T` a scheme `U`, carrying a relatively ample pullback of `L`, and then
Stacks 0D32 (`AlgebraicGeometry.Space.isRelativelyAmple_of_exists_scheme`) applies. -/
theorem isRelativelyAmple_of_isAmpleOnBaseChange {X Y XT : AlgebraicSpaces B S hS} {f : X ⟶ Y}
    {L : Modules.{u, u} B S hS X.1 X.2}
    (hLinv : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).property L)
    {T : BigFppfOver B S hS} {g : yoneda.obj T ⟶ Y.1} {pr : XT ⟶ X}
    {fT : XT ⟶ schemeSpace T}
    (hsq : IsPullback pr fT f (ObjectProperty.homMk g))
    (h : IsAmpleOnBaseChange B S hS f L T g) :
    IsRelativelyAmple B S hS fT ((modulePullback B S hS pr).obj L) := by
  obtain ⟨⟨U, q, p, hUp⟩, hamp⟩ := h
  have hsq' : IsPullback pr.hom fT.hom f.hom g := AlgebraicSpaces.isPullback_hom B S hS hsq
  obtain ⟨p₀, hp₀, hq₀, hsq₀⟩ := exists_isPullback_id_of_isPullback hsq' hUp
  have : IsIso p₀ := hsq₀.isIso_fst_of_isIso (inst := IsIso.id _)
  have hLT : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS XT.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS XT.1 XT.2).O)).property ((modulePullback B S hS pr).obj L) :=
    Stacks.SheafOfModules.isInvertible_pullbackModules_obj
      (f := smallEtaleRingedToposModulesHom B S hS pr) (L := L) (hL := hLinv)
  refine isRelativelyAmple_of_exists_scheme fT _ hLT T (Iso.refl _) ⟨U, asIso p₀, ?_⟩
  have hpre : yoneda.preimage ((asIso p₀).hom ≫ fT.hom ≫ (Iso.refl (schemeSpace T).obj).hom) = q :=
    yoneda.map_injective (by
      rw [Functor.map_preimage, asIso_hom, Iso.refl_hom]
      exact (congrArg (p₀ ≫ ·) (Category.comp_id fT.hom)).trans hq₀)
  rw [hpre]
  obtain ⟨hL0, hA0⟩ := hamp U p q hUp
  have e := baseChangeModuleCompIso B S hS pr L U p₀
  rw [hp₀] at e
  have := hL0
  have hL1 : Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj U)
      (baseChangeModule B S hS ((modulePullback B S hS pr).obj L) U p₀) :=
    Stacks.SheafOfModules.Invertible.isInvertible_of_iso _ _ e
  exact ⟨hL1, (Stacks.RelativeVeryAmple.isRelativelyAmple_congr _ _ _ e).mp hA0⟩

/-- **Relative ampleness of a base change gives the clause of Stacks 0D36 at that base change.**
Let `T` be a scheme of the site, `g : T ⟶ Y`, and let `pr : X_T ⟶ X`, `f_T : X_T ⟶ T` present
`X_T` as `T ×_Y X`. If the pullback of `L` to `X_T` is ample on `X_T/T` in the sense of Stacks
0D31, then `AlgebraicGeometry.Space.IsAmpleOnBaseChange` holds at `g`: every cartesian square
over `g` factors through `X_T` by a cartesian square over the identity of `T`. -/
theorem isAmpleOnBaseChange_of_isRelativelyAmple_of_isPullback {X Y XT : AlgebraicSpaces B S hS}
    {f : X ⟶ Y} {L : Modules.{u, u} B S hS X.1 X.2} {T : BigFppfOver B S hS}
    {g : yoneda.obj T ⟶ Y.1} {pr : XT ⟶ X} {fT : XT ⟶ schemeSpace T}
    (hsq : IsPullback pr fT f (ObjectProperty.homMk g))
    (h : IsRelativelyAmple B S hS fT ((modulePullback B S hS pr).obj L)) :
    IsAmpleOnBaseChange B S hS f L T g := by
  have hsq' : IsPullback pr.hom fT.hom f.hom g := AlgebraicSpaces.isPullback_hom B S hS hsq
  refine ⟨?_, fun U p q hUp => ?_⟩
  · obtain ⟨U, q, p₀, h₀⟩ := h.1 (𝟙 (yoneda.obj T))
    refine ⟨U, q, p₀ ≫ pr.hom, ?_⟩
    have h₁ := h₀.paste_horiz hsq'
    exact (congrArg (IsPullback (p₀ ≫ pr.hom) (yoneda.map q) f.hom) (Category.id_comp g)).mp h₁
  · obtain ⟨p₀, hp₀, -, hsq₀⟩ := exists_isPullback_id_of_isPullback hsq' hUp
    obtain ⟨hL0, hA0⟩ := h.2 T U (𝟙 _) p₀ q hsq₀
    have e := baseChangeModuleCompIso B S hS pr L U p₀
    rw [hp₀] at e
    have := hL0
    have hL1 : Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj U)
        (baseChangeModule B S hS L U p) :=
      Stacks.SheafOfModules.Invertible.isInvertible_of_iso _ _ e.symm
    exact ⟨hL1, (Stacks.RelativeVeryAmple.isRelativelyAmple_congr _ _ _ e.symm).mp hA0⟩

/-! ### Clause (3) implies clause (2) -/

/-- **Stacks 0D36, clause (3) implies clause (2).** Let `f : X ⟶ Y` be a morphism of algebraic
spaces and `L` an invertible `𝒪_X`-module. If for every affine scheme `Z` of the site and every
`Z ⟶ Y` the base change `X_Z` is a scheme and `L_Z` is ample on `X_Z/Z`, then the same holds for
every scheme `T` of the site and every `T ⟶ Y`.

That `X_T` is a scheme is
`AlgebraicGeometry.Space.relativelyRepresentable_of_forall_affine_isAmpleOnBaseChange`
(Stacks 03JH). Ampleness of `L_T` is local on `T`, Stacks 01VJ clause (2) implies clause (1), and
over an affine open `W ⊆ T` it is clause (3) at `W`, moved onto the restriction of `X_T` over `W`
by Stacks 0893 and the base-change compatibility of the chart reading of an invertible module. -/
theorem isAmpleOnBaseChange_of_forall_affine {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y}
    {L : Modules.{u, u} B S hS X.1 X.2}
    (hLinv : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).property L)
    (h3 : ∀ (T : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj T) →
      ∀ g : yoneda.obj T ⟶ Y.1, IsAmpleOnBaseChange B S hS f L T g)
    (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ Y.1) :
    IsAmpleOnBaseChange B S hS f L T g := by
  refine ⟨relativelyRepresentable_of_forall_affine_isAmpleOnBaseChange f L h3 g,
    fun U p q hUp => ?_⟩
  have hM := isInvertibleModule_baseChangeModule L hLinv U p
  have hqc : QuasiCompact ((BigFppfOver.toScheme B S hS).map q) := by
    have hloc : IsZariskiLocalAtTarget (@QuasiCompact : MorphismProperty Scheme.{u}) :=
      (HasAffineProperty.iff.mp
        AlgebraicGeometry.instHasAffinePropertyQuasiCompactCompactSpaceCarrierCarrierCommRingCat).1
    have key := presheaf_of_affineBaseChange B S hS (P := @QuasiCompact) hloc X.2 Y.2
      (f := f.hom) fun Z hZ gZ => by
        obtain ⟨⟨W, q', p', hsq'⟩, hamp⟩ := h3 Z hZ gZ
        obtain ⟨hL', hA'⟩ := hamp W p' q' hsq'
        exact ⟨W, q', p', hsq', hA'.1⟩
    exact key.property g p q hUp
  refine ⟨hM, Stacks.RelativeAmpleRestrictBase.isRelativelyAmple_of_forall_exists_isRelativelyAmple
    _ _ hqc fun x => ?_⟩
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ :=
    ((BigFppfOver.toScheme B S hS).obj T).isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ x) isOpen_univ
  obtain ⟨V, u, hu, hurange, hVaff⟩ := BigFppfOver.exists_affineOpen_restrict B S hS T ⟨W, hW⟩
  obtain ⟨⟨U', q', p', hsq'⟩, hamp⟩ := h3 V hVaff (yoneda.map u ≫ g)
  -- the base change over `V` maps to the one over `T`, by a cartesian square
  set r : yoneda.obj U' ⟶ yoneda.obj U := hUp.lift p' (yoneda.map q' ≫ yoneda.map u)
    (by rw [hsq'.w, Category.assoc]) with hrdef
  have hr₁ : r ≫ p = p' := hUp.lift_fst _ _ _
  have hr₂ : r ≫ yoneda.map q = yoneda.map q' ≫ yoneda.map u := hUp.lift_snd _ _ _
  have hsqr : IsPullback r (yoneda.map q') (yoneda.map q) (yoneda.map u) :=
    IsPullback.of_right (by rw [hr₁]; exact hsq') hr₂ hUp
  set r₀ : U' ⟶ U := yoneda.preimage r with hr₀def
  have hr₀ : yoneda.map r₀ = r := yoneda.map_preimage r
  have hsq₀ : IsPullback r₀ q' q u :=
    IsPullback.of_map yoneda (yoneda.map_injective (by simpa [hr₀] using hsqr.w))
      (by rw [hr₀]; exact hsqr)
  have hsqS := hsq₀.map (BigFppfOver.toScheme B S hS)
  obtain ⟨hL', hA'⟩ := hamp U' p' q' hsq'
  have := hL'
  obtain ⟨e⟩ := nonempty_baseChangeModule_baseChange_of_isInvertible L hLinv U U' p r₀
  rw [hr₀, hr₁] at e
  have hA'' : Stacks.RelativeAmple.IsRelativelyAmple ((BigFppfOver.toScheme B S hS).map q')
      (pullbackModule ((BigFppfOver.toScheme B S hS).map r₀) (baseChangeModule B S hS L U p)) :=
    (Stacks.RelativeVeryAmple.isRelativelyAmple_congr _ _ _ e).mp hA'
  -- the open of `T` that `V` is
  have := hu
  set O := ((BigFppfOver.toScheme B S hS).map u).opensRange with hOdef
  refine ⟨O, ?_, ?_⟩
  · show x ∈ Set.range ((BigFppfOver.toScheme B S hS).map u)
    rw [hurange]
    exact hxW
  set φ : O.toScheme ⟶ (BigFppfOver.toScheme B S hS).obj V :=
    ((BigFppfOver.toScheme B S hS).map u).isoOpensRange.inv with hφdef
  have hφ : φ ≫ (BigFppfOver.toScheme B S hS).map u = O.ι :=
    (Iso.inv_comp_eq _).mpr (Scheme.Hom.isoOpensRange_hom_ι _).symm
  have hbig := (isPullback_morphismRestrict ((BigFppfOver.toScheme B S hS).map q) O).flip
  set k := hsqS.lift ((BigFppfOver.toScheme B S hS).map q ⁻¹ᵁ O).ι
    (((BigFppfOver.toScheme B S hS).map q ∣_ O) ≫ φ)
    (by rw [Category.assoc, hφ, hbig.w]) with hkdef
  have hk₁ : k ≫ (BigFppfOver.toScheme B S hS).map r₀ =
      ((BigFppfOver.toScheme B S hS).map q ⁻¹ᵁ O).ι := hsqS.lift_fst _ _ _
  have hk₂ : k ≫ (BigFppfOver.toScheme B S hS).map q' =
      ((BigFppfOver.toScheme B S hS).map q ∣_ O) ≫ φ := hsqS.lift_snd _ _ _
  have hkp : IsPullback k ((BigFppfOver.toScheme B S hS).map q ∣_ O)
      ((BigFppfOver.toScheme B S hS).map q') φ :=
    IsPullback.of_right (by rw [hk₁, hφ]; exact hbig) hk₂ hsqS
  have hfin := Stacks.AmpleBridge.isRelativelyAmple_pullbackModule_of_isPullback hkp _ hA''
  refine (Stacks.RelativeVeryAmple.isRelativelyAmple_congr _ _ _ ?_).mp hfin
  exact (Stacks.RelativeAmpleBaseChange.pullbackModuleCompIso k _ _).symm ≪≫
    Stacks.RelativeAmpleBaseChange.pullbackModuleCongr hk₁ _

/-! ### Clause (4) implies clause (3) -/

/-- **Stacks 0D36, clause (4) implies clause (3).** Let `f : X ⟶ Y` be a morphism of algebraic
spaces and `L` an invertible `𝒪_X`-module. If there are a scheme `V` of the site and a surjective
étale morphism `V ⟶ Y` over which `X_V` is a scheme and `L_V` is ample on `X_V/V`, then for every
affine scheme `Z` of the site and every `Z ⟶ Y` the base change `X_Z` is a scheme and `L_Z` is
ample on `X_Z/Z`.

The base change of the chart to `Z` is refined by a surjective étale `V' ⟶ Z` with `V'` affine
(`AlgebraicGeometry.BigFppfOver.exists_affine_comp_etale_surjective`); over `V'` the pullback of
`L` is ample by Stacks 0D33, and Stacks 0D35
(`AlgebraicGeometry.Space.isRelativelyAmple_of_isRelativelyAmple_baseChange_etale`) descends
that to `X_Z/Z`. -/
theorem isAmpleOnBaseChange_of_exists_etaleChart {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y}
    {L : Modules.{u, u} B S hS X.1 X.2}
    (hLinv : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).property L)
    (h4 : ∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y.1),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) g ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) g ∧
      IsAmpleOnBaseChange B S hS f L V g)
    (Z : BigFppfOver B S hS) (hZ : IsAffine ((BigFppfOver.toScheme B S hS).obj Z))
    (gZ : yoneda.obj Z ⟶ Y.1) :
    IsAmpleOnBaseChange B S hS f L Z gZ := by
  obtain ⟨V, g, hgS, hgE, hV⟩ := h4
  -- the base change `P = V ×_Y Z` of the chart, a scheme surjective and étale over `Z`
  set a : hgE.rep.pullback gZ ⟶ V := hgE.rep.fst' gZ with hadef
  set b : hgE.rep.pullback gZ ⟶ Z := hgE.rep.snd gZ with hbdef
  have hab : yoneda.map a ≫ g = yoneda.map b ≫ gZ := (hgE.rep.isPullback' gZ).w
  have hbE : Etale ((BigFppfOver.toScheme B S hS).map b) :=
    hgE.property gZ (hgE.rep.fst gZ) (hgE.rep.snd gZ) (hgE.rep.isPullback gZ)
  have hbS : Surjective ((BigFppfOver.toScheme B S hS).map b) :=
    hgS.property gZ (hgE.rep.fst gZ) (hgE.rep.snd gZ) (hgE.rep.isPullback gZ)
  obtain ⟨V', c, hV'aff, hcbE, hcbS⟩ := BigFppfOver.exists_affine_comp_etale_surjective b
  -- the algebraic spaces involved
  set gV : representedAlgebraicSpace B S hS V ⟶ Y := ObjectProperty.homMk g with hgVdef
  set gZ' : representedAlgebraicSpace B S hS Z ⟶ Y := ObjectProperty.homMk gZ with hgZdef
  have hXV := AlgebraicSpaces.isPullback_fiberProduct B S hS f gV
  have hXZ := AlgebraicSpaces.isPullback_fiberProduct B S hS f gZ'
  set prV : AlgebraicSpaces.fiberProduct B S hS f gV ⟶ X :=
    ObjectProperty.homMk (pullback.fst f.hom gV.hom) with hprVdef
  set fV : AlgebraicSpaces.fiberProduct B S hS f gV ⟶ representedAlgebraicSpace B S hS V :=
    ObjectProperty.homMk (pullback.snd f.hom gV.hom) with hfVdef
  set prZ : AlgebraicSpaces.fiberProduct B S hS f gZ' ⟶ X :=
    ObjectProperty.homMk (pullback.fst f.hom gZ'.hom) with hprZdef
  set fZ : AlgebraicSpaces.fiberProduct B S hS f gZ' ⟶ representedAlgebraicSpace B S hS Z :=
    ObjectProperty.homMk (pullback.snd f.hom gZ'.hom) with hfZdef
  set hh : representedAlgebraicSpace B S hS V' ⟶ representedAlgebraicSpace B S hS Z :=
    ObjectProperty.homMk (yoneda.map (c ≫ b)) with hhdef
  set k : representedAlgebraicSpace B S hS V' ⟶ representedAlgebraicSpace B S hS V :=
    ObjectProperty.homMk (yoneda.map (c ≫ a)) with hkdef
  have hY' := AlgebraicSpaces.isPullback_fiberProduct B S hS fZ hh
  set pr' : AlgebraicSpaces.fiberProduct B S hS fZ hh ⟶ AlgebraicSpaces.fiberProduct B S hS f gZ' :=
    ObjectProperty.homMk (pullback.fst fZ.hom hh.hom) with hpr'def
  set f' : AlgebraicSpaces.fiberProduct B S hS fZ hh ⟶ representedAlgebraicSpace B S hS V' :=
    ObjectProperty.homMk (pullback.snd fZ.hom hh.hom) with hf'def
  -- `V' ×_Z X_Z` is also `V' ×_V X_V`
  have hhk : hh ≫ gZ' = k ≫ gV := ObjectProperty.hom_ext _ (by
    show yoneda.map (c ≫ b) ≫ gZ = yoneda.map (c ≫ a) ≫ g
    rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, hab])
  have hbigsq : IsPullback (pr' ≫ prZ) f' f (k ≫ gV) := by
    rw [← hhk]
    exact hY'.paste_horiz hXZ
  set pr'' := hXV.lift (pr' ≫ prZ) (f' ≫ k) (by rw [hbigsq.w, Category.assoc]) with hpr''def
  have hpr''₁ : pr'' ≫ prV = pr' ≫ prZ := hXV.lift_fst _ _ _
  have hpr''₂ : pr'' ≫ fV = f' ≫ k := hXV.lift_snd _ _ _
  have hsqk : IsPullback pr'' f' fV k :=
    IsPullback.of_right (by rw [hpr''₁]; exact hbigsq) hpr''₂ hXV
  -- relative ampleness over `V`, then over `V'`
  have hAV := isRelativelyAmple_of_isAmpleOnBaseChange hLinv hXV hV
  have hAV' := isRelativelyAmple_baseChange hsqk _ hAV
  have hN : IsRelativelyAmple B S hS f'
      ((modulePullback B S hS pr').obj ((modulePullback B S hS prZ).obj L)) := by
    refine (isRelativelyAmple_congr f' ?_).mp hAV'
    exact (modulePullbackCompIso B S hS pr'' prV).app L ≪≫
      eqToIso (congrArg (fun m => (modulePullback B S hS m).obj L) hpr''₁) ≪≫
      ((modulePullbackCompIso B S hS pr' prZ).app L).symm
  -- Stacks 0D35 over the surjective étale `V' ⟶ Z` of affine schemes
  have hLZ : Stacks.SheafOfModules.IsInvertible
      (structurePresheaf B S hS (AlgebraicSpaces.fiberProduct B S hS f gZ').1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
        (AlgebraicSpaces.fiberProduct B S hS f gZ').1
        (AlgebraicSpaces.fiberProduct B S hS f gZ').2).O)).property
      ((modulePullback B S hS prZ).obj L) :=
    Stacks.SheafOfModules.isInvertible_pullbackModules_obj
      (f := smallEtaleRingedToposModulesHom B S hS prZ) (L := L) (hL := hLinv)
  have hAZ := isRelativelyAmple_of_isRelativelyAmple_baseChange_etale hY' _ hLZ Z V' hZ hV'aff
    (Iso.refl _) (Iso.refl _) (c ≫ b) (by simp [hhdef]) hcbS hcbE hN
  exact isAmpleOnBaseChange_of_isRelativelyAmple_of_isPullback hXZ hAZ

/-! ### Stacks 0D36 -/

/-- **Stacks 0D36.** Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` and `L` an
invertible `𝒪_X`-module. The following are equivalent:

1. `L` is ample on `X/Y`;
2. for every scheme `T` of the site and every morphism `T ⟶ Y` the algebraic space
   `X_T = T ×_Y X` is a scheme and the pullback `L_T` is ample on `X_T/T`;
3. for every affine scheme `T` of the site and every morphism `T ⟶ Y` the algebraic space `X_T`
   is a scheme and `L_T` is ample on `X_T/T`;
4. there are a scheme `V` of the site and a surjective étale morphism `V ⟶ Y` such that `X_V` is
   a scheme and `L_V` is ample on `X_V/V`.

Clause (2) at `T ⟶ Y` is `AlgebraicGeometry.Space.IsAmpleOnBaseChange`; see
`StacksFrontier/AlgebraicGeometry/Spaces/RelativeAmpleBaseChangeCriteria.lean` for that spelling.
Clause (3) implies clause (2) is
`AlgebraicGeometry.Space.isAmpleOnBaseChange_of_forall_affine` (Stacks 03JH and 01VJ), and
clause (4) implies clause (3) is `AlgebraicGeometry.Space.isAmpleOnBaseChange_of_exists_etaleChart`
(Stacks 0D35). -/
@[stacks 0D36]
theorem isRelativelyAmple_tfae_of_isInvertible {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (L : Modules.{u, u} B S hS X.1 X.2)
    (hLinv : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O)).property L) :
    List.TFAE
      [IsRelativelyAmple B S hS f L,
        ∀ (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ Y.1),
          IsAmpleOnBaseChange B S hS f L T g,
        ∀ (T : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj T) →
          ∀ g : yoneda.obj T ⟶ Y.1, IsAmpleOnBaseChange B S hS f L T g,
        ∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y.1),
          (MorphismProperty.presheaf (MorphismProperty.inverseImage
            (@Surjective.{u} : MorphismProperty Scheme.{u})
            (BigFppfOver.toScheme B S hS))) g ∧
          (MorphismProperty.presheaf (MorphismProperty.inverseImage
            (@Etale.{u} : MorphismProperty Scheme.{u})
            (BigFppfOver.toScheme B S hS))) g ∧
          IsAmpleOnBaseChange B S hS f L V g] := by
  tfae_have 1 ↔ 2 := isRelativelyAmple_iff_forall_isAmpleOnBaseChange f L
  tfae_have 2 → 3 := fun h T _ g => h T g
  tfae_have 3 → 2 := fun h3 T g => isAmpleOnBaseChange_of_forall_affine hLinv h3 T g
  tfae_have 1 → 4 := fun h => exists_etaleChart_isAmpleOnBaseChange_of_isRelativelyAmple h
  tfae_have 4 → 3 := fun h4 T hT g => isAmpleOnBaseChange_of_exists_etaleChart hLinv h4 T hT g
  tfae_finish

end Space

end AlgebraicGeometry

end
