module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineCompletionAlongIdeal
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionFormalSpectrum
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionSubspaceComparison
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.KoszulRegularSmoothCover
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SquareZeroQuotientImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkAsPullback

/-!
# The infinitesimal neighbourhoods of a closed subspace of an affine chart

Let `S` be a scheme contained in a big fppf site `B` and let `W` be an object of the big fppf
site of `S` whose underlying scheme is affine. A closed subspace `G ⊆ W` is cut out by an ideal
of the ring of regular functions of `W`, and this file identifies the union of the
infinitesimal neighbourhoods of `G` in `W` — the subfunctor whose fppf sheafification is the
completion `W^∧_G` of Stacks 0GXU — with the union of the closed subschemes of the powers of
that ideal.

That identification is the chart-level step of the omitted proof of **Stacks 0GXY**: it is what
makes the completion of an affine chart a completion along an ideal, hence lets Stacks 0GXX read
off its type.

## Main definitions

* `AlgebraicGeometry.Space.closedChartIdeal` is the ideal of regular functions cutting out a
  closed subspace of a representable algebraic space, and
  `AlgebraicGeometry.Space.closedChartRingIdeal` is the same ideal read in `A` for the chart
  `Spec A`.
* `AlgebraicGeometry.Space.quotientToAffineOver` is the closed immersion of the site from the
  closed subscheme of an ideal of `A` into `Spec A`.
* `AlgebraicGeometry.Space.chartUnionSubfunctor` is the union of the infinitesimal
  neighbourhoods, and `AlgebraicGeometry.Space.chartNeighbourhoodCocone` is the cocone
  exhibiting each neighbourhood inside it.

## Main results

* `AlgebraicGeometry.Space.pow_closedChartIdeal_le_ker` and
  `AlgebraicGeometry.Space.isUniversalNthOrderThickening_of_pow_le_ker`: over an affine chart,
  the inverse image of a closed subspace along a scheme-valued point is universally an
  `n`th-order thickening exactly when the `(n+1)`st power of the cutting-out ideal is killed by
  pullback of regular functions along that point.
* `AlgebraicGeometry.Space.mem_completionSubspaceSubfunctor_of_factor` and
  `AlgebraicGeometry.Space.exists_factor_of_mem_completionSubspaceSubfunctor`: consequently a
  scheme-valued point of an affine chart lies in the union of the infinitesimal neighbourhoods
  of a closed subspace exactly when it factors through the closed subscheme of a power of the
  cutting-out ideal.
* `AlgebraicGeometry.Space.closedChartIdeal_preimage_of_isAffine`: between affine charts the
  cutting-out ideal of an inverse image is the extension of the cutting-out ideal.

## What is not proved here

The resulting isomorphism `W^∧_G ≅ completionAlongIdeal` of Stacks 0GXX is *not* proved. What
is missing is only the colimit step: that the cocone
`AlgebraicGeometry.Space.chartNeighbourhoodCocone` is a colimit cocone, which by
`CategoryTheory.Limits.evaluationJointlyReflectsColimits` is the objectwise statement that the
union of the infinitesimal neighbourhoods is the filtered colimit of its members — joint
surjectivity of the members being
`AlgebraicGeometry.Space.exists_factor_of_mem_completionSubspaceSubfunctor` and injectivity of
each member being `AlgebraicGeometry.Space.mono_quotientToAffineOver`.

## Implementation notes

The ideal is read off the identity chart: a closed subspace `G` of `yoneda.obj W` has a
representable inclusion, so base-changing it along the identity of `yoneda.obj W` gives a
closed immersion of schemes `T ⟶ W`, and `closedChartIdeal` is the kernel of its pullback map
on global sections. It agrees with the defining ideal of Stacks 03MB on the identity chart,
which is `AlgebraicGeometry.Space.definingIdealAt_idChart`.

Both halves of the chart description go through the order conditions of Stacks 05ZK read on
scheme charts, which is `AlgebraicGeometry.Space.isRepresentedNthOrder_iff`: a closed subspace
of a representable is represented by `n`th-order thickenings exactly when the closed immersion
of schemes cutting it out is one. Over an affine chart the kernel ideal sheaf of that immersion
is computed on the affine opens of the source, where the inverse image is the base change of
the subspace along a morphism of affine schemes and
`Stacks.AlgebraicGeometry.ker_appTop_pullback_snd` applies.

## References

* [Stacks Project, Tag 0GXY](https://stacks.math.columbia.edu/tag/0GXY)
* [Stacks Project, Tag 0GXX](https://stacks.math.columbia.edu/tag/0GXX)
* [Stacks Project, Tag 0GXU](https://stacks.math.columbia.edu/tag/0GXU)
* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Thickenings

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The ideal of a closed subspace of a representable -/

/-- The object of the site cutting out a closed subspace of a representable algebraic space:
the base change of the inclusion along the identity chart. -/
abbrev closedChartObj {V : BigFppfOver B S hS} (G : Subfunctor (yoneda.obj V))
    (hG : IsClosedSubspace B S hS G) : BigFppfOver B S hS :=
  hG.2.rep.pullback (𝟙 (yoneda.obj V))

/-- The closed immersion of the site cutting out a closed subspace of a representable. -/
abbrev closedChartHom {V : BigFppfOver B S hS} (G : Subfunctor (yoneda.obj V))
    (hG : IsClosedSubspace B S hS G) : closedChartObj B S hS G hG ⟶ V :=
  hG.2.rep.snd (𝟙 (yoneda.obj V))

/-- The morphism of schemes underlying `closedChartHom` is a closed immersion. -/
theorem isClosedImmersion_closedChartHom {V : BigFppfOver B S hS}
    (G : Subfunctor (yoneda.obj V)) (hG : IsClosedSubspace B S hS G) :
    _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (closedChartHom B S hS G hG)) :=
  hG.2.property_snd (𝟙 (yoneda.obj V))

/-- The ideal of regular functions cutting out a closed subspace `G` of a representable
algebraic space `V`: the kernel of pullback of regular functions along the closed immersion
of schemes exhibiting `G`. -/
def closedChartIdeal {V : BigFppfOver B S hS} (G : Subfunctor (yoneda.obj V))
    (hG : IsClosedSubspace B S hS G) :
    Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) :=
  RingHom.ker ((BigFppfOver.toScheme B S hS).map
    (closedChartHom B S hS G hG)).appTop.hom

/-- The inclusion of a closed subspace of a representable becomes, after an isomorphism of its
source, the Yoneda image of the cutting-out morphism of the site. -/
theorem isIso_rep_fst_id {V : BigFppfOver B S hS} (G : Subfunctor (yoneda.obj V))
    (hG : IsClosedSubspace B S hS G) :
    IsIso (hG.2.rep.fst (𝟙 (yoneda.obj V))) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := MorphismProperty.isomorphisms ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    (hG.2.rep.isPullback (𝟙 (yoneda.obj V))).flip
    (inferInstanceAs (IsIso (𝟙 (yoneda.obj V))))

/-- The first projection of the base change along the identity chart, followed by the inclusion
of `G`, is the Yoneda image of `closedChartHom`. -/
theorem rep_fst_id_comp_ι {V : BigFppfOver B S hS} (G : Subfunctor (yoneda.obj V))
    (hG : IsClosedSubspace B S hS G) :
    hG.2.rep.fst (𝟙 (yoneda.obj V)) ≫ G.ι =
      yoneda.map (closedChartHom B S hS G hG) := by
  simpa using (hG.2.rep.isPullback (𝟙 (yoneda.obj V))).w

/-- **The cutting-out ideal is the defining ideal of Stacks 03MB on the identity chart.** -/
theorem definingIdealAt_idChart {V : BigFppfOver B S hS} (G : Subfunctor (yoneda.obj V))
    (hG : IsClosedSubspace B S hS G) :
    definingIdealAt B S hS ((schemeSpaceFunctor B S hS).obj V) ⟨G, hG⟩
        (op (idChart B S hS V)) =
      closedChartIdeal B S hS G hG := by
  rw [definingIdealAt_eq_ker B S hS ((schemeSpaceFunctor B S hS).obj V) ⟨G, hG⟩
    (idChart B S hS V), Scheme.Γ_map_op]
  rfl


/-! ### Transport of cartesian squares along isomorphisms -/

/-- Replacing the right-hand vertical morphism of a cartesian square by a factor through an
isomorphism keeps the square cartesian. -/
theorem isPullback_comp_isIso_right {C : Type*} [Category C] {P X X' Y Z : C} {fst : P ⟶ X}
    {snd : P ⟶ Y} {u : X ⟶ X'} [IsIso u] {f : X' ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback fst snd (u ≫ f) g) : IsPullback (fst ≫ u) snd f g := by
  simpa using h.paste_horiz (IsPullback.of_horiz_isIso ⟨by simp⟩ :
    IsPullback u (u ≫ f) f (𝟙 Z))

/-- Replacing the vertex of a cartesian square by an isomorphic object keeps it cartesian. -/
theorem isPullback_iso_vertex {C : Type*} [Category C] {P P' X Y Z : C} {fst : P ⟶ X}
    {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) (e : P' ≅ P) :
    IsPullback (e.hom ≫ fst) (e.hom ≫ snd) f g := by
  simpa using (IsPullback.of_horiz_isIso ⟨by simp⟩ :
    IsPullback e.hom (e.hom ≫ snd) snd (𝟙 Y)).paste_horiz h

/-! ### Comparison of the cutting-out ideals along a morphism -/

/-- **The closed immersion cutting out the inverse image of a closed subspace is the base
change of the one cutting out the subspace.** -/
theorem exists_isPullback_closedChartHom {V W : BigFppfOver B S hS} (g : V ⟶ W)
    (G : Subfunctor (yoneda.obj W)) (hG : IsClosedSubspace B S hS G)
    (hG' : IsClosedSubspace B S hS (G.preimage (yoneda.map g))) :
    ∃ m : closedChartObj B S hS (G.preimage (yoneda.map g)) hG' ⟶
        closedChartObj B S hS G hG,
      IsPullback m (closedChartHom B S hS (G.preimage (yoneda.map g)) hG')
        (closedChartHom B S hS G hG) g := by
  have he₀ : IsIso (hG.2.rep.fst (𝟙 (yoneda.obj W))) := isIso_rep_fst_id B S hS G hG
  have he₁ : IsIso (hG'.2.rep.fst (𝟙 (yoneda.obj V))) := isIso_rep_fst_id B S hS _ hG'
  have hGι : G.ι = inv (hG.2.rep.fst (𝟙 (yoneda.obj W))) ≫
      yoneda.map (closedChartHom B S hS G hG) := by
    rw [← rep_fst_id_comp_ι B S hS G hG, IsIso.inv_hom_id_assoc]
  have hsq0 : IsPullback (G.fromPreimage (yoneda.map g))
      (G.preimage (yoneda.map g)).ι
      (inv (hG.2.rep.fst (𝟙 (yoneda.obj W))) ≫
        yoneda.map (closedChartHom B S hS G hG)) (yoneda.map g) := by
    rw [← hGι]; exact Subfunctor.isPullback_preimage (yoneda.map g) G
  have hsq1 := isPullback_iso_vertex (isPullback_comp_isIso_right hsq0)
    (asIso (hG'.2.rep.fst (𝟙 (yoneda.obj V))))
  rw [show (asIso (hG'.2.rep.fst (𝟙 (yoneda.obj V)))).hom ≫ (G.preimage (yoneda.map g)).ι =
      yoneda.map (closedChartHom B S hS (G.preimage (yoneda.map g)) hG') from
    rep_fst_id_comp_ι B S hS _ hG'] at hsq1
  refine ⟨Yoneda.fullyFaithful.preimage
      ((asIso (hG'.2.rep.fst (𝟙 (yoneda.obj V)))).hom ≫
        G.fromPreimage (yoneda.map g) ≫ inv (hG.2.rep.fst (𝟙 (yoneda.obj W)))),
    IsPullback.of_map_of_faithful yoneda ?_⟩
  rw [Functor.FullyFaithful.map_preimage]
  exact hsq1

/-- The cutting-out ideal of the inverse image of a closed subspace contains the extension of
the cutting-out ideal of the subspace. -/
theorem map_closedChartIdeal_le {V W : BigFppfOver B S hS} (g : V ⟶ W)
    (G : Subfunctor (yoneda.obj W)) (hG : IsClosedSubspace B S hS G)
    (hG' : IsClosedSubspace B S hS (G.preimage (yoneda.map g))) :
    Ideal.map ((BigFppfOver.toScheme B S hS).map g).appTop.hom
        (closedChartIdeal B S hS G hG) ≤
      closedChartIdeal B S hS (G.preimage (yoneda.map g)) hG' := by
  obtain ⟨m, hsq⟩ := exists_isPullback_closedChartHom B S hS g G hG hG'
  have hmap := congrArg (BigFppfOver.toScheme B S hS).map hsq.w
  rw [Functor.map_comp, Functor.map_comp] at hmap
  have happ := congrArg (fun t : _ ⟶ _ ↦ Scheme.Hom.appTop t) hmap
  simp only [Scheme.Hom.comp_appTop] at happ
  refine Ideal.map_le_iff_le_comap.2 fun a ha ↦ ?_
  have ha0 : ((BigFppfOver.toScheme B S hS).map
      (closedChartHom B S hS G hG)).appTop.hom a = 0 := ha
  have := congr($happ a)
  simp only [CommRingCat.comp_apply] at this
  exact RingHom.mem_ker.2 (by rw [← this, ha0, map_zero])

/-- The inverse image of a closed subspace of a representable under a morphism of the site is a
closed subspace. -/
private theorem isClosedSubspace_preimage_yoneda_map {V W : BigFppfOver B S hS} (g : V ⟶ W)
    (G : Subfunctor (yoneda.obj W)) (hG : IsClosedSubspace B S hS G) :
    IsClosedSubspace B S hS (G.preimage (yoneda.map g)) :=
  isClosedSubspace_preimage B S hS (yoneda.map g) G
    (isAlgebraicSpace_yoneda B S hS W) (isAlgebraicSpace_yoneda B S hS V) hG

/-- The Yoneda-lemma correspondent of a morphism `s` of the site is `yoneda.map s`. -/
private theorem yonedaEquiv_symm_eq_yoneda_map {V W : BigFppfOver B S hS} (s : V ⟶ W) :
    (yonedaEquiv.symm s : yoneda.obj V ⟶ yoneda.obj W) = yoneda.map s :=
  yonedaEquiv.injective (by rw [Equiv.apply_symm_apply, yonedaEquiv_yoneda_map])

/-! ### From a finite-order thickening to the vanishing of a power -/

/-- **One half of the chart description of the completion.** If the inverse image of a closed
subspace along a scheme-valued point of the ambient representable is universally an `n`th-order
thickening, then the `(n+1)`st power of the cutting-out ideal is killed by pullback of regular
functions along that point. -/
theorem pow_closedChartIdeal_le_ker {V W : BigFppfOver B S hS} (g : V ⟶ W)
    (G : Subfunctor (yoneda.obj W)) (hG : IsClosedSubspace B S hS G) {n : ℕ}
    (h : IsUniversalNthOrderThickening B S hS n V (G.preimage (yoneda.map g))) :
    closedChartIdeal B S hS G hG ^ (n + 1) ≤
      RingHom.ker ((BigFppfOver.toScheme B S hS).map g).appTop.hom := by
  have hG' := isClosedSubspace_preimage_yoneda_map B S hS g G hG
  have hth := h.isNthOrderThickening B S hS
  have hzero : closedChartIdeal B S hS (G.preimage (yoneda.map g)) hG' ^ (n + 1) = ⊥ := by
    rw [← definingIdealAt_idChart B S hS (G.preimage (yoneda.map g)) hG']
    exact hth.2 (idChart B S hS V)
  refine (Ideal.map_eq_bot_iff_le_ker _).1 (le_antisymm ?_ bot_le)
  rw [Ideal.map_pow, ← hzero]
  exact Ideal.pow_right_mono (map_closedChartIdeal_le B S hS g G hG hG') _


/-! ### The cutting-out ideal over an affine chart -/

/-- **The cutting-out ideal of the inverse image of a closed subspace, over affine charts.**
Over affine objects of the site the inverse image of a closed subspace is cut out by the
extension of the cutting-out ideal of the subspace. -/
theorem closedChartIdeal_preimage_of_isAffine {V W : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj W)] (g : V ⟶ W)
    (G : Subfunctor (yoneda.obj W)) (hG : IsClosedSubspace B S hS G)
    (hG' : IsClosedSubspace B S hS (G.preimage (yoneda.map g))) :
    closedChartIdeal B S hS (G.preimage (yoneda.map g)) hG' =
      Ideal.map ((BigFppfOver.toScheme B S hS).map g).appTop.hom
        (closedChartIdeal B S hS G hG) := by
  obtain ⟨m, hsq⟩ := exists_isPullback_closedChartHom B S hS g G hG hG'
  have hsqS := hsq.map (BigFppfOver.toScheme B S hS)
  have hci := isClosedImmersion_closedChartHom B S hS G hG
  rw [closedChartIdeal, closedChartIdeal, ← hsqS.isoPullback_hom_snd,
    Stacks.AlgebraicGeometry.ker_appTop_comp_iso,
    Stacks.AlgebraicGeometry.ker_appTop_pullback_snd]


/-! ### From the vanishing of a power to a finite-order thickening -/

/-- **Over an affine ambient chart, a vanishing power of the cutting-out ideal makes the
inverse image a thickening of that order.** The kernel ideal sheaf is computed on the affine
opens of the source, over each of which the inverse image is the base change of the subspace
along a morphism of affine schemes. -/
theorem ker_pow_eq_bot_closedChartHom_preimage {V W : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj W)] (g : V ⟶ W)
    (G : Subfunctor (yoneda.obj W)) (hG : IsClosedSubspace B S hS G)
    (hG' : IsClosedSubspace B S hS (G.preimage (yoneda.map g))) {n : ℕ}
    (hle : closedChartIdeal B S hS G hG ^ (n + 1) ≤
      RingHom.ker ((BigFppfOver.toScheme B S hS).map g).appTop.hom) :
    ((BigFppfOver.toScheme B S hS).map
      (closedChartHom B S hS (G.preimage (yoneda.map g)) hG')).ker ^ (n + 1) = ⊥ := by
  obtain ⟨m, hsq⟩ := exists_isPullback_closedChartHom B S hS g G hG hG'
  have hsqS := hsq.map (BigFppfOver.toScheme B S hS)
  have hci₀ : _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map
      (closedChartHom B S hS G hG)) := isClosedImmersion_closedChartHom B S hS G hG
  have hci₁ : _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map
      (closedChartHom B S hS (G.preimage (yoneda.map g)) hG')) :=
    isClosedImmersion_closedChartHom B S hS (G.preimage (yoneda.map g)) hG'
  refine Scheme.ker_pow_eq_bot_of_forall_affineOpens _ fun V₀ ↦ ?_
  have hV₀ : IsAffine V₀.1.toScheme := V₀.2
  refine ⟨pullback V₀.1.ι ((BigFppfOver.toScheme B S hS).map
      (closedChartHom B S hS (G.preimage (yoneda.map g)) hG')),
    pullback.fst _ _, pullback.snd _ _, IsPullback.of_hasPullback _ _, ?_⟩
  have hpaste := (IsPullback.of_hasPullback V₀.1.ι ((BigFppfOver.toScheme B S hS).map
    (closedChartHom B S hS (G.preimage (yoneda.map g)) hG'))).flip.paste_horiz hsqS
  rw [← hpaste.isoPullback_hom_snd, Stacks.AlgebraicGeometry.ker_appTop_comp_iso,
    Stacks.AlgebraicGeometry.ker_appTop_pullback_snd, ← Ideal.map_pow]
  refine (Ideal.map_eq_bot_iff_le_ker _).2 fun a ha ↦ RingHom.mem_ker.2 ?_
  have ha' : ((BigFppfOver.toScheme B S hS).map g).appTop.hom a = 0 :=
    RingHom.mem_ker.1 (hle ha)
  rw [Scheme.Hom.comp_appTop]
  show V₀.1.ι.appTop.hom (((BigFppfOver.toScheme B S hS).map g).appTop.hom a) = 0
  rw [ha', map_zero]

/-- The property of being represented by `n`th-order thickenings is the corresponding property
of the closed immersion of schemes cutting out the subspace. -/
theorem isRepresentedNthOrder_iff {V : BigFppfOver B S hS} (G : Subfunctor (yoneda.obj V))
    (hG : IsClosedSubspace B S hS G) {n : ℕ} :
    IsRepresentedAtOrder B S hS n G ↔
      thickOrder.{u} n
        ((BigFppfOver.toScheme B S hS).map (closedChartHom B S hS G hG)) := by
  have he₀ : IsIso (hG.2.rep.fst (𝟙 (yoneda.obj V))) := isIso_rep_fst_id B S hS G hG
  rw [← BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS (thickOrder.{u} n)
      (closedChartHom B S hS G hG),
    ← rep_fst_id_comp_ι B S hS G hG]
  exact (MorphismProperty.cancel_left_of_respectsIso
    (MorphismProperty.presheaf
      (MorphismProperty.inverseImage (thickOrder.{u} n) (BigFppfOver.toScheme B S hS)))
    (hG.2.rep.fst (𝟙 (yoneda.obj V))) G.ι).symm

/-- **The second half of the chart description of the completion.** Over an affine ambient
chart, a scheme-valued point killing a power of the cutting-out ideal has inverse image a
universal thickening of the corresponding order. -/
theorem isUniversalNthOrderThickening_of_pow_le_ker {V W : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj W)] (g : V ⟶ W)
    (G : Subfunctor (yoneda.obj W)) (hG : IsClosedSubspace B S hS G) {n : ℕ}
    (hle : closedChartIdeal B S hS G hG ^ (n + 1) ≤
      RingHom.ker ((BigFppfOver.toScheme B S hS).map g).appTop.hom) :
    IsUniversalNthOrderThickening B S hS n V (G.preimage (yoneda.map g)) := by
  have hG' := isClosedSubspace_preimage_yoneda_map B S hS g G hG
  refine isUniversalNthOrderThickening_of_isRepresentedAtOrder B S hS n _ hG' ?_
  refine (isRepresentedNthOrder_iff B S hS (G.preimage (yoneda.map g)) hG').2 ?_
  exact ⟨isClosedImmersion_closedChartHom B S hS (G.preimage (yoneda.map g)) hG',
    ker_pow_eq_bot_closedChartHom_preimage B S hS g G hG hG' hle⟩


/-! ### The infinitesimal neighbourhoods of an affine chart -/

open FormalSpace

/-- The closed immersion of the site from the closed subscheme of an ideal `K ⊆ A` into the
affine chart `Spec A`. -/
def quotientToAffineOver {A : Type u} [CommRing A] (str : Spec (.of A) ⟶ S)
    (hA : B.Contains (Spec (.of A))) (K : Ideal A) :
    (BigAffineFppf.inclusion B S hS).obj (quotientOver B S hS str hA K) ⟶
      affineOver B S hS hA str :=
  Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K))))
    (by apply ObjectProperty.hom_ext; rfl)

/-- The morphism of schemes underlying `quotientToAffineOver` is `Spec` of the quotient map
`A → A ⧸ K`. -/
@[simp] theorem toScheme_map_quotientToAffineOver {A : Type u} [CommRing A]
    (str : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A))) (K : Ideal A) :
    (BigFppfOver.toScheme B S hS).map (quotientToAffineOver B S hS str hA K) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K)) := rfl

/-- The scheme underlying the affine chart `affineOver` of `Spec A` is affine. -/
instance isAffine_toScheme_obj_affineOver {A : Type u} [CommRing A]
    (str : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A))) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj (affineOver B S hS hA str)) :=
  inferInstanceAs (IsAffine (Spec (CommRingCat.of A)))

/-- The cutting-out ideal of a closed subspace of the affine chart `Spec A`, read in the ring
of regular functions of `Spec A`. -/
def affineClosedChartIdeal {A : Type u} [CommRing A] (str : Spec (.of A) ⟶ S)
    (hA : B.Contains (Spec (.of A)))
    (G : Subfunctor (yoneda.obj (affineOver B S hS hA str)))
    (hG : IsClosedSubspace B S hS G) : Ideal Γ(Spec (CommRingCat.of A), ⊤) :=
  closedChartIdeal B S hS G hG

/-- The ideal of `A` cutting out a closed subspace of the affine chart `Spec A`. -/
def closedChartRingIdeal {A : Type u} [CommRing A] (str : Spec (.of A) ⟶ S)
    (hA : B.Contains (Spec (.of A)))
    (G : Subfunctor (yoneda.obj (affineOver B S hS hA str)))
    (hG : IsClosedSubspace B S hS G) : Ideal A :=
  Ideal.map (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom
    (affineClosedChartIdeal B S hS str hA G hG)

/-- Pulling back the `n`-th power of `closedChartRingIdeal` along the isomorphism
`Γ(Spec A, ⊤) ≅ A` gives the `n`-th power of `affineClosedChartIdeal`. -/
theorem comap_closedChartRingIdeal {A : Type u} [CommRing A] (str : Spec (.of A) ⟶ S)
    (hA : B.Contains (Spec (.of A)))
    (G : Subfunctor (yoneda.obj (affineOver B S hS hA str)))
    (hG : IsClosedSubspace B S hS G) (n : ℕ) :
    Ideal.comap (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom
        (closedChartRingIdeal B S hS str hA G hG ^ n) =
      affineClosedChartIdeal B S hS str hA G hG ^ n := by
  have hbij := ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).hom
  rw [closedChartRingIdeal, ← Ideal.map_pow,
    Ideal.comap_map_of_surjective _ hbij.2]
  refine sup_eq_left.2 fun x hx ↦ ?_
  have hx0 : (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom x =
      (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom 0 := by
    simpa using hx
  rw [hbij.1 hx0]
  exact Submodule.zero_mem _

/-- The kernel on global sections of the closed immersion cutting out the `K`-neighbourhood is
the cutting-out ideal of `K` read on the chart. -/
theorem ker_appTop_quotientToAffineOver {A : Type u} [CommRing A] (str : Spec (.of A) ⟶ S)
    (hA : B.Contains (Spec (.of A))) (K : Ideal A) :
    RingHom.ker ((BigFppfOver.toScheme B S hS).map
        (quotientToAffineOver B S hS str hA K)).appTop.hom =
      Ideal.comap (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom K := by
  have h := _root_.AlgebraicGeometry.ker_appTop_spec_map
    (CommRingCat.ofHom (Ideal.Quotient.mk K))
  simp only [CommRingCat.hom_ofHom, Ideal.mk_ker] at h
  exact h

/-! ### The chart description of the union of the infinitesimal neighbourhoods -/

/-- **A point factoring through an infinitesimal neighbourhood lies in the completion
subfunctor.** -/
theorem mem_completionSubspaceSubfunctor_of_factor {A : Type u} [CommRing A]
    (str : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
    (G : Subfunctor (yoneda.obj (affineOver B S hS hA str)))
    (hG : IsClosedSubspace B S hS G) {V : BigFppfOver B S hS} (n : ℕ)
    (t : V ⟶ (BigAffineFppf.inclusion B S hS).obj
      (quotientOver B S hS str hA
        (closedChartRingIdeal B S hS str hA G hG ^ (n + 1)))) :
    (ULift.up (t ≫ quotientToAffineOver B S hS str hA
          (closedChartRingIdeal B S hS str hA G hG ^ (n + 1))) :
        ((yoneda.obj (affineOver B S hS hA str)) ⋙
          uliftFunctor.{u + 1}).obj (op V)) ∈
      (completionSubspaceSubfunctor B S hS
        ((schemeSpaceFunctor B S hS).obj (affineOver B S hS hA str)) G).obj
          (op V) := by
  have hker : closedChartIdeal B S hS G hG ^ (n + 1) ≤
      RingHom.ker ((BigFppfOver.toScheme B S hS).map (t ≫ quotientToAffineOver B S hS str hA
        (closedChartRingIdeal B S hS str hA G hG ^ (n + 1)))).appTop.hom := by
    have h₁ : RingHom.ker ((BigFppfOver.toScheme B S hS).map
        (quotientToAffineOver B S hS str hA
          (closedChartRingIdeal B S hS str hA G hG ^ (n + 1)))).appTop.hom ≤
        RingHom.ker ((BigFppfOver.toScheme B S hS).map (t ≫ quotientToAffineOver B S hS str hA
          (closedChartRingIdeal B S hS str hA G hG ^ (n + 1)))).appTop.hom := by
      rw [Functor.map_comp, Scheme.Hom.comp_appTop]
      intro a ha
      refine RingHom.mem_ker.2 ?_
      show ((BigFppfOver.toScheme B S hS).map t).appTop.hom
        (((BigFppfOver.toScheme B S hS).map (quotientToAffineOver B S hS str hA
          (closedChartRingIdeal B S hS str hA G hG ^ (n + 1)))).appTop.hom a) = 0
      rw [RingHom.mem_ker.1 ha, map_zero]
    refine le_trans ?_ h₁
    rw [ker_appTop_quotientToAffineOver,
      comap_closedChartRingIdeal B S hS str hA G hG (n + 1)]
    exact le_rfl
  refine ⟨n, ?_⟩
  have key := isUniversalNthOrderThickening_of_pow_le_ker B S hS
    (t ≫ quotientToAffineOver B S hS str hA
      (closedChartRingIdeal B S hS str hA G hG ^ (n + 1))) G hG hker
  rwa [← yonedaEquiv_symm_eq_yoneda_map] at key


/-! ### Factoring a point of an affine chart through an infinitesimal neighbourhood -/

/-- A morphism into an affine scheme is its canonical morphism to the spectrum of its ring of
regular functions followed by the spectrum of the induced ring map. -/
theorem toSpecΓ_comp_specMap_appTop {X : Scheme.{u}} {R : CommRingCat.{u}} (f : X ⟶ Spec R) :
    X.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso R).inv ≫ f.appTop) = f := by
  rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
    AlgebraicGeometry.toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

/-- **A point of the completion subfunctor of an affine chart factors through an infinitesimal
neighbourhood.** -/
theorem exists_factor_of_mem_completionSubspaceSubfunctor {A : Type u} [CommRing A]
    (str : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
    (G : Subfunctor (yoneda.obj (affineOver B S hS hA str)))
    (hG : IsClosedSubspace B S hS G) {V : BigFppfOver B S hS}
    (s : V ⟶ affineOver B S hS hA str)
    (hs : (ULift.up s : ((yoneda.obj (affineOver B S hS hA str)) ⋙
        uliftFunctor.{u + 1}).obj (op V)) ∈
      (completionSubspaceSubfunctor B S hS
        ((schemeSpaceFunctor B S hS).obj (affineOver B S hS hA str)) G).obj (op V)) :
    ∃ (n : ℕ) (t : V ⟶ (BigAffineFppf.inclusion B S hS).obj
        (quotientOver B S hS str hA (closedChartRingIdeal B S hS str hA G hG ^ (n + 1)))),
      t ≫ quotientToAffineOver B S hS str hA
        (closedChartRingIdeal B S hS str hA G hG ^ (n + 1)) = s := by
  obtain ⟨n, hn⟩ := hs
  have hn' : IsUniversalNthOrderThickening B S hS n V (G.preimage (yoneda.map s)) := by
    rwa [← yonedaEquiv_symm_eq_yoneda_map] 
  have hle := pow_closedChartIdeal_le_ker B S hS s G hG hn'
  refine ⟨n, ?_⟩
  -- the ring map induced by `s`, and the ideal it kills
  set sS : (BigFppfOver.toScheme B S hS).obj V ⟶ Spec (CommRingCat.of A) :=
    (BigFppfOver.toScheme B S hS).map s with hsS
  set φ : CommRingCat.of A ⟶ Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ sS.appTop with hφ
  have hK : closedChartRingIdeal B S hS str hA G hG ^ (n + 1) ≤ RingHom.ker φ.hom := by
    rw [closedChartRingIdeal, ← Ideal.map_pow]
    refine Ideal.map_le_iff_le_comap.2 fun b hb ↦ ?_
    refine RingHom.mem_ker.2 ?_
    have hb0 : sS.appTop.hom b = 0 := RingHom.mem_ker.1 (hle hb)
    have hinv : (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
        ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom b) = b := by
      rw [← RingHom.comp_apply, ← CommRingCat.hom_comp,
        (Scheme.ΓSpecIso (CommRingCat.of A)).hom_inv_id, CommRingCat.hom_id,
        RingHom.id_apply]
    show sS.appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
        ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom b)) = 0
    rw [hinv, hb0]
  -- the factorization on rings, and the induced morphism of schemes
  set ψ : CommRingCat.of (A ⧸ closedChartRingIdeal B S hS str hA G hG ^ (n + 1)) ⟶
      Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) :=
    CommRingCat.ofHom (Ideal.Quotient.lift _ φ.hom fun a ha ↦ RingHom.mem_ker.1 (hK ha))
      with hψ
  have hmkψ : CommRingCat.ofHom (Ideal.Quotient.mk
      (closedChartRingIdeal B S hS str hA G hG ^ (n + 1))) ≫ ψ = φ := by
    ext a
    rfl
  have hfac : (((BigFppfOver.toScheme B S hS).obj V).toSpecΓ ≫ Spec.map ψ) ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (closedChartRingIdeal B S hS str hA G hG ^ (n + 1)))) =
      sS := by
    rw [Category.assoc, ← Spec.map_comp, hmkψ, hφ, toSpecΓ_comp_specMap_appTop]
  have hw : (((BigFppfOver.toScheme B S hS).obj V).toSpecΓ ≫ Spec.map ψ) ≫
      B.inclusion.map ((BigAffineFppf.inclusion B S hS).obj
        (quotientOver B S hS str hA
          (closedChartRingIdeal B S hS str hA G hG ^ (n + 1)))).hom =
      B.inclusion.map V.hom := by
    have hws : sS ≫ str = B.inclusion.map V.hom := by
      rw [hsS, ← Over.w s]
      rfl
    show (((BigFppfOver.toScheme B S hS).obj V).toSpecΓ ≫ Spec.map ψ) ≫
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (closedChartRingIdeal B S hS str hA G hG ^ (n + 1)))) ≫ str) = _
    rw [← Category.assoc, hfac]
    exact hws
  obtain ⟨t, ht⟩ := BigFppfOver.exists_hom_of_comp_eq B S hS
    (X := V)
    (Y := (BigAffineFppf.inclusion B S hS).obj
      (quotientOver B S hS str hA (closedChartRingIdeal B S hS str hA G hG ^ (n + 1))))
    (((BigFppfOver.toScheme B S hS).obj V).toSpecΓ ≫ Spec.map ψ) hw
  refine ⟨t, ?_⟩
  refine (BigFppfOver.toScheme B S hS).map_injective ?_
  rw [Functor.map_comp, ht, toScheme_map_quotientToAffineOver]
  exact hfac


/-- The abstract sheafification functor is the explicit one. -/
def presheafToSheafIsoPlusPlus :
    presheafToSheaf (BigFppfOver.topology B S hS) (Type (u + 1)) ≅
      plusPlusSheaf (BigFppfOver.topology B S hS) (Type (u + 1)) :=
  Adjunction.leftAdjointUniq (sheafificationAdjunction _ _) (plusPlusAdjunction _ _)




/-! ### The completion of an affine chart is the completion along the cutting-out ideal -/

/-- The closed immersions of the infinitesimal neighbourhoods into the chart are compatible
with the transitions between the neighbourhoods. -/
theorem quotientOverTransition_comp_quotientToAffineOver {A : Type u} [CommRing A]
    (str : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A))) {J K : Ideal A} (h : J ≤ K) :
    (BigAffineFppf.inclusion B S hS).map (quotientOverTransition B S hS str hA h) ≫
        quotientToAffineOver B S hS str hA J =
      quotientToAffineOver B S hS str hA K := by
  refine (BigFppfOver.toScheme B S hS).map_injective ?_
  rw [Functor.map_comp]
  show Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h)) ≫
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) =
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K))
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, Ideal.Quotient.factor_comp_mk]


/-- The closed immersions of the infinitesimal neighbourhoods into the chart are
monomorphisms. -/
theorem mono_quotientToAffineOver {A : Type u} [CommRing A] (str : Spec (.of A) ⟶ S)
    (hA : B.Contains (Spec (.of A))) (K : Ideal A) :
    Mono (quotientToAffineOver B S hS str hA K) := by
  have hci : _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map
      (quotientToAffineOver B S hS str hA K)) :=
    _root_.AlgebraicGeometry.IsClosedImmersion.spec_of_surjective _
      Ideal.Quotient.mk_surjective
  have hmono : Mono ((BigFppfOver.toScheme B S hS).map
      (quotientToAffineOver B S hS str hA K)) := inferInstance
  exact (BigFppfOver.toScheme B S hS).mono_of_mono_map hmono

section Colimit

variable {A : Type u} [CommRing A] (str : Spec (.of A) ⟶ S)
  (hA : B.Contains (Spec (.of A)))
  (G : Subfunctor (yoneda.obj (affineOver B S hS hA str)))
  (hG : IsClosedSubspace B S hS G)

/-- The diagram of infinitesimal neighbourhoods of a closed subspace of an affine chart, read
in presheaves of `Type (u + 1)`. -/
abbrev chartNeighbourhoodDiagram :
    ULift.{u + 1} ℕ ⥤ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)) :=
  infinitesimalNeighbourhoodDiagram B S hS str hA
      (closedChartRingIdeal B S hS str hA G hG) ⋙
    BigAffineFppf.inclusion B S hS ⋙ uliftYoneda.{u + 1}

/-- The union of the infinitesimal neighbourhoods of a closed subspace of an affine chart, as
a subfunctor of the universe lift of the chart. -/
def chartUnionSubfunctor : Subfunctor (uliftYoneda.{u + 1}.obj (affineOver B S hS hA str)) :=
  completionSubspaceSubfunctor B S hS
    ((schemeSpaceFunctor B S hS).obj (affineOver B S hS hA str)) G

/-- The union of the infinitesimal neighbourhoods, as a presheaf. -/
abbrev chartUnionFunctor : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1) :=
  (chartUnionSubfunctor B S hS str hA G).toFunctor

/-- The `n`-th leg of the cocone exhibiting the union of the infinitesimal neighbourhoods as
their colimit: the `n`-th neighbourhood sits inside the union. -/
def chartNeighbourhoodLeg (n : ULift.{u + 1} ℕ) :
    (chartNeighbourhoodDiagram B S hS str hA G hG).obj n ⟶
      chartUnionFunctor B S hS str hA G :=
  Subfunctor.lift (uliftYoneda.{u + 1}.map (quotientToAffineOver B S hS str hA
      (closedChartRingIdeal B S hS str hA G hG ^ (n.down + 1)))) (by
    intro V x hx
    obtain ⟨y, rfl⟩ := hx
    exact mem_completionSubspaceSubfunctor_of_factor B S hS str hA G hG n.down y.down)

/-- The leg `chartNeighbourhoodLeg n`, followed by the inclusion of the union into the chart, is
the Yoneda image of the closed immersion cut out by the `(n + 1)`-st power of
`closedChartRingIdeal`. -/
@[reassoc] theorem chartNeighbourhoodLeg_ι (n : ULift.{u + 1} ℕ) :
    chartNeighbourhoodLeg B S hS str hA G hG n ≫
        (chartUnionSubfunctor B S hS str hA G).ι =
      uliftYoneda.{u + 1}.map (quotientToAffineOver B S hS str hA
        (closedChartRingIdeal B S hS str hA G hG ^ (n.down + 1))) := rfl

/-- The cocone over the diagram of infinitesimal neighbourhoods whose vertex is their union
inside the chart. -/
def chartNeighbourhoodCocone :
    Limits.Cocone (chartNeighbourhoodDiagram B S hS str hA G hG) :=
  Limits.Cocone.mk (chartUnionFunctor B S hS str hA G)
    { app := chartNeighbourhoodLeg B S hS str hA G hG
      naturality := fun {n m} g ↦ by
        have hnm0 : n ≤ m := leOfHom g
        have hnm : n.down ≤ m.down := hnm0
        have hle : closedChartRingIdeal B S hS str hA G hG ^ (m.down + 1) ≤
            closedChartRingIdeal B S hS str hA G hG ^ (n.down + 1) :=
          Ideal.pow_le_pow_right (by omega)
        have key := congrArg uliftYoneda.{u + 1}.map
          (quotientOverTransition_comp_quotientToAffineOver B S hS str hA hle)
        rw [Functor.map_comp] at key
        refine (cancel_mono (chartUnionSubfunctor B S hS str hA G).ι).1 ?_
        exact key }


/-- The neighbourhood a section of the union is chosen to factor through. -/
def chartUnionIndex {V : (BigFppfOver B S hS)ᵒᵖ}
    (x : (chartUnionFunctor B S hS str hA G).obj V) : ℕ :=
  (exists_factor_of_mem_completionSubspaceSubfunctor B S hS str hA G hG x.1.down x.2).choose

/-- The chosen factorization of a section of the union through a neighbourhood. -/
def chartUnionFactor {V : (BigFppfOver B S hS)ᵒᵖ}
    (x : (chartUnionFunctor B S hS str hA G).obj V) :
    V.unop ⟶ (BigAffineFppf.inclusion B S hS).obj (quotientOver B S hS str hA
      (closedChartRingIdeal B S hS str hA G hG ^
        (chartUnionIndex B S hS str hA G hG x + 1))) :=
  (exists_factor_of_mem_completionSubspaceSubfunctor B S hS str hA G hG
    x.1.down x.2).choose_spec.choose

/-- The chosen factorization `chartUnionFactor x`, followed by the closed immersion of the
neighbourhood into the chart, recovers the section `x`. -/
theorem chartUnionFactor_spec {V : (BigFppfOver B S hS)ᵒᵖ}
    (x : (chartUnionFunctor B S hS str hA G).obj V) :
    chartUnionFactor B S hS str hA G hG x ≫ quotientToAffineOver B S hS str hA
        (closedChartRingIdeal B S hS str hA G hG ^
          (chartUnionIndex B S hS str hA G hG x + 1)) = x.1.down :=
  (exists_factor_of_mem_completionSubspaceSubfunctor B S hS str hA G hG
    x.1.down x.2).choose_spec.choose_spec

end Colimit

end AlgebraicGeometry.Space

end
